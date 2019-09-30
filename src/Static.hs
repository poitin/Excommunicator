module Main where 

import MCalculus
import PSL
import Evaluate
import Time
import Verify
import Debug.Trace 
import Directory
import System
import System.IO
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language

spec = emptyDef
       { commentStart    = "/*"
       , commentEnd      = "*/"
       , commentLine     = "--"
       , nestedComments  = True
       , reservedNames   = ["DEFINITIONS","ENDD","SYSTEM","ENDS","PROPERTIES","ENDP"]
       , caseSensitive   = True
       }

speclexer = T.makeTokenParser spec

reserve   = T.reserved speclexer

specification = do
                ds <-     do
                          reserve "DEFINITIONS"
                          ds <- many definition
                          reserve "ENDD"
                          return ds
                      <|> do
                          spaces
                          return []
                reserve "SYSTEM"
                p <- compoundprocess
                reserve "ENDS"
                ps <-     do
                          reserve "PROPERTIES"
                          ps <- many stochasticproperty
                          reserve "ENDP"
                          return ps
                      <|> do
                          spaces
                          return []
                return (addlets p ds [],ps)

parseSpecification input = parse specification "" input

checkprop p (n,prop) = do 
                       putStrLn ("Property " ++ show n ++ ": " ++ show prop)
                       if   (prove prop p (Finite 0,Finite 0) []) then putStrLn "Property satisfied " else putStrLn "Property violated"

main :: IO ()
main = do
       args <- getArgs
       file <- readFile (head args)
       case parseSpecification file of
          Left s -> error ("Could not parse M-Calculus specification in file "++file)
          Right (p,ps) -> do 
                          case ps of
                             [] -> error "No properties to verify"
                             ps -> let q = simplify (eval p (free p) [] Null)
                                   in  mapM_ (checkprop q) (zip [1..] ps)
