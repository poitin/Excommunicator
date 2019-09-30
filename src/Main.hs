
module Main where 

import MCalculus
import PSL
import Evaluate
import Time
import Verify
import Debug.Trace 
import System.Directory
import System.IO
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language

data Command = Load String 
             | Proc
             | Evaluate
             | Properties
             | Verify
             | Help 
             | Quit 
             | Unknown 

command str = let res = words str
              in case res of 
                   [":load",f] -> Load f
                   [":process"] -> Proc
                   [":evaluate"] -> Evaluate
                   [":properties"] -> Properties
                   [":verify"] -> Verify
                   [":help"] -> Help
                   [":quit"] -> Quit
                   _ -> Unknown

help_message = "\n:load filename\t\tTo load a file\n"++
               ":process\t\tTo show the current process\n"++
               ":evaluate\t\tTo evaluate the current process\n"++
               ":properties\t\tTo show the current properties\n"++
               ":verify\t\t\tTo verify the current process\n"++
               ":help\t\t\tTo print this message\n"++
               ":quit\t\t\tTo quit\n"

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

showprop (n,prop) = do 
                    putStrLn ("Property " ++ show n ++ ": " ++ show prop)

checkprop p (n,prop) = do 
                       putStrLn ("Property " ++ show n ++ ": " ++ show prop)
                       if   (prove prop p (Finite 0,Finite 0) []) then putStrLn "Property satisfied " else putStrLn "Property violated"

main = toplevel Nothing []

toplevel process properties = do putStr "Master> "
                                 hFlush stdout
                                 x <- getLine
                                 case (command x) of 
                                    Load f -> let f' = f++".M"
                                              in  do x <- doesFileExist f'
                                                     if   x 
                                                          then do
                                                               res <- readFile f'
                                                               case parseSpecification res of 
                                                                  Left s -> do putStrLn ("Err: Could not parse M-Calculus specification in file "++f'++show s)
                                                                               toplevel process properties
                                                                  Right (p,ps) -> do putStrLn ("Loading file: "++f')
                                                                                     toplevel (Just p) ps
                                                          else do putStrLn ("No such file: "++f') 
                                                                  toplevel process properties
                                    Proc -> case process of 
                                               Nothing -> do putStrLn "No specification loaded" 
                                                             toplevel process properties
                                               Just p -> do putStrLn (show p)
                                                            toplevel process properties
                                    Evaluate -> case process of 
                                                   Nothing -> do putStrLn "No program loaded" 
                                                                 toplevel process properties
                                                   Just p -> let q = simplify (eval p (free p) [] Null)
                                                             in  toplevel (Just q) properties
                                    Properties -> case properties of
                                                     [] -> do putStrLn "No properties"
                                                              toplevel process properties
                                                     ps -> do mapM_ showprop (zip [1..] ps)
                                                              toplevel process properties
                                    Verify -> case process of
                                                 Nothing -> do putStrLn "No process loaded"
                                                               toplevel process properties
                                                 Just p -> case properties of
                                                              [] -> do putStrLn "No properties to verify"
                                                                       toplevel process properties
                                                              ps -> let q = simplify (eval p (free p) [] Null)
                                                                    in  do mapM_ (checkprop q) (zip [1..] ps)
                                                                           toplevel process properties
                                    Help -> do putStrLn help_message 
                                               toplevel process properties
                                    Quit -> return ()
                                    Unknown -> do putStrLn "Err: Could not parse command, type ':help' for a list of commands"
                                                  toplevel process properties

