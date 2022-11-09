{- Pi-Calculus Definition, Parser and Pretty Printer -}

module PiCalculus where

import Prelude hiding ((<>))
import Data.Char
import Data.List 
import Data.Maybe
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec hiding (labels)
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language

-- pi-calculus processes

data Process = Null -- null process
             | Input String String Process -- input action
             | Output String String Process -- output action
             | Tau Process -- silent action
             | New String Process -- restriction
             | Compose Process Process -- parallel composition
             | Compose' Process Process -- blazed parallel composition
             | Match String String Process -- match
             | Choice Process Process -- non-deterministic choice
             | Call String [String] -- named process application

instance Show Process where
   show p = render $ prettyProcess p

type Spec = (Process,[(String,([String],Process))])

showSpec :: (Process, [(String, ([String], Process))]) -> String
showSpec s = renderStyle (Style { lineLength = 100, ribbonsPerLine = 1.1, mode = PageMode }) $ prettySpec s

-- rename bound variable

renameVar fv x = if   x `elem` fv
                 then renameVar fv (x++"'")
                 else x

-- free names in a process

free p = nub (free' p)

free' Null = []
free' (Input x y p) = (x:free' p) \\ [y]
free' (Output x y p) = x:y:free' p
free' (Tau p) = free' p
free' (New x p) = free' p \\ [x]
free' (Compose p q) = free' p ++ free' q
free' (Compose' p q) = free' p ++ free' q
free' (Match x y p) = x:y:free' p
free' (Choice p q) = free' p ++ free' q
free' (Call f xs) = xs

-- rename names in a process

rename r Null = Null
rename r (Input x y p) = let (xs,ys) = unzip r
                         in   if   y `elem` xs++ys
                              then let y' = renameVar (xs++ys++free (Input x y p)) y
                                   in  Input (renameName r x) y' (rename r (rename [(y,y')] p))
                              else Input (renameName r x) y (rename r p)
rename r (Output x y p) = Output (renameName r x) (renameName r y) (rename r p)
rename r (Tau p) = Tau (rename r p)
rename r (New x p) = let (xs,ys) = unzip r
                     in   if   x `elem` xs++ys
                          then let x' = renameVar (xs++ys++free (New x p)) x
                               in  New x' (rename  r (rename [(x,x')] p))
                          else New x (rename r p)
rename r (Compose p q) = Compose (rename r p) (rename r q)
rename r (Compose' p q) = Compose' (rename r p) (rename r q)
rename r (Match x y p) = Match (renameName r x) (renameName r y) (rename r p)
rename r (Choice p q) = Choice (rename r p) (rename r q)
rename r (Call f xs) = Call f (map (renameName r) xs)

renameName r x = fromMaybe x (lookup x r)

-- determine whether processes are renamings of each other

renaming p q = renaming' p q []

renaming' Null Null r = [r]
renaming' (Input x y p) (Input x' y' q) r = concat [renaming' p q ((y,y'):r') | r' <- extend x x' r]
renaming' (Output x y p) (Output x' y' q) r = concat [renaming' p q r'' | r' <- extend x x' r, r'' <- extend y y' r']
renaming' (Tau p) (Tau q) r = renaming' p q r
renaming' (New x p) (New x' q) r = renaming' p q ((x,x'):r)
renaming' (Compose p q) (Compose p' q') r = concat [renaming' p p' r' | r' <- renaming' q q' r]
renaming' (Compose' p q) (Compose' p' q') r = concat [renaming' p p' r' | r' <- renaming' q q' r]
renaming' (Match x y p) (Match x' y' q) r = concat [renaming' p q r'' | r' <- extend x x' r, r'' <- extend y y' r']
renaming' (Choice p q) (Choice p' q') r = concat [renaming' p p' r' | r' <- renaming' q q' r]
renaming' (Call f xs) (Call f' xs') r | f==f' = foldr (\(x,x') rs -> concat [extend x x' r | r <- rs]) [r] (zip xs xs')
renaming' p q r = []

extend x x' r = if    x `elem` map fst r
                then [r | (x,x') `elem` r]
                else [(x,x'):r]

-- named processes in a specification

procs p d = procs' d p []

procs' d Null fs = fs
procs' d (Input x y p) fs = procs' d p fs
procs' d (Output x y p) fs = procs' d p fs
procs' d (Tau p) fs = procs' d p fs
procs' d (New x p) fs = procs' d p fs
procs' d (Compose p q) fs = procs' d p (procs' d q fs)
procs' d (Compose' p q) fs = procs' d p (procs' d q fs)
procs' d (Match x y p) fs = procs' d p fs
procs' d (Choice p q) fs = procs' d p (procs' d q fs)
procs' d (Call f xs) fs = if   f `elem` fs
                          then fs
                          else case lookup f d of
                                  Nothing -> f:fs
                                  Just (xs,p)  -> procs' d p (f:fs)

-- convert named process definitions to serial form

blaze Null = Null
blaze (Input x y p) = Input x y (blaze p)
blaze (Output x y p) = Output x y (blaze p)
blaze (Tau p) = Tau (blaze p)
blaze (New x p) = New x (blaze p)
blaze (Compose p q) = Compose' (blaze p) (blaze q)
blaze (Compose' p q) = Compose' (blaze p) (blaze q)
blaze (Match x y p) = Match x y (blaze p)
blaze (Choice p q) = Choice (blaze p) (blaze q)
blaze (Call f xs) = Call f xs

-- pretty print processes

prettyName x = let (s1,s2) = span (/= '\'') x
               in  if null s2 then text s1 else text s1 <> int (length s2)

prettyProcess Null = text "0"
prettyProcess (Input x y p) = prettyName x <> parens (prettyName y) <> text "." <> prettyProcess' p
prettyProcess (Output x y p) = prettyName x <> text "<" <> prettyName y <> text ">" <> text "." <> prettyProcess' p
prettyProcess (Tau p) = text "tau" <> text "." <> prettyProcess' p
prettyProcess (New x p) = parens (text "new" <+> prettyName x) <+> prettyProcess' p
prettyProcess (Compose p q) = prettyProcess' p <+> text "|" <+> prettyProcess' q
prettyProcess (Compose' p q) = prettyProcess' p <+> text "|" <+> prettyProcess' q
prettyProcess (Match x y p) = brackets(prettyName x <> text "=" <> prettyName y) <> prettyProcess' p
prettyProcess (Choice p q) = prettyProcess' p <+> text "+" <+> prettyProcess' q
prettyProcess (Call f xs) = prettyName f <> parens (hcat (punctuate comma (map prettyName xs))) 

prettyProcess' Null = text "0"
prettyProcess' (Input x y p) = prettyName x <> parens (prettyName y) <> text "." <> prettyProcess' p
prettyProcess' (Output x y p) = prettyName x <> text "<" <> prettyName y <> text ">" <> text "." <> prettyProcess' p
prettyProcess' (Tau p) = text "tau" <> text "." <> prettyProcess' p
prettyProcess' (New x p) = parens (text "new" <+> prettyName x) <+> prettyProcess' p
prettyProcess' (Match x y p) = brackets(prettyName x <> text "=" <> prettyName y) <> prettyProcess' p
prettyProcess' (Call f xs) = prettyName f <> parens (hcat (punctuate comma (map prettyName xs))) 
prettyProcess' p = parens (prettyProcess p)

prettySpec (p,d) = let d' = [def | def <- d, fst def `elem` procs p d]          
                   in  if null d' then prettyProcess p else prettyProcess p $$ text "where" $$ prettyEnv d'

prettyEnv d = vcat (punctuate semi $ map (\(f,(xs,p)) -> prettyName f <> parens(hcat (punctuate comma (map prettyName xs))) <+> equals <+> prettyProcess p) d)

-- lexing and parsing

mcalc = emptyDef
        { commentStart    = "/*"
        , commentEnd      = "*/"
        , commentLine     = "--"
        , nestedComments  = True
        , identStart      = lower         
        , identLetter     = letter <|> digit <|> oneOf "_'"
        , reservedNames   = ["new","tau","where"]
        , reservedOpNames = ["+","|",".","="]
        , caseSensitive   = True
        }

lexer = T.makeTokenParser mcalc

symbol     = T.symbol lexer
paren      = T.parens lexer
bracket    = T.brackets lexer
brace      = T.braces lexer
semic      = T.semi lexer
coma       = T.comma lexer
identifier = T.identifier lexer
reserved   = T.reserved lexer
reservedOp = T.reservedOp lexer

fun = do
      c <- upper
      cs <- many (letter <|> digit <|> oneOf "_'")
      spaces
      return (c:cs)

spec = do
       p <- process
       ds <- do
             reserved "where"
             ds <- sepBy1 definition semic
             eof
             return ds
         <|> do
             eof
             return []
       return (p,ds)

definition = do
             f <- fun
             xs <- paren (sepBy identifier coma)
             symbol "="
             p <- process
             return (f,(xs,blaze p))

process = buildExpressionParser prec simple

prec = [ [ compose ],
        [ choice ]
        ]
        where
        compose = Infix (do
                         reservedOp "+"
                         return Choice
                        ) AssocRight 
        choice = Infix (do 
                        reservedOp "|"
                        return Compose
                       ) AssocRight
 
simple =     do
              symbol "0"
              return Null
         <|> do
             x <- identifier
             p <- do 
                  symbol "("
                  y <- identifier
                  symbol ")"
                  reservedOp "."
                  Input x y <$> process
              <|> do
                  symbol "<"
                  y <- identifier
                  symbol ">"
                  reservedOp "."
                  Output x y <$> process
             return p
         <|> do
             symbol "("
             p <- do
                  reserved "new"
                  x <- identifier
                  symbol ")"
                  New x <$> process
              <|> do
                  p <- process
                  symbol ")"
                  return p
             return p
                  
         <|> do
             symbol "["
             x <- identifier
             reservedOp "="
             y <- identifier
             symbol "]"
             Match x y <$> process
         <|> do
             reserved "tau"
             symbol "."
             Tau <$> process
         <|> do
             f <- fun
             xs <- paren (sepBy identifier coma)
             return (Call f xs)
             

parseSpec = parse spec "Parse error"