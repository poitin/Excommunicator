{- M-Calculus Definition, Parser and Pretty Printer -}

module MCalculus where

import Data.Char
import Data.List 
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language

import Debug.Trace 

rename bs a = if   a `elem` bs
              then rename bs (a++"'")
              else a

data Name = Free String
          | Bound Int
            deriving Eq

instance Show Name where
   show n = render (prettyName n)

prettyName (Free a) = text a
prettyName (Bound i) = (text "#") <> (int i)

freeName (Free a) = [a]
freeName (Bound i) = []

boundName d (Free a) = []
boundName d (Bound i) = if   i>=d
                        then [i-d]
                        else []

shiftName i d (Free a) = Free a
shiftName i d (Bound j) = if j >= d then Bound (j+i) else Bound j

substName i n (Free a) = Free a
substName i n (Bound j) = if   j<i
                           then Bound j
                           else if   i==j
                                then shiftName i 0 n
                                else Bound (j-1)

abstractName i x (Free a) = if a==x then Bound i else Free a
abstractName i x (Bound j) = if j>=i then Bound (j+1) else Bound j

data Process = Null
             | Input Name [String] Process
             | Output Double Double Name [Name] Process
             | Tau Double Double Name [(String,Name)] Process
             | Restriction String Process
             | Compose Process Process
             | Sequence Process Process
             | Match Name Name Process
             | Mismatch Name Name Process
             | Choice Process Process
             | ProbChoice Double Process Process
             | Let String Process Process
             | Call String [Name] 
             | Tag String Process

free p = free' [] p 
free' vs Null = vs
free' vs (Input n xs p) = union (freeName n) (free' vs p)
free' vs (Output t1 t2 n ns p) = foldr union (free' vs p) (map freeName (n:ns))
free' vs (Tau t1 t2 n xns p) = let (xs,ns) = unzip xns in foldr union (free' vs p) (map freeName (n:ns))
free' vs (Restriction x p) = free' vs p
free' vs (Compose p1 p2) = free' (free' vs p1) p2
free' vs (Sequence p1 p2) = free' (free' vs p1) p2
free' vs (Match n1 n2 p) = union (freeName n1) (union (freeName n2) (free' vs p))
free' vs (Mismatch n1 n2 p) = union (freeName n1) (union (freeName n2) (free' vs p))
free' vs (Choice p1 p2) = free' (free' vs p1) p2
free' vs (ProbChoice p p1 p2) = free' (free' vs p1) p2
free' vs (Let c p1 p2) = free' vs p2
free' vs (Call c ns) = foldr union vs (map freeName ns)
free' vs (Tag t p) = free' vs p

bound p = bound' 0 [] p 
bound' d bs Null = bs
bound' d bs (Input n xs p) = union (boundName d n) (bound' (d+length xs) bs p) 
bound' d bs (Output t1 t2 n ns p) = foldr union (bound' d bs p) (map (boundName d) (n:ns))
bound' d bs (Tau t1 t2 n xns p) = let (xs,ns) = unzip xns in foldr union (bound' d bs p) (map (boundName d) (n:ns))
bound' d bs (Restriction x p) = bound' (d+1) bs p
bound' d bs (Compose p1 p2) = bound' d (bound' d bs p1) p2
bound' d bs (Sequence p1 p2) = bound' d (bound' d bs p1) p2
bound' d bs (Match n1 n2 p) = union (boundName d n1) (union (boundName d n2) (bound' d bs p))
bound' d bs (Mismatch n1 n2 p) = union (boundName d n1) (union (boundName d n2) (bound' d bs p))
bound' d bs (Choice p1 p2) = bound' d (bound' d bs p1) p2
bound' d bs (ProbChoice p p1 p2) = bound' d (bound' d bs p1) p2
bound' d bs (Let c p1 p2) = bound' d bs p2
bound' d bs (Call c ns) = foldr union bs (map (boundName d) ns)
bound' d bs (Tag t p) = bound' d bs p

shift 0 d p = p
shift i d Null = Null
shift i d (Input n xs p) = Input (shiftName i d n) xs (shift i (d+length xs) p)
shift i d (Output t1 t2 n ns p) = Output t1 t2 (shiftName i d n) (map (shiftName i d) ns) (shift i d p)
shift i d (Tau t1 t2 n xns p) = Tau t1 t2 (shiftName i d n) (map (\(x,n) -> (x,shiftName i d n)) xns) (shift i d p)
shift i d (Restriction x p) = Restriction x (shift i (d+1) p)
shift i d (Compose p1 p2) = Compose (shift i d p1) (shift i d p2)
shift i d (Sequence p1 p2) = Sequence (shift i d p1) (shift i d p2)
shift i d (Match n1 n2 p) = Match (shiftName i d n1) (shiftName i d n2) (shift i d p)
shift i d (Mismatch n1 n2 p) = Mismatch (shiftName i d n1) (shiftName i d n2) (shift i d p)
shift i d (Choice p1 p2) = Choice (shift i d p1) (shift i d p2)
shift i d (ProbChoice p p1 p2) = ProbChoice p (shift i d p1) (shift i d p2)
shift i d (Let c p1 p2) = Let c p1 (shift i d p2)
shift i d (Call c ns) = Call c (map (shiftName i d) ns)
shift i d (Tag t p) = Tag t (shift i d p)

subst i n Null = Null
subst i n (Input n' xs p) = Input (substName i n n') xs (subst (i+length xs) n p)
subst i n (Output t1 t2 n' ns p) = Output t1 t2 (substName i n n') (map (substName i n) ns) (subst i n p)
subst i n (Tau t1 t2 n' xns p) = Tau t1 t2 (substName i n n') (map (\(x,n') -> (x,substName i n n')) xns) (subst i n p)
subst i n (Restriction x p) = Restriction x (subst (i+1) n p)
subst i n (Compose p1 p2) = Compose (subst i n p1) (subst i n p2)
subst i n (Sequence p1 p2) = Sequence (subst i n p1) (subst i n p2)
subst i n (Match n1 n2 p) = Match (substName i n n1) (substName i n n2) (subst i n p) 
subst i n (Mismatch n1 n2 p) = Mismatch (substName i n n1) (substName i n n2) (subst i n p) 
subst i n (Choice p1 p2) = Choice (subst i n p1) (subst i n p2)
subst i n (ProbChoice p p1 p2) = ProbChoice p (subst i n p1) (subst i n p2)
subst i n (Let c p1 p2) = Let c p1 (subst i n p2)
subst i n (Call c ns) = Call c (map (substName i n) ns)
subst i n (Tag t p) = Tag t (subst i n p)

abstract i b Null = Null
abstract i b (Input n xs p) = Input (abstractName i b n) xs (abstract (i+length xs) b p)
abstract i b (Output t1 t2 n ns p) = Output t1 t2 (abstractName i b n) (map (abstractName i b) ns) (abstract i b p)
abstract i b (Tau t1 t2 n xns p) = Tau t1 t2 (abstractName i b n) (map (\(x,n) -> (x,abstractName i b n)) xns) (abstract i b p)
abstract i b (Restriction x p) = Restriction x (abstract (i+1) b p)
abstract i b (Compose p1 p2) = Compose (abstract i b p1) (abstract i b p2)
abstract i b (Sequence p1 p2) = Sequence (abstract i b p1) (abstract i b p2)
abstract i b (Match n1 n2 p) = Match (abstractName i b n1) (abstractName i b n2) (abstract i b p) 
abstract i b (Mismatch n1 n2 p) = Mismatch (abstractName i b n1) (abstractName i b n2) (abstract i b p) 
abstract i b (Choice p1 p2) = Choice (abstract i b p1) (abstract i b p2)
abstract i b (ProbChoice p p1 p2) = ProbChoice p (abstract i b p1) (abstract i b p2)
abstract i b (Let c p1 p2) = Let c p1 (abstract i b p2)
abstract i b (Call c ns) = Call c (map (abstractName i b) ns)
abstract i b (Tag t p) = Tag t (abstract i b p)

addlets Null env phi = Null
addlets (Input n xs p) env phi = Input n xs (addlets p env phi)
addlets (Output t1 t2 n ns p) env phi = Output t1 t2 n ns (addlets p env phi)
addlets (Tau t1 t2 n ns p) env phi = Tau t1 t2 n ns (addlets p env phi)
addlets (Restriction x p) env phi = Restriction x (addlets p env phi)
addlets (Compose p1 p2) env phi = Compose (addlets p1 env phi) (addlets p2 env phi)
addlets (Sequence p1 p2) env phi = Sequence (addlets p1 env phi) (addlets p2 env phi)
addlets (Match n1 n2 p) env phi = Match n1 n2 (addlets p env phi)
addlets (Mismatch n1 n2 p) env phi = Mismatch n1 n2 (addlets p env phi)
addlets (Choice p1 p2) env phi = Choice (addlets p1 env phi) (addlets p2 env phi)
addlets (ProbChoice p p1 p2) env phi = ProbChoice p (addlets p1 env phi) (addlets p2 env phi)
addlets (Let c p1 p2) env phi = Let c (addlets p1 env phi) (addlets p2 env phi)
addlets (Call c ns) env phi = if   elem c phi
                              then Call c ns
                              else case (lookup c env) of
                                      Nothing -> error ("Undefined process: "++c)
                                      Just p -> Let c (addlets p env (c:phi)) (Call c ns)
addlets (Tag t p) env phi = Tag t (addlets p env phi)

renameCall c c' Null = Null
renameCall c c' (Input n xs p) = Input n xs (renameCall c c' p)
renameCall c c' (Output t1 t2  n ns p) = Output t1 t2 n ns (renameCall c c' p)
renameCall c c' (Tau t1 t2  n xns p) = Tau t1 t2 n xns (renameCall c c' p)
renameCall c c' (Restriction x p) = Restriction x (renameCall c c' p)
renameCall c c' (Compose p1 p2) = Compose (renameCall c c' p1) (renameCall c c' p2)
renameCall c c' (Sequence p1 p2) = Sequence (renameCall c c' p1) (renameCall c c' p2)
renameCall c c' (Match n1 n2 p) = Match n1 n2 (renameCall c c' p)
renameCall c c' (Mismatch n1 n2 p) = Mismatch n1 n2 (renameCall c c' p)
renameCall c c' (Choice p1 p2) = Choice (renameCall c c' p1) (renameCall c c' p2)
renameCall c c' (ProbChoice p p1 p2) = ProbChoice p (renameCall c c' p1) (renameCall c c' p2)
renameCall c c' (Let c'' p1 p2) = Let c'' (renameCall c c' p1) (renameCall c c' p2)
renameCall c c' (Call c'' ns) = if   c==c'' 
                                then Call c' ns
                                else Call c'' ns

instance Show Process where 
   show p = render (prettyProcess p)

prettyProcess :: Process -> Doc

prettyProcess Null = text "0"
prettyProcess (Input n xs p) = let xs' = map (rename (free p)) xs
                               in  (prettyName n) <> parens (hcat (punctuate comma (map text xs))) <> (text ".") <> (prettyProcess' (foldr (\x p->subst 0 (Free x) p) p xs'))
prettyProcess (Output t1 t2 n ns p) = if (t1==0) && (t2==0) then (prettyName n) <> (text "<") <> hcat (punctuate comma (map prettyName ns)) <> (text ">") <> (text ".") <> (prettyProcess' p)
                                                            else (prettyName n) <> brackets ((double t1) <> comma <> (double t2)) <> (text "<") <> hcat (punctuate comma (map prettyName ns)) <> (text ">") <> (text ".") <> (prettyProcess' p)
prettyProcess (Tau t1 t2 n xns p) = if (t1==0) && (t2==0) then (text "tau") <> (parens (prettyName n <> parens (hcat (punctuate comma (map (\(x,n) -> (text x) <> (text "=") <> (prettyName n)) xns))))) <> (text ".") <> (prettyProcess' p)
                                                          else (text "tau") <> (parens (prettyName n <> brackets ((double t1) <> comma <> (double t2)) <> parens (hcat (punctuate comma (map (\(x,n) -> (text x) <> (text "=") <> (prettyName n)) xns))))) <> (text ".") <> (prettyProcess' p)
prettyProcess (Restriction x p) = let x' = rename (free p) x
                                  in  (text "new") <+> (text x') <> (text ".") <> prettyProcess' (subst 0 (Free x') p)
prettyProcess (Compose p1 p2) = (prettyProcess' p1) <+> (text "|") <+> (prettyProcess' p2)
prettyProcess (Sequence p1 p2) = (prettyProcess' p1) <> (text ".") <> (prettyProcess' p2)
prettyProcess (Match n1 n2 p) = brackets ((prettyName n1) <> equals <> (prettyName n2)) <> (prettyProcess' p) 
prettyProcess (Mismatch n1 n2 p) = brackets ((prettyName n1) <> (text "<>") <> (prettyName n2)) <> (prettyProcess' p) 
prettyProcess (Choice p1 p2) = (prettyProcess' p1) <+> (text "+") <+> (prettyProcess' p2)
prettyProcess (ProbChoice p p1 p2) = (prettyProcess' p1) <+> (text "+") <> (brackets (double p)) <+> (prettyProcess' p2)
prettyProcess (Let c p1 p2) = let xs = free p2
                              in  (text "let") <+> (text c) <> braces (hcat (punctuate comma (map text xs))) <+> equals <+> (prettyProcess (foldr (\x p->subst 0 (Free x) p) p1 xs)) <+> (text "in") <+> (prettyProcess p2)
prettyProcess (Call c ns) = (text c) <> braces (hcat (punctuate comma (map prettyName ns))) 
prettyProcess (Tag t p) = (text "<<") <> (text t) <> (text ">>") <> (prettyProcess p)
prettyProcess' (Compose p1 p2) = parens (prettyProcess (Compose p1 p2))
prettyProcess' (Sequence p1 p2) = parens (prettyProcess (Sequence p1 p2))
prettyProcess' (Choice p1 p2) = parens (prettyProcess (Choice p1 p2))
prettyProcess' (ProbChoice p p1 p2) = parens (prettyProcess (ProbChoice p p1 p2))
prettyProcess' p = prettyProcess p

mcalc = emptyDef
        { commentStart    = "/*"
        , commentEnd      = "*/"
        , commentLine     = "--"
        , nestedComments  = True
        , identStart      = letter         
        , identLetter     = alphaNum
        , reservedNames   = ["DEFINITIONS","ENDD","SYSTEM","ENDS","PROPERTIES","ENDP","if","then","else","new","fi"]
        , reservedOpNames = ["+","|",".","=","<>"]
        , caseSensitive   = True
        }

lexer = T.makeTokenParser mcalc

symbol     = T.symbol lexer
paren      = T.parens lexer
bracket    = T.brackets lexer
brace      = T.braces lexer
coma       = T.comma lexer
identifier = T.identifier lexer
reserved   = T.reserved lexer
reservedOp = T.reservedOp lexer
real       = T.float lexer

definition = do
             n <- identifier
             xs <- brace (sepBy identifier coma)
             symbol "="
             p <- compoundprocess
             return (n,foldl (\p x->abstract 0 x p) p xs)

compoundprocess = buildExpressionParser prec1 process

prec1 = [ [ sequence ],
          [ compose ],
          [ choice ]
        ]
        where
        sequence = Infix (do
                          reservedOp "."
                          return (\x y -> Sequence x y)
                         ) AssocRight
        compose = Infix (do
                         reservedOp "|"
                         return (\x y -> Compose x y)
                        ) AssocRight 
        choice = Infix (do 
                        reservedOp "+"
                        c <-     do
                                 p <- bracket real   
                                 return (\x y -> ProbChoice p x y)
                             <|> do
                                 spaces
                                 return (\x y -> Choice x y)
                        return c
                       ) AssocRight
 
process =     do
              p <- paren compoundprocess
              return p
          <|> do
              symbol "0"
              return Null
          <|> do
              n <- identifier
              i <-     do
                       xs <- paren (sepBy identifier coma)
                       reservedOp "."
                       p <- process
                       return (Input (Free n) xs (foldl (\p x->abstract 0 x p) p xs))
                   <|> do
                       symbol "["
                       t1 <- real
                       coma
                       t2 <- real
                       symbol "]"
                       symbol "<"
                       ns <- sepBy identifier coma
                       symbol ">"
                       reservedOp "."
                       p <- process
                       return (Output t1 t2 (Free n) (map Free ns) p)
                   <|> do
                       symbol "<"
                       ns <- sepBy identifier coma
                       symbol ">"
                       reservedOp "."
                       p <- process
                       return (Output 0 0 (Free n) (map Free ns) p)
                   <|> do
                       ns <- brace (sepBy identifier coma)
                       return (Call n (map Free ns))
              return i
          <|> do
              reserved "new"
              x <- identifier
              reservedOp "."
              p <- process
              return (Restriction x (abstract 0 x p))
          <|> do
              reserved "if"
              symbol "("
              n1 <- identifier
              m <-     do
                       reservedOp "="
                       n2 <- identifier
                       symbol ")"
                       reserved "then"
                       p1 <- compoundprocess
                       reserved "else"
                       p2 <- compoundprocess
                       reserved "fi"
                       return (Compose (Match (Free n1) (Free n2) p1) (Mismatch (Free n1) (Free n2) p2))
                   <|> do
                       reservedOp "<>"
                       n2 <- identifier
                       symbol ")"
                       reserved "then"
                       p1 <- compoundprocess
                       reserved "else"
                       p2 <- compoundprocess
                       reserved "fi"
                       return (Compose (Mismatch (Free n1) (Free n2) p1) (Match (Free n1) (Free n2) p2))
              return m
          <|> do
              symbol "["
              n1 <- identifier
              m <-     do
                       reservedOp "="
                       n2 <- identifier
                       symbol "]"
                       p <- process
                       return (Match (Free n1) (Free n2) p)
                   <|> do
                       reservedOp "<>"
                       n2 <- identifier
                       symbol "]"
                       p <- process
                       return (Mismatch (Free n1) (Free n2) p)
              return m
          <|> do
              symbol "<<"
              t <- identifier
              symbol ">>"
              p <- compoundprocess
              return p

