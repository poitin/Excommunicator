{- PSL Definition, Parser and Pretty Printer -}

module PSL where

import Data.Char
import Data.List 
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language

import Debug.Trace 

data Property = Always Property
              | Eventually Property
              | Now BooleanProperty
              | Conjunction Property Property
              | Disjunction Property Property
              | Negation Property
              | Implication Property Property
              | Follows BooleanProperty BooleanProperty
              | After BooleanProperty TimeExpr TimeExpr
              | Within BooleanProperty TimeExpr TimeExpr
              | Before BooleanProperty TimeExpr TimeExpr
              | Confidence Double Property

instance Show Property where
   show p = render (prettyProperty p)

prettyProperty (Always p) = (text "G") <> parens (prettyProperty p)
prettyProperty (Eventually p) = (text "F") <> parens (prettyProperty p)
prettyProperty (Now b) = prettyBooleanProperty b
prettyProperty (Conjunction p1 p2) = (prettyProperty p1) <+> (text "and") <+> (prettyProperty p2)
prettyProperty (Disjunction p1 p2) = (prettyProperty p1) <+> (text "or") <+> (prettyProperty p2)
prettyProperty (Negation p) = (text "not") <+> (prettyProperty p)
prettyProperty (Implication p1 p2) = (prettyProperty p1) <+> (text "=>") <+> (prettyProperty p2)
prettyProperty (Follows p1 p2) = (prettyBooleanProperty p1) <+> (text ">") <+> (prettyBooleanProperty p2)
prettyProperty (After b t1 t2) = (prettyBooleanProperty b) <+> (text "after") <+> brackets ((prettyTimeExpr t1) <> comma <> (prettyTimeExpr t2))
prettyProperty (Within b t1 t2) = (prettyBooleanProperty b) <+> (text "within") <+> brackets ((prettyTimeExpr t1) <> comma <> (prettyTimeExpr t2))
prettyProperty (Before b t1 t2) = (prettyBooleanProperty b) <+> (text "before") <+> brackets ((prettyTimeExpr t1) <> comma <> (prettyTimeExpr t2))
prettyProperty (Confidence c p) = parens (prettyProperty p) <> (text "@") <> (double c)

data BooleanProperty = And BooleanProperty BooleanProperty
                     | Or BooleanProperty BooleanProperty
                     | Implies BooleanProperty BooleanProperty
                     | Not BooleanProperty
                     | Event String [EventArg]
                     | Equals String String
                       deriving Eq

instance Show BooleanProperty where
   show p = render (prettyBooleanProperty p)

prettyBooleanProperty (And b1 b2) = (prettyBooleanProperty' b1) <+> (text "and") <+> (prettyBooleanProperty' b2)
prettyBooleanProperty (Or b1 b2) = (prettyBooleanProperty' b1) <+> (text "or") <+> (prettyBooleanProperty' b2)
prettyBooleanProperty (Implies b1 b2) = (prettyBooleanProperty' b1) <+> (text "implies") <+> (prettyBooleanProperty' b2)
prettyBooleanProperty (Not b) = (text "not") <+> (prettyBooleanProperty' b)
prettyBooleanProperty (Event e as) = text e <> parens (hcat (punctuate comma (map prettyEventArg as)))
prettyBooleanProperty (Equals x y) = (text x) <> (text "=") <> (text y)
prettyBooleanProperty' (Event e as) = text e <> parens (hcat (punctuate comma (map prettyEventArg as)))
prettyBooleanProperty' b = parens (prettyBooleanProperty b)

data TimeExpr = Plus TimeExpr TimeExpr
              | Minus TimeExpr TimeExpr
              | Mod TimeExpr TimeExpr
              | Time Double
              | Evt String [EventArg]
                deriving Eq

instance Show TimeExpr where
   show t = render (prettyTimeExpr t)

prettyTimeExpr (Plus t1 t2) = (prettyTimeExpr t1) <+> (text "+") <+> (prettyTimeExpr t2)
prettyTimeExpr (Minus t1 t2) = (prettyTimeExpr t1) <+> (text "-") <+> (prettyTimeExpr t2)
prettyTimeExpr (Mod t1 t2) = (prettyTimeExpr t1) <+> (text "mod") <+> (prettyTimeExpr t2)
prettyTimeExpr (Time t) = double t
prettyTimeExpr (Evt e as) = text e <> parens (hcat (punctuate comma (map prettyEventArg as)))

data EventArg = Wild
              | Name String
                deriving Eq

instance Show EventArg where
   show a = render (prettyEventArg a)

prettyEventArg Wild = text "*"
prettyEventArg (Name a) = text a

psl = emptyDef
      { commentStart    = "/*"
      , commentEnd      = "*/"
      , commentLine     = "--"
      , nestedComments  = True
      , identStart      = letter         
      , identLetter     = alphaNum
      , reservedNames   = ["DEFINITIONS","ENDD","SYSTEM","ENDS","PROPERTIES","ENDP","F","G","before","within","after"]
      , reservedOpNames = ["and","or","not","implies","=>",">","+","-","mod","*"]
      , caseSensitive   = True
      }

lexer = T.makeTokenParser psl

symbol     = T.symbol lexer
paren      = T.parens lexer
bracket    = T.brackets lexer
brace      = T.braces lexer
coma       = T.comma lexer
identifier = T.identifier lexer
reserved   = T.reserved lexer
reservedOp = T.reservedOp lexer
real       = T.float lexer

stochasticproperty = do
                     p <- compoundproperty
                     s <-     do
                              symbol "@"
                              c <- real
                              return (Confidence c p)
                          <|> do
                              spaces
                              return p
                     return s 
       
compoundproperty = buildExpressionParser prec1 property

prec1 = [ [ unOp "not" Negation ],
          [ op "and" Conjunction AssocRight ],
          [ op "or" Disjunction AssocRight ],
          [ op "=>" Implication AssocRight ]
        ]
        where
        op o t assoc   = Infix (do 
                                reservedOp o
                                return (\x y -> t x y) 
                               ) assoc
        unOp o t       = Prefix (do
                                 reservedOp o
                                 return (\x -> t x)
                                )      

property =     do 
               reserved "G"
               p <- paren compoundproperty
               return (Always p)
           <|> do
               reserved "F"
               p <- paren compoundproperty
               return (Eventually p)
           <|> do
               p <- paren compoundproperty
               return p
           <|> do
               b <- booleanproperty
               e <-     do
                        reservedOp ">"
                        e <- identifier
                        as <- paren (sepBy eventarg coma)
                        return (Follows b (Event e as))    
                    <|> do
                        reserved "after"
                        symbol "["
                        e1 <- timeexpr
                        coma
                        e2 <- timeexpr
                        symbol "]"
                        return (After b e1 e2)
                    <|> do
                        reserved "within"
                        symbol "["
                        e1 <- timeexpr
                        coma
                        e2 <- timeexpr
                        symbol "]"
                        return (Within b e1 e2)
                    <|> do
                        reserved "before"
                        symbol "["
                        e1 <- timeexpr
                        coma
                        e2 <- timeexpr
                        symbol "]"
                        return (Before b e1 e2)
                    <|> do
                        spaces
                        return (Now b)
               return e

booleanproperty = buildExpressionParser prec2 simpleproperty

prec2 = [ [ unOp "not" Not ],
          [ op "and" And AssocRight ],
          [ op "or" Or AssocRight ],
          [ op "implies" Implies AssocRight ]
        ]
        where
        op o t assoc   = Infix (do 
                                reservedOp o
                                return (\x y -> t x y) 
                               ) assoc
        unOp o t       = Prefix (do
                                 reservedOp o
                                 return (\x -> t x)
                                )      

simpleproperty =     do
                     e <- identifier
                     s <-     do
                              as <- paren (sepBy eventarg coma)
                              return (Event e as)
                          <|> do
                              symbol "="
                              n <- identifier
                              return (Equals e n)
                     return s
                 <|> do
                     e <- paren (booleanproperty)
                     return e

timeexpr = buildExpressionParser prec3 timeterm

prec3 = [ [ op "mod" Mod AssocRight ],
          [ op "+" Plus AssocRight ],
          [ op "-" Minus AssocRight ]
        ]
        where
        op o t assoc   = Infix (do 
                                reservedOp o
                                return (\x y -> t x y) 
                               ) assoc

timeterm =     do
               e <- identifier
               as <- paren (sepBy eventarg coma)
               return (Evt e as)
           <|> do
               t <- real
               return (Time t)

eventarg =    do
              reservedOp "*"
              return Wild
          <|> do
              a <- identifier
              return (Name a)


