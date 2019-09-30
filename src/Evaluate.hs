
module Evaluate where 

import MCalculus
import Data.List 
import Data.Char
import Debug.Trace 
import Control.Monad

eval Null fv env Null = Null
eval Null fv env s = eval s fv env Null
eval (Input n xs p) fv env s = Input n xs (eval p fv env s)
eval (Output t1 t2 n ns p) fv env s = Output t1 t2 n ns (eval p fv env s)
eval (Tau t1 t2 n xns p) fv env s = Tau t1 t2 n xns (eval p fv env s)
eval (Restriction x p) fv env s = let x' = rename fv x
                                  in  eval (subst 0 (Free x') p) (x':fv) env s
eval (Compose p1 p2) fv env s = compose (eval p1 fv env Null) (eval p2 fv env Null) fv env s
eval (Sequence p1 p2) fv env Null = eval p1 fv env p2
eval (Sequence p1 p2) fv env s = eval p1 fv env (Sequence p2 s)
eval (Match n1 n2 p) fv env s = if   n1==n2
                                then eval p fv env s
                                else Match n1 n2 (eval p fv env s)
eval (Mismatch n1 n2 p) fv env s = if   n1/=n2
                                   then eval p fv env s
                                   else Mismatch n1 n2 (eval p fv env s)
eval (Choice p1 p2) fv env s = Choice (eval p1 fv env s) (eval p2 fv env s)
eval (ProbChoice p p1 p2) fv env s = ProbChoice p (eval p1 fv env s) (eval p2 fv env s)
eval (Let c p1 p2) fv env s = let (cs,ds) = unzip env
                                  c' = rename cs c
                              in  eval p2 fv ((c',renameCall c c' p1):env) s
eval (Call c ns) fv env s = case (lookup c env) of
                               Nothing -> error ("Undefined process: "++c)
                               Just p  -> Tag c (eval (foldr (\n p -> subst 0 n p) p ns) fv env s)
eval (Tag t p) fv env s = Tag t (eval p fv env s)

compose p q fv env s = Choice (comm p q fv env s) (Choice (leftfirst p q fv env s) (leftfirst q p fv env s))

leftfirst Null p fv env Null = Null
leftfirst Null p fv env s = eval s fv env Null
leftfirst (Input n xs p) q fv env s = Input n xs (compose p q fv env s)
leftfirst (Output t1 t2 n ns p) q fv env s = Output t1 t2 n ns (compose p q fv env s)
leftfirst (Tau t1 t2 n xns p) q fv env s = Tau t1 t2 n xns (compose p q fv env s)
leftfirst (Match n1 n2 p) q fv env s = Match n1 n2 (leftfirst p q fv env s)
leftfirst (Mismatch n1 n2 p) q fv env s = Mismatch n1 n2 (leftfirst p q fv env s)
leftfirst (Choice p1 p2) q fv env s = Choice (leftfirst p1 q fv env s) (leftfirst p2 q fv env s)
leftfirst (ProbChoice p p1 p2) q fv env s = ProbChoice p (leftfirst p1 q fv env s) (leftfirst p2 q fv env s)
leftfirst (Tag t p) q fv env s = Tag t (leftfirst p q fv env s)

comm (Input n' xs q) (Output t1 t2 n ns p) fv env s | n==n' && length ns == length xs = Tau t1 t2 n (zip xs ns) (compose p (foldr (\n p -> subst 0 n p) q ns) fv env s)
comm (Output t1 t2 n ns p) (Input n' xs q) fv env s | n==n' && length ns == length xs = Tau t1 t2 n (zip xs ns) (compose p (foldr (\n p -> subst 0 n p) q ns) fv env s)
comm (Match n1 n2 p) q fv env s = Match n1 n2 (comm p q fv env s)
comm q (Match n1 n2 p) fv env s = Match n1 n2 (comm p q fv env s)
comm (Mismatch n1 n2 p) q fv env s = Mismatch n1 n2 (comm p q fv env s)
comm q (Mismatch n1 n2 p) fv env s = Mismatch n1 n2 (comm p q fv env s)
comm (Choice p1 p2) q fv env s = Choice (comm p1 q fv env s) (comm p2 q fv env s)
comm q (Choice p1 p2) fv env s = Choice (comm p1 q fv env s) (comm p2 q fv env s)
comm (ProbChoice p p1 p2) q fv env s = ProbChoice p (comm p1 q fv env s) (comm p2 q fv env s)
comm q (ProbChoice p p1 p2) fv env s = ProbChoice p (comm p1 q fv env s) (comm p2 q fv env s)
comm (Tag t p) q fv env s = Tag t (comm p q fv env s)
comm q (Tag t p) fv env s = Tag t (comm p q fv env s)
comm p q fv env s = Null

simplify Null = Null
simplify (Input n xs p) = Null
simplify (Output t1 t2 n ns p) = Null
simplify (Tau t1 t2  n xns p) = Tau t1 t2 n xns (simplify p)
simplify (Match n1 n2 p) = Null
simplify (Mismatch n1 n2 p) = Null
simplify (Choice p1 p2) = simplifyChoice (simplify p1) (simplify p2)
simplify (ProbChoice p p1 p2) = simplifyProbChoice p (simplify p1) (simplify p2)
simplify (Tag t p) = simplifyTag t (simplify p)

simplifyChoice Null p = p
simplifyChoice p Null = p
simplifyChoice p q = Choice p q

simplifyProbChoice p Null Null = Null
simplifyProbChoice p p1 p2 = ProbChoice p p1 p2

simplifyTag t Null = Null
simplifyTag t p = Tag t p
