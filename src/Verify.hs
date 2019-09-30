
module Verify where 

import Evaluate
import MCalculus
import PSL
import Time
import Data.List 
import Data.Int 
import Data.Char
import Debug.Trace 
import Control.Monad

prove (Always b) p int env = always b p int env []
prove (Eventually b) p int env = eventually b p int env []
prove (Now b) p int env = now b p env
prove (Conjunction b1 b2) p int env = if   prove b1 p int env
                                      then prove b2 p int env
                                      else False
prove (Disjunction b1 b2) p int env = if   prove b1 p int env
                                      then True
                                      else prove b2 p int env
prove (Negation b) p int env = not (prove b p int env)
prove (Implication b1 b2) p int env = if   prove b1 p int env
                                      then prove b2 p int env
                                      else True
prove (Follows b1 b2) p int env = follows b1 b2 p env []
prove (Before b t1 t2) p int env = let rho = events p (free p) int [] []
                                   in  beforeInterval (boolean b p int (Infinite,Finite 0) env []) (time t1 rho)
prove (Within b t1 t2) p int env = let rho = events p (free p) int [] []
                                   in  withinInterval (boolean b p int (Infinite,Finite 0) env []) (snd (time t1 rho),fst (time t2 rho))
prove (After b t1 t2) p int env = let rho = events p (free p) int [] []
                                  in  afterInterval (boolean b p int (Infinite,Finite 0) env []) (time t2 rho)
prove (Confidence c b) p int env = let r = probability b p int env 1 []
                                   in  r >= c

always b Null int env phi = True
always b p@(Tau t1 t2 (Free n) xns q) int env phi = let int' = addInterval int (Finite t1,Finite t2)
                                                    in  if   prove b p int' env
                                                        then always b q int' (xns++env) phi
                                                        else False
always b (Choice p1 p2) int env phi = (always b p1 int env phi) && (always b p2 int env phi)
always b (ProbChoice p p1 p2) int env phi = (always b p1 int env phi) && (always b p2 int env phi)
always b (Tag t p) int env phi = if   elem t phi
                                 then True
                                 else always b p int env (t:phi)

eventually b Null int env phi = False
eventually b p@(Tau t1 t2 (Free n) xns q) int env phi = let int' = addInterval int (Finite t1,Finite t2)
                                                        in  if   prove b p int' env
                                                            then True
                                                            else eventually b q int' (xns++env) phi
eventually b (Choice p1 p2) int env phi = (eventually b p1 int env phi) && (eventually b p2 int env phi)
eventually b (ProbChoice p p1 p2) int env phi = (eventually b p1 int env phi) && (eventually b p2 int env phi)
eventually b (Tag t p) int env phi = if   elem t phi
                                     then False
                                     else eventually b p int env (t:phi)

now (And b1 b2) p env = (now b1 p env) && (now b2 p env)
now (Or b1 b2) p env = (now b1 p env) || (now b2 p env)
now (Implies b1 b2) p env = if   now b1 p env
                            then now b2 p env
                            else True
now (Not b) p env = not (now b p env)
now (Event e as) Null env = False
now (Event e as) (Tau t1 t2 (Free n) xns p) env = inst (Event e (map (renew (xns++env)) as)) (Event n (map (\(x,Free n) -> Name n) xns))
now (Equals v1 v2) Null env = (val v1 env) == (val v2 env)
now (Equals v1 v2) (Tau t1 t2 (Free n) xns p) env = let env' = xns++env in (val v1 env') == (val v2 env')
now b (Choice p1 p2) env = (now b p1 env) && (now b p2 env)
now b (ProbChoice p p1 p2) env = (now b p1 env) && (now b p2 env)
now b (Tag t p) env = now b p env

follows b1 b2 Null env phi = True
follows b1 b2 p@(Tau t1 t2 (Free n) xns q) env phi = if   now b2 p env
                                                     then eventually (Now b1) p (Infinite,Finite 0) env phi
                                                     else follows b1 b2 q (xns++env) phi
follows b1 b2 (Choice p1 p2) env phi = (follows b1 b2 p1 env phi) && (follows b1 b2 p2 env phi)
follows b1 b2 (ProbChoice p p1 p2) env phi = (follows b1 b2 p1 env phi) && (follows b1 b2 p2 env phi)
follows b1 b2 (Tag t p) env phi = if   elem t phi
                                  then False
                                  else follows b1 b2 p env phi

probability b Null int env r phi = 0
probability b p@(Tau t1 t2 (Free n) xns q) int env r phi = let int' = addInterval int (Finite t1,Finite t2)
                                                           in  if   prove b p int' env
                                                               then r
                                                               else probability b q int' (xns++env) r phi
probability b (Choice p1 p2) int env r phi = min (probability b p1 int env r phi) (probability b p2 int env r phi)
probability b (ProbChoice p p1 p2) int env r phi = (probability b p1 int env (r*(1-p)) phi) + (probability b p2 int env (r*p) phi)
probability b (Tag t p) int env r phi = let r1 = probability' b (Tag t p) int env r []
                                        in  case (lookup t phi) of
                                               Just r2 -> r*(r1/r2)/(1-r2)
                                               Nothing -> probability b p int env r ((t,r1):phi)

probability' b Null int env r phi = 0
probability' b p@(Tau t1 t2 (Free n) xns q) int env r phi = let int' = addInterval int (Finite t1,Finite t2)
                                                            in  if   prove b p int' env
                                                                then r
                                                                else probability' b q int' (xns++env) r phi
probability' b (Choice p1 p2) int env r phi = min (probability' b p1 int env r phi) (probability' b p2 int env r phi)
probability' b (ProbChoice p p1 p2) int env r phi = (probability' b p1 int env (r*(1-p)) phi) + (probability' b p2 int env (r*p) phi)
probability' b (Tag t p) int env r phi = if t `elem` phi then 0 else probability' b p int env r (t:phi)

events Null fv int rho phi = rho
events (Tau t1 t2 (Free n) xns p) fv int rho phi = let int' = addInterval int (Finite t1,Finite t2)
                                                       rho' = unionRho rho [(Event n (map (\(x,Free n) -> if (elem n fv) then (Name n) else Wild) xns),int')]
                                                   in  events p fv int' rho' phi
events (Choice p1 p2) fv int rho phi = unionRho (events p1 fv int rho phi) (events p2 fv int rho phi)
events (ProbChoice p p1 p2) fv int rho phi = unionRho (events p1 fv int rho phi) (events p2 fv int rho phi)
events (Tag t p) fv int rho phi = case (lookup t phi) of
                                     Nothing -> events p fv int rho ((t,rho):phi)
                                     Just rho' -> if   rho==rho'
                                                  then rho
                                                  else events p fv int rho ((t,extendRho rho rho'):phi)

boolean b Null int1 int2 env rho = int2
boolean b p@(Tau t1 t2 (Free n) xns q) int1 int2 env rho = let int1' = addInterval int1 (Finite t1,Finite t2)
                                                               int2' = unionInterval int2 int1'
                                                           in  if   now b p env
                                                               then boolean b q int1' int2' (xns++env) rho
                                                               else boolean b q int1' int2 (xns++env) rho
boolean b (Choice p1 p2) int1 int2 env rho = unionInterval (boolean b p1 int1 int2 env rho) (boolean b p2 int1 int2 env rho)
boolean b (ProbChoice p p1 p2) int1 int2 env rho = unionInterval (boolean b p1 int1 int2 env rho) (boolean b p2 int1 int2 env rho)
boolean b (Tag t p) int1 int2 env rho = case (lookup t rho) of
                                           Nothing -> boolean b p int1 int2 env ((t,int2):rho)
                                           Just int2' -> if   int2==int2'
                                                         then int2
                                                         else boolean b p int1 int2 env ((t,extendInterval int2 int2'):rho)

val v env = case (lookup v env) of
               Just (Free v') -> v'
               Nothing -> v

renew env Wild = Wild
renew env (Name n) = Name (val n env)

