
module Time where 

import Evaluate
import MCalculus
import PSL
import Data.List 
import Data.Int 
import Data.Char
import Debug.Trace 
import Control.Monad

data Time = Finite Double
          | Infinite
            deriving (Eq,Show)

greaterTime t Infinite = False
greaterTime Infinite t = True
greaterTime (Finite t1) (Finite t2) = t1>t2

maxTime t Infinite = Infinite
maxTime Infinite t = Infinite
maxTime (Finite t1) (Finite t2) = Finite (if t1>t2 then t1 else t2)

minTime t Infinite = t
minTime Infinite t = t
minTime (Finite t1) (Finite t2) = Finite (if t1<t2 then t1 else t2)

addTime t Infinite = Infinite
addTime Infinite t = Infinite
addTime (Finite t1) (Finite t2) = Finite (t1+t2)

subtractTime Infinite t = Infinite
subtractTime t Infinite = Finite 0
subtractTime (Finite t1) (Finite t2) = Finite (t1-t2)

modTime Infinite t = Infinite
modTime t Infinite = Infinite
modTime (Finite t1) (Finite t2) = Finite (t1-(fromIntegral(floor(t1/t2)))*t2)

time (Plus e1 e2) rho = addInterval (time e1 rho) (time e2 rho)
time (Minus e1 e2) rho = subtractInterval (time e1 rho) (time e2 rho)
time (Mod e1 e2) rho = modInterval (time e1 rho) (time e2 rho)
time (Time t) rho = (Finite t,Finite t)
time (Evt e as) rho = interval (Event e as) (Infinite,Finite 0) rho

addInterval (t1,t2) (t1',t2') = (addTime t1 t1',addTime t2 t2')

subtractInterval (t1,t2) (t1',t2') = (subtractTime t1 t1',subtractTime t2 t2')

modInterval (t1,t2) (t1',t2') = (modTime t1 t1',modTime t2 t2')

unionInterval (t1,t2) (t1',t2') = (minTime t1 t1',maxTime t2 t2')

interval e int [] = int
interval e int ((e',int'):rho) = if   inst e e'
                                 then interval e (unionInterval int int') rho
                                 else interval e int rho

extendInterval (t1,t2) (t1',t2') = if   greaterTime t2 t2'
                                   then (t1,Infinite)
                                   else (t1,t2)

beforeInterval (t1,t2) (t1',t2') = greaterTime t1' t2

withinInterval (t1,t2) (t1',t2') = (greaterTime t1 t1') && (greaterTime t2' t2)

afterInterval (t1,t2) (t1',t2') = greaterTime t1 t2'

unionRho [] rho = rho
unionRho rho [] = rho
unionRho ((e,int):rho) rho' = case (lookup e rho') of
                                 Nothing -> (e,int):unionRho rho rho'
                                 Just int' -> (e,unionInterval int int'):unionRho rho rho'

extendRho [] rho = rho
extendRho ((e,int):rho) rho' = case (lookup e rho') of
                                  Nothing -> (e,int):extendRho rho rho'
                                  Just int' -> (e,extendInterval int int'):extendRho rho rho'

inst (Event e as) (Event e' as') = (e==e') && (all instarg (zip as as'))

instarg (Wild,e) = True
instarg (Name n,Name n') = n==n'
instarg (a,a') = False
