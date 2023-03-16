
module Trans where 

import PiCalculus
import Data.List 
import Data.Char
import Control.Monad

-- transform parallel composition

par (New x p) q r m d = let x' = renameVar (free (Compose (New x p) q)) x
                        in  par (rename [(x,x')] p) q (x':r) m d
par p (New x q) r m d = let x' = renameVar (free (Compose p (New x q))) x
                        in  par p (rename [(x,x')] q) (x':r) m d
par (Match x y p) q r m d 
   | x==y = par p q r m d
   | x `elem` r || y `elem` r = (Null,m,d)
   | otherwise = let (p',m',d') = par p q r m d
                 in (Match x y p',m',d')
par p (Match x y q) r m d 
   | x==y = par p q r m d
   | x `elem` r || y `elem` r = (Null,m,d)
   | otherwise = let (p',m',d') = par p q r m d
                 in (Match x y p',m',d')
par (Choice p1 p2) q r m d = let (p',m',d') = par p1 q r m d
                                 (p'',m'',d'') = par p2 q r m' d'
                             in (choice p' p'',m'',d'')
par p (Choice q1 q2) r m d = let (p',m',d') = par p q1 r m d
                                 (p'',m'',d'') = par p q2 r m' d'
                             in (choice p' p'',m'',d'')
par (Compose p1 p2) q r m d = let (p',m',d') = par p1 p2 [] m d
                              in  par p' q r m' d'
par p (Compose q1 q2) r m d = let (p',m',d') = par q1 q2 [] m d
                              in  par p p' r m' d'
par (Compose' p1 p2) q r m d = let (p',m',d') = par p1 q [] m d
                                   (q',m'',d'') = par p2 q [] m' d'
                                   xs = free (Compose' p' q') `intersect` r
                               in  (foldr New (Compose' p' q') xs,m'',d'')
par p (Compose' q1 q2) r m d = let (p',m',d') = par p q1 [] m d
                                   (q',m'',d'') = par p q2 [] m' d'
                                   xs = free (Compose' p' q') `intersect` r
                               in  (foldr New (Compose' p' q') xs,m'',d'')
par (Call f xs) q r m d = let p = Compose (Call f xs) q
                              xs'' = free p \\ r
                          in  case [f' | (f',(xs',p')) <- m, length xs' == length xs'' && not (null (renaming' p' p (zip xs' xs'')))] of
                                 [] -> case lookup f d of
                                          Nothing -> error ("Undefined process: "++f)
                                          Just (xs',p')  -> let f' = renameVar (map fst m ++ map fst d) f
                                                                (q',m',d') = par (rename (zip xs' xs) p') q r ((f',(xs'',p)):m) d
                                                            in  if   f' `elem` procs q' d'
                                                                then (Call f' xs'',m',(f',(xs'',q')):d')
                                                                else (q',[p | p <- m', fst p /= f'],d')
                                 (f':_) -> (Call f' xs'',m,d)
par p (Call f xs) r m d = let q = Compose p (Call f xs)
                              xs'' = free q \\ r
                          in  case [f' | (f',(xs',p')) <- m, {-length xs' == length xs'' &&-} not (null (renaming' p' q []{-(zip xs' xs'')-}))] of
                                 [] -> case lookup f d of
                                          Nothing -> error ("Undefined process: "++f)
                                          Just (xs',p')  -> let f' = renameVar (map fst m ++ map fst d) f
                                                                (q',m',d') = par p (rename (zip xs' xs) p') r ((f',(xs'',q)):m) d
                                                            in  if   f' `elem` procs q' d'
                                                                then (Call f' xs'',m',(f',(xs'',q')):d')
                                                                else (q',[p | p <- m', fst p /= f'],d')
                                 (f':_) -> (Call f' xs'',m,d)
par p q r m d = let (p',m',d') = lpar p q r m d
                    (p'',m'',d'') = lpar q p r m' d'
                in (choice p' p'',m'',d'')

-- transform left-prioritised parallel composition

lpar (Output x y p) (Input x' y' q) r m d 
   | x `elem` r || x' `elem` r = (Null,m,d)
   | otherwise = let (p',m',d') = par (Match x x' p) (rename [(y',y)] q) (r \\[y]) m d
                     (p'',m'',d'') = par p (Input x' y' q) (r \\[y]) m' d'
                 in  if   y `elem` r
                     then (New y (choice p' (Output x y p'')),m'',d'')
                     else (choice p' (Output x y p''),m'',d'')
lpar (Output x y p) q r m d 
   | x `elem` r = (Null,m,d)
   | y `elem` r = let (p',m',d') = par p q (r \\ [y]) m d
                  in  (New y (Output x y p'),m',d')
   | otherwise = let (p',m',d') = par p q r m d
                 in  (Output x y p',m',d')
lpar (Input x y p) q r m d 
   | x `elem` r = (Null,m,d)
   | otherwise = let y' = renameVar (free (Compose (Input x y p) q)) y
                     (p',m',d') = par (rename [(y,y')] p) q r m d
                 in  (Input x y' p',m',d')
lpar (Tau p) q r m d = let (p',m',d') = par p q r m d
                       in (Tau p',m',d')
lpar Null q r m d = (Null,m,d)

choice Null p = p
choice p Null = p
choice p q = Choice p q
