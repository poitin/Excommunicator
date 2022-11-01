
module Trans where 

import PiCalculus
import Data.List 
import Data.Char
import Debug.Trace 
import Control.Monad

-- transform parallel composition

par (Match x y p) q r m d
   | x==y = par p q r m d
   | x `elem` r || y `elem` r = Null
   | otherwise = Match x y (par p q r m d)
par p (Match x y q) r m d
   | x==y = par p q r m d
   | x `elem` r || y `elem` r = Null
   | otherwise = Match x y (par p q r m d)
par (New x p) q r m d = let x' = renameVar (free (Compose (New x p) q)) x
                        in  par (rename [(x,x')] p) q (x':r) m d
par p (New x q) r m d = let x' = renameVar (free (Compose p (New x q))) x
                        in  par p (rename [(x,x')] q) (x':r) m d
par (Choice p1 p2) q r m d = choice (par p1 q r m d) (par p2 q r m d)
par p (Choice q1 q2) r m d = choice (par p q1 r m d) (par p q2 r m d)
par (Compose p1 p2) q r m d = let p = par p1 p2 [] [] d
                                  (p',d') = residualise p d
                              in  par p' q r m d'
par p (Compose q1 q2) r m d = let q = par q1 q2 [] [] d
                                  (q',d') = residualise q d
                              in  par p q' r m d'
par (Compose' p1 p2) q r m d = let p' = par p1 q [] m d
                                   q' = par p2 q [] m d
                                   xs = free (Compose' p' q') `intersect` r
                               in  foldr New (Compose' p' q') xs
par p (Compose' q1 q2) r m d = let p' = par p q1 [] m d
                                   q' = par p q2 [] m d
                                   xs = free (Compose' p' q') `intersect` r
                               in  foldr New (Compose' p' q') xs
par (Call f xs) q r m d = let p = Compose (Call f xs) q
                              xs'' = free p \\ r
                          in  case [f' | (f',(xs',p')) <- m, not (null (renaming' p' p (zip xs' xs'')))] of
                                 [] -> case lookup f d of
                                          Nothing -> error ("Undefined process: "++f)
                                          Just (xs',p')  -> let f' = renameVar (map fst m) f
                                                            in  Unfold f' xs'' (par (rename (zip xs' xs) p') q r ((f',(xs'',p)):m) d)
                                 (f':_) -> Fold f' xs''
par p (Call f xs) r m d = let q = Compose p (Call f xs)
                              xs'' = free q \\ r
                          in  case [f' | (f',(xs',p')) <- m, not (null (renaming' p' q (zip xs' xs'')))] of
                                 [] -> case lookup f d of
                                          Nothing -> error ("Undefined process: "++f)
                                          Just (xs',p')  -> let f' = renameVar (map fst m) f
                                                            in  Unfold f' xs'' (par p (rename (zip xs' xs) p') r ((f',(xs'',q)):m) d)
                                 (f':_) -> Fold f' xs''
par p q r m d = choice (lpar p q r m d) (lpar q p r m d)

-- transform left-prioritised parallel composition

lpar (Output x y p) (Input x' y' q) r m d 
   | x `elem` r = Null
   | y `elem` r = New y (choice (par (Match x x' p) (rename [(y',y)] q) r m d) (Output x y (par p (Input x' y' q) r m d)))
   | otherwise = choice (par (Match x x' p) (rename [(y',y)] q) r m d) (Output x y (par p (Input x' y' q) r m d))
lpar (Output x y p) q r m d 
   | x `elem` r = Null
   | y `elem` r = New y (Output x y (par p q r m d))
   | otherwise = Output x y (par p q r m d)
lpar (Input x y p) q r m d 
   | x `elem` r = Null
   | otherwise = let y' = renameVar (free (Compose (Input x y p) q)) y
                 in  Input x y' (par (rename [(y,y')] p) q r m d)
lpar (Tau p) q r m d = Tau (par p q r m d)
lpar Null q r m d = Null

choice Null p = p
choice p Null = p
choice p q = Choice p q

-- residualise result of transformation

residualise p d = residualise' p [] d

residualise' Null m d = (Null,d)
residualise' (Input x y p) m d = let (p',d') = residualise' p m d
                                 in  (Input x y p',d')
residualise' (Output x y p) m d = let (p',d') = residualise' p m d
                                  in  (Output x y p',d')
residualise' (Tau p) m d = let (p',d') = residualise' p m d
                           in  (Tau p',d')
residualise' (New x p) m d = let (p',d') = residualise' p m d
                             in  (New x p',d')
residualise' (Compose p q) m d = let (p',d') = residualise' p m d
                                     (q',d'') = residualise' q m d'
                                 in  (Compose p' q',d'')
residualise' (Compose' p q) m d = let (p',d') = residualise' p m d
                                      (q',d'') = residualise' q m d'
                                  in  (Compose' p' q',d'')
residualise' (Match x y p) m d = let (p',d') = residualise' p m d
                                 in  (Match x y p',d')
residualise' (Choice p q) m d = let (p',d') = residualise' p m d
                                    (q',d'') = residualise' q m d'
                                in  (Choice p' q',d'')
residualise' (Call f xs) m d = (Call f xs,d)
residualise' (Unfold f xs p) m d = if   f `elem` folds p
                                   then let f' = renameVar (map fst m ++ map fst d) f
                                            (p',d') = residualise' p ((f,f'):m) d
                                        in  (Call f' xs,(f',(xs,p')):d')
                                   else residualise' p m d
residualise' (Fold f xs) m d = case lookup f m of
                                  Nothing -> error ("Unmatched fold: " ++ f)
                                  Just f' -> (Call f' xs,d)

-- folds in a transformed process

folds Null = []
folds (Input x y p) = folds p
folds (Output x y p) = folds p
folds (Tau p) = folds p
folds (New x p) = folds p
folds (Compose p q) = folds p ++ folds q
folds (Compose' p q) = folds p ++ folds q
folds (Match x y p) = folds p
folds (Choice p q) = folds p ++ folds q
folds (Call f xs) = []
folds (Unfold f xs p) = [f' | f' <- folds p, f/=f']
folds (Fold f xs) = [f]