{-# LANGUAGE GADTs              #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}

module BoolExpressions where

import           Data.List   as L
import           Data.String

data Term a where
  And :: Term a -> Term a -> Term a
  Or :: Term a -> Term a -> Term a
  Not :: Term a -> Term a
  Var :: (Ord a, Eq a) => a -> Term a
  T :: Term a
  F :: Term a

deriving instance Eq (Term a)

instance (Ord a, IsString a) => IsString (Term a) where
  fromString ('~':s) = Not (fromString s)
  fromString s = Var (fromString s)

instance (Show a) => Show (Term a) where
  show a@(And _ _) = "(" ++ foldl1' concatAnds (andList a) ++ ")" where
    andList (And a1@(And _ _ ) a2@(And _ _)) = andList a1 ++ andList a2
    andList (And a1@(And _ _ ) t2) = andList a1 ++ [show t2]
    andList (And t1 a2@(And _ _)) = show t1 : andList a2
    andList (And t1 t2) = [show t1, show t2]
    concatAnds x y = x ++ " ∧ " ++ y
  show o@(Or _ _) = "(" ++ foldl1' concatOrs (orList o) ++ ")" where
    orList (Or o1@(Or _ _ ) o2@(Or _ _)) = orList o1 ++ orList o2
    orList (Or o1@(Or _ _ ) t2) = orList o1 ++ [show t2]
    orList (Or t1 o2@(Or _ _)) = show t1 : orList o2
    orList (Or t1 t2) = [show t1, show t2]
    concatOrs x y = x ++ " ∨ " ++ y
  show (Not t1) = "~"++show t1
  show (Var s) = show s

ands :: [Term a] -> Term a
ands = L.foldl1' And

ors :: [Term a] -> Term a
ors = L.foldl1' Or

nots :: [Term a] -> [Term a]
nots = L.map Not

cnf :: [[Term a]] -> Term a
cnf = ands . L.map ors

andOfOrs :: [[Term a]] -> Term a
andOfOrs = cnf

dnf :: [[Term a]] -> Term a
dnf = ors . L.map ands

orOfAnds :: [[Term a]] -> Term a
orOfAnds = dnf

notvar :: Ord a => a -> Term a
notvar a = Not $ Var a

(==>) :: Term a -> Term a -> Term a
t1 ==> t2 =  dnf [[t1,t2],[Not t2, Not t1], [t2, Not t1]]

xor :: Ord a => Term a -> Term a -> Term a
xor t1 t2 = Or (And t1 (Not t2)) (And (Not t1) t2)

mkOr :: (Ord a) => a -> a -> Term a
mkOr a b = Or (Var a) (Var b)

mkAnd :: (Ord a) => a -> a -> Term a
mkAnd a b = And (Var a) (Var b)

exactlyOne :: [Term a] -> Term a
exactlyOne (t:ts) =  f [] t ts -- (t1 and ~t2 and ~t3) or (~t1 and t2 and ~t3) etc.
  where f past current next@(n:ns) = Or (ands $ nots past ++ [current] ++ nots next) (f (past ++ [current]) n ns)
        f past current [] = ands $ nots past ++ [current]

applySimplifyStrat :: (Term a -> Term a) -> Term a -> Term a
applySimplifyStrat strat (And t1 t2) = strat (And (strat t1) (strat t2))
applySimplifyStrat strat (Or t1 t2) = strat (Or (strat t1) (strat t2))
applySimplifyStrat strat (Not t1) = strat (Not (strat t1))
applySimplifyStrat strat t = t

deMorgan :: Term a -> Term a
deMorgan (Not (And t1 t2)) = Or (Not t1) (Not t2)
deMorgan (Not (Or t1 t2)) = And (Not t1) (Not t2)
deMorgan t = t

doubleNeg :: Term a -> Term a
doubleNeg (Not (Not a)) = a
doubleNeg a = a

distribute :: Term a -> Term a
distribute (Or p (And q r)) = And (Or p q) (Or p r)
distribute (Or (And q r) p) = And (Or p q) (Or p r)
distribute t = t

stabilize :: Eq t => (t -> t) -> t -> t
stabilize f x   | x == y    = x
                | otherwise = stabilize f y
                where y = f x

simplify :: Term a -> Term a
simplify = stabilize (applySimplifyStrat distribute .
                      applySimplifyStrat doubleNeg .
                      applySimplifyStrat deMorgan)
