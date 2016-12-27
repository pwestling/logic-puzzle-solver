{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}

module BoolExpressions where

import           Data.List   as L
import           Data.String

type Name = String


data Term a where
  And :: Term a -> Term a -> Term a
  Or :: Term a -> Term a -> Term a
  Not :: Term a -> Term a
  Var :: (Ord a) => a -> Term a

instance (Ord a, IsString a) => IsString (Term a) where
  fromString ('~':s) = Not (fromString s)
  fromString s = Var (fromString s)

instance (Ord a, Show a) => Show (Term a) where
  show (And t1 t2) = "(" ++ show t1 ++ " ∧ " ++ show t2 ++ ")"
  show (Or t1 t2) = "(" ++ show t1 ++ " ∨ " ++ show t2 ++ ")"
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

andOfOrs = cnf

dnf :: [[Term a]] -> Term a
dnf = ors . L.map ands

orOfAnds = dnf

(==>) :: Term a -> Term a -> Term a
t1 ==> t2 =  dnf [[t1,t2],[Not t2, Not t1], [t2, Not t1]]

exactlyOne :: [Term a] -> Term a
exactlyOne (t:ts) =  f [] t ts -- (t1 and ~t2 and ~t3) or (~t1 and t2 and ~t3) etc.
  where f past current next@(n:ns) = Or (ands $ nots past ++ [current] ++ nots next) (f (past ++ [current]) n ns)
        f past current [] = ands $ nots past ++ [current]
