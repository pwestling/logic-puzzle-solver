{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module BoolSolver where

import           Control.Parallel
import           Data.List        as L
import           Data.Map.Strict  as M
import           Data.Maybe
import           GHC.Generics     (Generic)
import           Safe             as S

import           BoolExpressions

type Assignment a = M.Map a Bool

force :: Term a -> ()
force t = force' t `pseq` () where
  force' (And t1 t2) = force' t1 + force' t2
  force' (Or t1 t2) = force' t1 + force' t2
  force' (Not t) = force' t
  force' (Var a) = 1
  force' T = 1
  force' F = 1


consistent :: Assignment a -> Term a -> Bool
consistent a t = fromMaybe True (consistentHelper a t) where
  consistentHelper an (Var n) = Nothing
  consistentHelper an (Not t1) = fmap not $! consistentHelper an t1
  consistentHelper an (Or t1 t2) = Just $! consistent an t1 || consistent an t2
  consistentHelper an (And t1 t2) = Just $! consistent an t1 && consistent an t2
  consistentHelper an T = Just True
  consistentHelper an F = Just False

simp :: Term a -> Term a
simp (And T F) = F
simp (And F F) = F
simp (And F T) = F
simp (And T T) = T
simp (Or F F) = F
simp (Or T F) = T
simp (Or F T) = T
simp (Or T T) = T
simp (Not T) = F
simp (Not F) = T
simp t = t

toTerm :: Bool -> Term a
toTerm True = T
toTerm False = F

sub :: Term a -> Assignment a -> Term a
sub (And t1 t2) a = {-# SCC "sub-and" #-} simp $! And (sub t1 a) (sub t2 a)
sub (Or t1 t2) a = {-# SCC "sub-or" #-} simp $! Or (sub t1 a) (sub t2 a)
sub (Not t) a = {-# SCC "sub-not" #-} simp $! Not (sub t a)
sub var@(Var v) a = {-# SCC "sub-var" #-} maybe var toTerm (M.lookup v a)
      -- subHelper var@(Var v) a
      --   | v == a  = M.lookup
      --   | otherwise = var
sub t a = {-# SCC "sub-other" #-} simp t

getVars :: (Ord a) => Term a -> [a]
getVars t = nub $ f t where
  f (Var s) = [s]
  f (And t1 t2) = f t1 ++ f t2
  f (Or t1 t2) = f t1 ++ f t2
  f (Not t1) = f t1

deleteAll :: (Eq a) => [a] -> [a] -> [a]
deleteAll toDelete = L.foldl' (.) id $ L.delete <$> toDelete

nextGuess :: (Ord a) => Assignment a -> (a -> Bool -> Assignment a -> Assignment a) -> a -> [a] -> Term a -> Maybe (Assignment a)
nextGuess assign aTrans curr others term
  | isJust (falseGuess `par` trueGuess) = trueGuess
  | otherwise = falseGuess
  where
    next = headMay others
    remain = tail others
    remainTrue = deleteAll (keys newAssignsTrue) remain
    remainFalse = deleteAll (keys newAssignsFalse) remain
    trueGuess = nextSearchStep assignTrue aTrans next remainTrue (force trueExp `pseq` trueExp)
    falseGuess = nextSearchStep assignFalse aTrans next remainFalse (force falseExp `pseq` falseExp)
    falseExp = sub term newAssignsFalse
    trueExp = sub term newAssignsTrue
    assignFalse = aTrans curr False assign
    newAssignsFalse = M.difference assignFalse assign
    assignTrue = aTrans curr True assign
    newAssignsTrue = M.difference assignTrue assign

nextSearchStep :: (Eq a, Ord a) => Assignment a -> (a -> Bool -> Assignment a -> Assignment a) -> Maybe a -> [a] -> Term a -> Maybe (Assignment a)
nextSearchStep currAssign aTrans currVar nextVars term
  | isConsistent && isNothing currVar = Just currAssign -- Success Here
  | isConsistent && isJust guess = guess -- Success at a deeper level
  | otherwise = Nothing -- Go back
  where
    isConsistent = consistent currAssign term
    curVarVal = fromMaybe (error "Should only eval if there's a next term") currVar
    guess = nextGuess currAssign aTrans curVarVal nextVars term

mentions :: Term a -> a -> Int
mentions (Var t) a
  | a == t = 1
  | otherwise = 0
mentions (And t1 t2) a = mentions t1 a + mentions t2 a
mentions (Or t1 t2) a = mentions t1 a + mentions t2 a
mentions (Not t) a = mentions t a

createAssignment :: (Ord a) => Term a -> (a -> Bool -> Assignment a -> Assignment a) -> Maybe (Assignment a)
createAssignment t aTrans = nextSearchStep M.empty aTrans (headMay vars) (tail vars) t where
  vars = reverse $ L.sortOn (mentions t) (getVars t)

truths :: Assignment a -> Assignment a
truths = M.filter id
