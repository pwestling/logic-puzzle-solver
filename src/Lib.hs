module Lib where

import           Data.List       as L
import           Data.Map.Strict as M
import           Data.Maybe
import           Safe            as S

type Assignment = M.Map Name Bool
type Name = String

data Term =
  And Term Term |
  Or Term Term |
  Not Term |
  Var Name

instance Show Term where
  show (And t1 t2) = "(" ++ show t1 ++ " ∧ " ++ show t2 ++ ")"
  show (Or t1 t2) = "(" ++ show t1 ++ " ∨ " ++ show t2 ++ ")"
  show (Not t1) = "~"++show t1
  show (Var s) = s

ands :: [Term] -> Term
ands [t] = t
ands (t:ts) = And t (ands ts)

consistent :: Assignment -> Term -> Bool
consistent a t = fromMaybe True (consistentHelper a t) where
  consistentHelper a (Var n) = M.lookup n a
  consistentHelper a (Not t) = fmap not (consistentHelper a t)
  consistentHelper a (Or t1 t2) = Just $ consistent a t1 || consistent a t2
  consistentHelper a (And t1 t2) = Just $ consistent a t1 && consistent a t2

getVars :: Term -> [Name]
getVars t = nub $ f t where
  f (Var s) = [s]
  f (And t1 t2) = f t1 ++ f t2
  f (Or t1 t2) = f t1 ++ f t2
  f (Not t) = f t


mtrue :: Assignment -> Name -> Assignment
mtrue a n = M.insert n True a

mfalse :: Assignment -> Name -> Assignment
mfalse a n = M.insert n False a

nextGuess :: Assignment -> Maybe Name -> [Name] -> Term -> Maybe Assignment
nextGuess assign (Just curr) others term
  | isJust trueGuess = trueGuess
  | otherwise = falseGuess where
    next = S.headMay others
    remain = tail others
    trueGuess = nextSearchStep (mtrue assign curr) next remain term
    falseGuess = nextSearchStep (mfalse assign curr) next remain term
nextGuess _ _ _ _ = error "There should be a next variable here"

nextSearchStep :: Assignment -> Maybe Name -> [Name] -> Term -> Maybe Assignment
nextSearchStep currAssign currVar nextVars term
  | isConsistent && isNothing currVar = Just currAssign -- Success Here
  | isConsistent && isJust guess = guess -- Success at a deeper level
  | otherwise = Nothing -- Go back
  where
    isConsistent = consistent currAssign term
    guess = nextGuess currAssign currVar nextVars term

createAssignment :: Term -> Maybe Assignment
createAssignment t = nextSearchStep M.empty (S.headMay vars) (tail vars) t where
  vars = getVars t
