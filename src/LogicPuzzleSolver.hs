{-# LANGUAGE OverloadedStrings #-}

module LogicPuzzleSolver where

import           BoolExpressions
import           BoolSolver
import           Data.List       as L
import qualified Data.Map        as M
import           Data.Maybe
import           Debug.Trace

data Pair a = Pair a a deriving (Eq,Ord)
data Puzzle = Puzzle [Class] [Term (Pair ClassMember)] deriving Show

type Class = [ClassMember]
type ClassMember = String

instance (Show a) => Show (Pair a) where
  show (Pair a b) = show a ++ "=" ++ show b

pair :: Ord a => a -> a -> Pair a
pair a1 a2
  | a1 <= a2 = Pair a1 a2
  | otherwise = Pair a2 a1

singlePairExclusive :: (Ord a) => [a] -> [a] -> a -> a -> Term (Pair a)
singlePairExclusive c1 c2 el1 el2 = ands $ Var truePair : falseVars
  where
    truePair = pair el1 el2
    isNotTruePair = not . (==) truePair
    falsePairs = L.filter isNotTruePair $ L.map (pair el1) c2 ++ L.map (pair el2) c1
    falseVars = nots $ L.map Var falsePairs

optionsForVar :: Ord a => [a] -> [a] -> a -> Term (Pair a)
optionsForVar c1 c2 el1 = ors $ L.map (singlePairExclusive c1 c2 el1) c2

oneToOnePairing :: (Ord a) => [a] -> [a] -> Term (Pair a)
oneToOnePairing n1 n2 = ands $ L.map (optionsForVar n1 n2) n1

joinConstraint :: Ord a => a -> a -> a -> Term (Pair a)
joinConstraint a b c = ors [ands [Var (pair a b), Var (pair b c), Var (pair a c)],
                            ands [notvar (pair a b), notvar (pair b c), notvar (pair a c)],
                            ands [notvar (pair a b), notvar (pair b c), Var (pair a c)],
                            ands [Var (pair a b), notvar (pair b c), notvar (pair a c)],
                            ands [notvar (pair a b), Var (pair b c), notvar (pair a c)]]

allJoinConstraints :: (Ord a) => [[a]] -> Term (Pair a)
allJoinConstraints classes
  | L.length classes > 2 = ands $ L.map joins setsOfThree
    where
      setsOfThree = L.filter ((== 3).length) $ subsequences classes
      joins [a,b,c] = ands $ joinConstraint <$> a <*> b <*> c

allPairingConstraints :: (Ord a) => [[a]] -> Term (Pair a)
allPairingConstraints classes = ands $ L.map oto classPairs
  where
    classPairs = L.filter ((== 2).length) $ subsequences classes
    oto [a,b] = oneToOnePairing a b

puzzleExpression :: Puzzle -> Term (Pair ClassMember)
puzzleExpression (Puzzle classes rules) = ands $ rules ++ [ allJoinConstraints classes, allPairingConstraints classes]

getClass :: (Eq a) => a -> [[a]] -> ([a],[[a]])
getClass a cs = (fromJust $ L.find hasIt cs, L.filter (not . hasIt) cs) where
  hasIt = elem a

insertAll :: (Ord a) => [a] -> b -> M.Map a b -> M.Map a b
insertAll as b = foldl' (.) id $ (`M.insert` b) <$> as

pairingConstraintsAssignment :: (Ord a) => a -> [a] -> a -> [a] -> Assignment (Pair a)
pairingConstraintsAssignment a1 c1 a2 c2 = insertAll pairsToAssign False M.empty where
  pairsToAssign = L.filter (/= pair a1 a2) (pair a1 <$> c2) ++ (pair a2 <$> c1)


trade :: (Ord a) => a -> a -> Pair a -> Pair a
trade target result (Pair a b)
  | a == target = pair result b
  | b == target = pair a result
  | otherwise = pair a b

joinConstraintsAssignment :: (Ord a) => a -> [[a]] -> a -> [[a]] -> Assignment (Pair a) -> Assignment (Pair a)
joinConstraintsAssignment a1 others1 a2 others2 currAssign = M.union truths falses where
  isAssignedTrue = L.filter (fromMaybe False . (`M.lookup` currAssign))
  isAssignedFalse = L.filter (maybe False not . (`M.lookup` currAssign))
  pairsToAssignFor1 = map (trade a1 a2) $ isAssignedTrue $ map (pair a1) (concat others1)
  pairsToAssignFor2 = map (trade a2 a1) $ isAssignedTrue $ map (pair a2) (concat others2)
  pairsToDisjoinFor1 = map (trade a1 a2) $ isAssignedFalse $ map (pair a1) (concat others1)
  pairsToDisjoinFor2 = map (trade a2 a1) $ isAssignedFalse $ map (pair a2) (concat others2)
  truths = insertAll (pairsToAssignFor1 ++ pairsToAssignFor2) True M.empty
  falses = insertAll (pairsToDisjoinFor1 ++ pairsToDisjoinFor2) False M.empty

applyContraints :: Puzzle -> Pair ClassMember -> Bool -> Assignment (Pair ClassMember) -> Assignment (Pair ClassMember)
applyContraints (Puzzle classes rules) pr@(Pair c1 c2) True currAssigns = M.union (M.insert pr True currAssigns) allConstraints where
  (class1, others1) = getClass c1 classes
  (class2, others2) = getClass c2 classes
  pairConstraints = pairingConstraintsAssignment c1 class1 c2 class2
  joinConstraints = joinConstraintsAssignment c1 others1 c2 others2 currAssigns
  allConstraints = M.union pairConstraints joinConstraints
applyContraints _ pr False currAssigns = M.insert pr False currAssigns


solve :: Puzzle -> Maybe (Assignment (Pair ClassMember))
solve p = truths <$> createAssignment (puzzleExpression p) (applyContraints p)

nLessThan :: (Ord a) => a -> a -> [a] -> Int -> Term (Pair a)
nLessThan _ _ [] _ = error "Empty class"
nLessThan a b cs n = nLessThanHelper a b cs (drop n cs) where
  nLessThanHelper el1 el2 (v1:_) [v2] = And (Var (pair el1 v1)) (Var (pair el2 v2))
  nLessThanHelper el1 el2 (v1:el1Vals) (v2:el2Vals) =
    Or (And (Var (pair el1 v1)) (Var (pair el2 v2))) (nLessThanHelper el1 el2 el1Vals el2Vals)

lessThan :: Ord a => a -> a -> [a] -> Term (Pair a)
lessThan a b cs = ors $ L.map (nLessThan a b cs) [1..(length cs - 1)]

greaterThan :: Ord a => a -> a -> [a] -> Term (Pair a)
greaterThan a b = lessThan b a

nGreaterThan :: Ord a => a -> a -> [a] -> Int -> Term (Pair a)
nGreaterThan a b = nLessThan b a

isOneOf :: Ord a => a -> a -> a -> Term (Pair a)
isOneOf a b c = xor (Var (pair a b)) (Var (pair a c))

allDisjointRule :: (Ord a) => [a] -> Term (Pair a)
allDisjointRule [a1,a2] = notvar (pair a1 a2)
allDisjointRule (a:as) = And (ands $ map (notvar.pair a) as) (allDisjointRule as)

matchTo :: (Ord a) => [a] -> [a] -> Term (Pair a)
matchTo [a1,a2] [b1,b2] = ands [Or (mkAnd (pair a1 b1) (pair a2 b2)) (mkAnd (pair a1 b2) (pair a2 b1)),
                                      notvar $ pair a1 a2,
                                      notvar $ pair b1 b2]
matchTo _ _ = error "matchTo only works on a pair of pairs"

is :: (Ord a) => a -> a -> Term (Pair a)
is a b = Var $ pair a b

isNot :: (Ord a) => a -> a -> Term (Pair a)
isNot a b = notvar $ pair a b

dates = ["6","13","20","27","4", "11","18"]
survivors = ["colin","darrell","hector","jon","pedro","steven","victor"]
countries = ["bol","cam","kir","mya","nic","new","van"]
tools = ["duct","fire","hatchet","knife","pot","rope","water"]
rule1 = "knife" `isOneOf` "bol" $ "13"
rule2 = ["20","pot"] `matchTo` ["mya","jon"]
rule3 = greaterThan "mya" "nic" dates
rule4 = "colin" `isOneOf` "rope" $ "4"
rule5 = greaterThan "new" "cam" dates
rule6 = "pedro" `is` "13"
rule7 = allDisjointRule ["van","20","jon","water","4","pedro","18"]
rule8 = nGreaterThan "steven" "jon" dates 3
rule9 = greaterThan "cam" "jon" dates
rule10 = "4" `is` "knife"
rule11 = "fire" `isOneOf` "hector" $ "18"
rule12 = "rope" `isOneOf` "20" $ "6"
rule13 = "colin" `isNot` "bol"
rule14 = ["darrell","rope"] `matchTo` ["new","20"]
rule15 = nLessThan "hatchet" "kir" dates 3

z = Puzzle [dates, survivors, countries, tools]
  [rule1, rule2, rule3, rule4, rule5, rule6, rule7, rule8, rule9, rule10, rule11, rule12, rule13, rule14, rule15]

showSolution :: (Show a) => Assignment a -> String
showSolution a = L.foldl1' (++) $ L.map ((++ "\n") . show) (M.keys (truths a))

solveAndPrint :: Puzzle -> IO ()
solveAndPrint p = fromMaybe (putStrLn "No Solution") (putStrLn <$> (showSolution <$> solve p))
