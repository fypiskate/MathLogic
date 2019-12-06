module FindMin where

import Synt(parser)
import Lex
import Expr

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe
import Data.Bits
import Data.List

makeSetFromExpr:: Ex -> S.Set Ex -> S.Set Ex
makeSetFromExpr ( BinOper op ex1 ex2 ) sset = S.insert (BinOper op ex1 ex2) newSet 
    where
        newSet = S.union (makeSetFromExpr ex1 sset) (makeSetFromExpr ex2 sset)   
makeSetFromExpr ( Not ex ) sset = S.insert (Not ex) newSet
    where newSet = makeSetFromExpr ex sset
makeSetFromExpr ex sset = S.insert ex sset  

isVar:: Ex -> Bool
isVar (Var ex) = True
isVar _ = False 

make_1_map::String -> [M.Map String Bool]
make_1_map a = mmap
    where mmap = [M.insert a False M.empty] 
              ++ [M.insert a True M.empty]

make_2_maps::String -> String -> [M.Map String Bool]
make_2_maps a b = mmap
    where mmap = [M.insert a False (M.insert b False M.empty)]
              ++ [M.insert a False (M.insert b True M.empty)]
              ++ [M.insert a True (M.insert b False M.empty)]
              ++ [M.insert a True (M.insert b True M.empty)]

make_3_maps::String -> String -> String -> [M.Map String Bool]
make_3_maps a b c = mmap
    where mmap = [M.insert a False (M.insert b False (M.insert c False M.empty))]
              ++ [M.insert a False (M.insert b False (M.insert c True M.empty))]
              ++ [M.insert a False (M.insert b True (M.insert c False M.empty))]
              ++ [M.insert a False (M.insert b True (M.insert c True M.empty))]
              ++ [M.insert a True (M.insert b False (M.insert c False M.empty))]
              ++ [M.insert a True (M.insert b False (M.insert c True M.empty))]
              ++ [M.insert a True (M.insert b True (M.insert c False M.empty))]
              ++ [M.insert a True (M.insert b True (M.insert c True M.empty))]

is_axiom :: Ex -> Bool
is_axiom e = case e of
    (BinOper Impl a (BinOper Impl b c)) | a == c -> True
    (BinOper Impl (BinOper Impl a b) (BinOper Impl (BinOper Impl c (BinOper Impl d e)) (BinOper Impl f g ))) | a == c && a == f && b == d && e == g -> True
    (BinOper Impl a (BinOper Impl b (BinOper And c d))) | a == c && b == d -> True
    (BinOper Impl (BinOper And a b) c) | a == c -> True
    (BinOper Impl (BinOper And a b) c) | b == c -> True
    (BinOper Impl a (BinOper Or b c)) | a == b -> True
    (BinOper Impl a (BinOper Or b c)) | a == c -> True
    (BinOper Impl (BinOper Impl a b) (BinOper Impl (BinOper Impl c d) (BinOper Impl (BinOper Or e f) g))) | a == e && b == d && b == g && c == f -> True
    (BinOper Impl (BinOper Impl a b) (BinOper Impl (BinOper Impl c d) e)) | a == c && Not b == d && Not a == e -> True
    (BinOper Impl (Not (Not a)) b) | a == b -> True
    _ -> False

is_axiom_or_hypothesis :: Ex -> S.Set Ex -> Bool
is_axiom_or_hypothesis e hyps = is_axiom e || (S.member e hyps)

impl::Bool -> Bool -> Bool
impl False False = True
impl False True = True
impl True False = False
impl True True = True

returnBool:: M.Map String Bool -> Ex -> Bool
returnBool vars (BinOper Or ex1 ex2) = (returnBool vars ex1) || (returnBool vars ex2)
returnBool vars (BinOper And ex1 ex2) = (returnBool vars ex1) && (returnBool vars ex2)
returnBool vars (BinOper Impl ex1 ex2) = (returnBool vars ex1) `impl` (returnBool vars ex2)
returnBool vars (Not ex) = not $ returnBool vars ex 
returnBool vars (Var str) = fromMaybe False (M.lookup str vars)

xor':: Maybe Bool -> Maybe Bool -> Bool
xor' (Just a) (Just b) = a `xor` b
xor' _ _ = False

sum_of_difference:: [String] -> M.Map String Bool -> M.Map String Bool -> (Int, String) -> (Int, String)
sum_of_difference [] fstmap sndmap (sum, dif) = (sum, dif)
sum_of_difference (v:vars) fstmap sndmap (sum, dif) = do
    let first = M.lookup v fstmap
    let second = M.lookup v sndmap
    if xor' first second
    then sum_of_difference vars fstmap sndmap (sum + 1, v)
    else sum_of_difference vars fstmap sndmap (sum, dif)

try_to_delete::[String] -> M.Map String Bool -> [M.Map String Bool] -> [(M.Map String Bool, String)] -> [(M.Map String Bool, String)]
try_to_delete vars fstmap [] minlist = minlist
try_to_delete vars fstmap (s:sndmaps) minlist = do
    if ((M.keys fstmap) == (M.keys s)) 
    then do
        let sumDif = sum_of_difference vars fstmap s (0, "")
        if fst sumDif == 1
        then try_to_delete vars fstmap sndmaps (minlist ++ [(s, snd sumDif)])
        else try_to_delete vars fstmap sndmaps minlist
    else try_to_delete vars fstmap sndmaps minlist 


cutMaps::[(M.Map String Bool, String)] -> [M.Map String Bool] -> [M.Map String Bool]
cutMaps [] result = result
cutMaps (m:maps) result = do
    let var = snd m
    let newMap = M.delete var (fst m)
    cutMaps maps (result ++ [newMap]) 

minimization::[String] -> [M.Map String Bool] -> [M.Map String Bool] -> [M.Map String Bool]
minimization vars [] minTable = minTable
minimization vars (l:logicMaps) minTable = do
    let minList = try_to_delete vars l logicMaps [] 
    if minList == []
    then minimization vars logicMaps minTable
    else do
        let newList = cutMaps minList [] 
        minimization vars logicMaps (minTable ++ newList)

good_minlist::[M.Map String Bool] -> Bool
good_minlist [] = False
good_minlist (x:xs) = bool || good_minlist xs
    where
    only_false_map = M.filter (== False) x
    len = M.size only_false_map
    bool = (len == 0)
    
find_min_true_hyps::Int -> [String] -> [M.Map String Bool] -> [M.Map String Bool]
find_min_true_hyps 0 vars maps = maps
find_min_true_hyps n vars maps = do 
    let minlist = minimization vars maps [] 
    if minlist == [] 
    then find_min_true_hyps 0 vars maps 
    else do
        if good_minlist minlist
        then find_min_true_hyps (n-1) vars minlist
        else find_min_true_hyps 0 vars maps

bad_minlist::[M.Map String Bool] -> Bool
bad_minlist [] = False
bad_minlist (x:xs) = bool || good_minlist xs
    where
    only_true_map = M.filter (== True) x
    len = M.size only_true_map
    bool = (len == 0)
    
find_min_false_hyps::Int -> [String] -> [M.Map String Bool] -> [M.Map String Bool]
find_min_false_hyps 0 vars maps = maps
find_min_false_hyps n vars maps = do 
    let minlist = minimization vars maps [] 
    if minlist == [] 
    then find_min_false_hyps 0 vars maps 
    else do
        if bad_minlist minlist
        then find_min_false_hyps (n-1) vars minlist
        else find_min_false_hyps 0 vars maps

trueOrFalse::[M.Map String Bool] -> Ex -> ([M.Map String Bool], [M.Map String Bool]) -> ([M.Map String Bool], [M.Map String Bool])
trueOrFalse [] ex pair = pair
trueOrFalse (l:logicTable) ex (listTrue, listFalse) 
                                        =  trueOrFalse logicTable ex (newListTrue,  newListFalse)
    where
         newListTrue = case (returnBool l ex) of
             True  -> listTrue ++ [l]
             False -> listTrue
         newListFalse = case (returnBool l ex) of
             True  -> listFalse
             False -> listFalse ++ [l]

make_maps::Int -> [String] -> [M.Map String Bool]
make_maps 0 vars = []
make_maps 1 vars = make_1_map  (head vars)
make_maps 2 vars = make_2_maps (head vars) (head $ tail vars)
make_maps 3 vars = make_3_maps (head vars) (head $ tail vars) (head $ tail $ tail vars)

trueMap::[String] -> M.Map String Bool -> M.Map String Bool
trueMap [] mmap = mmap
trueMap (v:vars) mmap = trueMap vars (M.insert v True mmap)

falseMap::[String] -> M.Map String Bool -> M.Map String Bool
falseMap [] mmap = mmap
falseMap (v:vars) mmap = falseMap vars (M.insert v False mmap)

forecast::[String] -> Ex -> Int -> Int
forecast [] ex n = n
forecast vars ex n = do
    if returnBool (trueMap vars M.empty) ex
    then forecast [] ex 1
    else do
        if returnBool (falseMap vars M.empty) ex
        then forecast [] ex 3
        else forecast [] ex 2 

check_true::[(String, Bool)] -> Bool
check_true [] = True
check_true (x:xs) = (snd x) && check_true xs

check_false::[(String, Bool)] -> Bool
check_false [] = False
check_false (x:xs) = (snd x) || check_false xs

return_true_hyps::[M.Map String Bool] -> M.Map String Bool -> M.Map String Bool
return_true_hyps [] mmap = mmap
return_true_hyps (m:maps) mmap = do
    if check_true (M.toList m)
    then return_true_hyps [] m
    else return_true_hyps maps mmap

return_false_hyps::[M.Map String Bool] -> M.Map String Bool -> M.Map String Bool
return_false_hyps [] mmap = mmap
return_false_hyps (m:maps) mmap = do
    if not  $ check_false (M.toList m)
    then return_false_hyps [] m
    else return_false_hyps maps mmap

