module Merger where

import Synt(parser)
import Lex
import Expr
import FindMin
import ProofGenerate

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe
import Data.Bits
import Data.List

addInMaps::[(String, Bool)] -> [M.Map String Bool] -> [M.Map String Bool]
addInMaps [] maps = maps
addInMaps (h:hyps) maps = addInMaps hyps (map (M.insert (fst h) (snd h)) maps)

returnNotHyps::[String] -> M.Map String Bool -> [String] -> [String]
returnNotHyps [] hyps nothyps = nothyps
returnNotHyps (v:vars) hyps nothyps = returnNotHyps vars hyps newnot
    where newnot = case M.lookup v hyps of
                   Just key -> nothyps
                   Nothing -> nothyps ++ [v]

goToSimple::[String] -> [String] -> M.Map String Bool -> [M.Map String Bool] -> [M.Map String Bool]
goToSimple [] freevars minhyps allhyps = allhyps
goToSimple vars [] minhyps allhyps = [minhyps]
goToSimple vars freevars minhyps allhyps = do
    let logicTable = make_maps (length $ freevars) freevars
    let allVarMaps = addInMaps (M.toList minhyps) logicTable
    goToSimple [] freevars minhyps allVarMaps

fromLogicStrToSetEx::[(String, Bool)] -> S.Set Ex -> S.Set Ex
fromLogicStrToSetEx [] sset = sset
fromLogicStrToSetEx (l:logic) sset = case snd l of
                                     True -> S.insert (Var (fst l)) (fromLogicStrToSetEx logic sset)
                                     False -> S.insert (Not (Var (fst l))) (fromLogicStrToSetEx logic sset)

fromStrToEx::M.Map String Bool -> String -> Ex
fromStrToEx logicmap var = case logicmap M.! var of
                           True -> Var var
                           False -> Not (Var var)

fromListToMpMap::[Ex] -> M.Map Ex Ex -> M.Map Ex Ex
fromListToMpMap [] mpmap = mpmap
fromListToMpMap (e:exs) mpmap = case e of
                                (BinOper Impl ex1 ex2) -> fromListToMpMap exs (M.insert ex2 ex1 mpmap)
                                _ -> fromListToMpMap exs mpmap

packToAnswer::[M.Map String Bool] -> [String] -> Ex -> S.Set Ex -> [String] -> [String]
packToAnswer [] freevars ex setSubExpr proof = proof
packToAnswer (l:logic) freevars ex setSubExpr proof = packToAnswer logic freevars ex setSubExpr (proof ++ (doingDeduction l freevars ex [] setSubExpr)) 


doingDeduction::M.Map String Bool -> [String] -> Ex -> [String] -> S.Set Ex -> [String]
doingDeduction logicstr freevars ex [] setSubExpr = doingDeduction logicstr freevars ex (generate ex logicstr (from_set_to_map (S.toList setSubExpr) logicstr M.empty) []) setSubExpr
doingDeduction logicstr [] ex proof setSubExpr = proof
doingDeduction logicstr (fr:freevars) ex proof setSubExpr = doingDeduction (M.delete fr logicstr) freevars ex newproof setSubExpr
    where 
        listExpr = (map (parser . alexScanTokens) proof)
        newproof = map show $ deductionTheorem (fromLogicStrToSetEx (M.toList (M.delete fr logicstr)) S.empty) (fromStrToEx logicstr fr) ex listExpr [] M.empty S.empty


trueVars::Int -> Ex -> [String] -> [M.Map String Bool] -> [String] -> S.Set Ex -> [String]
trueVars n ex [] maps proof setSubExpr = proof
trueVars n ex vars maps proof setSubExpr = do
    let truelist = fst $ trueOrFalse maps ex ([],[])
    let goodHyps = find_min_true_hyps n vars truelist
    let answerHyps = return_true_hyps goodHyps M.empty
    let firstStr = (intercalate ", " (M.keys answerHyps)) ++ "|- " ++ (show ex)
    let freevars = returnNotHyps vars answerHyps []
    let elementaryProofs = packToAnswer (goToSimple vars freevars answerHyps []) freevars ex setSubExpr []
    let lemma = chooseLemma (reverse freevars) ex
    trueVars n ex [] maps (proof ++ [firstStr] ++ elementaryProofs ++ lemma) setSubExpr-------------------------------
    {-let logicstr = head $ goToSimple vars freevars answerHyps []
    let proof1 = generate ex (logicstr) (from_set_to_map (S.toList setSubExpr) (logicstr) M.empty) []
    let listExpr = (map (parser . alexScanTokens) proof1)
    let mpmap = fromListToMpMap listExpr M.empty
    let fr = head $ freevars
    let dodeduc1 = doingDeduction logicstr freevars ex [] setSubExpr
    let newlogicstr1 = M.delete fr logicstr
    let setEx1 = fromLogicStrToSetEx (M.toList newlogicstr1) S.empty
    let deduc1 = map show $ deductionTheorem (setEx1) (fromStrToEx logicstr fr) ex listExpr [] mpmap S.empty-----------
    ---------------
    let logicstr2 = head $ tail $ goToSimple vars freevars answerHyps []
    let proof2 = generate ex (logicstr2) (from_set_to_map (S.toList setSubExpr) (logicstr2) M.empty) []
    let listExpr2 = (map (parser . alexScanTokens) proof2)
    let mpmap2 = fromListToMpMap listExpr2 M.empty
    let fr2 = head $ freevars
    let dodeduc2 = doingDeduction logicstr2 freevars ex [] setSubExpr
    let deduc2 = map show $ deductionTheorem (fromLogicStrToSetEx (M.toList (M.delete fr2 logicstr2)) S.empty) (fromStrToEx logicstr2 fr2) ex listExpr2 [] mpmap2 S.empty----------
    ------------------
    let logicstr3 = head $ tail $ tail $ goToSimple vars freevars answerHyps []
    let proof3 = generate ex (logicstr3) (from_set_to_map (S.toList setSubExpr) (logicstr3) M.empty) []
    let listExpr3 = (map (parser . alexScanTokens) proof3)
    let mpmap3 = fromListToMpMap listExpr3 M.empty
    let fr3 = head $ freevars
    let dodeduc3 = doingDeduction logicstr3 freevars ex [] setSubExpr
    let deduc3 = map show $ deductionTheorem (fromLogicStrToSetEx (M.toList (M.delete fr3 logicstr3)) S.empty) (fromStrToEx logicstr3 fr3) ex listExpr3 [] mpmap3 S.empty-----------
    let logicstr4 = head $ tail $ tail $ tail $ goToSimple vars freevars answerHyps []
    let proof4 = generate ex (logicstr4) (from_set_to_map (S.toList setSubExpr) (logicstr4) M.empty) []
    let listExpr4 = (map (parser . alexScanTokens) proof4)
    let mpmap4 = fromListToMpMap listExpr4 M.empty
    let fr4 = head $ freevars
    let dodeduc4 = doingDeduction logicstr4 freevars ex [] setSubExpr
    let deduc4 = map show $ deductionTheorem (fromLogicStrToSetEx (M.toList (M.delete fr4 logicstr4)) S.empty) (fromStrToEx logicstr4 fr4) ex listExpr4 [] mpmap4 S.empty------------
    trueVars n ex [] maps ([firstStr] ++ elementaryProofs{-++ [fr] ++ [S.showTree setEx1] ++ [M.showTree newlogicstr1]-}) setSubExpr----------------------------------------------------------}

falseVars::Int -> Ex -> [String] -> [M.Map String Bool] -> [String] -> S.Set Ex -> [String]
falseVars n ex [] maps proof setSubExpr = proof
falseVars n ex vars maps proof setSubExpr = do
    let falselist = snd $ trueOrFalse maps ex ([],[])
    let goodHyps = find_min_false_hyps n vars falselist
    let answerHyps = return_false_hyps goodHyps M.empty
    let firstStr = (intercalate ", " (map ("!" ++)(M.keys answerHyps))) ++ " |- !" ++ (show ex)
    let negAnswerHyps = negHyps (M.keys answerHyps) M.empty
    let freevars = returnNotHyps vars negAnswerHyps []
    let elementaryProofs = packToAnswer (goToSimple vars freevars negAnswerHyps []) freevars ex setSubExpr []
    let lemma = chooseLemma (reverse freevars) (Not ex)
    falseVars n ex [] maps (proof ++ [firstStr] ++ elementaryProofs ++ lemma) setSubExpr
    {-let logicstr = head $ tail $ goToSimple vars freevars answerHyps []
    --generate:: Ex -> M.Map String Bool -> M.Map Ex Bool -> [String] -> [String]
    --generate (BinOper Impl ex1 ex2) mmap subExprBool proof
    let proof = generate ex (logicstr) (from_set_to_map (S.toList setSubExpr) (logicstr) M.empty) []
    let listExpr = (map (parser . alexScanTokens) proof)
    let mpmap = fromListToMpMap listExpr M.empty
    let fr = head $ freevars
    --deductionTheorem hyps alpha beta (p:proofB) proofImplAB mpMap
    --deductionTheorem::S.Set Ex -> Ex -> Ex -> [Ex] -> [Ex] -> M.Map Ex Ex -> [Ex]
    let deduc1 = map show $ deductionTheorem (fromLogicStrToSetEx (M.toList (M.delete fr logicstr)) S.empty) (fromStrToEx logicstr fr) ex listExpr [] mpmap
    falseVars n ex [] maps ([firstStr] ++ proof) setSubExpr-}

negHyps::[String] -> M.Map String Bool -> M.Map String Bool
negHyps [] result = result
negHyps (h:hyps) result = negHyps hyps (M.insert h False result)

add_to_mpMap::Ex -> M.Map Ex Ex -> M.Map Ex Ex
add_to_mpMap (BinOper Impl ex1 ex2) mpMap = M.insert ex2 ex1 mpMap
 {-   if M.notMember (BinOper Impl ex1 ex2) mpMap
    then add_to_mpMap (Var "BREAK") (M.insert ex2 ex1 mpMap)
    else do 
        let m = M.delete ex2 mpMap
        add_to_mpMap (Var "BREAK") (M.insert ex2 ex1 m)-}
add_to_mpMap _ mpMap = mpMap

deductionTheorem::S.Set Ex -> Ex -> Ex -> [Ex] -> [Ex] -> M.Map Ex Ex -> S.Set Ex -> [Ex]
deductionTheorem hyps alpha beta [] proofImplAB mpMap setAbove = proofImplAB
deductionTheorem hyps alpha beta (pi:proofB) proofImplAB mpMap setAbove = do
    if S.member pi setAbove
    then do
        let m1 = add_to_mpMap pi mpMap
        deductionTheorem hyps alpha beta proofB (proofImplAB ++ [BinOper Impl alpha pi]) m1 setAbove
    else do
        if is_axiom_or_hypothesis pi hyps
        then do
            let newProof = proofImplAB ++ [pi] 
                                       ++ [BinOper Impl pi (BinOper Impl alpha pi)]
                                       ++ [BinOper Impl alpha pi]
            let m1 = add_to_mpMap pi mpMap
            deductionTheorem hyps alpha beta proofB newProof m1 (S.insert pi setAbove)
        else do
            if pi == alpha
            then do
                let newProof = proofImplAB ++ [BinOper Impl pi (BinOper Impl pi pi)]
                                           ++ [BinOper Impl (BinOper Impl pi (BinOper Impl pi pi)) (BinOper Impl (BinOper Impl pi (BinOper Impl (BinOper Impl pi pi) pi)) (BinOper Impl pi pi ))]
                                           ++ [BinOper Impl (BinOper Impl pi (BinOper Impl (BinOper Impl pi pi) pi)) (BinOper Impl pi pi )]
                                           ++ [BinOper Impl pi (BinOper Impl (BinOper Impl pi pi) pi)]
                                           ++ [BinOper Impl pi pi]
                let m2 = add_to_mpMap pi mpMap
                deductionTheorem hyps alpha beta proofB newProof m2 (S.insert pi setAbove)
            else do
                let pj = fromMaybe (Var ("ERR")) (M.lookup pi mpMap)
                let newProof = proofImplAB ++ [BinOper Impl (BinOper Impl alpha pj) (BinOper Impl (BinOper Impl alpha (BinOper Impl pj pi)) (BinOper Impl alpha pi))]
                                           ++ [BinOper Impl (BinOper Impl alpha (BinOper Impl pj pi)) (BinOper Impl alpha pi)]
                                           ++ [BinOper Impl alpha pi]
                let m3 = add_to_mpMap pi mpMap
                deductionTheorem hyps alpha beta proofB newProof m3 (S.insert pi setAbove)


chooseLemma::[String] -> Ex -> [String]
chooseLemma [] ex = [(show ex)]
chooseLemma (v1:[]) ex = lemmaExcepFor1 v1 ex
chooseLemma (v1:v2:[]) ex = lemmaExcepFor2 v1 v2 ex
chooseLemma (v1:v2:v3:[]) ex = lemmaExcepFor3 v1 v2 v3 ex

lemmaExcepFor1::String -> Ex -> [String]
lemmaExcepFor1 v1 ex =  (change varnotvar (Var v1) (Var "") []) 
                     ++ (change exception (Var v1) ex [])
                     ++ (change exception (Var v1) ex [])

lemmaExcepFor2::String -> String -> Ex -> [String]
lemmaExcepFor2 v1 v2 ex =  (change varnotvar (Var v1) (Var "") []) 
                        ++ (change exception (Var v1) (BinOper Impl (Var v2) ex) [])
                        ++ (change exception (Var v1) (BinOper Impl (Not(Var v2)) ex) [])
                        ++ (lemmaExcepFor1 v2 ex)

lemmaExcepFor3::String -> String -> String -> Ex -> [String]
lemmaExcepFor3 v1 v2 v3 ex =  (change varnotvar (Var v1) (Var "") []) 
                           ++ (change exception (Var v1) (BinOper Impl (Var v2) (BinOper Impl (Var v3) ex)) [])
                           ++ (change exception (Var v1) (BinOper Impl (Var v2) (BinOper Impl (Not(Var v3)) ex)) [])
                           ++ (change exception (Var v1) (BinOper Impl (Not(Var v2)) (BinOper Impl (Var v3) ex)) [])
                           ++ (change exception (Var v1) (BinOper Impl (Not(Var v2)) (BinOper Impl (Not(Var v3)) ex)) [])
                           ++ (lemmaExcepFor2 v2 v3 ex)

