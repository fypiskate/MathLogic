module ProofGenerate where

import Synt(parser)
import Lex
import Expr
import FindMin

import qualified Data.Map as M
import Data.Maybe

changeStr:: String -> String -> String -> String -> String
changeStr [] ex1 ex2 ys = ys
changeStr (x:xs) ex1 ex2 ys = changeStr xs ex1 ex2 str
    where 
          str = case x of
              'A' -> ys ++ ex1
              'B' -> ys ++ ex2
              _   -> ys ++ [x]

change:: [String] -> Ex -> Ex -> [String] -> [String]
change [] ex1 ex2 result = result
change (x:xs) ex1 ex2 result = change xs ex1 ex2 (result ++ [(changeStr x (show ex1) (show ex2) [])])

from_set_to_map::[Ex] -> M.Map String Bool -> M.Map Ex Bool -> M.Map Ex Bool 
from_set_to_map [] hyps mmap = mmap
from_set_to_map (ex:exs) hyps mmap = from_set_to_map exs hyps (M.insert ex (returnBool hyps ex) mmap)

generate:: Ex -> M.Map String Bool -> M.Map Ex Bool -> [String] -> [String]
generate (BinOper Impl ex1 ex2) mmap subExprBool proof =  (generate ex1 mmap subExprBool proof) 
                                                       ++ (generate ex2 mmap subExprBool proof) 
                                                       ++ templateImpl (fromMaybe False (M.lookup ex1 subExprBool)) (fromMaybe False (M.lookup ex2 subExprBool)) ex1 ex2
generate (BinOper Or ex1 ex2) mmap subExprBool proof =  (generate ex1 mmap subExprBool proof) 
                                                     ++ (generate ex2 mmap subExprBool proof) 
                                                     ++ templateOr (fromMaybe False (M.lookup ex1 subExprBool)) (fromMaybe False (M.lookup ex2 subExprBool)) ex1 ex2
generate (BinOper And ex1 ex2) mmap subExprBool proof =  (generate ex1 mmap subExprBool proof) 
                                                      ++ (generate ex2 mmap subExprBool proof) 
                                                      ++ templateAnd (fromMaybe False (M.lookup ex1 subExprBool)) (fromMaybe False (M.lookup ex2 subExprBool)) ex1 ex2
generate (Not ex) mmap subExprBool proof =  generate ex mmap subExprBool proof
                                         ++ templateNot (fromMaybe False (M.lookup ex subExprBool)) ex
generate (Var str) mmap subExprBool proof = case (fromMaybe False (M.lookup str mmap)) of 
                                            True -> [str]
                                            False -> ["!" ++ str] 

templateNot::Bool -> Ex -> [String]
templateNot True  ex = change tempnot ex (Var "") []
templateNot False ex = change ["!(A)"] ex (Var "") []

templateImpl::Bool -> Bool -> Ex -> Ex -> [String]
templateImpl False False ex1 ex2 = change ffimpl ex1 ex2 []
templateImpl False True  ex1 ex2 = change ftimpl ex1 ex2 []
templateImpl True  False ex1 ex2 = change tfimpl ex1 ex2 []
templateImpl True  True  ex1 ex2 = change ttimpl ex1 ex2 []

templateOr::Bool -> Bool -> Ex -> Ex -> [String]
templateOr False False ex1 ex2 = change ffor ex1 ex2 []
templateOr False True  ex1 ex2 = change ftor ex1 ex2 []
templateOr True  False ex1 ex2 = change tfor ex1 ex2 []
templateOr True  True  ex1 ex2 = change ttor ex1 ex2 []

templateAnd::Bool -> Bool -> Ex -> Ex -> [String]
templateAnd False False ex1 ex2 = change ffand ex1 ex2 []
templateAnd False True  ex1 ex2 = change ftand ex1 ex2 []
templateAnd True  False ex1 ex2 = change tfand ex1 ex2 []
templateAnd True  True  ex1 ex2 = change ttand ex1 ex2 []


ffimpl = ["!(A)",
        "(!(A)->((A)->!(A)))",
        "((A)->!(A))",
        "!(B)",
        "(!(B)->((A)->!(B)))",
        "((A)->!(B))",
        "((A)->((A)->(A)))",
        "((A)->(((A)->(A))->(A)))",
        "(((A)->((A)->(A)))->(((A)->(((A)->(A))->(A)))->((A)->(A))))",
        "(((A)->(((A)->(A))->(A)))->((A)->(A)))",
        "((A)->(A))",
        "((!(B)->(A))->((!(B)->!(A))->!!(B)))",
        "(((!(B)->(A))->((!(B)->!(A))->!!(B)))->((A)->((!(B)->(A))->((!(B)->!(A))->!!(B)))))",
        "((A)->((!(B)->(A))->((!(B)->!(A))->!!(B))))",
        "((A)->(!(B)->(A)))",
        "(((A)->(!(B)->(A)))->((A)->((A)->(!(B)->(A)))))",
        "((A)->((A)->(!(B)->(A))))",
        "(((A)->(A))->(((A)->((A)->(!(B)->(A))))->((A)->(!(B)->(A)))))",
        "(((A)->((A)->(!(B)->(A))))->((A)->(!(B)->(A))))",
        "((A)->(!(B)->(A)))",
        "(!(A)->(!(B)->!(A)))",
        "((!(A)->(!(B)->!(A)))->((A)->(!(A)->(!(B)->!(A)))))",
        "((A)->(!(A)->(!(B)->!(A))))",
        "(((A)->!(A))->(((A)->(!(A)->(!(B)->!(A))))->((A)->(!(B)->!(A)))))",
        "(((A)->(!(A)->(!(B)->!(A))))->((A)->(!(B)->!(A))))",
        "((A)->(!(B)->!(A)))",
        "(((A)->(!(B)->(A)))->(((A)->((!(B)->(A))->((!(B)->!(A))->!!(B))))->((A)->((!(B)->!(A))->!!(B)))))",
        "(((A)->((!(B)->(A))->((!(B)->!(A))->!!(B))))->((A)->((!(B)->!(A))->!!(B))))",
        "((A)->((!(B)->!(A))->!!(B)))",
        "(((A)->(!(B)->!(A)))->(((A)->((!(B)->!(A))->!!(B)))->((A)->!!(B))))",
        "(((A)->((!(B)->!(A))->!!(B)))->((A)->!!(B)))",
        "((A)->!!(B))",
        "(!!(B)->(B))",
        "((!!(B)->(B))->((A)->(!!(B)->(B))))",
        "((A)->(!!(B)->(B)))",
        "(((A)->!!(B))->(((A)->(!!(B)->(B)))->((A)->(B))))",
        "(((A)->(!!(B)->(B)))->((A)->(B)))",
        "((A)->(B))"]

ftimpl = ["(B)->((A)->(B))",
        "(B)",
        "(A)->(B)"]

tfimpl = ["(A)",
    "!(B)",
    "!(B)->(((A)->(B))->!(B))",
    "((A)->(B))->!(B)",
    "((A)->(((A)->(B))->(A)))",
    "(((A)->(B))->(A))",
    "(((A)->(B))->(((A)->(B))->((A)->(B))))",
    "((((A)->(B))->(((A)->(B))->((A)->(B))))->((((A)->(B))->((((A)->(B))->((A)->(B)))->((A)->(B))))->(((A)->(B))->((A)->(B)))))",
    "((((A)->(B))->((((A)->(B))->((A)->(B)))->((A)->(B))))->(((A)->(B))->((A)->(B))))",
    "(((A)->(B))->((((A)->(B))->((A)->(B)))->((A)->(B))))",
    "(((A)->(B))->((A)->(B)))",
    "((((A)->(B))->(A))->((((A)->(B))->((A)->(B)))->(((A)->(B))->(B))))",
    "((((A)->(B))->((A)->(B)))->(((A)->(B))->(B)))",
    "(((A)->(B))->(B))",
    "(((A)->(B))->(B))->((((A)->(B))->!(B))->!((A)->(B)))",
    "(((A)->(B))->!(B))->!((A)->(B))",
    "!((A)->(B))"]

ttimpl = ["(B)->((A)->(B))",
    "(B)",
    "(A)->(B)"]

ffor = ["!(A)",
        "!(B)",
        "((((A) | (B)) -> (A)) -> ((((A) | (B)) -> !(A)) -> !((A) | (B))))",
        "(!(A) -> (((A) | (B)) -> !(A)))",
        "(((A) | (B)) -> !(A))",
        "(!(B) -> (((A) | (B)) -> !(B)))",
        "(((A) | (B)) -> !(B))",
        "(((A) | (B)) -> (((A) | (B)) -> ((A) | (B))))",
        "(((A) | (B)) -> ((((A) | (B)) -> ((A) | (B))) -> ((A) | (B))))",
        "((((A) | (B)) -> (((A) | (B)) -> ((A) | (B)))) -> ((((A) | (B)) -> ((((A) | (B)) -> ((A) | (B))) -> ((A) | (B)))) -> (((A) | (B)) -> ((A) | (B)))))",
        "((((A) | (B)) -> ((((A) | (B)) -> ((A) | (B))) -> ((A) | (B)))) -> (((A) | (B)) -> ((A) | (B))))",
        "(((A) | (B)) -> ((A) | (B)))",
        "((A) -> ((A) -> (A)))",
        "(((A) -> ((A) -> (A))) -> (((A) | (B)) -> ((A) -> ((A) -> (A)))))",
        "(((A) | (B)) -> ((A) -> ((A) -> (A))))",
        "(((A) -> ((A) -> (A))) -> (((A) -> (((A) -> (A)) -> (A))) -> ((A) -> (A))))",
        "((((A) -> ((A) -> (A))) -> (((A) -> (((A) -> (A)) -> (A))) -> ((A) -> (A)))) -> (((A) | (B)) -> (((A) -> ((A) -> (A))) -> (((A) -> (((A) -> (A)) -> (A))) -> ((A) -> (A))))))",
        "(((A) | (B)) -> (((A) -> ((A) -> (A))) -> (((A) -> (((A) -> (A)) -> (A))) -> ((A) -> (A)))))",
        "((A) -> (((A) -> (A)) -> (A)))",
        "(((A) -> (((A) -> (A)) -> (A))) -> (((A) | (B)) -> ((A) -> (((A) -> (A)) -> (A)))))",
        "(((A) | (B)) -> ((A) -> (((A) -> (A)) -> (A))))",
        "((((A) | (B)) -> ((A) -> ((A) -> (A)))) -> ((((A) | (B)) -> (((A) -> ((A) -> (A))) -> (((A) -> (((A) -> (A)) -> (A))) -> ((A) -> (A))))) -> (((A) | (B)) -> (((A) -> (((A) -> (A)) -> (A))) -> ((A) -> (A))))))",
        "((((A) | (B)) -> (((A) -> ((A) -> (A))) -> (((A) -> (((A) -> (A)) -> (A))) -> ((A) -> (A))))) -> (((A) | (B)) -> (((A) -> (((A) -> (A)) -> (A))) -> ((A) -> (A)))))",
        "(((A) | (B)) -> (((A) -> (((A) -> (A)) -> (A))) -> ((A) -> (A))))",
        "((((A) | (B)) -> ((A) -> (((A) -> (A)) -> (A)))) -> ((((A) | (B)) -> (((A) -> (((A) -> (A)) -> (A))) -> ((A) -> (A)))) -> (((A) | (B)) -> ((A) -> (A)))))",
        "((((A) | (B)) -> (((A) -> (((A) -> (A)) -> (A))) -> ((A) -> (A)))) -> (((A) | (B)) -> ((A) -> (A))))",
        "(((A) | (B)) -> ((A) -> (A)))",
        "(!(B) -> ((B) -> !(B)))",
        "((!(B) -> ((B) -> !(B))) -> (((A) | (B)) -> (!(B) -> ((B) -> !(B)))))",
        "(((A) | (B)) -> (!(B) -> ((B) -> !(B))))",
        "((((A) | (B)) -> !(B)) -> ((((A) | (B)) -> (!(B) -> ((B) -> !(B)))) -> (((A) | (B)) -> ((B) -> !(B)))))",
        "((((A) | (B)) -> (!(B) -> ((B) -> !(B)))) -> (((A) | (B)) -> ((B) -> !(B))))",
        "(((A) | (B)) -> ((B) -> !(B)))",
        "((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))",
        "(((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A))) -> (((A) | (B)) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))))",
        "(((A) | (B)) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A))))",
        "(((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))))",
        "((((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A))))) -> (((A) | (B)) -> (((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))))))",
        "(((A) | (B)) -> (((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A))))))",
        "((((A) | (B)) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))) -> ((((A) | (B)) -> (((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))))) -> (((A) | (B)) -> ((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))))))",
        "((((A) | (B)) -> (((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))))) -> (((A) | (B)) -> ((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A))))))",
        "(((A) | (B)) -> ((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))))",
        "((B) -> (!(A) -> (B)))",
        "(((B) -> (!(A) -> (B))) -> (((A) | (B)) -> ((B) -> (!(A) -> (B)))))",
        "(((A) | (B)) -> ((B) -> (!(A) -> (B))))",
        "(!(B) -> (!(A) -> !(B)))",
        "((!(B) -> (!(A) -> !(B))) -> (((A) | (B)) -> (!(B) -> (!(A) -> !(B)))))",
        "(((A) | (B)) -> (!(B) -> (!(A) -> !(B))))",
        "((!(B) -> (!(A) -> !(B))) -> ((B) -> (!(B) -> (!(A) -> !(B)))))",
        "(((!(B) -> (!(A) -> !(B))) -> ((B) -> (!(B) -> (!(A) -> !(B))))) -> (((A) | (B)) -> ((!(B) -> (!(A) -> !(B))) -> ((B) -> (!(B) -> (!(A) -> !(B)))))))",
        "(((A) | (B)) -> ((!(B) -> (!(A) -> !(B))) -> ((B) -> (!(B) -> (!(A) -> !(B))))))",
        "((((A) | (B)) -> (!(B) -> (!(A) -> !(B)))) -> ((((A) | (B)) -> ((!(B) -> (!(A) -> !(B))) -> ((B) -> (!(B) -> (!(A) -> !(B)))))) -> (((A) | (B)) -> ((B) -> (!(B) -> (!(A) -> !(B)))))))",
        "((((A) | (B)) -> ((!(B) -> (!(A) -> !(B))) -> ((B) -> (!(B) -> (!(A) -> !(B)))))) -> (((A) | (B)) -> ((B) -> (!(B) -> (!(A) -> !(B))))))",
        "(((A) | (B)) -> ((B) -> (!(B) -> (!(A) -> !(B)))))",
        "(((B) -> !(B)) -> (((B) -> (!(B) -> (!(A) -> !(B)))) -> ((B) -> (!(A) -> !(B)))))",
        "((((B) -> !(B)) -> (((B) -> (!(B) -> (!(A) -> !(B)))) -> ((B) -> (!(A) -> !(B))))) -> (((A) | (B)) -> (((B) -> !(B)) -> (((B) -> (!(B) -> (!(A) -> !(B)))) -> ((B) -> (!(A) -> !(B)))))))",
        "(((A) | (B)) -> (((B) -> !(B)) -> (((B) -> (!(B) -> (!(A) -> !(B)))) -> ((B) -> (!(A) -> !(B))))))",
        "((((A) | (B)) -> ((B) -> !(B))) -> ((((A) | (B)) -> (((B) -> !(B)) -> (((B) -> (!(B) -> (!(A) -> !(B)))) -> ((B) -> (!(A) -> !(B)))))) -> (((A) | (B)) -> (((B) -> (!(B) -> (!(A) -> !(B)))) -> ((B) -> (!(A) -> !(B)))))))",
        "((((A) | (B)) -> (((B) -> !(B)) -> (((B) -> (!(B) -> (!(A) -> !(B)))) -> ((B) -> (!(A) -> !(B)))))) -> (((A) | (B)) -> (((B) -> (!(B) -> (!(A) -> !(B)))) -> ((B) -> (!(A) -> !(B))))))",
        "(((A) | (B)) -> (((B) -> (!(B) -> (!(A) -> !(B)))) -> ((B) -> (!(A) -> !(B)))))",
        "((((A) | (B)) -> ((B) -> (!(B) -> (!(A) -> !(B))))) -> ((((A) | (B)) -> (((B) -> (!(B) -> (!(A) -> !(B)))) -> ((B) -> (!(A) -> !(B))))) -> (((A) | (B)) -> ((B) -> (!(A) -> !(B))))))",
        "((((A) | (B)) -> (((B) -> (!(B) -> (!(A) -> !(B)))) -> ((B) -> (!(A) -> !(B))))) -> (((A) | (B)) -> ((B) -> (!(A) -> !(B)))))",
        "(((A) | (B)) -> ((B) -> (!(A) -> !(B))))",
        "(((B) -> (!(A) -> (B))) -> (((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))) -> ((B) -> ((!(A) -> !(B)) -> !!(A)))))",
        "((((B) -> (!(A) -> (B))) -> (((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))) -> ((B) -> ((!(A) -> !(B)) -> !!(A))))) -> (((A) | (B)) -> (((B) -> (!(A) -> (B))) -> (((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))) -> ((B) -> ((!(A) -> !(B)) -> !!(A)))))))",
        "(((A) | (B)) -> (((B) -> (!(A) -> (B))) -> (((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))) -> ((B) -> ((!(A) -> !(B)) -> !!(A))))))",
        "((((A) | (B)) -> ((B) -> (!(A) -> (B)))) -> ((((A) | (B)) -> (((B) -> (!(A) -> (B))) -> (((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))) -> ((B) -> ((!(A) -> !(B)) -> !!(A)))))) -> (((A) | (B)) -> (((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))) -> ((B) -> ((!(A) -> !(B)) -> !!(A)))))))",
        "((((A) | (B)) -> (((B) -> (!(A) -> (B))) -> (((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))) -> ((B) -> ((!(A) -> !(B)) -> !!(A)))))) -> (((A) | (B)) -> (((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))) -> ((B) -> ((!(A) -> !(B)) -> !!(A))))))",
        "(((A) | (B)) -> (((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))) -> ((B) -> ((!(A) -> !(B)) -> !!(A)))))",
        "((((A) | (B)) -> ((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A))))) -> ((((A) | (B)) -> (((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))) -> ((B) -> ((!(A) -> !(B)) -> !!(A))))) -> (((A) | (B)) -> ((B) -> ((!(A) -> !(B)) -> !!(A))))))",
        "((((A) | (B)) -> (((B) -> ((!(A) -> (B)) -> ((!(A) -> !(B)) -> !!(A)))) -> ((B) -> ((!(A) -> !(B)) -> !!(A))))) -> (((A) | (B)) -> ((B) -> ((!(A) -> !(B)) -> !!(A)))))",
        "(((A) | (B)) -> ((B) -> ((!(A) -> !(B)) -> !!(A))))",
        "(((B) -> (!(A) -> !(B))) -> (((B) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> !!(A))))",
        "((((B) -> (!(A) -> !(B))) -> (((B) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> !!(A)))) -> (((A) | (B)) -> (((B) -> (!(A) -> !(B))) -> (((B) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> !!(A))))))",
        "(((A) | (B)) -> (((B) -> (!(A) -> !(B))) -> (((B) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> !!(A)))))",
        "((((A) | (B)) -> ((B) -> (!(A) -> !(B)))) -> ((((A) | (B)) -> (((B) -> (!(A) -> !(B))) -> (((B) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> !!(A))))) -> (((A) | (B)) -> (((B) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> !!(A))))))",
        "((((A) | (B)) -> (((B) -> (!(A) -> !(B))) -> (((B) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> !!(A))))) -> (((A) | (B)) -> (((B) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> !!(A)))))",
        "(((A) | (B)) -> (((B) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> !!(A))))",
        "((((A) | (B)) -> ((B) -> ((!(A) -> !(B)) -> !!(A)))) -> ((((A) | (B)) -> (((B) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> !!(A)))) -> (((A) | (B)) -> ((B) -> !!(A)))))",
        "((((A) | (B)) -> (((B) -> ((!(A) -> !(B)) -> !!(A))) -> ((B) -> !!(A)))) -> (((A) | (B)) -> ((B) -> !!(A))))",
        "(((A) | (B)) -> ((B) -> !!(A)))",
        "(!!(A) -> (A))",
        "((!!(A) -> (A)) -> (((A) | (B)) -> (!!(A) -> (A))))",
        "(((A) | (B)) -> (!!(A) -> (A)))",
        "((!!(A) -> (A)) -> ((B) -> (!!(A) -> (A))))",
        "(((!!(A) -> (A)) -> ((B) -> (!!(A) -> (A)))) -> (((A) | (B)) -> ((!!(A) -> (A)) -> ((B) -> (!!(A) -> (A))))))",
        "(((A) | (B)) -> ((!!(A) -> (A)) -> ((B) -> (!!(A) -> (A)))))",
        "((((A) | (B)) -> (!!(A) -> (A))) -> ((((A) | (B)) -> ((!!(A) -> (A)) -> ((B) -> (!!(A) -> (A))))) -> (((A) | (B)) -> ((B) -> (!!(A) -> (A))))))",
        "((((A) | (B)) -> ((!!(A) -> (A)) -> ((B) -> (!!(A) -> (A))))) -> (((A) | (B)) -> ((B) -> (!!(A) -> (A)))))",
        "(((A) | (B)) -> ((B) -> (!!(A) -> (A))))",
        "(((B) -> !!(A)) -> (((B) -> (!!(A) -> (A))) -> ((B) -> (A))))",
        "((((B) -> !!(A)) -> (((B) -> (!!(A) -> (A))) -> ((B) -> (A)))) -> (((A) | (B)) -> (((B) -> !!(A)) -> (((B) -> (!!(A) -> (A))) -> ((B) -> (A))))))",
        "(((A) | (B)) -> (((B) -> !!(A)) -> (((B) -> (!!(A) -> (A))) -> ((B) -> (A)))))",
        "((((A) | (B)) -> ((B) -> !!(A))) -> ((((A) | (B)) -> (((B) -> !!(A)) -> (((B) -> (!!(A) -> (A))) -> ((B) -> (A))))) -> (((A) | (B)) -> (((B) -> (!!(A) -> (A))) -> ((B) -> (A))))))",
        "((((A) | (B)) -> (((B) -> !!(A)) -> (((B) -> (!!(A) -> (A))) -> ((B) -> (A))))) -> (((A) | (B)) -> (((B) -> (!!(A) -> (A))) -> ((B) -> (A)))))",
        "(((A) | (B)) -> (((B) -> (!!(A) -> (A))) -> ((B) -> (A))))",
        "((((A) | (B)) -> ((B) -> (!!(A) -> (A)))) -> ((((A) | (B)) -> (((B) -> (!!(A) -> (A))) -> ((B) -> (A)))) -> (((A) | (B)) -> ((B) -> (A)))))",
        "((((A) | (B)) -> (((B) -> (!!(A) -> (A))) -> ((B) -> (A)))) -> (((A) | (B)) -> ((B) -> (A))))",
        "(((A) | (B)) -> ((B) -> (A)))",
        "(((A) -> (A)) -> (((B) -> (A)) -> (((A) | (B)) -> (A))))",
        "((((A) -> (A)) -> (((B) -> (A)) -> (((A) | (B)) -> (A)))) -> (((A) | (B)) -> (((A) -> (A)) -> (((B) -> (A)) -> (((A) | (B)) -> (A))))))",
        "(((A) | (B)) -> (((A) -> (A)) -> (((B) -> (A)) -> (((A) | (B)) -> (A)))))",
        "((((A) | (B)) -> ((A) -> (A))) -> ((((A) | (B)) -> (((A) -> (A)) -> (((B) -> (A)) -> (((A) | (B)) -> (A))))) -> (((A) | (B)) -> (((B) -> (A)) -> (((A) | (B)) -> (A))))))",
        "((((A) | (B)) -> (((A) -> (A)) -> (((B) -> (A)) -> (((A) | (B)) -> (A))))) -> (((A) | (B)) -> (((B) -> (A)) -> (((A) | (B)) -> (A)))))",
        "(((A) | (B)) -> (((B) -> (A)) -> (((A) | (B)) -> (A))))",
        "((((A) | (B)) -> ((B) -> (A))) -> ((((A) | (B)) -> (((B) -> (A)) -> (((A) | (B)) -> (A)))) -> (((A) | (B)) -> (((A) | (B)) -> (A)))))",
        "((((A) | (B)) -> (((B) -> (A)) -> (((A) | (B)) -> (A)))) -> (((A) | (B)) -> (((A) | (B)) -> (A))))",
        "(((A) | (B)) -> (((A) | (B)) -> (A)))",
        "((((A) | (B)) -> ((A) | (B))) -> ((((A) | (B)) -> (((A) | (B)) -> (A))) -> (((A) | (B)) -> (A))))",
        "((((A) | (B)) -> (((A) | (B)) -> (A))) -> (((A) | (B)) -> (A)))",
        "(((A) | (B)) -> (A))",
        "((((A) | (B)) -> !(A)) -> !((A) | (B)))",
        "!((A) | (B))"]

ftor = ["(B)",
        "(B)->((A)|(B))",
        "(A)|(B)"]

tfor = ["(A)",
        "(A)->((A)|(B))",
        "(A)|(B)"]

ttor = ["(A)",
        "(A)->((A)|(B))",
        "(A)|(B)"]

ffand = ["((A)&(B))->(A)",
        "!(A)",
        "!(A)->(((A)&(B))->!(A))",
        "((A)&(B))->!(A)",
        "(((A)&(B))->(A))->((((A)&(B))->!(A))->!((A)&(B)))",
        "(((A)&(B))->!(A))->!((A)&(B))",
        "!((A)&(B))"]

ftand = ["((A)&(B))->(A)",
        "!(A)->(((A)&(B))->!(A))",
        "!(A)",
        "((A)&(B))->!(A)",
        "(((A)&(B))->(A))->((((A)&(B))->!(A))->!((A)&(B)))",
        "(((A)&(B))->!(A))->!((A)&(B))",
        "!((A)&(B))"]

tfand = ["((A)&(B))->(B)",
        "!(B)",
        "!(B)->(((A)&(B))->!(B))",
        "((A)&(B))->!(B)",
        "(((A)&(B))->(B))->((((A)&(B))->!(B))->!((A)&(B)))",
        "(((A)&(B))->!(B))->!((A)&(B))",
        "!((A)&(B))"]

ttand = ["(A)",
        "(B)",
        "(A)->((B)->((A)&(B)))",
        "(B)->((A)&(B))",
        "(A)&(B)"]

varnotvar = ["(A)->((A)|!(A))",
    "(!((A)|!(A))->((A)->!((A)|!(A))))->((!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->!(A)))",
    "((!((A)|!(A))->((A)->!((A)|!(A))))->((!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->!(A))))->(((A)->((A)|!(A)))->((!((A)|!(A))->((A)->!((A)|!(A))))->((!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->!(A)))))",
    "((A)->((A)|!(A)))->((!((A)|!(A))->((A)->!((A)|!(A))))->((!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->!(A))))",
    "!((A)|!(A))->((A)->!((A)|!(A)))",
    "(!((A)|!(A))->((A)->!((A)|!(A))))->(((A)->((A)|!(A)))->(!((A)|!(A))->((A)->!((A)|!(A)))))",
    "((A)->((A)|!(A)))->(!((A)|!(A))->((A)->!((A)|!(A))))",
    "(((A)->((A)|!(A)))->(!((A)|!(A))->((A)->!((A)|!(A)))))->((((A)->((A)|!(A)))->((!((A)|!(A))->((A)->!((A)|!(A))))->((!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->!(A)))))->(((A)->((A)|!(A)))->((!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->!(A)))))",
    "(((A)->((A)|!(A)))->((!((A)|!(A))->((A)->!((A)|!(A))))->((!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->!(A)))))->(((A)->((A)|!(A)))->((!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->!(A))))",
    "((A)->((A)|!(A)))->((!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->!(A)))",
    "(!((A)|!(A))->((A)->((A)|!(A))))->((!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A))))",
    "((!((A)|!(A))->((A)->((A)|!(A))))->((!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))))->(((A)->((A)|!(A)))->((!((A)|!(A))->((A)->((A)|!(A))))->((!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A))))))",
    "((A)->((A)|!(A)))->((!((A)|!(A))->((A)->((A)|!(A))))->((!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))))",
    "((A)->((A)|!(A)))->(!((A)|!(A))->((A)->((A)|!(A))))",
    "(((A)->((A)|!(A)))->(!((A)|!(A))->((A)->((A)|!(A)))))->((((A)->((A)|!(A)))->((!((A)|!(A))->((A)->((A)|!(A))))->((!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A))))))->(((A)->((A)|!(A)))->((!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A))))))",
    "(((A)->((A)|!(A)))->((!((A)|!(A))->((A)->((A)|!(A))))->((!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A))))))->(((A)->((A)|!(A)))->((!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))))",
    "((A)->((A)|!(A)))->((!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A))))",
    "(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))",
    "((((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A)))))->(((A)->((A)|!(A)))->((((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))))",
    "((A)->((A)|!(A)))->((((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A)))))",
    "((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))",
    "(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A)))->(((A)->((A)|!(A)))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))",
    "((A)->((A)|!(A)))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A)))",
    "(((A)->((A)|!(A)))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))->((((A)->((A)|!(A)))->((((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))))->(((A)->((A)|!(A)))->(!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))))",
    "(((A)->((A)|!(A)))->((((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))))->(((A)->((A)|!(A)))->(!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A)))))",
    "((A)->((A)|!(A)))->(!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))",
    "(((A)->((A)|!(A)))->(!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A)))))->((((A)->((A)|!(A)))->((!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))))->(((A)->((A)|!(A)))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))))",
    "(((A)->((A)|!(A)))->((!((A)|!(A))->(((A)->((A)|!(A)))->(((A)->!((A)|!(A)))->!(A))))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))))->(((A)->((A)|!(A)))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A))))",
    "((A)->((A)|!(A)))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))",
    "(((A)->((A)|!(A)))->(!((A)|!(A))->(((A)->!((A)|!(A)))->!(A))))->((((A)->((A)|!(A)))->((!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->!(A))))->(((A)->((A)|!(A)))->(!((A)|!(A))->!(A))))",
    "(((A)->((A)|!(A)))->((!((A)|!(A))->(((A)->!((A)|!(A)))->!(A)))->(!((A)|!(A))->!(A))))->(((A)->((A)|!(A)))->(!((A)|!(A))->!(A)))",
    "((A)->((A)|!(A)))->(!((A)|!(A))->!(A))",
    "!((A)|!(A))->!(A)",
    "!(A)->((A)|!(A))",
    "(!((A)|!(A))->(!(A)->!((A)|!(A))))->((!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->!!(A)))",
    "((!((A)|!(A))->(!(A)->!((A)|!(A))))->((!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->!!(A))))->((!(A)->((A)|!(A)))->((!((A)|!(A))->(!(A)->!((A)|!(A))))->((!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->!!(A)))))",
    "(!(A)->((A)|!(A)))->((!((A)|!(A))->(!(A)->!((A)|!(A))))->((!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->!!(A))))",
    "!((A)|!(A))->(!(A)->!((A)|!(A)))",
    "(!((A)|!(A))->(!(A)->!((A)|!(A))))->((!(A)->((A)|!(A)))->(!((A)|!(A))->(!(A)->!((A)|!(A)))))",
    "(!(A)->((A)|!(A)))->(!((A)|!(A))->(!(A)->!((A)|!(A))))",
    "((!(A)->((A)|!(A)))->(!((A)|!(A))->(!(A)->!((A)|!(A)))))->(((!(A)->((A)|!(A)))->((!((A)|!(A))->(!(A)->!((A)|!(A))))->((!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->!!(A)))))->((!(A)->((A)|!(A)))->((!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->!!(A)))))",
    "((!(A)->((A)|!(A)))->((!((A)|!(A))->(!(A)->!((A)|!(A))))->((!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->!!(A)))))->((!(A)->((A)|!(A)))->((!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->!!(A))))",
    "(!(A)->((A)|!(A)))->((!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->!!(A)))",
    "(!((A)|!(A))->(!(A)->((A)|!(A))))->((!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A))))",
    "((!((A)|!(A))->(!(A)->((A)|!(A))))->((!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))))->((!(A)->((A)|!(A)))->((!((A)|!(A))->(!(A)->((A)|!(A))))->((!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A))))))",
    "(!(A)->((A)|!(A)))->((!((A)|!(A))->(!(A)->((A)|!(A))))->((!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))))",
    "(!(A)->((A)|!(A)))->(!((A)|!(A))->(!(A)->((A)|!(A))))",
    "((!(A)->((A)|!(A)))->(!((A)|!(A))->(!(A)->((A)|!(A)))))->(((!(A)->((A)|!(A)))->((!((A)|!(A))->(!(A)->((A)|!(A))))->((!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A))))))->((!(A)->((A)|!(A)))->((!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A))))))",
    "((!(A)->((A)|!(A)))->((!((A)|!(A))->(!(A)->((A)|!(A))))->((!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A))))))->((!(A)->((A)|!(A)))->((!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))))",
    "(!(A)->((A)|!(A)))->((!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A))))",
    "((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))",
    "(((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A)))))->((!(A)->((A)|!(A)))->(((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))))",
    "(!(A)->((A)|!(A)))->(((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A)))))",
    "(!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))",
    "((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A)))->((!(A)->((A)|!(A)))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))",
    "(!(A)->((A)|!(A)))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A)))",
    "((!(A)->((A)|!(A)))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))->(((!(A)->((A)|!(A)))->(((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))))->((!(A)->((A)|!(A)))->(!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))))",
    "((!(A)->((A)|!(A)))->(((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))))->((!(A)->((A)|!(A)))->(!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A)))))",
    "(!(A)->((A)|!(A)))->(!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))",
    "((!(A)->((A)|!(A)))->(!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A)))))->(((!(A)->((A)|!(A)))->((!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))))->((!(A)->((A)|!(A)))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))))",
    "((!(A)->((A)|!(A)))->((!((A)|!(A))->((!(A)->((A)|!(A)))->((!(A)->!((A)|!(A)))->!!(A))))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))))->((!(A)->((A)|!(A)))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A))))",
    "(!(A)->((A)|!(A)))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))",
    "((!(A)->((A)|!(A)))->(!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A))))->(((!(A)->((A)|!(A)))->((!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->!!(A))))->((!(A)->((A)|!(A)))->(!((A)|!(A))->!!(A))))",
    "((!(A)->((A)|!(A)))->((!((A)|!(A))->((!(A)->!((A)|!(A)))->!!(A)))->(!((A)|!(A))->!!(A))))->((!(A)->((A)|!(A)))->(!((A)|!(A))->!!(A)))",
    "(!(A)->((A)|!(A)))->(!((A)|!(A))->!!(A))",
    "(!((A)|!(A))->!!(A))",
    "(!((A)|!(A))->!(A))->((!((A)|!(A))->!(!(A)))->!(!((A)|!(A))))",
    "(!((A)|!(A))->!(!(A)))->!(!((A)|!(A)))",
    "!(!((A)|!(A)))",
    "!(!((A)|!(A)))->((A)|!(A))",
    "(A)|!(A)"]

exception = [
              "((A)->(B))->(!(A)->(B))->(((A)|!(A))->(B))",
              "(!(A)->(B))->(((A)|!(A))->(B))",
              "((A)|!(A))->(B)",
              "(B)"
            ]

tempnot = [ "(A)",
            "((A) -> (!(A) -> (A)))",
            "(!(A) -> (A))",
            "(!(A) -> (!(A) -> !(A)))",
            "((!(A) -> (!(A) -> !(A))) -> ((!(A) -> ((!(A) -> !(A)) -> !(A))) -> (!(A) -> !(A))))",
            "((!(A) -> ((!(A) -> !(A)) -> !(A))) -> (!(A) -> !(A)))",
            "(!(A) -> ((!(A) -> !(A)) -> !(A)))",
            "(!(A) -> !(A))",
            "((!(A) -> (A)) -> ((!(A) -> !(A)) -> !!(A)))", 
            "((!(A) -> !(A)) -> !!(A))",
            "!!(A)"
          ]











                                                       