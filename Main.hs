module Main where

import Synt(parser)
import Lex
import Expr
import ProofGenerate
import FindMin
import Merger

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe
import Data.Bits
import Data.List


printList::[String] -> IO ()
printList [] = putStr ""
printList (x:xs) = do
    putStrLn x
    printList xs

main :: IO ()
main = do
    line <- getLine
    let expr = parser . alexScanTokens $ line
    let setExpr = makeSetFromExpr expr S.empty
    let listVar = S.toList (S.filter (isVar) setExpr)
    let listStrVar = map show listVar
    let n = length listStrVar
    let maps = make_maps n listStrVar
    let sadreturn = [":("]
    let answerlist = case forecast listStrVar expr 0 of
                     1 -> trueVars n expr listStrVar maps [] setExpr
                     2 -> falseVars n expr listStrVar maps [] setExpr
                     3 -> sadreturn
    printList answerlist






