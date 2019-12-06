module Expr where

data Ex = BinOper Oper Ex Ex | Not Ex | Var String deriving ( Eq, Ord )

data Oper = And | Or | Impl deriving ( Eq, Ord )

instance Show Oper where
  show And  = "&"
  show Or   = "|"
  show Impl = "->"

instance Show Ex where
  show ( BinOper op ex1 ex2 )
    = "(" ++ show ex1 ++ " " ++ show op ++ " " ++ show ex2 ++ ")"
  show ( Not ex )
    = "(!" ++ show ex ++ ")"
  show ( Var str ) = str



