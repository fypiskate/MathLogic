{
module Synt where
import Lex
import Expr
}

%name      parser
%tokentype { Token }
%error     { parseError }


%token

  var   { TVariable $$ }
  '->'  { TImplication }
  '|'   { TOr }
  '&'   { TAnd }
  '!'   { TNot }
  '('   { TOpenBracket  }
  ')'   { TCloseBracket }
  
%%


Exp     : Disj           { $1 }
	| Disj '->' Exp  { BinOper Impl $1 $3 }

Disj    : Conj           { $1 }
	| Disj '|' Conj  { BinOper Or $1 $3 }

Conj    : Not            { $1 }
	| Conj '&' Not   { BinOper And $1 $3 }

Not     : '!' Not        { Not $2 }
	| var            { Var $1 }
	| '(' Exp ')'    { $2 }


{

parseError :: [Token] -> a
parseError e = error "Parse error"

}


  
