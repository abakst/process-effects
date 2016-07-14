{
module Language.Haskell.MessagePassing.Parse ( parseEffTy
             , parseTokens
             ) where
import Language.Haskell.MessagePassing.Lex
import Language.Haskell.MessagePassing.EffectTypes
import Control.Monad.Except
}

%name effty
%tokentype { Token }
%monad { Except String } { (>>=) } { return }
%error { parseError }
%token
  '->' { TokenArrow }
  '|'  { TokenPar }
  '('  { TokenLParen }
  ')'  { TokenRParen }
  '{'  { TokenLBrace }
  '}'  { TokenRBrace }
  '['  { TokenLBrack }
  ']'  { TokenRBrack }
  ':'  { TokenColon }
  '.'  { TokenPeriod }
  '\\' { TokenBackSlash }
  'forall' { TokenForAll }
  '>>=' { TokenBind }
  '0'  { TokenZero }
  VAR  { TokenSym   $$ }
  EVAR { TokenDSym  $$ }

%right '>>='
%%

effty : '{' '}'                   { EffTerm (EffLit "0") } 
      | '0'                       { EffNone }
      | '{' effTerm '}'           { EffTerm $2 }
      | '(' effty ')'             { $2 }
      | VAR ':' effty '->' effty  { EPi (symbol $1)  $3 $5 }
      | 'forall' EVAR '.' effty   { ETermAbs (symbol $2) $4 }
      | effty '->' effty          { EPi (symbol "_") $1 $3 }

effTerm : '\\' effVar '.' effTerm       { AbsEff $2 $4 }
        | '[' VAR ']' effTerm           { Nu (symbol $2) $4 }
        | '[' VAR ':' VAR ']' effTerm   { Nu (symbol $2) $6 }
        | effTerm '>>=' effTerm         { Bind $1 $3 }
        | effTerm '|' effTerm           { Par $1 $3 }
        | effTerm simpleTerm            { AppEff $1 $2 }
        | simpleTerm                    { $1 }

simpleTerm : effVar                  { EffVar $1 }
           | '(' effTerm ')'         { $2 }

effVar : VAR  { Src (symbol $1) }
       | EVAR { Eff (symbol $1) }

{

parseError :: [Token] -> Except String a
parseError (l:ls) = throwError (show l)
parseError [] = throwError "Unexpected end of Input"

parseEffTy :: String -> Either String EffTy
parseEffTy input = runExcept $ do
  tokenStream <- scanTokens input
  effty tokenStream

parseTokens :: String -> Either String [Token]
parseTokens = runExcept . scanTokens
    
}
