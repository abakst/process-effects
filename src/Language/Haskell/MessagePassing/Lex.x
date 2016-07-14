{
{-# Language FlexibleContexts #-}
module Lex (
  Token(..),
  scanTokens
)  where
import Control.Monad.Except
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$lowerAlpha = [a-z]
$upperAlpha = [A-z]
$eol   = [\n]

tokens :-

  $eol ;
  $white+ ;
  \{      { \s -> TokenLBrace }
  \}      { \s -> TokenRBrace }
  \[      { \s -> TokenLBrack }
  \]      { \s -> TokenRBrack }
  "->"    { \s -> TokenArrow }
  \(      { \s -> TokenLParen }
  \)      { \s -> TokenRParen }
  ":"     { \s -> TokenColon }
  "|"     { \s -> TokenPar }
  \\      { \s -> TokenBackSlash}
  \.      { \s -> TokenPeriod}
  "forall" { \s -> TokenForAll }
  ">>="    { \s -> TokenBind }
  $alpha [$alpha $digit \_ \']* { \s -> TokenSym s }
  "$" [$alpha $digit \_ \']* { \s -> TokenDSym s }
  0       { \s -> TokenZero }

{
data Token = TokenLBrack
           | TokenRBrack
           | TokenLBrace
           | TokenRBrace
           | TokenLParen
           | TokenRParen
           | TokenArrow
           | TokenColon
           | TokenBackSlash
           | TokenPeriod
           | TokenForAll
           | TokenBind
           | TokenPar
           | TokenSym String
           | TokenDSym String
           | TokenZero
           deriving (Eq,Show)

scanTokens :: String -> Except String [Token]
scanTokens str = go ('\n',[],str) where 
  go inp@(_,_bs,str) =
    case alexScan inp 0 of
     AlexEOF -> return []
     AlexError _ -> throwError "Invalid lexeme."
     AlexSkip  inp' len     -> go inp'
     AlexToken inp' len act -> do
      res <- go inp'
      let rest = act (take len str)
      return (rest : res)
}
