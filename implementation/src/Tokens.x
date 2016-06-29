{
module Tokens where

import Common
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-

  $white+                       ;
  "--".*                        ;
  let                           { \s -> TLet }
  in                            { \s -> TIn }
  int                           { \s -> TIntTy }
  bool                          { \s -> TBoolTy }
  true                          { \s -> TBool True }
  false                         { \s -> TBool False }
  if                            { \s -> TIf }
  then                          { \s -> TThen }
  else                          { \s -> TElse }
  $digit+                       { \s -> TInt (read s) }
  \=                            { \s -> TEq }
  \:                            { \s -> TColon }
  \,                            { \s -> TComma }
  \.                            { \s -> TDot }
  \#                            { \s -> TSharp }
  \\                            { \s -> TLam }
  \-\>                          { \s -> TArr }
  \+                            { \s -> TAdd }
  \-                            { \s -> TSub }
  \*                            { \s -> TMul }
  \/                            { \s -> TDiv }
  \=\=                          { \s -> TEqu }
  \!\=                          { \s -> TNeq }
  \<                            { \s -> TLt }
  \>                            { \s -> TGt }
  \(                            { \s -> TLParen }
  \)                            { \s -> TRParen }
  \[                            { \s -> TLSquare }
  \]                            { \s -> TRSquare }
  \{                            { \s -> TLCurly }
  \}                            { \s -> TRCurly }
  \&                            { \s -> TAnd }
  \,\,                          { \s -> TMerge }
  \.\_                          { \s -> TProj }
  T                             { \s -> TTop }
  $alpha [$alpha $digit \_ \']* { \s -> TStr s }

{
data Token = TLet | TIn
           | TIntTy | TInt Int
           | TBoolTy | TBool Bool
           | TStr String
           | TEq
           | TLam
           | TArr
           | TColon | TComma | TDot
           | TAdd | TSub | TMul | TDiv | TEqu | TNeq | TLt | TGt
           | TLParen | TRParen | TLSquare | TRSquare | TLCurly | TRCurly
           | TSharp
           | TAnd | TMerge
           | TIf | TThen | TElse
           | TProj
           | TTop
           deriving (Eq, Show)

scanTokens = alexScanTokens
}
