{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Source.Syntax where

import           Common
import           Data.Typeable                    (Typeable)
import           GHC.Generics                     (Generic)
import           Unbound.Generics.LocallyNameless


type TmName = Name Expr


data Expr = Anno Expr Type
          | Var TmName
          | App Expr Expr
          | Lam (Bind TmName Expr)
          | Merge Expr Expr
          | IntV Int
          | BoolV Bool
          | PrimOp Operation Expr Expr
          | If Expr Expr Expr
          | Let (Bind (TmName, Embed Expr) Expr)
          | Pair Expr Expr
          | Project Expr Int
          | Top
  deriving (Show, Generic, Typeable)


data Type = IntT
          | BoolT
          | Arr Type Type
          | Inter Type Type
          | Product Type Type
          | TopT
  deriving (Eq, Show, Generic, Typeable)


instance Alpha Type
instance Alpha Expr


instance Subst Expr Type
instance Subst Expr ArithOp
instance Subst Expr LogicalOp
instance Subst Expr Operation
instance Subst Expr Expr where
  isvar (Var v) = Just (SubstName v)
  isvar _ = Nothing


evar :: String -> Expr
evar = Var . s2n

ebindt :: Alpha a => (String, a) -> Expr -> Bind (TmName, Embed a) Expr
ebindt (n, e1) = bind (s2n n, embed e1)

ebind :: String -> Expr -> Bind TmName Expr
ebind n = bind (s2n n)

elam :: String -> Expr -> Expr
elam x e = Lam (ebind x e)

eapp :: Expr -> Expr -> Expr
eapp = App
