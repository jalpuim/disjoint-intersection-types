{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Target.Syntax where

import           Common
import           Data.Typeable                    (Typeable)
import           GHC.Generics                     (Generic)
import           Unbound.Generics.LocallyNameless


type TmName = Name Expr


data Expr = Var TmName
          | App Expr Expr
          | Lam (Bind (TmName, Type) Expr)
          | Pair Expr Expr
          | Project Expr Int
          | IntV Int
          | BoolV Bool
          | Unit
          | PrimOp Operation Expr Expr
          | If Expr Expr Expr
  deriving (Show, Generic, Typeable)


data Type = IntT
          | BoolT
          | UnitT
          | Arr Type Type
          | Product Type Type
  deriving (Show, Generic, Typeable)


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

ebindt :: (String, Type) -> Expr -> Bind (TmName, Type) Expr
ebindt (n, e1) = bind (s2n n, e1)
-- ebindt :: (String, Type) -> Expr -> Bind (TmName, Embed Type) Expr
-- ebindt (n, e1) = bind (s2n n, embed e1)

ebind :: String -> Expr -> Bind TmName Expr
ebind n = bind (s2n n)

elam :: (String, Type) -> Expr -> Expr
elam b e = Lam (ebindt b e)

eapp :: Expr -> Expr -> Expr
eapp = App
