{-# LANGUAGE DeriveGeneric #-}

module Common where

import           Data.Typeable                    (Typeable)
import           GHC.Generics                     (Generic)
import           Unbound.Generics.LocallyNameless


data Operation = Arith ArithOp
               | Logical LogicalOp
               deriving (Eq, Show, Generic, Typeable)


data ArithOp = Add | Sub | Mul | Div deriving (Eq, Show, Generic, Typeable)


data LogicalOp = Lt | Gt | Equ | Neq deriving (Eq, Show, Generic, Typeable)


instance Alpha ArithOp
instance Alpha LogicalOp
instance Alpha Operation
