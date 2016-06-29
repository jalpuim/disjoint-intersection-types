{-# LANGUAGE OverloadedStrings #-}

module PrettyPrint where

import           Common
import qualified Source.Syntax                    as S
import qualified Target.Syntax                    as T
import           Text.PrettyPrint.ANSI.Leijen     (Doc, colon, dot, parens,
                                                   text, (<+>), (<>))
import           Unbound.Generics.LocallyNameless


class Pretty p where
  ppr :: (Applicative m, LFresh m) => p -> m Doc


instance Pretty ArithOp where
  ppr Add = return $ text "+"
  ppr Mul = return $ text "*"
  ppr Sub = return $ text "-"
  ppr Div = return $ text "/"


instance Pretty LogicalOp where
  ppr Equ = return $ text "=="
  ppr Neq = return $ text "!="
  ppr Lt = return $ text "<"
  ppr Gt = return $ text ">"


instance Pretty Operation where
  ppr (Arith a) = ppr a
  ppr (Logical a) = ppr a


instance Pretty S.Type where
  ppr (S.Arr t1 t2) =
    do t1' <- ppr t1
       t2' <- ppr t2
       return $ parens (t1' <+> text "->" <+> t2')

  ppr S.IntT = return $ text "int"

  ppr S.BoolT = return $ text "bool"

  ppr (S.Inter t1 t2) =
    do t1' <- ppr t1
       t2' <- ppr t2
       return $ parens (t1' <+> text "&" <+> t2')

  ppr (S.Product t1 t2) =
    do t1' <- ppr t1
       t2' <- ppr t2
       return $ parens (t1' <> text "," <+> t2')

  ppr S.TopT = return $ text "T"


instance Pretty S.Expr where
  ppr (S.Anno e t) =
    do e' <- ppr e
       t' <- ppr t
       return $ e' <+> colon <+> t'

  ppr (S.Var x) = return . text . show $ x

  ppr (S.App f a) =
    do f' <- ppr f
       a' <- ppr a
       return $ parens (f' <+> a')

  ppr (S.Lam bnd) =
    lunbind bnd $
    \(x, b) ->
      do b' <- ppr b
         return (parens $ text "\\" <> text (show x) <+> dot <+> b')

  ppr (S.IntV n) = return . text . show $ n

  ppr (S.BoolV b) = return . text . show $ b

  ppr (S.PrimOp op e1 e2) =
    do e1' <- ppr e1
       e2' <- ppr e2
       op' <- ppr op
       return $ parens (e1' <+> op' <+> e2')

  ppr (S.Merge e1 e2) =
    do e1' <- ppr e1
       e2' <- ppr e2
       return $ parens (e1' <+> ",," <+> e2')

  ppr (S.If p e1 e2) =
    do p' <- ppr p
       e1' <- ppr e1
       e2' <- ppr e2
       return $ text "if" <+> p' <+> text "then" <+> e1' <+> text "else" <+> e2'

  ppr (S.Let bnd) =
    lunbind bnd $
    \((x, Embed e), b) ->
      do b' <- ppr b
         e' <- ppr e
         return $ text "let" <+> text (show x) <+> text "=" <+> e' <+> text "in" <+> b'

  ppr (S.Pair e1 e2) =
    do e1' <- ppr e1
       e2' <- ppr e2
       return $ parens (e1' <> "," <+> e2')

  ppr (S.Project e i) =
    do e' <- ppr e
       return $ e' <> dot <> text (show i)

  ppr S.Top = return $ text "T"


instance Pretty T.Type where
  ppr (T.Arr t1 t2) =
    do t1' <- ppr t1
       t2' <- ppr t2
       return $ parens (t1' <+> text "->" <+> t2')

  ppr T.IntT = return $ text "int"

  ppr T.BoolT = return $ text "bool"

  ppr (T.Product t1 t2) =
    do t1' <- ppr t1
       t2' <- ppr t2
       return $ parens (t1' <> text "," <+> t2')

  ppr T.UnitT = return $ text "()"


instance Pretty T.Expr where
  ppr (T.Var x) = return . text . show $ x

  ppr (T.App f a) =
    do f' <- ppr f
       a' <- ppr a
       return $ parens (f' <+> a')

  ppr (T.Lam bnd) =
    lunbind bnd $
    \((x, t), b) ->
      do b' <- ppr b
         t' <- ppr t
         return (parens $ text "\\" <> text (show x) <> colon <> t' <+> dot <+> b')

  ppr (T.IntV n) = return . text . show $ n

  ppr (T.BoolV b) = return . text . show $ b

  ppr (T.PrimOp op e1 e2) =
    do e1' <- ppr e1
       e2' <- ppr e2
       op' <- ppr op
       return $ parens (e1' <+> op' <+> e2')

  ppr (T.Pair e1 e2) =
    do e1' <- ppr e1
       e2' <- ppr e2
       return $ parens (e1' <> "," <+> e2')

  ppr (T.Project e i) =
    do e' <- ppr e
       return $ e' <> dot <> text (show i)

  ppr T.Unit = return $ text "()"

  ppr (T.If p e1 e2) =
    do p' <- ppr p
       e1' <- ppr e1
       e2' <- ppr e2
       return $ text "if" <+> p' <+> text "then" <+> e1' <+> text "else" <+> e2'


pprint :: (Pretty a) => a -> String
pprint = show . runLFreshM . ppr
