module Target.TypeCheck (typecheck, eval) where

import           Common
import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Trans.Maybe
import qualified Data.Text                        as T
import           Env
import           PrettyPrint
import           Target.Syntax
import           Unbound.Generics.LocallyNameless


type TMonad = TcMonad TmName Type


typecheck :: Expr -> Either T.Text Type
typecheck = runTcMonad . check


check :: Expr -> TMonad Type
check Unit = return UnitT
check (Var x) = lookupTy x
check (Lam bnd) = do
  ((x, t), b) <- unbind bnd
  bt <- extendCtx (x, t) (check b)
  return $ Arr t bt
check (IntV _) = return IntT
check (BoolV _) = return BoolT
check (App f a) = do
  ft <- check f
  at <- check a
  case ft of
    (Arr t1 t2) | t1 `aeq` at -> return t2
    _ -> throwStrErr $ "Cannot apply " ++ pprint ft ++ " to " ++ pprint at
check (PrimOp op a b) = do
  at <- check a
  bt <- check b
  let rt = case op of (Arith _) -> IntT
                      (Logical _) -> BoolT
  if at `aeq` IntT && bt `aeq` IntT
    then return rt
    else throwStrErr $ pprint at ++ " and " ++ pprint bt ++ " must both be int"
check (Pair a b) = do
  at <- check a
  bt <- check b
  return $ Product at bt
check (Project e i) = do
  t <- check e
  case t of
    (Product a b) -> return $ if i == 1 then a else b
    _ -> throwStrErr $ pprint t ++ " is not a product type"
check (If p e1 e2) = do
  tp <- check p
  case tp of
    BoolT -> do
      t1 <- check e1
      t2 <- check e2
      if t1 `aeq` t2
        then return t1
        else throwStrErr $ pprint t1 ++ " and " ++ pprint t2 ++ " must be the same type"
    _ -> throwStrErr $ pprint tp ++ " must be a bool type"


done :: MonadPlus m => m a
done = mzero


step :: Expr -> MaybeT FreshM Expr
step Unit = done
step (Var _) = done
step (Lam _) = done
step (IntV _) = done
step (BoolV _) = done
step (App f a) =
  let
    c1 = do f' <- step f
            return $ App f' a
    c2 = do a' <- step a
            return $ App f a'
    c3 = case f of (Lam bnd) -> do
                     ((x, _), b) <- unbind bnd
                     return $ subst x a b
                   _ -> error $ "Panic! not a function: " ++ pprint f
  in
  c1 <|> c2 <|> c3
step (PrimOp op e1 e2) =
  case (e1, e2) of
    (IntV n, IntV m) -> return $ evalOp op n m
    _ ->
      let
        c1 = do e1' <- step e1
                return $ PrimOp op e1' e2
        c2 = do e2' <- step e2
                return $ PrimOp op e1 e2'
      in
      c1 <|> c2
step (Pair e1 e2) =
  let
    c1 = do e1' <- step e1
            return $ Pair e1' e2
    c2 = do e2' <- step e2
            return $ Pair e1 e2'
  in
  c1 <|> c2
step (Project e i) =
  case e of
    (Pair e1 e2) -> return $ if i == 1 then e1 else e2
    _ -> do
      e' <- step e
      return $ Project e' i
step (If p e1 e2) =
  case p of
    (BoolV b) -> return $ if b then e1 else e2
    _ -> do
      p' <- step p
      return $ If p' e1 e2


evalOp :: Operation -> Int -> Int -> Expr
evalOp op x y =
  case op of
    (Arith Add) -> IntV $ x + y
    (Arith Sub) -> IntV $ x - y
    (Arith Mul) -> IntV $ x * y
    (Arith Div) -> IntV $ x `div` y
    (Logical Equ) -> BoolV $ x == y
    (Logical Neq) -> BoolV $ x /= y
    (Logical Lt) -> BoolV $ x < y
    (Logical Gt) -> BoolV $ x > y


eval :: Expr -> Expr
eval x = runFreshM (tc step x)
  where
    tc f a = do
      ma' <- runMaybeT (f a)
      case ma' of
        Nothing -> return a
        Just a' -> tc f a'
