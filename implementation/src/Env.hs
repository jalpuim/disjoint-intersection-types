{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}

module Env (lookupTy, runTcMonad, TcMonad, extendCtx, throwStrErr) where

import           Control.Monad.Except
import           Control.Monad.Reader
import qualified Data.Text as T
import           Unbound.Generics.LocallyNameless


data (Eq i, Show i) => Context i t = Ctx {env :: [(i, t)]}


emptyCtx :: (Eq i, Show i) => Context i t
emptyCtx = Ctx []


type TcMonad i t = FreshMT (ReaderT (Context i t) (Except T.Text))


runTcMonad :: (Eq i, Show i) => TcMonad i t a -> Either T.Text a
runTcMonad m = runExcept $ runReaderT (runFreshMT m) emptyCtx


lookupTy :: (Eq i, Show i, MonadReader (Context i t) m, MonadError T.Text m) => i -> m t
lookupTy v = do
  x <- lookupTyMaybe v
  case x of
    Nothing  -> throwError $ T.concat ["Not in scope: ", T.pack . show $ v]
    Just res -> return res


lookupTyMaybe :: (Eq i, Show i, MonadReader (Context i t) m, MonadError T.Text m) => i -> m (Maybe t)
lookupTyMaybe v = do
  ctx <- asks env
  return (lookup v ctx)


extendCtx :: (Eq i, Show i, MonadReader (Context i t) m) => (i, t) -> m a -> m a
extendCtx d = local (\ctx -> ctx { env = d : env ctx })


throwStrErr :: MonadError T.Text m => String -> m a
throwStrErr = throwError . T.pack
