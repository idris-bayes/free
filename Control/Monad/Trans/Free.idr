module Control.Monad.Trans.Free

import Control.Monad.Trans

import Control.Monad.Free

data FreeF : (f : Type -> Type) -> (a : Type) -> (b : Type) -> Type where
  Pure : a -> FreeF f a b
  Free : f b -> FreeF f a b

Functor f => Functor (FreeF f a) where
  map _ (Pure a)  = Pure a
  map g (Free as) = Free $ map g as

transFreeF : (forall x. f x -> g x) -> FreeF f a b -> FreeF g a b
transFreeF _   (Pure a)  = Pure a
transFreeF phi (Free as) = Free $ phi as

record FreeT f m a where
  constructor MkFreeT
  runFreeT : m (FreeF f a (FreeT f m a))


export
iterT : {f : _} -> (Functor f, Monad m) => (f (m a) -> m a) -> FreeT f m a -> m a
iterT f (MkFreeT m) = do
  val <- m
  case map (iterT f) val of
    Pure a  => pure a
    Free as => f as
