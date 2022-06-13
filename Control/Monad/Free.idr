module Control.Monad.Free

public export
interface MonadFree (f : Type -> Type) (m : Type -> Type) where
  wrap : (Functor f, Monad m) => f (m a) -> m a

export
liftF : {f : _} -> {m : _} -> (Functor f, Monad m, MonadFree f m) => f a -> m a
liftF = wrap . map pure
