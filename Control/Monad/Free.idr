module Control.Monad.Free

public export
interface MonadFree (0 f : Type -> Type) (0 m : Type -> Type) where
  wrap : (Functor f, Monad m) => f (m a) -> m a

export
liftF : (Functor f, Monad m, MonadFree f m) => f a -> m a
liftF = wrap . map pure
