module Control.Monad.Trans.Free.Church

import Control.Monad.Trans

import Control.Monad.Free
import Control.Monad.Free.Church

||| Church-encoded free monad transformer. Translated from:
||| https://hackage.haskell.org/package/free-5.1.8/docs/src/Control.Monad.Trans.Free.Church.html
public export
record FT (f : Type -> Type) (m : Type -> Type) (a : Type) where
  constructor MkFT
  runFT : forall r. (a -> m r) -> (forall x. (x -> m r) -> f x -> m r) -> m r

export
Functor (FT f m) where
  map f (MkFT k) = MkFT $ \kp, kf => k (kp . f) kf

export
Applicative (FT f m) where
  pure a =  MkFT (\k, _ => k a)
  (MkFT fk) <*> (MkFT ak) = MkFT $ \b, fr => fk (\e => ak (\d => b (e d)) fr) fr

export
Monad (FT f m) where
  (MkFT fk) >>= f = MkFT $ \b, fr => fk (\d => runFT (f d) b fr) fr

export
MonadTrans (FT f) where
  lift m = MkFT (\a, _ => m >>= a)

export
{f : _} -> {m : _} -> MonadFree f (FT f m) where
  wrap f = MkFT (\kp, kf => kf (\ft => runFT ft kp kf) f)

export
hoistFT : (Monad m, Monad n) => (forall x. m x -> n x) -> FT f m a -> FT f n a
hoistFT phi (MkFT m) = MkFT (\kp, kf => join . phi $ m (pure . kp) (\xg => pure . kf (join . phi . xg)))

export
iterT : (Functor f, Monad m) => (f (m a) -> m a) -> FT f m a -> m a
iterT f (MkFT m) = m pure (\xg => f . map xg)

export
iterTM : (Functor f, Monad m, MonadTrans t, Monad (t m)) => (f (t m a) -> t m a) -> FT f m a -> t m a
iterTM f (MkFT m) = join . lift $ m (pure . pure) (\xg => pure . f . map (join . lift . xg))
