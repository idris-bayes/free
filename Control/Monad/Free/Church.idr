module Control.Monad.Free.Church

import Control.Monad.Trans

import Control.Monad.Free

record F (f : Type -> Type) (a : Type) where
  constructor MkF
  runF : forall z. (a -> z) -> (f z -> z) -> z

Functor (F f) where
  map f (MkF g) = MkF (\kp => g (kp . f))

Applicative (F f) where
  pure x = MkF (\kp, _ => kp x)
  MkF f <*> MkF g = MkF (\kp, kf => f (\a => g (kp . a) kf) kf)

Monad (F f) where
  MkF m >>= f = MkF (\kp, kf => m (\a => runF (f a) kp kf) kf)

MonadTrans F where
  lift f = MkF (\kp, kf => kf (liftM kp f))
    where liftM : (a -> b) -> m a -> m b
          liftM f m = pure $ f !m

{f : _} -> MonadFree f (F f) where
  wrap f = MkF (\kp, kf => kf (map (\(MkF m) => m kp kf) f))
