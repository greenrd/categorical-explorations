> module Machines () where

> import Data.Functor.Compose
> import Data.List.NonEmpty (fromList, NonEmpty(..))
> import qualified Data.List.NonEmpty as NE
> import Numeric.Natural (Natural)
> import Subfunctor

From the machines package:

> newtype Mealy a b = Mealy { runMealy :: a -> (b, Mealy a b) }

> instance Functor (Mealy a) where
>  fmap f (Mealy m) = Mealy $ \a -> case m a of
>    (b, n) -> (f b, fmap f n)
>  {-# INLINE fmap #-}
>  b <$ _ = pure b
>  {-# INLINE (<$) #-}

> instance Applicative (Mealy a) where
>  pure b = r where r = Mealy (const (b, r))
>  {-# INLINE pure #-}
>  Mealy m <*> Mealy n = Mealy $ \a -> case m a of
>    (f, m') -> case n a of
>       (b, n') -> (f b, m' <*> n')
>  m <* _ = m
>  {-# INLINE (<*) #-}
>  _ *> n = n
>  {-# INLINE (*>) #-}

Let's also define an infinite list type:

> data InfList a = InfList a (InfList a)

> instance Functor InfList where
>    fmap f (InfList x xs) = InfList (f x) $ fmap f xs

> nonEmptyToInfiniteList :: NonEmpty a -> InfList a
> nonEmptyToInfiniteList = impl . NE.cycle
>     where
>         impl :: NonEmpty a -> InfList a
>         impl xs = InfList (NE.head xs) $ impl . NE.fromList $ NE.tail xs

> type InfListAndNat = Compose ((,) Natural) InfList

> natLength :: NonEmpty a -> Natural
> natLength (x :| xs) = 1 + fromIntegral (length xs)

> takeInf :: Natural -> InfList a -> NonEmpty a
> takeInf 1 (InfList x _) = x :| []
> takeInf n (InfList x xs) = x :| NE.toList (takeInf (n - 1) xs)

> instance Subfunctor NonEmpty InfListAndNat where
>     promote xs = Compose (natLength xs, nonEmptyToInfiniteList xs)
>     retract (Compose (n, il)) = takeInf n il

> instance Subfunctor InfList (Mealy b) where
>     promote (InfList x xs) = Mealy . const $ (x, promote xs)
>     retract (Mealy f) = let (x, xs) = f undefined in InfList x $ retract xs

Here's another opportunity to play with composition of functors:

> instance (Functor f, Subfunctor g h) => Subfunctor (Compose f g) (Compose f h) where
>     promote = Compose . fmap promote . getCompose
>     retract = Compose . fmap retract . getCompose