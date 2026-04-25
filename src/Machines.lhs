> module Machines () where

> import Data.Functor.Compose
> import Data.List.Infinite (Infinite(..))
> import Data.List.NonEmpty (fromList, NonEmpty(..))
> import qualified Data.List.NonEmpty as NE
> import Data.Machine.Mealy (Mealy(..))
> import Numeric.Natural (Natural)
> import Subfunctor

We can promote non-empty lists to infinite lists:

> nonEmptyToInfiniteList :: NonEmpty a -> Infinite a
> nonEmptyToInfiniteList = impl . NE.cycle
>     where
>         impl :: NonEmpty a -> Infinite a
>         impl xs = NE.head xs :< (impl . NE.fromList $ NE.tail xs)

But this is lossy because although we don't lose any data from inside the non-empty list, we lose information
about the list's structure which is necessary to retain for a retract function to be able to work - namely,
its length.

So let's instead declare a type synonym InfListAndNat:

> type InfListAndNat = Compose ((,) Natural) Infinite

> natLength :: NonEmpty a -> Natural
> natLength (x :| xs) = 1 + fromIntegral (length xs)

> takeInf :: Natural -> Infinite a -> NonEmpty a
> takeInf 1 (x :< _ ) = x :| []
> takeInf n (x :< xs) = x :| NE.toList (takeInf (n - 1) xs)

And now we can declare the subfunctor relationship:

> instance Subfunctor NonEmpty InfListAndNat where
>     promote xs = Compose (natLength xs, nonEmptyToInfiniteList xs)
>     retract (Compose (n, il)) = takeInf n il

Infinite is a subfunctor of a Mealy machine - we don't need the length to come along for the ride for this one:

> instance Subfunctor Infinite (Mealy b) where
>     promote (x :< xs) = Mealy . const $ (x, promote xs)
>     retract (Mealy f) = let (x, xs) = f undefined in x :< retract xs

But in order to have a subfunctor relationship between NonEmpty and Mealy - my original goal - we would again
need to compose in the length, so that we could chain together the aboe two relationships.

For this, I see another opportunity to code a general solution!

And it's also another opportunity to play with composition of functors:

> instance (Functor f, Subfunctor g h) => Subfunctor (Compose f g) (Compose f h) where
>     promote = Compose . fmap promote . getCompose
>     retract = Compose . fmap retract . getCompose

If we set f to ((,) Natural), we get what we want here, namely:

instance Subfunctor InfListAndNat (Compose ((,) Natural) (Mealy b))

which can then be chained together with instance Subfunctor NonEmpty InfListAndNat above, using the instance in Transitive.lhs.