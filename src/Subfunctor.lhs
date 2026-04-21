> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE AllowAmbiguousTypes #-}

A Subfunctor g of f in Haskell

> module Subfunctor (Subfunctor(..)) where

> import qualified Control.Category as C (Category(..))
> import Control.Lens.Iso (Iso', iso, under)
> import Control.Natural
> import Data.Functor.Const (Const, getConst)
> import Data.Functor.Identity (Identity(..))
> import Data.Functor.Product
> import Data.List.NonEmpty (fromList, NonEmpty(..))
> import qualified Data.List.NonEmpty as NE
> import Data.Void (absurd, Void)
> import Numeric.Natural (Natural)

is exhibited by a natural transformation "promote"

> class (Functor f, Functor g) => Subfunctor f g where
>     promote :: f :~> g

from f to g that is injective (i.e. it is lossless - it does not throw away any information - all the original data can always be reconstructed).

There is a Functor Category (already defined in Control.Natural), whose objects are Functors, and whose morphisms are Natural Transformations.

The identity morphism in this category is obviously lossless, so it gives rise to a subfunctor relationship between every functor and itself:

> instance Functor f => Subfunctor f f where
>     promote = C.id

And composing two lossless natural transformations obviously forms a natural transformation that is itself lossless,
so the subfunctor relationship is transitive, as one would intuitively expect:

> instance {-# INCOHERENT #-} (Functor f, Functor h, Subfunctor f g, Subfunctor g h) => Subfunctor f h where
>     promote = promote @g @h C.. promote @f @g

So we can form a wide subcategory of the Functor Category, which I will call the Subfunctor Category.

The initial object in both categories is:

> type InitialFunctor = Const Void

It is initial because it is a subfunctor of every functor as exhibited by the unique natural transformation:

> instance Functor g => Subfunctor InitialFunctor g where
>     promote = NT $ absurd . getConst

This natural transformation is necessarily unique because its input argument cannot exist, so it has an empty range,
so it cannot have different outputs:

> instance Functor g => Eq (InitialFunctor :~> g) where
>     x == y = True

Products are category-theoretic products in the Subfunctor Category:

> instance (Functor y, Functor x1, Functor x2, Subfunctor y x1, Subfunctor y x2) => Subfunctor y (Product x1 x2) where
>     promote = NT $ \y -> Pair (promote # y) (promote # y)

  # Examples

There is only one such natural transformation making Identity a subfunctor of Maybe:

> instance Subfunctor Identity Maybe where
>     promote = NT $ pure . runIdentity

The empty box

> type EmptyBox = Const ()

is also a subfunctor of Maybe:

> instance Subfunctor EmptyBox Maybe where
>     promote = NT $ const Nothing

Identity also has a natural transformation making it a subfunctor of NonEmpty:

> instance Subfunctor Identity NonEmpty where
>     promote = NT $ pure . runIdentity

But there are also an infinite number of alternative such natural transformations:

> first :: Natural -> [a] -> [a]
> first 0 _ = []
> first i (h:t) = h : first (i - 1) t

> neProductIso :: Iso' (a, [a]) (NonEmpty a)
> neProductIso = iso (\(x, xs) -> x :| xs) (\(x :| xs) -> (x, xs))

> mapTail :: ([a] -> [a]) -> NonEmpty a -> NonEmpty a
> mapTail = under neProductIso . fmap

> withDuplicatesNE :: Natural -> NonEmpty :~> NonEmpty
> withDuplicatesNE n = NT $ mapTail (first n) . NE.cycle

> genSfIdentityNE :: Natural -> Identity :~> NonEmpty
> genSfIdentityNE n = withDuplicatesNE n C.. promote

If we define:

> eqAt :: Eq (g a) => f a -> (f :~> g) -> (f :~> g) -> Bool
> eqAt b (NT nt1) (NT nt2) = nt1 b == nt2 b

> headNT :: NonEmpty :~> Identity
> headNT = NT $ Identity . NE.head

then all of those natural transformations are equal to each other under the following equality:

> instance Eq (Identity :~> NonEmpty) where
>    sf1 == sf2 = eqAt (Identity ()) (headNT C.. sf1) (headNT C.. sf2)

In the Functor Category, headNT is a morphism and is a retraction of genSfIdentityNE n for all n

Similarly, Maybe has a natural transformation making it a subfunctor of the list functor:

> instance Subfunctor Maybe [] where
>    promote = NT $ maybe [] pure

And again, there are also an infinite number of alternatives:

> withDuplicates :: Natural -> [] :~> []
> withDuplicates n = NT $ first (n + 1) . cycle

> genSfMaybeList :: Natural -> Maybe :~> []
> genSfMaybeList n = withDuplicates n C.. promote