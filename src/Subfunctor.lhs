> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE AllowAmbiguousTypes #-}

A Subfunctor g of f in Haskell

> module Subfunctor (Subfunctor(..)) where

> import qualified Control.Category as C (Category(..))
> import Control.Lens.Iso (Iso', iso, under)
> import Control.Natural
> import Data.Functor.Compose
> import Data.Functor.Const (Const(..), getConst)
> import Data.Functor.Identity (Identity(..))
> import Data.Functor.Product
> import Data.List ((!!))
> import Data.List.NonEmpty (fromList, NonEmpty(..))
> import qualified Data.List.NonEmpty as NE
> import Data.Maybe (isJust)
> import Data.Void (absurd, Void)
> import Numeric.Natural (Natural)

is exhibited by a natural transformation "promote"

> class (Functor f, Functor g) => Subfunctor f g where
>     promote :: f ~> g

from f to g that is injective (i.e. it is lossless - it does not throw away any information - all the original data can always be reconstructed).

There is a Functor Category (already defined in Control.Natural), whose objects are Functors, and whose morphisms are Natural Transformations.

The identity morphism in this category is obviously lossless, so it gives rise to a subfunctor relationship between every functor and itself:

> instance Functor f => Subfunctor f f where
>     promote = unwrapNT $ C.id @(:~>)

And composing two lossless natural transformations obviously forms a natural transformation that is itself lossless,
so the subfunctor relationship is transitive, as one would intuitively expect:

> instance {-# INCOHERENT #-} (Functor f, Functor h, Subfunctor f g, Subfunctor g h) => Subfunctor f h where
>     promote = (NT (promote @g @h) C.. NT promote #)

So we can form a wide subcategory of the Functor Category, which I will call the Subfunctor Category.

The initial object in both categories is:

> type InitialFunctor = Const Void

It is initial because it is a subfunctor of every functor as exhibited by the unique natural transformation:

> instance Functor g => Subfunctor InitialFunctor g where
>     promote = absurd . getConst

This natural transformation is necessarily unique because its input argument cannot exist, so it has an empty range,
so it cannot have different outputs:

> instance Functor g => Eq (InitialFunctor :~> g) where
>     x == y = True

Products are category-theoretic products in the Subfunctor Category:

> instance (Functor y, Functor x1, Functor x2, Subfunctor y x1, Subfunctor y x2) => Subfunctor y (Product x1 x2) where
>     promote y = Pair (promote y) (promote y)

  # Examples

Identity is a Subfunctor of any Applicative:

> instance Applicative f => Subfunctor Identity f where
>     promote = pure . runIdentity

The empty box

> type EmptyBox = Const ()

is also a subfunctor of Maybe:

> instance Subfunctor EmptyBox Maybe where
>     promote = const Nothing

and a subfunctor of Void-valued functions:

> instance Subfunctor EmptyBox ((->) Void) where
>     promote = const absurd

This natural transformation is actually a natural isomorphism because we can go both ways:

> instance Subfunctor ((->) Void) EmptyBox where
>     promote = const $ Const ()

Similarly, in the special case of unit-valued functions, Identity is isomorphic to them:

> instance Subfunctor ((->) ()) Identity where
>     promote f = pure $ f ()

Enum-valued functions are isomorphic to lists:

> instance Enum e => Subfunctor ((->) e) [] where
>     promote f = map f [(toEnum 0)..]

> instance Enum e => Subfunctor [] ((->) e) where
>     promote xs = (xs !!) . fromEnum

Identity has a natural transformation making it a subfunctor of NonEmpty:

instance Subfunctor Identity NonEmpty where
    promote = pure . runIdentity

(this is a special case of the Applicative instance above.)

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
> genSfIdentityNE n = withDuplicatesNE n C.. NT promote

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
>    promote = maybe [] pure

And again, there are also an infinite number of alternatives:

> withDuplicates :: Natural -> [] :~> []
> withDuplicates n = NT $ first (n + 1) . cycle

> genSfMaybeList :: Natural -> Maybe :~> []
> genSfMaybeList n = withDuplicates n C.. NT promote

NonEmpty can also be promoted to list:

> instance Subfunctor NonEmpty [] where
>     promote = NE.toList

There are also an infinite number of alternatives here:

> genSfNonEmptyList :: Natural -> NonEmpty :~> []
> genSfNonEmptyList n = withDuplicates n C.. NT promote

But in this case, we should not consider the alternatives to be equal because there exists no retraction of genSfNonEmptyList n for all n simultaneously,
because a retraction would need to know the length of the original list, but without knowing n (the number of duplicates) we don't know it.

Maybe can be promoted to Either ():

> instance Subfunctor Maybe (Either ()) where
>     promote = maybe (Left ()) Right

This natural transformation is actually a natural isomorphism because we can go both ways:

> instance Subfunctor (Either ()) Maybe where
>     promote (Left ()) = Nothing
>     promote (Right x) = Just x

> eitherMaybeIso :: Iso' (Maybe a) (Either () a)
> eitherMaybeIso = iso promote promote

An arbitrary pair can be promoted to a function, but only if the domain is not a subsingleton type and the codomain is something with sufficient structure, like Either.

Let's write down the simplest approach:

> type Discriminator c = Compose ((->) Bool) (Either c)

> instance Subfunctor ((,) c) (Discriminator c) where
>     promote (x, y) = Compose $ \b -> if b then Left x else Right y

This natural transformation is actually a natural isomorphism because we can go both ways:

instance Subfunctor (Discriminator c) ((,) c) where
    promote (Compose f) = (f True, f False)

Oops, this doesn't work - we would need dependent types for it to work, but Haskell doesn't have dependent types!

What about composition of functors in general?

> instance (Applicative h, Subfunctor h f, Subfunctor h g) => Subfunctor h (Compose f g) where
>     promote x = Compose $ fmap (promote @h @g . pure) $ promote x

This works because each step is injective, and fmap can't throw away data or that would break the first fmap law (fmap id == id).
fmap can't "look inside" an arbitrary function in Haskell, it has to behave the same for all functions.
(This is a key distinction between Haskell and many other languages such as Scala!)

Now let's try to decompose Discriminator into two Subfunctors.

How about:

instance Subfunctor ((,) c) ((->) b) where
    promote (x, y) = const y

This wouldn't be a valid instance, because it isn't injective - it throws away x.

OK, what about the other part, just for a laugh?

instance Subfunctor ((,) c) (Either c) where
    promote (x, y) = Left x

Also not a valid instance, because it throws away y.

We could also pick something richer than Bool for the domain of the function, e.g.:

> type Ternary = Maybe Bool

> class Distinguishable d where
>     distinguish :: d -> Bool

Law for Distinguishable: there must exist at least one value for which distinguish returns True and at least one value for which it returns False

> instance Distinguishable Bool where
>     distinguish = id

> instance Distinguishable Ternary where
>     distinguish = isJust

> type ExtravagantDiscriminator c d = Compose ((->) d) (Either c)

> instance Distinguishable d => Subfunctor ((,) c) (ExtravagantDiscriminator c d) where
>     promote (x, y) = Compose $ \d -> if distinguish d then Left x else Right y

