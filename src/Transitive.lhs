> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE AllowAmbiguousTypes #-}

> module Transitive () where

> import qualified Control.Category as C (Category(..))
> import Control.Natural
> import Subfunctor

And composing two lossless natural transformations obviously forms a natural transformation that is itself lossless,
so the subfunctor relationship is transitive, as one would intuitively expect:

> instance {-# INCOHERENT #-} (Functor f, Functor h, Subfunctor f g, Subfunctor g h) => Subfunctor f h where
>     promote = (NT (promote @g @h) C.. NT promote #)
>     retract = (NT (retract @f @g) C.. NT (retract @g @h) #)