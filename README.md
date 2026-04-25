This diagram shows the subfunctor relationships between various Haskell type constructors that have been implemented in this library.

A subfunctor is an injective natural transformation (a mapping between functors). This library also implements the associated retractions.

**NOTE**: The retractions are not necessarily total functions, although we do try to make them total where possible, e.g. by
mapping back values outside the range of the natural transformation to dummy values. Inside the range of the natural transformation,
calling the retraction must "undo" the effect of the natural transformation, i.e. yield the original value.

`InitialFunctor` is in fact a subfunctor of everything - but this fact is not shown in the diagram because it would be too messy!

For more details on what the node labels mean, check out the Haskell source code in [src].

![Subfunctor relationships](./instances.svg)