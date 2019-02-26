module Equivalences

%access export

interface IsEquivalence (rel : a -> a -> Type) where 
    symmetry: rel x y -> rel y x
    reflectivity: rel x x 
    transitivity: rel x y -> rel y z -> rel x z


data Setoid: (a: Type) -> Type where
    MkSetoid : IsEquivalence rel => (rel: a -> a -> Type) -> Setoid a

seteq: Setoid a -> a -> a -> Type
seteq (MkSetoid rel) = rel