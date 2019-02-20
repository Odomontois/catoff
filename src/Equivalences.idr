module Equivalences

%access export

interface IsEquivalence (rel : a -> a -> Type) where 
    symmetry: rel x y -> rel y x
    reflectivity: rel x x 
    transitivity: rel x y -> rel y z -> rel x z