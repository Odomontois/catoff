module Equivalences

%access export

interface IsEquivalence (rel : a -> a -> Type) where 
    symmetry: rel x y -> rel y x
    reflectivity: rel x x 
    transitivity: rel x y -> rel y z -> rel x z


record Eqv (a: Type) (rel: a -> a -> Type) where
    constructor MkEqv     
    eqvSymm: {u, v : a} -> rel u v-> rel v u
    eqvReflect: {x : a} -> rel x x 
    eqvTrans: {x, y, z : a} -> rel x y -> rel y z -> rel x z


record SomeEqv a where
    constructor MkSomeEqv 
    rel: a -> a -> Type
    eqv: Eqv a rel

mkEqv: IsEquivalence {a} r => Eqv a r
mkEqv = MkEqv symmetry reflectivity transitivity