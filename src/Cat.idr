module Cat 
%default total

record Cat where
    constructor MkCat
    ob : Type
    hom : ob -> ob -> Type
    ident : (a : ob) -> hom a a 
    compose : {a ,b, c : ob} -> hom b c -> hom a b -> hom a c
    l_unit : {a,b : ob} -> (f : hom a b) -> compose (ident b) f = f 
    r_unit : {a, b : ob} -> (f : hom a b) -> compose f (ident a) = f
    assoc : {a,b,c,d : ob} -> (f: 
    hom c d) -> (g: hom b c) -> (h: hom a b) -> 
            compose (compose f g) h = compose f (compose g h)


Set : Cat 
Set = MkCat Type (\a, b => (a -> b)) (\_ => id) (\f,g => f . g) (\f => Refl) (\f => Refl) (\f, g, h => Refl)

record Functor (cod : Cat) (dom : Cat) where
    constructor MkFunctor
    mob : ob cod -> ob dom
    map : {a, b : ob cod} -> hom cod a b -> hom dom (mob a) (mob b)
    functor_id : {a : ob cod} -> map (ident cod a) = ident dom (mob a)
    functor_comp : {a, b, c : ob cod} -> (f : hom cod b c) -> (g : hom cod a b) -> map (compose cod f g) = compose dom (map f) (map g)
