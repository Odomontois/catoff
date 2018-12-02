module Cat 
%default total


record Cat where
    constructor MkCat
    ob : Type
    hom : ob -> ob -> Type
    ident : (a : ob) -> hom a a 
    compose : (a ,b, c : ob) -> hom b c -> hom a b -> hom a c
    l_unit : (a,b : ob) -> (f : hom a b) -> compose a b b (ident b) f = f 
    r_unit : (a, b : ob) -> (f : hom a b) -> compose a a b f (ident a) = f
    assoc : (a,b,c,d : ob) -> (f: hom c d) -> (g: hom b c) -> (h: hom a b) -> 
            compose a b d (compose b c d f g) h = compose a c d f (compose a b c g h)

Set : Cat 
Set = MkCat Type (\a, b => (a -> b)) (\_ => id) (\_, _, _, f,g => f . g) (\_, _, _ => Refl) (\_, _, _ => Refl) (\_, _, _, _, _, _, _ => Refl)

UnitCat : Cat 
UnitCat = MkCat () (\_,_ => ()) (\_ => ()) (\_,_,_,_,_ => ()) lu ru ass where
    lu  _ _ f = case f of () => Refl
    ru _ _ f = case f of () => Refl
    ass _ _ _ _ f g h = Refl

infixr 7 ..

(..) : {cat : Cat} -> {a, b, c : ob cat} -> hom cat b c -> hom cat a b -> hom cat a c
(..) {cat} {a} {b} {c} f g = compose cat a b c f g    


infix 6 ~>
(~>) : {cat : Cat} -> (a, b: ob cat) -> Type
(~>) {cat} = hom cat

record Functor (dom : Cat) (cod : Cat) where
    constructor MkFunctor
    mob : ob dom -> ob cod
    map : {a, b : ob dom} -> hom dom a b -> hom cod (mob a) (mob b)
    functor_id : {a : ob dom} -> map (ident dom a) = ident cod (mob a)
    functor_comp : {a,b,c: ob dom} -> (f: b ~> c) -> (g : a ~> b) -> map (f .. g) = map f .. map g


