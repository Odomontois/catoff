module Category
%default total

-- record Cat where
--     constructor MkCat
--     ob : Type
--     hom : ob -> ob -> Type
--     ident : (a : ob) -> hom a a 
--     compose : (a ,b, c : ob) -> hom b c -> hom a b -> hom a c
--     l_unit : (a,b : ob) -> (f : hom a b) -> compose a b b (ident b) f = f 
--     r_unit : (a, b : ob) -> (f : hom a b) -> compose a a b f (ident a) = f
--     assoc : (a,b,c,d : ob) -> (f: hom c d) -> (g: hom b c) -> (h: hom a b) -> 
--             compose a b d (compose b c d f g) h = compose a c d f (compose a b c g h)

interface Category ob where
    hom : ob -> ob -> Type
    ident : (a : ob) -> hom a a
    compose: (a,b,c: ob)->hom b c->hom a b->hom a c
    category_l_unit: (a,b: ob)->(f: hom a b)->compose a b b (ident b) f = f
    category_r_unit: (a,b: ob)->(f: hom a b)->compose a a b f (ident a) = f
    category_assoc: (a,b,c,d : ob)->(f: hom c d)->(g: hom b c)->(h: hom a b)->
        compose a b d (compose b c d f g) h = compose a c d f (compose a b c g h)


infix 6 ~>
(~>) : Category ob=>(a, b: ob)->Type
(~>) a b = hom a b

infixr 7 ..
(..) : Category ob=>{a,b,c: ob}->hom b c->hom a b-> hom a c
(..) {a} {b} {c} f g = compose a b c f g

Category Type where
    hom a b = a -> b
    ident a x = x
    compose _ _ _ f g = f . g
    category_l_unit a b f = Refl
    category_r_unit a b f = Refl
    category_assoc a b c d f g h = Refl

Category () where
    hom a b = ()
    ident a = ()
    compose _ _ _ () () = ()
    category_l_unit a b () = Refl
    category_r_unit a b () = Refl
    category_assoc a b c d () () () = Refl
