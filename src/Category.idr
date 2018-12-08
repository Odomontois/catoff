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

pair_ident: a = b -> x = y -> (a,x) = (b,y)
pair_ident Refl Refl = Refl
    
(Category a, Category b) => Category (a, b) where
    hom (x, u) (y, v) = (hom x y, hom u v)
    ident (x, u) = (ident x, ident u)
    compose (x, u) (y, v) (z, w) (f, k) (g, l) = (compose x y z f g, compose u v w k l)
    category_l_unit (x, u) (y, v) (f, k) = 
       pair_ident (category_l_unit x y f) (category_l_unit u v k)
    category_r_unit (x, u) (y, v) (f, k) = 
       pair_ident (category_r_unit x y f) (category_r_unit u v k)    
    category_assoc (a1, a2) (b1, b2) (c1, c2) (d1, d2) (f1, f2) (g1, g2) (h1, h2) = 
       pair_ident (category_assoc a1 b1 c1 d1 f1 g1 h1) (category_assoc a2 b2 c2 d2 f2 g2 h2) 

interface (Category a, Category b) => Funct a b F where
    fob: F -> a -> b 
    fmap: (x, y: a) -> (f : F) -> hom x y -> hom (fob f x) (fob f y)  
    functor_identity : (x : a) -> (f : F) -> fmap x x f (ident x) = ident (fob f x)
    functor_compose :  (x,y,z: a) ->  (f : F) -> (s: hom y z)->(t: hom x y)-> (
        fmap x z f (compose x y z s t)) = compose (fob f x) (fob f y) (fob f z) (fmap y z f s) (fmap x y f t)

data IdF a = IdF'

Category a => Funct a a (IdF a) where
    fob _ = id
    fmap _ _  _ = id
    functor_identity _ _ = Refl
    functor_compose _ _ _ _ f g = Refl


data ComposeF f g = ComposeF' f g

(abg: Funct a b g', bcf: Funct b c f') => Funct a c (ComposeF f' g') where
    fob (ComposeF' f g) = fob f . fob g 
    fmap : (x, y : a) -> (cfg: ComposeF f' g') -> hom x y -> hom (fob @{bcf} f $ fob @{abg} g x) (fob @{bcf} f $ fob @{abg} g y)
    fmap x y (ComposeF' f g ) = fmap @{bcf} (fob @{abg} g x) (fob @{abg} g y) f . fmap @{abg} g x y
    functor_identity = ?compose_identity
    functor_compose = ?compose_compose
