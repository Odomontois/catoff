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

data Funct : Type -> Type -> Type where
    MkFunct :
    (Category a, Category b) =>
    (fob: a -> b) ->
    (fmap: (x, y: a) -> hom x y -> hom (fob x) (fob y)  ) ->
    (functor_identity : (x : a) -> fmap x x (ident x) = ident (fob x)) -> 
    (functor_compose :  (x,y,z: a) -> (s: hom y z)->(t: hom x y)-> (
        fmap x z (compose x y z s t)) = compose (fob x) (fob y) (fob z) (fmap y z s) (fmap x y t)) -> 
    Funct a b

fob: Funct a b -> a -> b
fob (Funct ob _ _ _) = ob

-- fmap: (f: Funct a b) -> (x, y: a) -> hom x y -> hom (fob f x) (fob f y)
-- fmap 

IdF : (ca: Category a) => Funct a a 
IdF = MkFunct fob fmap fid fcomp where
    fob: a -> a
    fob = id
    fmap : (x, y: a) -> hom x y -> hom x y
    fmap x y = the (hom x y -> hom x y) id
    fid : (x : a) -> fmap x x (ident x ) = ident (fob x)
    fid _ = Refl
    fcomp : (x,y,z: a) -> (s: hom y z) -> (t: hom x y) -> compose x y z s t = compose x y z s t
    fcomp _ _ _ _ _ = Refl

infixl 4 &>
(&>): a = b -> b = c -> a = c
Refl &> Refl = Refl 

ComposeF : Funct b c -> Funct a b -> Funct a c
ComposeF (MkFunct fob fmap fid fcomp) (MkFunct gob gmap gid gcomp) = MkFunct rob rmap rid rcomp where
    rob: a -> c
    rob = fob . gob
    rmap: (x, y: a) -> hom x y -> hom (rob x) (rob y)
    rmap x y = fmap (gob x) (gob y) . gmap x y
    rid: (x: a) -> fmap (gob x) (gob x) (gmap x x (ident x)) = ident (rob x)
    rid x = cong (gid x)  &> fid (gob x)
    rcomp : (x,y,z: a)->(s: hom y z)->(t: hom x y)->rmap x z((..) {ob=a} s t) =  (..) {ob=c} (rmap y z s) (rmap x y t)
    rcomp x y z s t = cong (gcomp x y z s t) &> fcomp (gob x) (gob y) (gob z) (gmap y z s) (gmap x y t) 


getCat : {auto c: Category a} -> Category a
getCat {c} = c

fdom: Funct a b -> Category a
fdom (MkFunct _ _ _ _ ) = getCat {a}

fcod: Funct a b -> Category b
fcod (MkFunct _ _ _ _ ) = getCat {a=b}

functor_eq: (x: Funct a b) -> (y: Funct a b) -> {auto obeq: fob x = fob y} -> {auto mapeq: fmap x = fmap y} -> x = y
-- functor_eq 

-- functor_left_unit: (f: Funct a b) -> ComposeF (IdF @{fcod f}) f = f
-- functor_left_unit (MkFunct fob fmap fid fcomp) = Refl