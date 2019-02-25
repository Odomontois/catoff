module Cat 
import Equivalences

%default total

infixl 4 &>
(&>): a = b -> b = c -> a = c
Refl &> Refl = Refl 

record CatBase (ob: Type) where
    constructor MkCatBase
    hom : ob -> ob -> Type
    ident : (a : ob) -> hom a a
    compose : (a ,b, c : ob) -> hom b c -> hom a b -> hom a c


record CatIdent (ob: Type) where
    constructor MkCatBaseIdent
    base: CatBase ob
    eqv: (a: ob) -> (b: ob) -> SomeEqv (hom base a b)

record CatLaws (o: Type) (ci: CatIdent o) where
    constructor MkCatLaws
    l_unit : (a, b : o) -> hom (base ci) a b 
    -- -> identity i (compose a b b (ident b) f) f 
    -- r_unit : (a, b : o) -> (f : hom a b) -> identity i (compose a a b f (ident a)) f
    -- assoc : (a,b,c,d : o) -> (f: hom c d) -> (g: hom b c) -> (h: hom a b) -> 
    --         compose a b d (compose b c d f g) h = compose a c d f (compose a b c g h)



-- record Cat ob where
--     constructor MkCat
    
    
    


-- Set : Cat Type
-- Set = MkCat (\a, b => (a -> b)) (\_ => id) (\_, _, _, f,g => f . g) (\_, _, _ => Refl) (\_, _, _ => Refl) (\_, _, _, _, _, _, _ => Refl)

-- UnitCat : Cat ()
-- UnitCat = MkCat (\_,_ => ()) (\_ => ()) (\_,_,_,_,_ => ()) lu ru ass where
--     lu  _ _ f = case f of () => Refl
--     ru _ _ f = case f of () => Refl
--     ass _ _ _ _ f g h = Refl

-- infixr 7 ..
-- (..) : {auto cat : Cat o} -> {a, b, c : o} -> hom cat b c -> hom cat a b -> hom cat a c
-- (..) {cat} {a} {b} {c} f g = compose cat a b c f g    

-- infixr 7 ..
-- ccmp  : (cat : Cat o) -> {a, b, c : o} -> hom cat b c -> hom cat a b -> hom cat a c
-- ccmp cat {a} {b} {c} f g = compose cat a b c f g   

-- infix 6 ~>
-- (~>) : {auto cat : Cat o} -> (x, y: o) -> Type
-- (~>) {cat} = hom cat

-- record Funct a b (dom: Cat a) (cod: Cat b) where
--     constructor MkFunct
--     mob : a -> b
--     map : {x,y : a} -> hom dom x y -> hom cod (mob x) (mob y)
--     functor_id : (x : a) -> map (ident dom x) = ident cod (mob x)
--     functor_comp : (x,y,z: a) -> (f: hom dom y z) -> (g:hom dom x y) -> map (ccmp dom f g) = ccmp cod (map f) (map g)

-- Functr:{a, b: Type}->(dom: Cat a)->(cod: Cat b)->Type
-- Functr {a} {b} dom cod = Funct a b dom cod

-- record FunctEq a b
--                (dom: Cat a) (cod: Cat b)
--                 (f: Functr dom cod)
--                 (g: Functr dom cod)  where
--     constructor FunctRefl
--     obEq: (x: a) -> mob f x = mob g x
--     mapEq: {x, y: a} -> (t: hom dom x y) -> map f t = map g t 

-- infix 4 =##=
-- (=##=): {a, b: Type}->{dom: Cat a}->{cod: Cat b}->(f: Functr dom cod)->(g: Functr dom cod)->Type
-- (=##=) {a} {b} {dom} {cod} f g = FunctEq a b dom cod f g 

-- functTrans: f =##= g -> g =##= h -> f =##= h
-- functTrans fgeq gheq = FunctRefl (\x => trans (obEq fgeq x) (obEq gheq x) ) (\t => trans (mapEq fgeq t) (mapEq gheq t) )

-- functSym: f =##= g -> g =##= f
-- functSym fgeq = FunctRefl (\x => sym $ obEq fgeq x) (\t => sym $ mapEq fgeq t)


-- IsEquivalence (FunctEq a b dom cod) where
--    reflectivity = FunctRefl (\u => Refl) (\t => Refl)
--    symmetry = functSym
--    transitivity = functTrans
    

-- IdF: (ca: Cat a) -> Funct a a ca ca
-- IdF (ca) = MkFunct id map' id' comp' where
--     map': {x,y: a} -> (hom ca x y) -> (hom ca x y)
--     map' x = x
--     id': (x : a) -> ident ca x = ident ca x
--     id' x = Refl
--     comp': (x,y,z: a) -> (f: hom ca y z) -> (g:hom ca x y) -> ccmp ca f g = ccmp ca f g
--     comp' x y z f g = Refl

-- ComposeF: {ca: Cat a}->{cb: Cat b}->{cc: Cat c}->Functr cb cc->Functr ca cb->Functr ca cc
-- ComposeF {ca} {cb} {cc} f g = MkFunct ob' map' id' comp' where
--     ob': a -> c
--     ob' = mob f . mob g
--     map': {x,y: a} -> hom ca x y -> hom cc (ob' x) (ob' y)
--     map' = map f . map g
--     id': (x: a) -> map' (ident ca x) = ident cc (ob' x)
--     id' x = cong (functor_id g x)  &> functor_id f (mob g x)
--     comp': (x,y,z: a) -> (f: hom ca y z) -> (g: hom ca x y)-> map' (ccmp ca f g) = ccmp cc (map' f) (map' g)  
--     comp' x y z u v = cong (functor_comp g x y z u v) &> functor_comp f (mob g x) (mob g y) (mob g z) (map g u) (map g v) 

-- functorLeftUnit: (f: Funct a b ca cb) ->  ComposeF (IdF cb) f =##= f
-- functorLeftUnit f = FunctRefl (\_ => Refl) (\_ => Refl)

-- functorRightUnit: (f: Funct a b ca cb) -> ComposeF f (IdF ca) =##= f
-- functorRightUnit f = FunctRefl (\_ => Refl) (\_ => Refl)

-- functorAssocitativity: ComposeF (ComposeF f g) h =##= ComposeF f (ComposeF g h)
-- functorAssocitativity = FunctRefl (\_ => Refl) (\_ => Refl)

-- SomeCat:Type
-- SomeCat = (t : Type ** Cat t)


-- catHom : SomeCat -> SomeCat -> Type
-- catHom (a ** ca) (b ** cb)  = Funct a b ca cb

-- catIdent : (c: SomeCat) -> catHom c c
-- catIdent (x ** cx) =  IdF {a=x} cx

-- catCompose: (cx: SomeCat) -> (cy: SomeCat) -> (cz: SomeCat) -> (f: catHom cy cz) -> (g: catHom cx cy) -> catHom cx cz
-- catCompose (a ** ca) (b ** cb) (c ** cc) f g  = ComposeF f g

-- сat_l_unit : (sa, sb : SomeCat) -> (f : catHom sa sb) -> catCompose sa sb sb (catIdent sb) f = f
-- сat_l_unit  (a**ca) (b**cb) f = functorLeftUnit {a} {b} {ca} {cb} f

-- catCat: Cat SomeCat


-- catCat = MkCat catHom catIdent catCompose ?cat_l_unit ?cat_r_unit ?catAssoc 