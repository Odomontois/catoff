module Cat 
%default total

infixl 4 &>
(&>): a = b -> b = c -> a = c
Refl &> Refl = Refl 

record Cat ob where
    constructor MkCat
    hom : ob -> ob -> Type
    ident : (a : ob) -> hom a a 
    compose : (a ,b, c : ob) -> hom b c -> hom a b -> hom a c
    l_unit : (a,b : ob) -> (f : hom a b) -> compose a b b (ident b) f = f 
    r_unit : (a, b : ob) -> (f : hom a b) -> compose a a b f (ident a) = f
    assoc : (a,b,c,d : ob) -> (f: hom c d) -> (g: hom b c) -> (h: hom a b) -> 
            compose a b d (compose b c d f g) h = compose a c d f (compose a b c g h)


Set : Cat Type
Set = MkCat (\a, b => (a -> b)) (\_ => id) (\_, _, _, f,g => f . g) (\_, _, _ => Refl) (\_, _, _ => Refl) (\_, _, _, _, _, _, _ => Refl)

UnitCat : Cat ()
UnitCat = MkCat (\_,_ => ()) (\_ => ()) (\_,_,_,_,_ => ()) lu ru ass where
    lu  _ _ f = case f of () => Refl
    ru _ _ f = case f of () => Refl
    ass _ _ _ _ f g h = Refl

infixr 7 ..
(..) : {auto cat : Cat o} -> {a, b, c : o} -> hom cat b c -> hom cat a b -> hom cat a c
(..) {cat} {a} {b} {c} f g = compose cat a b c f g    

infixr 7 ..
ccmp  : (cat : Cat o) -> {a, b, c : o} -> hom cat b c -> hom cat a b -> hom cat a c
ccmp cat {a} {b} {c} f g = compose cat a b c f g   

infix 6 ~>
(~>) : {auto cat : Cat o} -> (x, y: o) -> Type
(~>) {cat} = hom cat

record Funct a b (cod: Cat a) (dom: Cat b) where
    constructor MkFunct
    mob : a -> b
    map : {x,y : a} -> hom cod x y -> hom dom (mob x) (mob y)
    functor_id : (x : a) -> map (ident cod x) = ident dom (mob x)
    functor_comp : (x,y,z: a) -> (f: hom cod y z) -> (g:hom cod x y) -> map (ccmp cod f g) = ccmp dom (map f) (map g)

Functr:{a, b: Type}->(cod: Cat a)->(dom: Cat b)->Type
Functr {a} {b} cod dom = Funct a b cod dom

record FunctEq a b
               (cod: Cat a) (dom: Cat b)
                (f: Functr cod dom)
                (g: Functr cod dom)  where
    constructor FunctRefl
    obEq: (x: a) -> mob f x = mob g x
    mapEq: {x, y: a} -> (t: hom cod x y) -> map f t = map g t 

infix 4 =##=
(=##=): {a, b: Type}->{cod: Cat a}->{dom: Cat b}->(f: Functr cod dom)->(g: Functr cod dom)->Type
(=##=) {a} {b} {cod} {dom} f g = FunctEq a b cod dom f g 

functTrans: f =##= g -> g =##= h -> f =##= h
functTrans fgeq gheq = FunctRefl (\x => trans (obEq fgeq x) (obEq gheq x) ) (\t => trans (mapEq fgeq t) (mapEq gheq t) )

functSym: f =##= g -> g =##= f
functSym fgeq = FunctRefl (\x => sym $ obEq fgeq x) (\t => sym $ mapEq fgeq t)
    

IdF: {ca: Cat a} -> Functr ca ca
IdF {ca} = MkFunct id map' id' comp' where
    map': {x,y: a} -> (hom ca x y) -> (hom ca x y)
    map' x = x
    id': (x : a) -> ident ca x = ident ca x
    id' x = Refl
    comp': (x,y,z: a) -> (f: hom ca y z) -> (g:hom ca x y) -> ccmp ca f g = ccmp ca f g
    comp' x y z f g = Refl

ComposeF: {ca: Cat a}->{cb: Cat b}->{cc: Cat c}->Functr cb cc->Functr ca cb->Functr ca cc
ComposeF {ca} {cb} {cc} f g = MkFunct ob' map' id' comp' where
    ob': a -> c
    ob' = mob f . mob g
    map': {x,y: a} -> hom ca x y -> hom cc (ob' x) (ob' y)
    map' = map f . map g
    id': (x: a) -> map' (ident ca x) = ident cc (ob' x)
    id' x = cong (functor_id g x)  &> functor_id f (mob g x)
    comp': (x,y,z: a) -> (f: hom ca y z) -> (g: hom ca x y)-> map' (ccmp ca f g) = ccmp cc (map' f) (map' g)  
    comp' x y z u v = cong (functor_comp g x y z u v) &> functor_comp f (mob g x) (mob g y) (mob g z) (map g u) (map g v) 

functorLeftUnit: ComposeF IdF f =##= f
functorLeftUnit = FunctRefl (\_ => Refl) (\_ => Refl)

functorRightUnit: ComposeF f IdF =##= f
functorRightUnit = FunctRefl (\_ => Refl) (\_ => Refl)

functorAssocitativity: ComposeF (ComposeF f g) h =##= ComposeF f (ComposeF g h)
functorAssocitativity = FunctRefl (\_ => Refl) (\_ => Refl)