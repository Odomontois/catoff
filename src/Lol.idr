module Lol

%default total

data Part = System | Molecule

data Tag: (p: Part) -> Type where
    PdbS: Tag System 
    UserS: Tag System

data Datas: {p: Part} -> (tag: Tag t) -> Type where 
    PdbData: Bool -> Datas PdbS

data TTags: {p: Part} -> (tags: List (Tag p)) -> Type where
    TNil: {p: Part} -> TTags []
    TCons: {p: Part} -> {th: Tag p} -> {tt: List (Tag p)} -> Datas th -> TTags tt -> TTags (th::tt)

extract2: TTags [PdbS] -> Bool
extract2 (TCons (PdbData b) TNil) = b

check: {n: Nat} -> S n = Z -> Void
check = absurd


record Foo where
    constructor MkFoo
    num : Nat -> Type
    bar : num 0

foo: Foo
foo = MkFoo ?fnum ?fbar    

data Foo1 : Type where
    MkFoo1 : (num : Nat -> Type) -> (bar : num 0) -> Foo1

foo1: Foo1
foo1 = MkFoo1 ?fnum ?fbar
