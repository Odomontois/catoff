module Main

main: IO ()
main = putStrLn "Hello World"

tt : {a : Type} -> List a -> List a
tt xs = xs ++ xs

ttt : tt {a = Int} [1, 2, 3] = [1,2,3,1,2,3]
ttt = Refl