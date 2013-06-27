\begin{code}
module Composition where
\end{code}

Function Composition
--------------------

Consinder a function that takes one argument and adds `3` to it.
Its refinement type can fully capture its behaviour.
\begin{code}
{-@ plus3' :: x:Int -> {v:Int | v = x + 3} @-}
plus3'     :: Int -> Int
plus3' x   = x + 3
\end{code}

Now, consider this addition happens as a composition of two functions.
We first add `2` to the argument and then add `1` to the intermediate result.
\begin{code}
{-@ plus3'' :: x:Int -> {v:Int | v = x + 3} @-}
plus3''     :: Int -> Int
plus3''     = (+1) . (+2)
\end{code}

This function is not safe because there is no way to `compose` refinements in our first order setting.
We want to capture the fact that the refinement of the result is the 
*composition* of the refinements of both argument results.

To do so, we redifine the composition operator and give it a quite descriptive type:

\begin{code}
{-@ c :: forall < p :: b -> c -> Prop
                , q :: a -> b -> Prop>.
         (x:b -> c<p x>) 
      -> g:(x:a -> b<q x>) 
      -> y:a 
      -> exists[z:b<q y>].c<p z>
 @-}
c :: (b -> c) -> (a -> b) -> a -> c
c f g x = f (g x)
\end{code}

With this type for composition, we can verify the desired `plus3` function:
\begin{code}
{-@ plus3 :: x:Int -> {v:Int | v = x + 3} @-}
plus3     :: Int -> Int
plus3     = (+1) `c` (+2)
\end{code}

Though, we need to give it another hint.
We need to inform liquidHaskell that the information that a value
is equal to a sum of values interests us, and it needs to propagate it.
\begin{code}
{-@ qualif Plus(v:int,a:int,b:int): v = a + b @-}
\end{code}
