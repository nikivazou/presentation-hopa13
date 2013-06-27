\begin{code}
module AbstractRefinements where
\end{code}

Abstract Refinements
====================

Consider the following monomorphic `max` function on `Int` values:

\begin{code}
maxInt     :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 
\end{code}

\begin{code} We could give `maxInt` many, quite different and incomparable refinement types like
maxInt :: Nat -> Nat -> Nat
\end{code}

\begin{code}or
maxInt :: Even -> Even -> Even
\end{code}

\begin{code}or even 
maxInt :: {v:Int | (prime v)} -> {v:Int | (prime v)} -> {v:Int | (prime v)}
\end{code}

Defining Parametric Invariants 
------------------------------

`maxInt` returns *one of* its two arguments `x` and `y`. 

This means that if *both* arguments satisfy some property then the output
*must* satisfy that property, *regardless of what that property was!*

We introduce the idea of **abstracting over refinements**
or, parameterizing a type over its refinements.

We type `maxInt` as

\begin{code}
{-@ maxInt :: forall <p :: Int -> Prop>. Int<p> -> Int<p> -> Int<p> @-}
\end{code}
where <center>`Int<p> = {v:Int | (p v)}`</center>


Here, the definition says explicitly: *for any property* `p` that is a
property of `Int`, the function takes two inputs each of which satisfy `p`
and returns an output that satisfies `p`. 

We encode abstract refinements `p` 
as _uninterpreted function symbols_ in the refinement logic. These are
special symbols which which satisfy only the *congruence axiom*.

<center>
forall X, Y. X = Y => p(X) = p(Y)
</center>

Using Abstract Refinements
--------------------------
With this, if we call `maxInt` if we call it with two `Int`s
that have the same refinement,
the abstract refinement `p` will be instantiated with this concrete refinement.

So, the abstract refinement, can be instantiated with `\v -> v >= 0`
to return `Nat`:
\begin{code}
{-@ maxNat :: Nat @-}
maxNat     :: Int
maxNat     = maxInt 2 5
\end{code}

Or any arbitrary property:
\begin{code}
{-@ type RGB = {v: Int | ((0 <= v) && (v < 256)) } @-}

{-@ maxRGB :: RGB @-}
maxRGB     :: Int
maxRGB     = maxInt 56 8
\end{code}
