\begin{code}
module Loop where
import Prelude hiding ((!!), length)
import SimpleRefinements
\end{code}

Higher Order Specifications
---------------------------

Consider a `loop` function:
\begin{code}
loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f = go lo base
  where go i acc | i < hi    = go (i+1) (f i acc)
                 | otherwise = acc
\end{code}

We can use `(!!)` to write a function that adds the elements of a list of `Nat`s:
\begin{code}
{-@ listNatSum :: L Nat -> Nat @-}
listNatSum     :: L Int -> Int
listNatSum xs  = loop 0 n 0 body 
  where body   = \i acc -> acc + (xs !! i)
        n      = length xs
\end{code}
We note that `0 <= i < llen xs` which makes indexing safe.
Also, `(+) :: Nat -> Nat -> Nat` and the function is safe, as
in `loop`'s type `a` is instantiated with `Nat` getting:

`loop :: Int -> Int -> Nat -> (Int -> Nat -> Nat) -> Nat`

We use the same code to add the elements of an `Even` list.
\begin{code}
{-@ listEvenSum :: L Even -> Even @-}
listEvenSum     :: L Int -> Int
listEvenSum xs  = loop 0 n 0 body 
  where body   = \i acc -> acc + (xs !! i)
        n      = length xs
\end{code}

With the same reasoning, `(+) :: Even -> Even -> Even` and the function is safe, as
in `loop`'s type `a` is instantiated with `Even` getting

`loop :: Int -> Int -> Even -> (Int -> Even -> Even) -> Even`

Another Example
---------------

Consinder a simpler example:
\begin{code}
{-@ add :: n:Nat -> m:Nat -> {v:Int| v = m + n} @-}
add     :: Int -> Int -> Int
add n m = loop 0 m n (\_ i -> i + 1)
\end{code}
 
We cannot use the same reasoning as before, as if we substitute 
`a` with `{v:Int|v = n + m}` in the `loop`'s type, we take an invalid type.

It turns out that the invariant we want *depends* on the index `i`.
The loop invariant is:
<center>I(acc, i) <=> acc = i + n</center>

And the result satisfies the invariant at `m`:
<center>I(add n m , m) <=> add n m = m + n </center>

To prove `add` is safe we need to express `index dependent refinements`...
