\begin{code}
module Loop where
import Prelude hiding ((!!), length, (++))
import SimpleRefinements
\end{code}

Inductive Refinements
=====================

*The problem:*
`add` does not typecheck, because the `loop` invariant `I` is *index dependent*
\begin{code}
{-@ add :: n:Nat -> m:Nat -> {v:Int| v = m + n} @-}
add :: Int -> Int -> Int
add n m = loop 0 m n (\_ i -> i + 1)
\end{code}
 
Remember the `loop` function:
\begin{code}
loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f = go lo base
  where go i acc | i < hi    = go (i+1) (f i acc)
                 | otherwise = acc
\end{code}

Consinder the `loop`'s invariant that relates the index `i` with the accumulator `acc`:

<center>`I(acc, i)`</center>

To prove that the result satisfies the invariant at `hi`, 
by induction, we need to prove:

- The base case satisfies the invariant at low, or
<center>`I(base, lo)`</center>

- The `f` inductively presernes the invariant, or
<center>`if I(acc, i) then I(f (i + 1) acc, i+1)`</center>

We encode this reasoning using abstract refinements.
The invariant `I(acc, i)` maps to a refinent on `acc` that depends on `i`, or 
<center> I(acc, i)  <=> `acc :: a <p i>` </center>

So, we type loop as:

\begin{code}
{-@ loop :: forall a <p :: Int -> a -> Prop>.
             lo:{v:Int|v>=0} 
          -> hi:{v:Int|v>=lo}
          -> a<p lo> 
          -> (i:Int -> a<p i> -> a<p (i+1)>) 
          -> a<p hi>
  @-}
\end{code}

\begin{code}Back to `add`:
add n m = loop 0 m n (\_ i -> i + 1)
\end{code}
The invariant is `I(acc, i) <=> acc = i + n`
We can prove:

- The base case satisfies the invariant at low:
`I(n, 0) <=> n = 0 + n`

- The `f` inductively presernes the invariant:
`if (acc =  i + n) then acc + 1 = (i+1) + n`

\begin{code}So, the result satisfies the desired predicate:
add :: n:Nat -> m:Nat -> {v:Int| v = m + n}
\end{code}

Structural Induction
--------------------

We define a `efoldr` funtion that resembles loop.
\begin{code}
{-@ efoldr :: forall a b <p :: L a -> b -> Prop>. 
                (xs:L a -> x:a -> b <p xs> -> b <p (C x xs)>) 
              -> b <p N> 
              -> ys: L a
              -> b <p ys>
  @-}
efoldr :: (L a -> a -> b -> b) -> b -> L a -> b
efoldr op b N        = b
efoldr op b (C x xs) = op xs x (efoldr op b xs)
\end{code}
 
In the `size` function we have an invariant:
`I(xs, acc) <=> acc = llen xs`
\begin{code}
{-@ size :: xs:L a -> {v: Int | v = llen(xs)} @-}
size :: L a -> Int
size = efoldr (\_ _ n -> n + 1) 0
\end{code}

In the `++` function, we have the invariant
`I(xs, acc) <=> llen acc = llen acc + llen ys`:
\begin{code}
 {-@ ++  :: xs: L a 
         -> ys: L a 
        -> {v: L a | (llen(v) = llen(xs) + llen(ys))} 
 @-} 
xs ++ ys = efoldr (\_ z zs -> C z zs) ys xs 
\end{code}
