\begin{code}
module SimpleRefinements where
import Prelude hiding ((!!), length)
import Language.Haskell.Liquid.Prelude
\end{code}


Simple Refinement Types
=======================
The type

<center><h1>`{v:Int | v = 0}`</h1></center>

describes a value `v` which is Integer and equal to `0`.


\begin{code}
{-@ zero :: {v:Int | v = 0} @-}
zero     :: Int
zero     =  0
\end{code}

We treat refinements as *logical formulas* whose implications give subtyping:

Since
`v = 0 => v >= 0` 

Therefore
 `{v:Int | v = 0} <: {v:Int | v >= 0}`

\begin{code}So we can have a type for natural numbers:
type Nat = {v:Int | v >= 0}
\end{code}

and type `0` as `Nat`:
\begin{code}
{-@ zero' :: Nat @-}
zero'     :: Int
zero'     =  0
\end{code}

Similarly, since
`v = 0 => v mod 2 = 0` 

Therefore
`{v:Int | v = 0} <: {v:Int | v mod 2 = 0}`

\begin{code}
{-@ type Even = {v:Int | v mod 2 = 0} @-}

{-@ zero'' :: Even @-}
zero''     :: Int
zero''     =  0
\end{code}


Lists
-----
Refinemets may live inside type constructors:

\begin{code}
infixr `C`
data L a = N | C a (L a)
\end{code}

\begin{code}
{-@ natList :: L Nat @-}
natList     :: L Int
natList     =  0 `C` 1 `C` 3 `C` N

{-@ evenList :: L Even @-}
evenList     :: L Int
evenList     =  0 `C` 2 `C` 8 `C` N
\end{code}

Demo

Dependent Functions
-------------------
Consinder a `safeDiv` operator:
\begin{code}
safeDiv    :: Int -> Int -> Int
safeDiv x y = x `div` y
\end{code}

We can use refinement types to specify that its
<center>*second argument is different than zero*</center>

\begin{code}
{-@ safeDiv :: Int -> {v:Int | v != 0} -> Int @-}
\end{code}

Demo

Now, consinder list indexing:
\begin{code}
(!!)       :: L a -> Int -> a
(C x _) !!0 = x
(C _ xs)!!n = xs!!(n-1)
_       !!_ = error "This should not happen!"
\end{code}


*Precondition:*
<center> The index `i` should be `0 <= i < len list`</center>

Expressing list's length in logic
\begin{code}
{-@ measure llen :: (L a) -> Int
    llen(N)      = 0
    llen(C x xs) = 1 + (llen xs)
  @-}
\end{code}

\begin{code}We use the *measure* to automatically strengthen the type of data constructors
data L a where 
  N :: {v : L a | (llen v) = 0}
  C :: a -> xs:(L a) -> {v:(L a) |(llen v) = 1 + (llen xs)}
\end{code}

So we can prove:
\begin{code}
{-@ length :: xs:(L a) -> {v:Int | v = (llen xs)} @-}
length     :: L a -> Int
length N        = 0
length (C _ xs) = 1 + (length xs)
\end{code}

With this we type `(!!)` as
\begin{code}
{-@ (!!) :: ls:(L a)
         -> {v:Int | ((v >= 0) && (v < (llen ls)))} 
         -> a
  @-}
\end{code}

Demo
