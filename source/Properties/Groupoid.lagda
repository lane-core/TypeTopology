\begin{code}

{-# OPTIONS --safe --without-K #-}

module Properties.Groupoid where

open import Prim.Type
open import Properties.HLevel

is-groupoid : (X : 𝓤 ̇) → 𝓤 ̇
is-groupoid A = is-hlevel 3 A

\end{code}
