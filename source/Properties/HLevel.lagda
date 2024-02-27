\begin{code}

{-# OPTIONS --safe --without-K #-}

module Properties.HLevel where

open import Prim.Prelude
open import Prim.Naturals
open import Properties.Contractible
open import Properties.Proposition

is-hlevel : ℕ → 𝓤 ̇ → Type _
is-hlevel zero A = is-contr A
is-hlevel (suc zero) A = is-prop A
is-hlevel (suc (suc n)) A = Π x ꞉ A , Π y ꞉ A , is-hlevel n (x ＝ y)

\end{code}
