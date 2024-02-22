\begin{code}

{-# OPTIONS --safe --without-K #-}

module Properties.Contractible where

open import Prim.Prelude

is-contr : End (𝓤 ̇)
is-contr X = Σ c ꞉ X , Π x ꞉ X , c ＝ x

\end{code}
