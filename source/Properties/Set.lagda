citing UF.Subsingletons written by Martin Escardo on TypeTopology

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Properties.Set where

open import Prim.Prelude
open import Properties.Proposition

is-set : End (𝓤 ̇)
is-set X = Π x ꞉ X , Π y ꞉ X , is-prop (x ＝ y)

\end{code}
