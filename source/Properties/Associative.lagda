\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import Prim.Type
open import Prim.Path

module Properties.Associative where

associative : {X : 𝓤 ̇} (_·_ : X → X → X) → 𝓤 ̇
associative _·_ = ∀ x y z → x · (y · z) ＝ (x · y) · z

\end{code}
