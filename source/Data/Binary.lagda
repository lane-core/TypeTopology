\begin{code}

{-# OPTIONS --safe --without-K #-}

module Data.Binary where

open import Prim.Type
open import Prim.Path
open import Prim.Sigma

data 𝔹 : 𝓤₀ ̇ where
 center : 𝔹
 left : 𝔹 → 𝔹
 right : 𝔹 → 𝔹

_∩_ : 𝔹 → 𝔹 → 𝔹
center ∩ y = y
left x ∩ center = left x
left x ∩ left y = left (x ∩ y)
left x ∩ right y = x ∩ y
right x ∩ center = right x
right x ∩ left y = x ∩ y
right x ∩ right y = right (x ∩ y)

-- scalar multiplication
half double : 𝔹 → 𝔹
half center = left center
half (left x) = left (left (half x))
half (right center) = center
half (right (left xs)) = left (right (double xs))
half (right (right xs)) = right (half xs)
double center = right center
double (left center) = center
double (left (left xs)) = left (double xs)
double (left (right xs)) = right (left (half xs))
double (right x) = right (right (double x))

\end{code}

x ∙ y / x ∙ y + 1 = (L x ∙ L y)

u / u + 1 = v

u + 1 = u / v
