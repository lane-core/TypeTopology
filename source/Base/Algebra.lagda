\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Algebra where

open import Base.Type
open import Base.Pi
open import Base.Sigma
open import Base.Id
open import Base.Homotopy
open import Base.Nat
open import Base.Definitions
open import Base.Operators
open import Base.Sets

forth-and-back-transport : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                           {x y : X} (p : x ＝ y) {a : A x}
                         → (A ↜ p) ((p ↝ A) a) ＝ a
forth-and-back-transport refl = refl

back-and-forth-transport : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                           {x y : X} (p : y ＝ x) {a : A x}
                         → (p ↝ A) ((A ↜ p) a) ＝ a
back-and-forth-transport refl = refl

transport⁻¹-is-pre-comp : {X X' : 𝓤 ̇ } {Y : 𝓥 ̇ } (p : X ＝ X') (g : X' → Y)
                        → ((λ _ → _ → Y) ↜ p) g ＝ g ∘ Idtofun p
transport⁻¹-is-pre-comp refl g = refl

transport-is-pre-comp : {X X' : 𝓤 ̇ } {Y : 𝓥 ̇ } (p : X ＝ X') (g : X → Y)
                      → (p ↝ (λ _ → _ → Y)) g ＝ g ∘ Idtofun (p ⁻¹)
transport-is-pre-comp refl g = refl

trans-sym : {X : 𝓤 ̇ } {x y : X} (r : x ＝ y) → r ⁻¹ ∙ r ＝ refl
trans-sym refl = refl

trans-sym' : {X : 𝓤 ̇ } {x y : X} (r : x ＝ y) → r ∙ r ⁻¹ ＝ refl
trans-sym' refl = refl

transport-× : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
              {x y : X} {c : A x × B x} (p : x ＝ y)
            → (p ↝ (x ꞉ X ↦ (A x × B x))) c
            ＝ (p ↝ A) (pr₁ c) , (p ↝ B) (pr₂ c)
transport-× A B refl = refl

transportd : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : (x : X) → A x → 𝓦 ̇ )
             {x : X}  (a : A x) {y : X} (p : x ＝ y)
           → B x a → B y ((p ↝ A) a)
transportd A B a refl = id

transport-Σ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : (x : X) → A x → 𝓦 ̇ )
              {x : X} (y : X) (p : x ＝ y) (a : A x) {b : B x a}
            → (p ↝ (x ꞉ X ↦ (Σ y ꞉ A x , B x y))) (a , b)
            ＝ (p ↝ A) a , transportd A B a p b

transport-Σ A B {x} x refl a = refl

transport-∙ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
              {x y z : X} (q : x ＝ y) (p : y ＝ z) {a : A x}
            → ((q ∙ p) ↝ A) a ＝ (p ↝ A) ((q ↝ A) a)
transport-∙ A refl refl = refl

transport-∙' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
               {x y z : X} (q : x ＝ y) (p : y ＝ z)
             → (q ∙ p) ↝ A ＝ p ↝ A ∘ q ↝ A
transport-∙' A refl refl = refl

transport-ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ )
               (f : X → Y) {x x' : X} (p : x ＝ x') {a : A(f x)}
             → (p ↝ (A ∘ f)) a ＝ ((f ∘ p) ↝ A) a
transport-ap A f refl = refl

transport-ap' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ )
                (f : X → Y) {x x' : X} (p : x ＝ x')
              → p ↝ (A ∘ f) ＝ (f ∘ p) ↝ A
transport-ap' A f refl = refl


nat-transport : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
                (f : Nat A B) {x y : X} (p : x ＝ y) {a : A x}
              → f y (transport A p a) ＝ transport B p (f x a)
nat-transport f refl = refl

transport-fam : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (P : {x : X} → Y x → 𝓦 ̇ )
               (x : X) (y : Y x) → P y → (x' : X) (r : x ＝ x') → P (transport Y r y)
transport-fam P x y p x refl = p

transport-left-rel : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (_≺_ : {x : X} → Y x → Y x → 𝓦 ̇ )
                   → (a x : X) (b : Y a) (v : Y x) (r : x ＝ a)
                   → transport Y r v ≺ b
                   → v ≺ transport⁻¹ Y r b
transport-left-rel _≺_ a a b v refl = id

transport-right-rel : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (_≺_ : {x : X} → Y x → Y x → 𝓦 ̇ )
                    → (a x : X) (b : Y a) (v : Y x) (p : a ＝ x)
                    →  v ≺ transport Y p b
                    → transport⁻¹ Y p v ≺ b
transport-right-rel _≺_ a a b v refl = id

transport⁻¹-right-rel : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (_≺_ : {x : X} → Y x → Y x → 𝓦 ̇ )
                      → (a x : X) (b : Y a) (v : Y x) (r : x ＝ a)
                      → v ≺ transport⁻¹ Y r b
                      → transport Y r v ≺ b
transport⁻¹-right-rel _≺_ a a b v refl = id

transport⁻¹-left-rel : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (_≺_ : {x : X} → Y x → Y x → 𝓦 ̇ )
                     → (a x : X) (b : Y a) (v : Y x) (p : a ＝ x)
                     → transport⁻¹ Y p v ≺ b
                     → v ≺ transport Y p b
transport⁻¹-left-rel _≺_ a a b v refl = id

transport-const : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x x' : X} {y : Y} (p : x ＝ x')
                → (p ↝ (_ ꞉ X ↦ Y)) y ＝ y
transport-const refl = refl

apd' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (f : (x : X) → A x)
       {x y : X} (p : x ＝ y)
     → (p ↝ A) (f x) ＝ f y
apd' A f refl = refl

apd : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f : (x : X) → A x)
      {x y : X} (p : x ＝ y)
    → (p ↝ A) (f x) ＝ f y
apd = apd' _

ap-id-is-id : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) → ap id p ＝ p
ap-id-is-id refl = refl

ap-id-is-id' : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) → p ＝ ap id p
ap-id-is-id' refl = refl

ap-∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y z : X} (p : x ＝ y) (q : y ＝ z)
     → f ∘ (p ∙ q) ＝ (f ∘ p) ∙ (f ∘ q)
ap-∙ f refl refl = refl

ap-∙' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y : X} (p : x ＝ y)
      → (f ∘ (p ⁻¹)) ∙ (f ∘ p) ＝ refl
ap-∙' f refl = refl

ap-sym : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y : X} (p : x ＝ y)
       → (f ∘ p) ⁻¹ ＝ f ∘ p ⁻¹
ap-sym f refl = refl

ap-ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y) (g : Y → Z)
        {x x' : X} (r : x ＝ x')
      → ap g (ap f r) ＝ ap (g ∘ f) r
ap-ap {𝓤} {𝓥} {𝓦} {X} {Y} {Z} f g refl = refl

\end{code}

Added by Ettore Aldrovandi, Sun Sep 24 00:35:12 UTC 2023

\begin{code}

ap₂-refl-left : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x : X} {y₀ y₁ : Y}
                (q : y₀ ＝ y₁)
              → ap₂ f refl q ＝ ap (f x) q
ap₂-refl-left f refl = refl

ap₂-refl-right : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x₀ x₁ : X} {y : Y}
                (p : x₀ ＝ x₁)
              → ap₂ f p refl ＝ ap (λ v → f v y) p
ap₂-refl-right f refl = refl

ap₂-∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
        (p₀ : x₀ ＝ x₁) (p₁ : x₁ ＝ x₂)
        (q₀ : y₀ ＝ y₁) (q₁ :  y₁ ＝ y₂)
      → ap₂ f (p₀ ∙ p₁) (q₀ ∙ q₁) ＝ ap₂ f p₀ q₀ ∙ ap₂ f p₁ q₁
ap₂-∙ f refl refl refl refl = refl

\end{code}


\begin{code}

ap₃ : {W : 𝓣 ̇} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
      (f : W → X → Y → Z) {w₀ w₁ : W} {x₀ x₁ : X} {y₀ y₁ : Y}
    → w₀ ＝ w₁ → x₀ ＝ x₁ → y₀ ＝ y₁ → f w₀ x₀ y₀ ＝ f w₁ x₁ y₁
ap₃ f refl refl refl = refl

\end{code}

Added by Ettore Aldrovandi, Sun Sep 24 00:35:12 UTC 2023

\begin{code}

ap₃-∙ : {W : 𝓣 ̇} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
        (f : W → X → Y → Z) {w₀ w₁ w₂ : W} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
        (r₀ : w₀ ＝ w₁) (r₁ : w₁ ＝ w₂)
        (p₀ : x₀ ＝ x₁) (p₁ : x₁ ＝ x₂)
        (q₀ : y₀ ＝ y₁) (q₁ :  y₁ ＝ y₂)
      → ap₃ f (r₀ ∙ r₁) (p₀ ∙ p₁) (q₀ ∙ q₁) ＝ ap₃ f r₀ p₀ q₀ ∙ ap₃ f r₁ p₁ q₁
ap₃-∙ f refl refl refl refl refl refl = refl

ap₃-refl-left : {W : 𝓣 ̇} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                (f : W → X → Y → Z) {w : W} {x₀ x₁ : X} {y₀ y₁ : Y}
                (p : x₀ ＝ x₁) (q : y₀ ＝ y₁)
              → ap₃ f refl p q ＝ ap₂ (f w) p q
ap₃-refl-left f refl refl = refl

ap₃-refl-mid : {W : 𝓣 ̇} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
               (f : W → X → Y → Z) {w₀ w₁ : W} {x : X} {y₀ y₁ : Y}
               (r : w₀ ＝ w₁) (q : y₀ ＝ y₁)
              → ap₃ f r refl q ＝ ap₂ (λ w y → f w x y) r q
ap₃-refl-mid f refl refl = refl

ap₃-refl-right : {W : 𝓣 ̇} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
               (f : W → X → Y → Z) {w₀ w₁ : W} {x₀ x₁ : X} {y : Y}
               (r : w₀ ＝ w₁) (p : x₀ ＝ x₁)
              → ap₃ f r p refl ＝ ap₂ (λ w x → f w x y) r p
ap₃-refl-right f refl refl = refl

\end{code}


ap-refl-is-refl : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y} {x : X} → ap f (ℰ x) ＝ ℰ (f x)
ap-refl-is-refl = refl

ap-refl : {Y : 𝓥 ̇} (f : X → Y) {x : X} {y : Y} (p : y ＝ f x) → p ∙ ap f refl ＝ p
ap-refl f refl = refl

ap-refl' : {Y : 𝓥 ̇} (f : X → Y) {x : X} {y : Y} (p : f x ＝ y) → ap f refl ∙ p ＝ p
ap-refl' f refl = refl

ap-refl-comm-if-set : {Y : 𝓥 ̇} {x y z : X} (f g : X → Y)
             → (p : x ＝ y) (q : f x ＝ g x) (r : f y ＝ g y)
             → is-set Y
             → q ∙ ap g p ＝ ap f p ∙ r
ap-refl-comm-if-set f g refl q r =
 -------------------------------------
 q ＝⟨ ap-refl g q ⟩
 q ＝⟨ {!!} ⟩
 r ＝⟨ {!!} ⟩
 (r ↝ ((_＝_) ∘ f) _) (ap f refl) ∎


homotopy-ap : {Y : 𝓥 ̇} {f g : X → Y} → {x y : X} (e : f ∼ g) (p : x ＝ y)
     → e x ∙ ap g p ＝ (p ↝ u ↦ (f x ＝ g u)) (e x)
homotopy-ap e refl = refl

homotopy-ap2 : {Y : 𝓥 ̇} {f g : X → Y} → {x y : X} (e : f ∼ g) (p : x ＝ y)
     → (e x ⁻¹) ∙ ap f p ∙ e y ＝ ap g p
homotopy-ap2 e refl = {!!}

homotopy-ap' : {Y : 𝓥 ̇} {f g : X → Y} → {x y : X} (e : f ∼ g) (p : x ＝ y)
     → (ap f p) ∙ (e y) ＝ (p ↝ u ↦ (f x ＝ g u)) (e x)
homotopy-ap' e refl = {!!}

homotopies-are-natural' : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                          (f g : X → A)
                          (H : f ∼ g)
                          {x y : X}
                          {p : x ＝ y}
                        → H x ∙ (g ◦ p) ∙ (H y)⁻¹ ＝ (f ◦ p)
homotopies-are-natural' f g H {x} {_} {refl} = {!!}

homotopies-are-natural'' : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                           (f g : X → A)
                           (H : f ∼ g)
                           {x y : X}
                           {p : x ＝ y}
                         → (H x) ⁻¹ ∙ f ◦ p ∙ H y ＝ g ◦ p
homotopies-are-natural'' f g H {x} {.x} {refl} = {!!}

homotopies-are-natural : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                         (f g : X → A)
                         (H : f ∼ g)
                         {x y : X}
                         {p : x ＝ y}
                       → H x ∙ ap g p ＝ ap f p ∙ H y
homotopies-are-natural f g H {x} {_} {refl} = refl-left-neutral ⁻¹

-- product of identity terms gives an identity of product terms (uncurried)
-- two products are equal if their projections are equal
＝pr-gives-＝× : {X : 𝓤 ̇} {Y : 𝓥 ̇} {z z' : X × Y}
            → (pr₁ z ＝ pr₁ z') → (pr₂ z ＝ pr₂ z') → z ＝ z'
＝pr-gives-＝× refl refl = refl

×＝pr-gives-＝× : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z z' : X × Y}
          → (pr₁ z ＝ pr₁ z') × (pr₂ z ＝ pr₂ z')
          → z ＝ z'
×＝pr-gives-＝× = uncurry ＝pr-gives-＝×

＝×-gives-×＝pr : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z z' : X × Y}
            → z ＝ z'
            → (pr₁ z ＝ pr₁ z') × (pr₂ z ＝ pr₂ z' )
＝×-gives-×＝pr refl = (refl , refl)

＝×-gives-＝pr₁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z z' : X × Y}
            → z ＝ z'
            → (pr₂ z ＝ pr₂ z') → (pr₁ z ＝ pr₁ z')
＝×-gives-＝pr₁ p q = ap pr₁ p

＝×-gives-＝pr₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z z' : X × Y}
            → z ＝ z'
            → (pr₁ z ＝ pr₁ z') → (pr₂ z ＝ pr₂ z' )
＝×-gives-＝pr₂ p q = ap pr₂ p

-- tofrom-×-＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
--               {z z' : X × Y} (p : z ＝ z')
--             → p ＝ ＝²-gives-＝×, (pr₁ (from-×-＝' p)) (pr₂ (from-×-＝' p))
-- tofrom-×-＝ refl = refl

from-Σ-＝'' : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {u v : Σ Y} (r : u ＝ v)
         → ((ap pr₁ r) ↝ Y) (pr₂ u) ＝ (pr₂ v)
from-Σ-＝'' {𝓤} {𝓥} {X} {Y} {u} {v} refl = refl

from-Σ-＝' : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {u v : Σ Y} (r : u ＝ v)
           → ((pr₁ ◦ r) ↝ Y) (pr₂ u) ＝ (pr₂ v)
from-Σ-＝' {𝓤} {𝓥} {X} {Y} {u} {v} refl = refl

from-Σ-＝ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {σ τ : Σ Y} (r : σ ＝ τ)
          → Σ p ꞉ pr₁ σ ＝ pr₁ τ , (p ↝ Y) (pr₂ σ) ＝ (pr₂ τ)
from-Σ-＝ r = (pr₁ ◦ r , from-Σ-＝' r)

to-Σ-＝ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
        → (Σ p ꞉ pr₁ σ ＝ pr₁ τ , (p ↝ A) (pr₂ σ) ＝ pr₂ τ)
        → σ ＝ τ
to-Σ-＝ (refl , refl) = refl

ap-pr₁-to-Σ-＝ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
                 (w : Σ p ꞉ pr₁ σ ＝ pr₁ τ , (p ↝ A) (pr₂ σ) ＝ pr₂ τ)
               → (pr₁ ◦ to-Σ-＝ w) ＝ pr₁ w
ap-pr₁-to-Σ-＝ (refl , refl) = refl

to-Σ-＝' : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y y' : Y x}
         → y ＝ y'
         → (x , y) ＝[ Σ Y ] (x , y')
to-Σ-＝' {𝓤} {𝓥} {X} {Y} {x} = ap (λ - → (x , -))

fromto-Σ-＝ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
              {σ τ : Σ A}
              (w : Σ p ꞉ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ)
            → from-Σ-＝ (to-Σ-＝ w) ＝ w
fromto-Σ-＝ (refl , refl) = refl

tofrom-Σ-＝ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A} (r : σ ＝ τ)
            → to-Σ-＝ (from-Σ-＝ r) ＝ r
tofrom-Σ-＝ refl = refl

ap-pr₁-to-×-＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z t : X × Y}
              → (p₁ : pr₁ z ＝ pr₁ t)
              → (p₂ : pr₂ z ＝ pr₂ t)
              → ap pr₁ (＝pr-gives-＝× p₁ p₂) ＝ p₁
ap-pr₁-to-×-＝ refl refl = refl

ap-pr₂-to-×-＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z t : X × Y}
              → (p₁ : pr₁ z ＝ pr₁ t)
              → (p₂ : pr₂ z ＝ pr₂ t)
              → ap pr₂ (＝pr-gives-＝× p₁ p₂) ＝ p₂
ap-pr₂-to-×-＝ refl refl = refl

\end{code}

Added by Tom de Jong
22 March 2021:

\begin{code}

-- ap-pr₁-refl-lemma : {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ )
--                     {x : X} {y y' : Y x}
--                     (w : (x , y) ＝[ Σ Y ] (x , y'))
--                   → ap pr₁ w ＝ refl
--                   → y ＝ y'
-- ap-pr₁-refl-lemma Y {x} {y} {y'} w p = γ (ap pr₁ w) p ∙ h
--  where
--   γ : (r : x ＝ x) → (r ＝ refl) → y ＝ transport Y r y
--   γ r refl = refl
--   h : transport Y (ap pr₁ w) y ＝ y'
--   h = from-Σ-＝' w

-- transport-along-＝ : {X : 𝓤 ̇ } {x y : X} (q : x ＝ y) (p : x ＝ x)
--                   → transport (λ - → - ＝ -) q p ＝ q ⁻¹ ∙ p ∙ q
-- transport-along-＝ refl p = (refl ⁻¹ ∙ (p ∙ refl) ＝⟨ refl              ⟩
--                             refl ⁻¹ ∙ p          ＝⟨ refl-left-neutral ⟩
--                             p                    ∎                     ) ⁻¹

-- transport-along-→ : {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) (Z : X → 𝓦 ̇ )
--                     {x y : X}
--                     (p : x ＝ y) (f : Y x → Z x)
--                   → transport (λ - → (Y - → Z -)) p f
--                   ＝ transport Z p ∘ f ∘ transport Y (p ⁻¹)
-- transport-along-→ Y Z refl f = refl

-- \end{code}

-- Added by Ettore Aldrovandi
-- September 19, 2022:

-- \begin{code}

-- ap-refl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x : X}
--         → ap f (𝓻𝓮𝒻𝓵 x) ＝ 𝓻𝓮𝒻𝓵 (f x)
-- ap-refl f = refl
\end{code}
