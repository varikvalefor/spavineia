\begin{code}
open import Level
  using (
    Level;
    _⊔_
  )
open import Data.Fin
  using (
    Fin
  )
open import Data.Nat
  using (
    ℕ
  )
open import Data.Maybe
  using (
    nothing;
    Maybe;
    maybe;
    just
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≡_
  )

record PKED {lTg} {lTs} {j} : Set (Level.suc (lTg ⊔ lTs ⊔ j))
  where
  field
    Tg : Set lTg
    Ts : Set lTs
    J : Set j
    traji₁ : Maybe ℕ
    traji₂ : Maybe ℕ

  ES₁ : Set
  ES₁ = maybe Fin ℕ traji₁

  ES₂ : Set
  ES₂ = maybe Fin ℕ traji₂

  field
    M : Tg → Ts → Set
    enc : Tg → J → ES₁ → ES₂
    dec? : Ts → J → ES₂ → Maybe ES₁

  field
    dec∘enc : (tg : Tg)
            → (ts : Ts)
            → (j : J)
            → (es : ES₁)
            → M tg ts
            → just es ≡ dec? ts j (enc tg j es)

O< : ∀ {lTg lTs j}
   → (p : PKED {lTg} {lTs} {j})
   → PKED.Tg p
   → PKED.J p
   → PKED.ES₁ p
   → PKED.ES₂ p
O< p t j es = PKED.enc p t j es

<O : ∀ {lTg lTs j}
   → (p : PKED {lTg} {lTs} {j})
   → PKED.Ts p
   → PKED.J p
   → PKED.ES₂ p
   → Maybe (PKED.ES₁ p)
<O = PKED.dec?

record PKSig : Set {!!}
  where

Cryptosystem : Set
Cryptosystem = {!!}
\end{code}
