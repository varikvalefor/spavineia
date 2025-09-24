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
open import Data.List
  using (
    List
  )
open import Data.Maybe
  using (
    nothing;
    Maybe;
    maybe;
    just
  )
open import Data.String
  using (
    String
  )
open import Data.Product
  using (
    Σ
  )
open import Data.Nat.DivMod
  using (
  )
open import Relation.Nullary
  using (
    Dec
  )
open import Truthbrary.Record.SR
  using (
    show;
    showNat
  )
open import Truthbrary.Record.LLC
  using (
    _++_;
    liliString
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≡_
  )

record PKED (lTg lTs j : _) : Set (Level.suc (lTg ⊔ lTs ⊔ j))
  where
  field
    cmene : String
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
   → (p : PKED lTg lTs j)
   → PKED.Tg p
   → PKED.J p
   → PKED.ES₁ p
   → PKED.ES₂ p
O< = PKED.enc

<O : ∀ {lTg lTs j}
   → (p : PKED lTg lTs j)
   → PKED.Ts p
   → PKED.J p
   → PKED.ES₂ p
   → Maybe (PKED.ES₁ p)
<O = PKED.dec?

<O∘O< : ∀ {lTg lTs j}
      → (p : PKED lTg lTs j)
      → (tg : PKED.Tg p)
      → (ts : PKED.Ts p)
      → (j : PKED.J p)
      → (es₁ : PKED.ES₁ p)
      → PKED.M p tg ts
      → just es₁ ≡ <O p ts j (O< p tg j es₁)
<O∘O< = PKED.dec∘enc

instance
  rsaN : (n : ℕ) → PKED _ _ _
  rsaN n = record {
    cmene = "RSA-" ++ show n;
    Ts = {!!};
    Tg = {!!};
    traji₁ = just {!!};
    traji₂ = just {!!};
    J = Fin 1;
    M = {!!};
    enc = {!!};
    dec? = {!!};
    dec∘enc = {!!}
    }

record ArkasaF (M₁l M₂l : _) : Set (Level.suc (M₁l ⊔ M₂l))
  where
  field
    cmene : String
    M₁ : ℕ → Set M₁l
    M₂ : ℕ → Set M₂l
  ES₁ = Σ ℕ M₁
  ES₂ = Σ ℕ M₂
  field
    arkasa : ES₁ → ES₂

record PKSig (lTg lTs j M₁l M₂l : _) : Set (Level.suc (lTg ⊔ lTs ⊔ j ⊔ M₁l ⊔ M₂l))
  where
  field
    pked : PKED lTg lTs j
    arkasaf : ArkasaF M₁l M₂l

sha256 : ArkasaF _ _
sha256 = record {
  cmene = "SHA-256";
  M₁ = λ x → ℕ;
  M₂ = Data.Nat._< (2 Data.Nat.^ 256);
  arkasa = {!!}
  }

record Av (lTg lTs j : _) : Set (Level.suc (lTg ⊔ lTs ⊔ j))
  where
  field
    pked : List (PKED lTg lTs j)
\end{code}
