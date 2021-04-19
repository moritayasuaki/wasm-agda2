module Evaluation where
open import Syntax
open import Data.Nat renaming (ℕ to Nat)
open import Data.Bool renaming (not to not')

module Equality where
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Function.Injection
  open import Data.Nat as N
  open import Data.Nat.Properties as P
  to : valtype → Nat
  to i32 = 1
  to i64 = 2

  injective : ∀ {x y : valtype} → to x ≡ to y → x ≡ y
  injective {i32} {i32} p = refl
  injective {i64} {i64} p = refl
  module _ where
    infix 4 _==-vt_
    _==-vt_ : Decidable _≡_
    _==-vt_ = via-injection (injection to injective) P._≟_

module Monad where
  open import Data.String using (String)
  open import Data.Product
  open import Data.Unit
  open import Function
  open import Category.Monad

  data result (X : Set) : Set where
    ok : X → result X
    error : String → result X

  evaluation : Set → Set → Set
  evaluation C X = C → (result X × C)

  unit : ∀{C X} → X → evaluation C X
  unit x = λ c → ok x , c
  bind : ∀{C X Y} → evaluation C X → (X → evaluation C Y) → evaluation C Y
  bind mx mxy = λ c → mx c |> λ { (ok x , c') → mxy x c'
                                ; (error msg , c') → error msg , c' }

  evaluationMonad : ∀ C → RawMonad (evaluation C)
  evaluationMonad C = record
    { return = unit
    ; _>>=_ = bind
    }

open Monad
open import Data.Unit
open import Data.Product
open import Data.List

interp-vt : valtype → Set
interp-vt i32 = U32
interp-vt i64 = U64

push : val → evaluation configuration ⊤
push v (config st vs is bctx) = ok tt , config st (v ∷ vs) is bctx 

pop : evaluation configuration val
pop (config st (v ∷ vs) is bctx) = ok v , config st vs is bctx
pop cfg@(config st [] is bctx) = error "value stack underflow" , cfg

