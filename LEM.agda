{-
Copyright 2025 Shea Levy

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module LEM where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary
open import Cubical.Data.Sum
open import Cubical.Data.Prod

lem : ∀ {ℓ} {P : Type ℓ} → ¬ (¬ (P ⊎ (¬ P)))
lem {P = P} ¬[P∨¬P] = ¬[P∨¬P] (inr ¬P)
  where
    ¬P : ¬ P
    ¬P p = ¬[P∨¬P] (inl p)

-- Heyting if restricted to Prop
lem-bicartesian-closed : ∀ {ℓ} {P : Type ℓ} → ¬ (¬ (P ⊎ (¬ P)))
lem-bicartesian-closed = eval ∘ ⟨ λ' (eval ∘ (id ×ₕ inr)) , λ' (eval ∘ (id ×ₕ inl)) ⟩
  where
    id : ∀ {ℓ} {A : Type ℓ} → A → A
    id x = x

    ⟨_,_⟩ : ∀ {ℓₐ ℓₘ ℓₙ} {A : Type ℓₐ} {M : Type ℓₘ} {N : Type ℓₙ} → (A → M) → (A → N) → (A → M × N)
    ⟨_,_⟩ = intro

    -- × is a functor, ₕ for 'hom' since there's no f subscript
    _×ₕ_ : ∀ {ℓₘ ℓₙ ℓₘ' ℓₙ'} {M : Type ℓₘ} {N : Type ℓₙ} {M' : Type ℓₘ'} {N' : Type ℓₙ'} → (M → M') → (N → N') → (M × N → M' × N')
    _×ₕ_ f g (x , y) = (f x , g y)

    eval : ∀ {ℓₘ ℓₙ} {M : Type ℓₘ} {N : Type ℓₙ} → ((M → N) × M) → N
    eval (f , x) = f x

    λ' : ∀ {ℓₐ ℓₘ ℓₙ} {A : Type ℓₐ} {M : Type ℓₘ} {N : Type ℓₙ} → (A × M → N) → (A → (M → N))
    λ' f a m = f (a , m)
