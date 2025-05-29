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
open import Cubical.Relation.Nullary
open import Cubical.Data.Sum

lem : ∀ {ℓ} {P : Type ℓ} → ¬ (¬ (P ⊎ (¬ P)))
lem ¬[P∨¬P] = ¬[P∨¬P] ∘ inr $ ¬[P∨¬P] ∘ inl
