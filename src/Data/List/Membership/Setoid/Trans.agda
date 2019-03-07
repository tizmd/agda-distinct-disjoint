{-# OPTIONS --safe --without-K #-}
open import Relation.Binary
module Data.List.Membership.Setoid.Trans {a p} (S : Setoid a p) where
open Setoid S
open import Data.List.Membership.Setoid (S)
open import Data.List.Any

≈-trans-∈ : ∀ {x y xs} → x ≈ y → y ∈ xs → x ∈ xs
≈-trans-∈ x≈y (here px) = here (trans x≈y px)
≈-trans-∈ x≈y (there p) = there (≈-trans-∈ x≈y p)

