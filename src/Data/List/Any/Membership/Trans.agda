open import Relation.Binary
module Data.List.Any.Membership.Trans {a p} (S : Setoid a p) where
open Setoid S
open import Data.List.Any.Membership (S)
open import Data.List.Any

≈-trans-∈ : ∀ {x y xs} → x ≈ y → y ∈ xs → x ∈ xs
≈-trans-∈ x≈y (here px) = here (trans x≈y px)
≈-trans-∈ x≈y (there p) = there (≈-trans-∈ x≈y p)

