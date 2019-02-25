open import Relation.Binary

module Data.List.Membership.Setoid.Disjoint {a p} (S : Setoid a p) where
open Setoid S renaming (Carrier to A)
open import Data.List using (List ; [])
open import Data.List.Membership.Setoid (S)
open import Data.List.Membership.Setoid.Trans (S)
open import Data.Empty

open import Function


Disjoint : Rel (List A) _
Disjoint xs ys = ∀ {x} → x ∈ xs → x ∈ ys → ⊥  

disjoint-sym : Symmetric Disjoint
disjoint-sym dis = flip dis

disjoint-[]ˡ : ∀ {xs} → Disjoint xs []
disjoint-[]ˡ _ ()

disjoint-[]ʳ :  ∀ {xs} → Disjoint [] xs
disjoint-[]ʳ ()

disjointness : ∀ {xs ys} → Disjoint xs ys → ∀ {x} → x ∈ xs → ∀ {y} → y ∈ ys → x ≈ y → ⊥
disjointness xs⋈ys x∈xs y∈ys x≈y = xs⋈ys x∈xs (≈-trans-∈ x≈y y∈ys)

