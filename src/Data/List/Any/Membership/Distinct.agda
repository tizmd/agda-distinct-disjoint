open import Relation.Binary

module Data.List.Any.Membership.Distinct  where

open import Data.List as List using (List; [];  _∷_; _++_)
open import Data.List.Any as Any hiding (map; tail)
open import Data.List.Any.Properties

import Relation.Binary.PropositionalEquality as P
open import Function
open import Function.Equivalence using (_⇔_; equivalence)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using ()
open import Function.Injection using (_↣_; Injection)
open import Data.Product hiding (map)
open import Data.Sum     hiding (map)
import Level as L
open import Data.Fin as Fin
open import Data.Nat as ℕ

module _ {a p} {S : Setoid a p} where
  open Setoid S renaming (Carrier to A)
  open import Data.List.Any.Membership (S)
  open import Data.List.Any.Membership.Disjoint (S) renaming (Disjoint to _⋈_)  
  open import Data.List.Any.Membership.Trans (S)
  data Distinct : List A → Set (a L.⊔ p) where
    distinct-[] : Distinct []
    _distinct-∷_by_ : ∀ x {xs} → Distinct xs → x ∉ xs → Distinct (x ∷ xs)
  
  head : ∀ {x}{xs : List A} → Distinct (x ∷ xs) → A
  head (x distinct-∷ _ by _) = x
  
  tail : ∀ {x}{xs : List A} → Distinct (x ∷ xs) → Distinct xs
  tail (_ distinct-∷ dis by _) = dis

  head∉tail : ∀ {x}{xs : List A} → Distinct (x ∷ xs) → x ∉ xs
  head∉tail (_ distinct-∷ _ by x∉xs) = x∉xs

  distinct-[_] : ∀ x → Distinct (List.[ x ])
  distinct-[ x ] = x distinct-∷ distinct-[] by (λ ())
  
  ⋈-++ : ∀ (xs ys : List A) →
    Distinct (xs ++ ys) ⇔ (Distinct xs × Distinct ys × xs ⋈ ys)
  ⋈-++ xs ys = equivalence to from
    where
      to : ∀ {xs ys : List A} → Distinct (xs ++ ys) → (Distinct xs × Distinct ys × xs ⋈ ys)
      to {[]} dys = distinct-[] , dys , disjoint-[]ʳ 
      to {x ∷ xs} {ys} (.x distinct-∷ dis by x∉xsys) with to {xs = xs} dis
      ... | dxs , dys , xs⋈ys = x distinct-∷ dxs by (λ x∈xs → x∉xsys (++⁺ˡ x∈xs)) , dys ,
            λ { (here px) ∈ys → x∉xsys (++⁺ʳ xs (≈-trans-∈ (sym px) ∈ys)) ; (there ∈xs) ∈ys → xs⋈ys ∈xs ∈ys}
  
      from : ∀ {xs ys : List A} →
           (Distinct xs × Distinct ys × xs ⋈ ys) → Distinct (xs ++ ys)
      from (distinct-[] , dys , xs⋈ys) = dys
      from {xs = .x ∷ xs} ((x distinct-∷ dxs by x∉xs) , dys , xxs⋈ys) with from (dxs , dys , xxs⋈ys ∘ there)
      ... | dxsys = x distinct-∷ dxsys by λ x∈xsys → case ++⁻ xs x∈xsys of λ { (inj₁ x∈xs) → x∉xs x∈xs
                                                                             ; (inj₂ x∈ys) → xxs⋈ys (here refl) x∈ys}
module _ {a₁ a₂ p₁ p₂}{S₁ : Setoid a₁ p₁} {S₂ : Setoid a₂ p₂} where
  open Setoid S₁ renaming (Carrier to A) using ()
  open Setoid S₂ renaming (Carrier to B) using ()
  open import Data.List.Any.Membership (S₂) renaming (_∉_ to _∉₂_) using ()
  open import Data.List.Any.Membership.Properties
  open import Data.List.Any.Membership.Trans (S₁)  
  map : (f : Injection S₁ S₂) → ∀ {xs : List A} → Distinct {S = S₁} xs → Distinct {S = S₂} (List.map (Injection.to f ⟨$⟩_) xs)          
  map f {[]} distinct-[] = distinct-[]
  map f {.x ∷ xs} (x distinct-∷ dis by x∉xs) = fx distinct-∷ map f dis by lemma
      where
        fx = Injection.to f ⟨$⟩ x

        lemma : fx ∉₂ List.map (Injection.to f ⟨$⟩_) xs
        lemma p with ∈-map⁻ S₁ S₂ p
        ... | _ , y∈xs , fx≈fy = x∉xs (≈-trans-∈ (Injection.injective f fx≈fy) y∈xs)  

