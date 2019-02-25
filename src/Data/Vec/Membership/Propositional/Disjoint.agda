module Data.Vec.Membership.Propositional.Disjoint where
open import Data.Vec
open import Data.Vec.Membership.Propositional
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (flip)

Disjoint : ∀ {a} {A : Set a} {n m} → Vec A n → Vec A m → Set a
Disjoint xs ys = ∀ {x} → x ∈ xs → x ∈ ys → ⊥ 

disjoint-sim : ∀ {a} {A : Set a} {n m} {xs : Vec A n}{ys :  Vec A m} → Disjoint xs ys → Disjoint ys xs
disjoint-sim dis = flip dis

disjoint-[]ˡ : ∀ {a} {A : Set a} {n} {xs : Vec A n} → Disjoint [] xs
disjoint-[]ˡ () 

disjoint-[]ʳ : ∀ {a} {A : Set a} {n} {xs : Vec A n} → Disjoint xs []
disjoint-[]ʳ = disjoint-sim disjoint-[]ˡ

disjointness :  ∀ {a} {A : Set a} {n m} {xs : Vec A n}{ys :  Vec A m} → Disjoint xs ys →
             ∀ {x y} → x ∈ xs → y ∈ ys → x ≢ y  
disjointness dis x∈xs y∈ys x≡y rewrite x≡y = dis x∈xs y∈ys
