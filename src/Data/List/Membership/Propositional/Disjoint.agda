{-# OPTIONS --safe --without-K #-}
module Data.List.Membership.Propositional.Disjoint {ℓ} {A : Set ℓ} where
import Relation.Binary.PropositionalEquality as P
open import Data.List.Membership.Setoid.Disjoint (P.setoid A) public
