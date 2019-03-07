{-# OPTIONS --safe --without-K #-}
module Data.List.Membership.Propositional.Distinct where

open import Data.List using (List)
import Relation.Binary.PropositionalEquality as P
open import Data.List.Membership.Setoid.Distinct as D hiding (Distinct) public

Distinct : ∀ {a} {A : Set a} → List A → Set a
Distinct {A = A} = D.Distinct {S = P.setoid A}



