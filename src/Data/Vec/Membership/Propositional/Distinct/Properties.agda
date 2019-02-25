module Data.Vec.Membership.Propositional.Distinct.Properties where
open import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality as P
open import Data.Vec as Vec using (Vec; [] ; _∷_ ; _++_)
open import Data.Vec.Any
open import Data.Vec.Membership.Propositional.Distinct
open import Data.Vec.Membership.Propositional.Disjoint renaming (Disjoint to _⋈_)
open import Data.Vec.Membership.Propositional.Properties
open import Data.Vec.Membership.Propositional
open import Data.Product
open import Data.Empty using (⊥-elim)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)

distinct-++ˡ : ∀ {a}{A : Set a}{m n} (xs : Vec A m){ys : Vec A n} → Distinct (xs ++ ys) → Distinct xs
distinct-++ˡ [] dis = distinct-[]
distinct-++ˡ (x ∷ xs) (.x distinct-∷ dis by x∉xsys) = x distinct-∷ distinct-++ˡ xs dis by λ x∈xs → x∉xsys (∈-++⁺ˡ x∈xs)

distinct-++ʳ : ∀ {a}{A : Set a}{m n} (xs : Vec A m) {ys : Vec A n} → Distinct (xs ++ ys) → Distinct ys
distinct-++ʳ [] dys = dys
distinct-++ʳ (x ∷ xs) (.x distinct-∷ dxsys by _) = distinct-++ʳ xs dxsys

distinct-++→disjoint : ∀ {a}{A : Set a}{m n} (xs : Vec A m) {ys : Vec A n} → Distinct (xs ++ ys) → xs ⋈ ys
distinct-++→disjoint [] dxsys {z} () z∈ys 
distinct-++→disjoint (x ∷ xs) (.x distinct-∷ dxsys by x∉xsys) {.x} (here refl) x∈ys = x∉xsys (∈-++⁺ʳ xs x∈ys)
distinct-++→disjoint (x ∷ xs) (.x distinct-∷ dxsys by x₁) {z} (there z∈xs) z∈ys = distinct-++→disjoint xs dxsys z∈xs z∈ys

⋈→distinct-++ : ∀ {a}{A : Set a}{m n}{xs : Vec A m}{ys : Vec A n} → Distinct xs → Distinct ys → xs ⋈ ys → Distinct (xs ++ ys)
⋈→distinct-++ {xs = []}  _ dys _ = dys
⋈→distinct-++ {xs = x ∷ xs} (.x distinct-∷ dxs by x∉xs) dys xxs⋈ys = x distinct-∷ ⋈→distinct-++ dxs dys (xxs⋈ys ∘ there)
  by λ x∈xs++ys → xxs⋈ys (here P.refl) (x∈xs++ys→x∉xs→x∈ys xs x∈xs++ys x∉xs) 
  where
    x∈xs++ys→x∉xs→x∈ys : ∀ {a} {A : Set a} {m n} (xs : Vec A m){ys : Vec A n} → 
                       ∀ {x} → x ∈ xs ++ ys → x ∉ xs → x ∈ ys
    x∈xs++ys→x∉xs→x∈ys [] x∈ys _ = x∈ys
    x∈xs++ys→x∉xs→x∈ys (x ∷ xs) (here refl) x∉xs = ⊥-elim (x∉xs (here refl))
    x∈xs++ys→x∉xs→x∈ys (x ∷ xs) (there x∈xsys) x∉xs = x∈xs++ys→x∉xs→x∈ys xs x∈xsys (x∉xs ∘ there)

distinct-++⇔⋈ : ∀ {a}{A : Set a}{m n} {xs : Vec A m}{ys : Vec A n} →
  Distinct (xs ++ ys) ⇔ (Distinct xs × Distinct ys × xs ⋈ ys)
distinct-++⇔⋈ = equivalence to from
  where
    open import Data.Nat.Properties
      
    to : ∀ {a}{A : Set a} {m n} {xs : Vec A m}{ys : Vec A n} →
         Distinct (xs ++ ys) → (Distinct xs × Distinct ys × xs ⋈ ys)
    to {xs = xs} dxsys = distinct-++ˡ xs dxsys , distinct-++ʳ xs dxsys , distinct-++→disjoint xs dxsys
    from : ∀ {a}{A : Set a} {m n} {xs : Vec A m}{ ys : Vec A n} → 
         (Distinct xs × Distinct ys × xs ⋈ ys) → Distinct (xs ++ ys)
    from (dxs , dys , xs⋈ys) = ⋈→distinct-++ dxs dys xs⋈ys 


private
  lookup-∈ : ∀ {a n}{A : Set a} i (xs : Vec A n) → Vec.lookup i xs ∈ xs
  lookup-∈ () []
  lookup-∈ zero (x ∷ xs) = here P.refl
  lookup-∈ (suc i) (x ∷ xs) = there (lookup-∈ i xs)
  
lookup-injective : ∀ {a n}{A : Set a} {xs : Vec A n}{i j} →
  Distinct xs → Vec.lookup i xs ≡ Vec.lookup j xs → i ≡ j
lookup-injective {i = ()} {j} distinct-[] _
lookup-injective {i = zero} {zero} (x distinct-∷ dxs by x∉xs) eq = P.refl
lookup-injective {i = suc i} {suc j} (x distinct-∷ dxs by x∉xs) eq = P.cong Fin.suc (lookup-injective dxs eq)
lookup-injective {xs = _ ∷ xs} {i = zero} {suc j} (x distinct-∷ dxs by x∉xs) eq rewrite eq =
  ⊥-elim (x∉xs (lookup-∈ j xs))
lookup-injective {xs = _ ∷ xs} {i = suc i} {zero} (x distinct-∷ dxs by x∉xs) eq  rewrite P.sym eq = ⊥-elim (x∉xs (lookup-∈ i xs))
