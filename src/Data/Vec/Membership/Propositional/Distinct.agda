module Data.Vec.Membership.Propositional.Distinct where

open import Data.Vec as Vec using (Vec; [];  _∷_; _++_)

open import Data.Vec.Membership.Propositional
open import Data.Vec.Any hiding (map; index; head; tail)
open import Data.List as List using (List)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; _≗_ )
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; _≇_)
import Data.List.Membership.Propositional.Distinct as ListDistinct
open import Data.Product as Prod hiding (map)
open import Data.Sum     hiding (map)
open import Data.Empty   using (⊥-elim)
open import Relation.Nullary
open import Data.Fin as Fin
open import Data.Fin.Properties using (suc-injective) 
open import Data.Nat as ℕ
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Function.Equality as F using (_⟨$⟩_)
open import Function.Injection using (_↣_; Injection)

data Distinct {a}{A : Set a} : ∀ {n} → Vec A n → Set a where
  distinct-[] : Distinct [] 
  _distinct-∷_by_ : ∀ {n} x {xs : Vec A n} → Distinct xs → x ∉ xs → Distinct (x ∷ xs)

head : ∀ {a}{A : Set a} {n} {x}{xs : Vec A n} → Distinct (x ∷ xs) → A
head (x distinct-∷ _ by _) = x

tail : ∀ {a}{A : Set a} {n} {x}{xs : Vec A n} → Distinct (x ∷ xs) → Distinct xs
tail (_ distinct-∷ dis by _) = dis

head∉tail : ∀ {a}{A : Set a} {n} {x}{xs : Vec A n} → Distinct (x ∷ xs) → x ∉ xs
head∉tail (_ distinct-∷ _ by x∉xs) = x∉xs

[_] : ∀{a}{A : Set a}(x : A) → Distinct Vec.[ x ]  
[ x ] = x distinct-∷ distinct-[] by (λ ())

{-
_distinct-∷ʳ_by_ : ∀ {a}{A : Set a} {n} {xs : Vec A n} → Distinct xs → (x : A) → x ∉ xs → Distinct (xs Vec.∷ʳ x)
distinct-[] distinct-∷ʳ x by x∉xs = x distinct-∷ distinct-[] by x∉xs
(y distinct-∷ dxs by y∉xs) distinct-∷ʳ x by x∉yxs = y distinct-∷ dxs distinct-∷ʳ x by (x∉yxs ∘ there) by lemma y∉xs x∉yxs
  where
    lemma : ∀ {a}{A : Set a} {n} {xs : Vec A n} {x y} → y ∉ xs → x ∉ y Vec.∷ xs → y ∉ xs Vec.∷ʳ x
    lemma {xs = []} y∉xs x∉y∷xs (here P.refl) = x∉y∷xs (here P.refl)
    lemma {xs = []} y∉xs x∉y∷xs (there ())
    lemma {xs = _ ∷ xs} y∉xs x∉y∷xs (here P.refl) = y∉xs (here P.refl)
    lemma {xs = x₁ ∷ xs}{x}{y} y∉xs x∉y∷xs (there y∈xs∷ʳx) = {!!}
-}
initLast : ∀ {a n} {A : Set a}{xs : Vec A (suc n)} → Distinct xs →
  let (ys , y , xs≡ysy) = Vec.initLast xs in Distinct ys × y ∉ ys
initLast {n = zero} {xs = x ∷ []} (.x distinct-∷ distinct-[] by x∉[]) = distinct-[] , x∉[]
initLast {n = suc n} {xs = x ∷ xs} (.x distinct-∷ dxs by x∉xs) with Vec.initLast xs | initLast dxs
initLast {_} {suc n} {_} {x ∷ .(ys Vec.∷ʳ y)} (.x distinct-∷ dxs by x∉xs) | ys , y , P.refl | dys , y∉ys =
             x distinct-∷ dys by (x∉xs ∘ ∈-∷ʳ) , λ { (here P.refl) → x∉xs (∷ʳ-∈ y ys) 
                                                  ; ( there p) → y∉ys p }
         where
           ∈-∷ʳ : ∀ {a n} {A : Set a}{xs : Vec A n}{x y} → x ∈ xs → x ∈ xs Vec.∷ʳ y
           ∈-∷ʳ {xs = []} ()
           ∈-∷ʳ {xs = x ∷ xs} (here eq) = here eq
           ∈-∷ʳ {xs = x ∷ xs} (there x∈xs) = there (∈-∷ʳ x∈xs)
           ∷ʳ-∈ : ∀ {a n} {A : Set a} x (xs : Vec A n) → x ∈ xs Vec.∷ʳ x
           ∷ʳ-∈ x [] = here P.refl
           ∷ʳ-∈ x (y ∷ xs) = there (∷ʳ-∈ x xs)

private
  initLast₁≡init  : ∀ {a n} {A : Set a}(xs : Vec A (suc n)) → proj₁ (Vec.initLast xs) ≡ Vec.init xs
  initLast₁≡init xs with Vec.initLast xs
  initLast₁≡init .(ys Vec.∷ʳ y) | ys , y , P.refl = P.refl

  initLast₂≡last  : ∀ {a n} {A : Set a}(xs : Vec A (suc n)) → proj₁ (proj₂ (Vec.initLast xs)) ≡ Vec.last xs
  initLast₂≡last xs with Vec.initLast xs
  initLast₂≡last .(ys Vec.∷ʳ y) | ys , y , P.refl = P.refl

init : ∀ {a n} {A : Set a}{xs : Vec A (suc n)} → Distinct xs → Distinct (Vec.init xs)
init {xs = xs} dxs with initLast dxs 
... | dys , y∉ys rewrite initLast₁≡init xs = dys


last : ∀ {a n} {A : Set a}{xs : Vec A (suc n)} → Distinct xs → Vec.last xs ∉ Vec.init xs
last {xs = xs} dxs with initLast dxs
... | dys , y∉ys rewrite initLast₁≡init xs | initLast₂≡last xs = y∉ys

map : ∀ {a b}{A : Set a}{B : Set b} → (f : A ↣ B) → ∀ {n}{xs : Vec A n} → Distinct xs → Distinct (Vec.map (Injection.to f ⟨$⟩_) xs)          
map f {0}{[]} distinct-[] = distinct-[]
map {A = A} f {ℕ.suc _} {x ∷ xs} (.x distinct-∷ dis by x∉xs) = fx distinct-∷ map f dis by fx∉mapfxs
    where

      fx = Injection.to f ⟨$⟩ x
      -- missing
      ∈-map⁻ : ∀{a b}{A : Set a}{B : Set b}(f : A → B){m}{xs : Vec A m}{y} →
        y ∈ Vec.map f xs → ∃ λ x → x ∈ xs × y ≡ f x
      ∈-map⁻ f {xs = []} ()
      ∈-map⁻ f {xs = x ∷ xs} (here P.refl) = x , here P.refl , P.refl
      ∈-map⁻ f {xs = x ∷ xs} (there y∈mapfxs) with ∈-map⁻ _ y∈mapfxs
      ... | v , v∈xs , eq = v , there v∈xs , eq

      fx∉mapfxs : fx ∉ Vec.map (Injection.to f ⟨$⟩_) xs  
      fx∉mapfxs fx∈mapfxs with ∈-map⁻ _ fx∈mapfxs
      ... | v , v∈xs , fx≡fv with Injection.injective f fx≡fv
      fx∉mapfxs fx∈mapfxs | v , v∈xs , fx≡fv | P.refl = x∉xs v∈xs

private
  injection : ∀ {a b}{A : Set a}{B : Set b} {f : A → B} → (∀ {x y} → f x ≡ f y → x ≡ y) → A ↣ B
  Injection.to (injection {f = f} inj) = P.→-to-⟶ f
  Injection.injective (injection inj) = inj

tabulate : ∀ {a}{A : Set a}{n} → (f : Fin n ↣ A) → Distinct (Vec.tabulate (Injection.to f ⟨$⟩_))
tabulate {n = zero} f = distinct-[]
tabulate {n = suc n} f = (Injection.to f ⟨$⟩ zero) distinct-∷ tabulate (f ⟨∘⟩ injection suc-injective) by lemma
  where
    open import Function.Injection using () renaming (_∘_ to _⟨∘⟩_)
    open import Data.Vec.Membership.Propositional.Properties
    ∈-tabulateˡ : ∀ {a}{A : Set a}{n}{x}(f : Fin n → A) → x ∈ Vec.tabulate f →
      ∃ λ i → x ≡ f i
    ∈-tabulateˡ {n = zero} f ()
    ∈-tabulateˡ {n = suc n} f (here P.refl) = _ , P.refl
    ∈-tabulateˡ {n = suc n} f (there x∈tabf) with ∈-tabulateˡ _ x∈tabf
    ... | i , eq = suc i , eq
    
    lemma : (Injection.to f ⟨$⟩ zero) ∉ Vec.tabulate ((Injection.to f ⟨$⟩_) ∘ Fin.suc)
    lemma p with ∈-tabulateˡ _ p
    lemma p | i , fi≡f0 with Injection.injective f fi≡f0
    lemma p | i , fi≡f0 | ()
    
allFin : ∀ n → Distinct (Vec.allFin n)
allFin n = tabulate ⟨id⟩
  where
    open import Function.Injection using () renaming (id to ⟨id⟩)

private
  ∈-zipˡ : ∀ {a b n}{A : Set a}{B : Set b}{xs : Vec A n}{ys : Vec B n} {x y} →
    (x , y) ∈ Vec.zip xs ys → x ∈ xs  
  ∈-zipˡ {xs = []} {[]} ()
  ∈-zipˡ {xs = x ∷ xs} {y ∷ ys} (here P.refl) = here P.refl
  ∈-zipˡ {xs = x ∷ xs} {y ∷ ys} (there p) = there (∈-zipˡ p)   
    
  ∈-zipʳ : ∀ {a b n}{A : Set a}{B : Set b}{xs : Vec A n}{ys : Vec B n} {x y} →
    (x , y) ∈ Vec.zip xs ys → y ∈ ys  
  ∈-zipʳ {xs = []} {[]} ()
  ∈-zipʳ {xs = x ∷ xs} {y ∷ ys} (here P.refl) = here P.refl
  ∈-zipʳ {xs = x ∷ xs} {y ∷ ys} (there p) = there (∈-zipʳ p)   
    
zipˡ : ∀ {a b n}{A : Set a}{B : Set b}{xs : Vec A n} → 
     Distinct xs → (ys : Vec B n) → Distinct (Vec.zip xs ys)
zipˡ distinct-[] [] = distinct-[]
zipˡ (x distinct-∷ dxs by x∉xs) (y ∷ ys) = (x , y) distinct-∷ zipˡ dxs ys
  by λ p → x∉xs (∈-zipˡ p)

zipʳ : ∀ {a b n}{A : Set a}{B : Set b}(xs : Vec A n){ys : Vec B n} →
  Distinct ys → Distinct (Vec.zip xs ys)
zipʳ [] distinct-[] = distinct-[]
zipʳ (x ∷ xs) (y distinct-∷ dys by y∉ys) = (x , y) distinct-∷ zipʳ xs dys
  by λ p → y∉ys (∈-zipʳ p)

toList : ∀ {a n}{A : Set a}{xs : Vec A n} → Distinct xs → ListDistinct.Distinct (Vec.toList xs)
toList distinct-[] = ListDistinct.distinct-[]
toList (x distinct-∷ dxs by x∉xs) = x ListDistinct.distinct-∷ toList dxs
  by λ x∈xs → x∉xs (lemma x∈xs) 
  where
    import Data.List.Membership.Propositional as ListMem
    import Data.List.Any as ListAny
    lemma : ∀ {a n}{A : Set a}{x}{xs : Vec A n} → x ListMem.∈ Vec.toList xs → x ∈ xs
    lemma {xs = []} ()
    lemma {xs = x ∷ xs} (ListAny.here P.refl) = here P.refl
    lemma {xs = x ∷ xs} (ListAny.there p) = there (lemma p)

fromList : ∀ {a}{A : Set a}{xs : List A} → ListDistinct.Distinct xs → Distinct (Vec.fromList xs)
fromList ListDistinct.distinct-[] = distinct-[]
fromList (x ListDistinct.distinct-∷ dxs by x∉xs) =
  x distinct-∷ fromList dxs by λ x∈xs → x∉xs (lemma x∈xs)
    where
      import Data.List.Membership.Propositional as ListMem
      import Data.List.Any as ListAny
      lemma : ∀ {a}{A : Set a}{x}{xs : List A} → x ∈ Vec.fromList xs → 
        x ListMem.∈ xs
      lemma {xs = List.[]} ()
      lemma {xs = x List.∷ xs} (here P.refl) = ListAny.here P.refl
      lemma {xs = x List.∷ xs} (there p) = ListAny.there (lemma p)

        
