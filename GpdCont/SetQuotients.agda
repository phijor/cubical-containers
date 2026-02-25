module GpdCont.SetQuotients where

open import GpdCont.Prelude
open import GpdCont.Prelude.Path

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Relation.Binary.Base
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma

open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_] ; eq/)
open import Cubical.HITs.GroupoidQuotients as GQ using (_//_ ; [_])
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B : Type ℓ
    R S : A → A → Type ℓ'

open Iso

map : (f : A → B) (pres : ∀ {a a'} → R a a' → S (f a) (f a')) → A / R → B / S
map f pres = SQ.rec SQ.squash/ ([_] ∘ f) λ a a' p → eq/ _ _ (pres p)

module _
  (isoA : Iso A B)
  (presS : ∀ {a a'} → R a a' → S (isoA .fun a) (isoA .fun a'))
  (presR : ∀ {b b'} → S b b' → R (isoA .inv b) (isoA .inv b'))
  where
  relBiimpl→QuotIso : Iso (A / R) (B / S)
  relBiimpl→QuotIso .fun = map (isoA .fun) presS
  relBiimpl→QuotIso .inv = map (isoA .inv) presR
  relBiimpl→QuotIso .sec = SQ.elimProp (λ _ → _/_.squash/ _ _) λ a → cong [_] (isoA .sec a)
  relBiimpl→QuotIso .ret = SQ.elimProp (λ _ → _/_.squash/ _ _) λ b → cong [_] (isoA .ret b)

  relBiimpl→QuotEquiv : (A / R) ≃ (B / S)
  relBiimpl→QuotEquiv = isoToEquiv relBiimpl→QuotIso

module _
  {A : Type ℓ}
  {R S : A → A → Type ℓ'}
  (presS : ∀ {a a'} → R a a' → S a a')
  (presR : ∀ {a a'} → S a a' → R a a')
  where
  relBiimpl→QuotIdIso : Iso (A / R) (A / S)
  relBiimpl→QuotIdIso = relBiimpl→QuotIso idIso presS presR

  relBiimpl→QuotIdEquiv : (A / R) ≃ (A / S)
  relBiimpl→QuotIdEquiv = relBiimpl→QuotEquiv idIso presS presR

relIso→QuotIdIso : {R S : A → A → Type ℓ'} → (∀ {a a'} → Iso (R a a') (S a a')) → Iso (A / R) (A / S)
relIso→QuotIdIso rel-iso = relBiimpl→QuotIdIso (rel-iso .fun) (rel-iso .inv)

relEquiv→QuotIdEquiv : {R S : A → A → Type ℓ'} → (∀ {a a'} → (R a a') ≃ (S a a')) → (A / R) ≃ (A / S)
relEquiv→QuotIdEquiv rel-equiv = isoToEquiv (relIso→QuotIdIso (equivToIso rel-equiv))

pullbackRel : (f : A → B) (S : B → B → Type ℓ') → (A → A → Type ℓ')
pullbackRel f S = λ a a′ → S (f a) (f a′)

pullbackQuotIso : (i : Iso A B) → Iso (A / R) (B / pullbackRel (i .inv) R)
pullbackQuotIso {R} i = relBiimpl→QuotIso i ret-rel (id $ R (g _) (g _)) where
  open module i = Iso i renaming (fun to f ; inv to g) using ()
  ret-rel : ∀ {a a'} → R a a' → R (g (f a)) (g (f a'))
  ret-rel {a} {a'} = subst2 R (sym (i.ret a)) (sym (i.ret a'))

pullbackQuotEquiv : (e : A ≃ B) → (A / R) ≃ (B / pullbackRel (invEq e) R)
pullbackQuotEquiv e = isoToEquiv (pullbackQuotIso (equivToIso e))

SetTruncSetQuotientPathIso : Iso ∥ A ∥₂ (A / _≡_)
SetTruncSetQuotientPathIso .Iso.fun = ST.rec SQ.squash/ SQ.[_]
SetTruncSetQuotientPathIso .Iso.inv = SQ.rec ST.isSetSetTrunc ∣_∣₂ λ a b → cong ∣_∣₂
SetTruncSetQuotientPathIso .Iso.sec = SQ.elimProp (λ x → SQ.squash/ _ x) λ _ → refl
SetTruncSetQuotientPathIso .Iso.ret = ST.elim (λ _ → isProp→isSet (ST.isSetSetTrunc _ _)) λ _ → refl

SetTrunc→SetQuotientPath : ∥ A ∥₂ → (A / _≡_)
SetTrunc→SetQuotientPath = ST.rec SQ.squash/ SQ.[_]

SetTrunc≃SetQuotientPath : ∥ A ∥₂ ≃ (A / _≡_)
SetTrunc≃SetQuotientPath = isoToEquiv SetTruncSetQuotientPathIso
-- SetTrunc≃SetQuotientPath : ∥ A ∥₂ ≃ (A / _≡_)
-- SetTrunc≃SetQuotientPath .fst = SetTrunc→SetQuotientPath
-- SetTrunc≃SetQuotientPath {A} .snd .equiv-proof = SQ.elimProp (λ _ → isPropIsContr) goal where
--   lemma : ∀ a (x y : ∥ A ∥₂) (p : SetTrunc→SetQuotientPath x ≡ SQ.[ a ]) (q : SetTrunc→SetQuotientPath y ≡ SQ.[ a ]) → Path (fiber SetTrunc→SetQuotientPath SQ.[ a ]) (x , p) (y , q)
--   lemma a = ST.elim2 (λ x y → isSetΠ2 λ p q → isProp→isSet (isSetΣSndProp ST.isSetSetTrunc (λ x → SQ.squash/ _ _) (x , p) (y , q)))
--     λ (b b′ : A) (p : SQ.[ b ] ≡ SQ.[ a ]) (q : SQ.[ b′ ] ≡ SQ.[ a ]) → ΣPathP ({! !} , {! !})

--   is-prop-fiber : ∀ a → isProp (fiber SetTrunc→SetQuotientPath SQ.[ a ])
--   is-prop-fiber a (x , p) (y , q) = lemma a x y p q
--   goal : ∀ a → isContr (fiber SetTrunc→SetQuotientPath SQ.[ a ])
--   goal a = inhProp→isContr
--     (∣ a ∣₂ , refl)
--     (is-prop-fiber a)

mapGroupoidQuotient : (Rt : BinaryRelation.isTrans R) → A / R → A // Rt
mapGroupoidQuotient {A} {R} Rt = SQ.rec→Gpd.fun GQ.squash// [_] (λ a b → GQ.eq// {a = a} {b = b}) constant where
  constant : ∀ a b → isProp (GQ.[ a ] ≡ GQ.[ b ])
  constant = {! !}

rec→Gpd' : isGroupoid B
  → (Rt : BinaryRelation.isTrans R)
  → (f : A → B)
  → (f[_] : ∀ {a a′} → R a a′ → f a ≡ f a′)
  → (r-∙ : ∀ {a₀ a₁ a₂} → (r : R a₀ a₁) → (s : R a₁ a₂) → f[ Rt _ _ _ r s  ] ≡ f[ r ] ∙ f[ s ])
  → (f[-]-const : ∀ {a a′} → (r s : R a a′) → f[ r ] ≡ f[ s ])
  → A / R → B
rec→Gpd' {B} {A} {R} is-groupoid-B Rt f f[_] r-∙ f[-]-const = SQ.rec→Gpd.fun is-groupoid-B f (λ _ _ → f[_]) is-prop-f-path where
  is-prop-f-path : (a a′ : A) → (p q : f a ≡ f a′) → p ≡ q
  is-prop-f-path = {!  !}
  -- from-trunc ∘ to-trunc where
  -- open import Cubical.HITs.TypeQuotients as TQ using (_/ₜ_)
  
  -- to-trunc : A / R → ∥ A /ₜ R ∥₂
  -- to-trunc = SQ.typeQuotSetTruncIso .fun

  -- f/ₜ : A /ₜ R → B
  -- f/ₜ = TQ.rec f λ _ _ → f[_]

  -- coh : (x y : A /ₜ R) → (p q : x ≡ y) → cong f/ₜ p ≡ cong f/ₜ q
  -- coh = TQ.elimProp2 (λ x y → isPropΠ2 λ p q → is-groupoid-B _ _ (cong f/ₜ p) (cong f/ₜ q)) {! !}

  -- from-trunc : ∥ A TQ./ₜ R ∥₂ → B
  -- from-trunc = ST.rec→Gpd.fun is-groupoid-B f/ₜ coh

record Definable (A : Type ℓ) (_∼_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  field
    emb : (A / _∼_) → A
    complete : (a : A) → emb [ a ] ≡ a
    stable : (x : A / _∼_) → [ emb x ] ≡ x

  sound : ∀ a b → a ∼ b → [ a ] ≡ [ b ]
  sound = SQ.eq/

  exact : BinaryRelation.isPropValued _∼_
    → BinaryRelation.isEquivRel _∼_
    → ∀ a b → Path (A / _∼_) [ a ] [ b ] → a ∼ b
  exact = SQ.effective

module _ {ℓB ℓS}
  (is-effective-R : BinaryRelation.isEffective R)
  (B : A / R → Type ℓB)
  (S : (x : A / R) → B x → B x → Type ℓS)
  (is-effective-S : ∀ x → BinaryRelation.isEffective (S x))
  where
  private
    refl-R : ∀ a → R a a
    refl-R a = invEq (_ , is-effective-R a a) refl

    opaque
      refl-Rᴰ : ∀ a b → PathP (λ i → B (eq/ a a (refl-R a) i)) b b
      refl-Rᴰ a b = toPathP $
        subst B (eq/ a a (refl-R a)) b
          ≡⟨ cong (λ - → subst B - b) (secIsEq (is-effective-R a a) refl) ⟩
        subst B refl b
          ≡⟨ substRefl {B = B} b ⟩
        b
          ∎

  setQuotientΣIso : Iso
      (Σ[ x ∈ A / R ] (B x / S x))
      ((Σ[ a ∈ A ] B [ a ]) / λ { (a₀ , b₀) (a₁ , b₁) → Σ[ r ∈ R a₀ a₁ ] Σ[ (b , _) ∈ singlP (λ i → B (eq/ a₀ a₁ r i)) b₀ ] S [ a₁ ] b b₁ })
  setQuotientΣIso = go where
    go : Iso _ _
    go .fun = uncurry $ SQ.elim (λ x → isSet→ SQ.squash/) fun* wd*
      where
        fun* : (a : A) (y : B [ a ] / S [ a ]) → (Σ[ a ∈ A ] B [ a ]) / _
        fun* a = SQ.rec SQ.squash/ (λ b → [ a , b ]) λ where
          b₀ b₁ s → eq/ (a , b₀) (a , b₁) (refl-R a , (b₀ , refl-Rᴰ a b₀) , s)

        wd* : ∀ a₀ a₁ → (r : R a₀ a₁) → PathP (λ i → B (eq/ _ _ r i) / S (eq/ _ _ r i) → (Σ[ a ∈ A ] B [ a ]) / _) (fun* a₀) (fun* a₁)
        wd* a₀ a₁ r = funExtNonDep λ {x₀} {x₁} → SQ.elimProp2
          {P = λ x₀ x₁ → PathP (λ i → B (eq/ a₀ a₁ r i) / S (eq/ a₀ a₁ r i)) x₀ x₁ → fun* a₀ x₀ ≡ fun* a₁ x₁}
          (λ x₀ x₁ → isPropΠ λ p → SQ.squash/ _ _)
          (λ b₀ b₁ pᴰ → eq/ (a₀ , b₀) (a₁ , b₁) (r , (subst B (eq/ _ _ r) b₀ , subst-filler B _ b₀) , invEq (_ , is-effective-S _ _ _) (fromPathP pᴰ)))
          x₀ x₁
    go .inv = SQ.rec (isSetΣ SQ.squash/ λ x → SQ.squash/) (λ (a , b) → [ a ] , [ b ]) λ where
      (a₀ , b₀) (a₁ , b₁) (r , (b , eq) , s) → ΣPathP λ where
        .fst → eq/ a₀ a₁ r
        .snd → toPathP (eq/ (transport (λ i → B (eq/ a₀ a₁ r i)) b₀) b₁ $ subst (λ - → S [ a₁ ] - b₁) (sym (fromPathP eq)) s)
    go .sec = SQ.elimProp (λ _ → SQ.squash/ _ _) λ _ → refl
    go .ret = uncurry (SQ.elimProp (λ _ → isPropΠ λ _ → isSetΣ SQ.squash/ (λ _ → SQ.squash/) _ _) λ a → SQ.elimProp (λ _ → isSetΣ SQ.squash/ (λ _ → SQ.squash/) _ _) λ _ → refl)

  setQuotientΣ≃ :
    (Σ[ x ∈ A / R ] (B x / S x))
      ≃
    ((Σ[ a ∈ A ] B [ a ]) / λ { (a₀ , b₀) (a₁ , b₁) → Σ[ r ∈ R a₀ a₁ ] Σ[ (b , _) ∈ singlP (λ i → B (eq/ a₀ a₁ r i)) b₀ ] S [ a₁ ] b b₁ })
  setQuotientΣ≃ = isoToEquiv setQuotientΣIso

module _ {ℓA ℓB ℓS}
  {A : Type ℓA}
  (is-set-A : isSet A)
  (B : A → Type ℓB)
  (S : ∀ a → B a → B a → Type ℓS)
  where
  private
    is-set-ΣAB/S : isSet (Σ[ a ∈ A ] (B a / S a))
    is-set-ΣAB/S = isSetΣ is-set-A (λ _ → SQ.squash/)

  setQuotientΣSndIso : Iso
    (Σ[ a ∈ A ] (B a / S a))
    ((Σ[ a ∈ A ] B a) / λ { (a₀ , b₀) (a₁ , b₁) → Σ[ p ∈ a₀ ≡ a₁ ] Σ[ (b , _) ∈ singlP (λ i → B (p i)) b₀ ] S a₁ b b₁ })
  setQuotientΣSndIso .fun = uncurry λ a → map (a ,_) λ s → refl , (_ , refl) , s
  setQuotientΣSndIso .inv = SQ.rec is-set-ΣAB/S (map-snd [_]) λ where
    (a₀ , b₀) (a₁ , b₁) r → ΣPathP λ where
      .fst → r .fst
      .snd → toPathP $ eq/ _ _ $ subst (λ - → S a₁ - b₁) (sym (fromPathP (r .snd .fst .snd))) (r .snd .snd)
  setQuotientΣSndIso .sec = SQ.elimProp (λ _ → SQ.squash/ _ _) λ _ → refl
  setQuotientΣSndIso .ret = uncurry λ a → SQ.elimProp (λ _ → is-set-ΣAB/S _ _) λ _ → refl

  setQuotientΣSnd≃ :
    (Σ[ a ∈ A ] (B a / S a))
      ≃
    ((Σ[ a ∈ A ] B a) / λ { (a₀ , b₀) (a₁ , b₁) → Σ[ p ∈ a₀ ≡ a₁ ] Σ[ (b , _) ∈ singlP (λ i → B (p i)) b₀ ] S a₁ b b₁ })
  setQuotientΣSnd≃ = isoToEquiv setQuotientΣSndIso

module _ {ℓA ℓR ℓS}
  {A : Type ℓA}
  (R : A → A → Type ℓR)
  (S : A / R → A / R → Type ℓS)
  (is-sub-rel : ∀ {a b} → R a b → S [ a ] [ b ])
  where

  setQuotientMergeIso : Iso ((A / R) / S) (A / λ a b → S [ a ] [ b ])
  setQuotientMergeIso .fun = SQ.rec SQ.squash/
    (SQ.elim (λ _ → SQ.squash/) [_] λ a b r → eq/ a b (is-sub-rel r))
    (SQ.elimProp2 (λ _ _ → isPropΠ λ _ → SQ.squash/ _ _) λ a b s → eq/ a b s)
  setQuotientMergeIso .inv = SQ.rec SQ.squash/ (λ a → [ [ a ] ]) λ a b s → eq/ [ a ] [ b ] s
  setQuotientMergeIso .sec = SQ.elimProp (λ _ → SQ.squash/ _ _) λ a → refl′ [ a ]
  setQuotientMergeIso .ret = SQ.elimProp (λ _ → SQ.squash/ _ _) (SQ.elimProp (λ _ → SQ.squash/ _ _) λ a → refl′ [ [ a ] ])

  setQuotientMerge≃ : ((A / R) / S) ≃ (A / λ a b → S [ a ] [ b ])
  setQuotientMerge≃ = isoToEquiv setQuotientMergeIso
