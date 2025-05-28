open import GpdCont.Prelude hiding (_⋆_)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base

module GpdCont.Categories.Fiber
  {ℓo ℓh ℓoᴰ ℓhᴰ}
  (C : Category ℓo ℓh)
  (Cᴰ : Categoryᴰ C ℓoᴰ ℓhᴰ)
  where

  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Isomorphism hiding (isIso)
  open import Cubical.Foundations.Transport using (substEquiv)
  open import Cubical.Data.Sigma
  open import Cubical.Categories.Constructions.TotalCategory renaming (∫C to ∫)

  import Cubical.Categories.Displayed.Reasoning Cᴰ as Reasoning

  private
    open module C = Category C using (_⋆_)
    open module Cᴰ = Categoryᴰ Cᴰ using (_⋆ᴰ_)

  module _ (c : C.ob) where
    FiberCategory : Category ℓoᴰ ℓhᴰ
    FiberCategory .Category.ob = Cᴰ.ob[ c ]
    FiberCategory .Category.Hom[_,_] = Cᴰ.Hom[ C.id {c} ][_,_]
    FiberCategory .Category.id = Cᴰ.idᴰ
    FiberCategory .Category._⋆_ {x = xᴰ} {y = yᴰ} {z = zᴰ} fᴰ gᴰ = Reasoning.reind id-comp (fᴰ ⋆ᴰ gᴰ) where
      id-comp : C.id C.⋆ C.id ≡ C.id
      id-comp = C.⋆IdL C.id
    FiberCategory .Category.⋆IdL fᴰ = Reasoning.rectify $ Reasoning.≡out $
      (C.id , Reasoning.reind (C.⋆IdL C.id) (Cᴰ.idᴰ ⋆ᴰ fᴰ)) ≡⟨ sym (Reasoning.reind-filler (C.⋆IdL C.id) (Cᴰ.idᴰ ⋆ᴰ fᴰ)) ⟩
      (C.id ⋆ C.id , (Cᴰ.idᴰ ⋆ᴰ fᴰ)) ≡[ i ]⟨ C.⋆IdL C.id i , Cᴰ.⋆IdLᴰ fᴰ i ⟩
      (C.id , fᴰ) ∎
    FiberCategory .Category.⋆IdR fᴰ = Reasoning.rectify $ Reasoning.≡out $
      (C.id , Reasoning.reind (C.⋆IdL C.id) (fᴰ ⋆ᴰ Cᴰ.idᴰ)) ≡⟨ sym (Reasoning.reind-filler (C.⋆IdL C.id) (fᴰ ⋆ᴰ Cᴰ.idᴰ)) ⟩
      (C.id ⋆ C.id , (fᴰ ⋆ᴰ Cᴰ.idᴰ)) ≡[ i ]⟨ C.⋆IdR C.id i , Cᴰ.⋆IdRᴰ fᴰ i ⟩
      (C.id , fᴰ) ∎
    FiberCategory .Category.⋆Assoc = {! !}
    FiberCategory .Category.isSetHom = Cᴰ.isSetHomᴰ

  opaque
    isPropIsIsoᴰ : ∀ {x y : C.ob} {f : C.Hom[ x , y ]}
      → (is-iso-f : isIso C f)
      → {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
      → isProp (isIsoᴰ Cᴰ is-iso-f fᴰ)
    isPropIsIsoᴰ {x} {y} {f} is-iso-f {xᴰ} {yᴰ} fᴰ p q = goal where
      module f = isIso is-iso-f

      module p = isIsoᴰ p
      module q = isIsoᴰ q

      ∫inv-path : Path (Σ[ g ∈ C.Hom[ y , x ] ] Cᴰ.Hom[ g ][ yᴰ , xᴰ ]) (f.inv , p.invᴰ) (f.inv , q.invᴰ)
      ∫inv-path =
        (f.inv , p.invᴰ) ≡[ i ]⟨ C.⋆IdL f.inv (~ i) , Cᴰ.⋆IdLᴰ p.invᴰ (~ i) ⟩
        (C.id ⋆ f.inv , Cᴰ.idᴰ ⋆ᴰ p.invᴰ) ≡[ i ]⟨ (f.sec (~ i) ⋆ f.inv) , (q.secᴰ (~ i) ⋆ᴰ p.invᴰ) ⟩
        ((f.inv ⋆ f) ⋆ f.inv , (q.invᴰ ⋆ᴰ fᴰ) ⋆ᴰ p.invᴰ) ≡[ i ]⟨ C.⋆Assoc f.inv f f.inv i , Cᴰ.⋆Assocᴰ q.invᴰ fᴰ p.invᴰ i ⟩
        (f.inv ⋆ (f ⋆ f.inv) , q.invᴰ ⋆ᴰ (fᴰ ⋆ᴰ p.invᴰ)) ≡[ i ]⟨ (f.inv ⋆ f.ret i) , (q.invᴰ ⋆ᴰ p.retᴰ i) ⟩
        (f.inv ⋆ C.id , q.invᴰ ⋆ᴰ Cᴰ.idᴰ) ≡[ i ]⟨ C.⋆IdR f.inv i , Cᴰ.⋆IdRᴰ q.invᴰ i ⟩
        (f.inv , q.invᴰ) ∎

      inv-path : p.invᴰ ≡ q.invᴰ
      inv-path = Reasoning.rectify $ Reasoning.≡out ∫inv-path

      goal : p ≡ q
      goal i .isIsoᴰ.invᴰ = inv-path i
      goal i .isIsoᴰ.secᴰ j = isSet→SquareP (λ i j → Cᴰ.isSetHomᴰ) p.secᴰ q.secᴰ (cong (_⋆ᴰ fᴰ) inv-path) refl i j
      goal i .isIsoᴰ.retᴰ j = isSet→SquareP (λ i j → Cᴰ.isSetHomᴰ) p.retᴰ q.retᴰ (cong (fᴰ ⋆ᴰ_) inv-path) refl i j

  module _ (c : C.ob) (xᴰ yᴰ : Cᴰ.ob[ c ]) where
    isIsoFiberCat≃isIsoᴰId : (fᴰ : Cᴰ.Hom[ C.id ][ xᴰ , yᴰ ]) → isIso (FiberCategory c) fᴰ ≃ isIsoᴰ Cᴰ (idCatIso .snd) fᴰ
    isIsoFiberCat≃isIsoᴰId fᴰ = propBiimpl→Equiv (isPropIsIso fᴰ) (isPropIsIsoᴰ (idCatIso .snd) fᴰ)
      (λ { (isiso inv sec ret) → isisoᴰ inv (toPathP sec) (toPathP ret) })
      (λ { (isisoᴰ invᴰ secᴰ retᴰ) → isiso invᴰ (fromPathP secᴰ) (fromPathP retᴰ) })

    FiberCatIso≃CatIsoᴰId : CatIso (FiberCategory c) xᴰ yᴰ ≃ CatIsoᴰ Cᴰ idCatIso xᴰ yᴰ
    FiberCatIso≃CatIsoᴰId = Σ-cong-equiv-snd isIsoFiberCat≃isIsoᴰId

  ΣIsoᴰ≃TotalCatIso : (x y : C.ob) (xᴰ : Cᴰ.ob[ x ]) (yᴰ : Cᴰ.ob[ y ])
    → (Σ[ f ∈ CatIso C x y ] CatIsoᴰ Cᴰ f xᴰ yᴰ) ≃ CatIso (∫ Cᴰ) (x , xᴰ) (y , yᴰ)
  ΣIsoᴰ≃TotalCatIso x y xᴰ yᴰ = strictEquiv ΣIsoᴰ→TotalCatIso TotalCatIso→ΣIsoᴰ where
    ΣIsoᴰ→TotalCatIso : _ → _
    ΣIsoᴰ→TotalCatIso ((f , isiso g sec ret) , fᴰ , isisoᴰ gᴰ secᴰ retᴰ) .fst = (f , fᴰ)
    ΣIsoᴰ→TotalCatIso ((f , isiso g sec ret) , fᴰ , isisoᴰ gᴰ secᴰ retᴰ) .snd = isiso (g , gᴰ) (ΣPathP (sec , secᴰ)) (ΣPathP (ret , retᴰ))

    TotalCatIso→ΣIsoᴰ : _ → _
    TotalCatIso→ΣIsoᴰ ((f , fᴰ) , isiso (g , gᴰ) Σsec Σret) .fst = (f , isiso g (cong fst Σsec) (cong fst Σret))
    TotalCatIso→ΣIsoᴰ ((f , fᴰ) , isiso (g , gᴰ) Σsec Σret) .snd = (fᴰ , isisoᴰ gᴰ (cong snd Σsec) (cong snd Σret))

  isUnivalentFiber→isUnivalentTotalCategory : isUnivalent C → (∀ c → isUnivalent (FiberCategory c)) → isUnivalent (∫ {C = C} Cᴰ)
  isUnivalentFiber→isUnivalentTotalCategory univ-C univ-fiber-C .isUnivalent.univ (x , xᴰ) (y , yᴰ) = {! univ x y xᴰ yᴰ !} where
    module _ (x y : C.ob) where
      univ-equivᴰ : (p : x ≡ y)
        → (xᴰ : Cᴰ.ob[ x ])
        → (yᴰ : Cᴰ.ob[ y ])
        → PathP (λ i → Cᴰ.ob[ p i ]) xᴰ yᴰ ≃ CatIsoᴰ Cᴰ (pathToIso p) xᴰ yᴰ
      univ-equivᴰ = J (λ y p → ∀ xᴰ yᴰ → PathP (λ i → Cᴰ.ob[ p i ]) xᴰ yᴰ ≃ CatIsoᴰ Cᴰ (pathToIso p) xᴰ yᴰ) univ-equivᴰ-id where
        univ-equivᴰ-id : ∀ (xᴰ yᴰ : Cᴰ.ob[ x ]) → (xᴰ ≡ yᴰ) ≃ CatIsoᴰ Cᴰ (pathToIso refl) xᴰ yᴰ
        univ-equivᴰ-id xᴰ yᴰ =
          (xᴰ ≡ yᴰ) ≃⟨ isUnivalent.univEquiv (univ-fiber-C x) xᴰ yᴰ ⟩
          CatIso (FiberCategory x) xᴰ yᴰ ≃⟨ FiberCatIso≃CatIsoᴰId x xᴰ yᴰ ⟩
          CatIsoᴰ Cᴰ idCatIso xᴰ yᴰ ≃⟨ substEquiv (λ f → CatIsoᴰ Cᴰ f xᴰ yᴰ) $ sym pathToIso-refl ⟩
          CatIsoᴰ Cᴰ (pathToIso refl) xᴰ yᴰ ≃∎

      univ-equiv : (xᴰ : Cᴰ.ob[ x ]) (yᴰ : Cᴰ.ob[ y ]) → Path (Σ C.ob Cᴰ.ob[_]) (x , xᴰ) (y , yᴰ) ≃ CatIso (∫ Cᴰ) (x , xᴰ) (y , yᴰ)
      univ-equiv xᴰ yᴰ =
        Path (Σ C.ob Cᴰ.ob[_]) (x , xᴰ) (y , yᴰ) ≃⟨ invEquiv ΣPathP≃PathPΣ ⟩
        (Σ[ p ∈ x ≡ y ] PathP (λ i → Cᴰ.ob[ p i ]) xᴰ yᴰ) ≃⟨ Σ-cong-equiv (isUnivalent.univEquiv univ-C x y) (λ p → univ-equivᴰ p xᴰ yᴰ) ⟩
        (Σ[ f ∈ CatIso C x y ] CatIsoᴰ Cᴰ f xᴰ yᴰ) ≃⟨ ΣIsoᴰ≃TotalCatIso x y xᴰ yᴰ ⟩
        CatIso (∫ Cᴰ) (x , xᴰ) (y , yᴰ) ≃∎

    module _ (x y : C.ob) where
      univ≡pathToIso-ext :
        ∀ (p : x ≡ y)
        → (xᴰ : Cᴰ.ob[ x ]) (yᴰ : Cᴰ.ob[ y ])
        → (pᴰ : PathP (λ i → Cᴰ.ob[ p i ]) xᴰ yᴰ) → equivFun (univ-equiv x y xᴰ yᴰ) (ΣPathP (p , pᴰ)) ≡ pathToIso (ΣPathP (p , pᴰ))
      univ≡pathToIso-ext = J
        (λ y p → (xᴰ : Cᴰ.ob[ x ]) (yᴰ : Cᴰ.ob[ y ]) → (pᴰ : PathP (λ i → Cᴰ.ob[ p i ]) xᴰ yᴰ) → equivFun (univ-equiv x y xᴰ yᴰ) (ΣPathP (p , pᴰ)) ≡ pathToIso (ΣPathP (p , pᴰ)))
        (λ xᴰ yᴰ → J (λ yᴰ pᴰ → equivFun (univ-equiv x x xᴰ yᴰ) (ΣPathP (refl , pᴰ)) ≡ pathToIso (ΣPathP (refl , pᴰ))) {! !})

      univ≡pathToIso : (xᴰ : Cᴰ.ob[ x ]) (yᴰ : Cᴰ.ob[ y ]) → equivFun (univ-equiv x y xᴰ yᴰ) ≡ pathToIso
      univ≡pathToIso xᴰ yᴰ = funExt {! !} -- (λ p* → goal (cong fst p*) (cong snd p*)) where

      univ : (xᴰ : Cᴰ.ob[ x ]) (yᴰ : Cᴰ.ob[ y ]) → isEquiv (pathToIso {C = ∫ Cᴰ} {x = x , xᴰ} {y = y , yᴰ})
      univ xᴰ yᴰ = subst isEquiv (univ≡pathToIso xᴰ yᴰ) (equivIsEquiv (univ-equiv x y xᴰ yᴰ))
