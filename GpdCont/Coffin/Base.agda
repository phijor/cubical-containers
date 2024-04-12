module GpdCont.Coffin.Base where

open import GpdCont.Prelude
open import GpdCont.Groups.Base
open import GpdCont.GroupAction
open import GpdCont.Skeleton using (Skeleton)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels using (isGroupoidΣ ; isSet→isGroupoid ; hSet)

record Coffin (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Shape : Type ℓ
    is-groupoid-shape : isGroupoid Shape
    shape-skeleton : Skeleton (Shape , is-groupoid-shape)

  open Skeleton shape-skeleton public
    using
      ( Index
      ; sk
      ; sk-section
      ; Component
      ; component-section
      ; isSetIndex
      ; ComponentGroup
      ; ComponentGroupStr
      ; index-of
      ; Total
      ; TotalEquiv
      )

  field
    componentGroupSet : ∀ idx → (ComponentGroup idx) -Set

  module _ (idx : Index) where
    open GroupStr (ComponentGroupStr idx) public
      renaming (is-groupoid to isGroupoidComponent ; is-connected to isConnectedComponent)

  PosSetIndex : Index → hSet ℓ
  PosSetIndex idx = componentGroupSet idx .action (sk.component-section idx) where
    open _-Set
    module sk = Skeleton shape-skeleton

  PosSetTotal : Total → hSet ℓ
  PosSetTotal (idx , idx-fib) = componentGroupSet idx .action idx-fib where
    open _-Set

  PosSet : Shape → hSet ℓ
  PosSet = PosSetTotal ∘ equivFun TotalEquiv

  Pos : Shape → Type ℓ
  Pos = ⟨_⟩ ∘ PosSet

  isSetPos : ∀ s → isSet (Pos s)
  isSetPos = str ∘ PosSet


-- open Coffin

-- CoffinPath : ∀ {ℓ} {C D : Coffin ℓ}
--   → (sk-path : C .shape-skeleton ≡ D .shape-skeleton)
--   → (pos-path : PathP (λ i → (idx : Skeleton.Index (sk-path i)) → Skeleton.ComponentGroup (sk-path i) idx -Set) (C .PosSet) (D .PosSet))
--   → C ≡ D
-- CoffinPath sk-path pos-path i .shape-skeleton = sk-path i
-- CoffinPath sk-path pos-path i .PosSet = pos-path i
