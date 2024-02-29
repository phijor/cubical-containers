module GpdCont.RecordEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism hiding (iso)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_$_)
open import Cubical.Data.Unit.Base
open import Cubical.Data.List.Base as List using (List ; _∷_ ; [])

open import Cubical.Reflection.Base
open import Cubical.Reflection.StrictEquiv public
open import Cubical.Reflection.RecordEquiv public

import Agda.Builtin.Reflection as R

open Iso

private
  pattern _hω∷_ a l = harg {q = R.quantity-ω} a ∷ l
  pattern iarg t = R.arg (R.arg-info R.instance′ (R.modality R.relevant R.quantity-ω)) t

  _<$>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → R.TC A → R.TC B
  f <$> t = t >>= λ x → R.returnTC (f x)

  hideArg : ∀ {ℓ} {A : Type ℓ} → R.Arg A → R.Arg A
  hideArg (R.arg (R.arg-info _ m) a) = R.arg (R.arg-info R.hidden m) a

  underPi : ∀ {ℓ} {A : Type ℓ}
    → (ty : R.Type)
    → (f : (tele : R.Telescope) → (ity : R.Type) → A)
    → A
  underPi {A = A} = go [] where
    go : (tele : R.Telescope)
      → (ty : R.Type)
      → (f : (tele : R.Telescope) → (ity : R.Type) → A)
      → A
    go tele (R.pi pi-arg (R.abs name ty)) f = go ((name , pi-arg) ∷ tele) ty f
    go tele ty@(_) f = f (List.rev tele) ty

  getRecordDefinition : (r : R.Term) → R.TC R.Definition
  getRecordDefinition (R.def f _) = R.getDefinition f
  getRecordDefinition r@(_) = R.typeError $ R.strErr "Not a record definition: " ∷ R.termErr r ∷ []

  getRecordΣFormat : (r : R.Term) → R.TC ΣFormat
  getRecordΣFormat (R.def name _) = do
    (R.record-type _ fs) ← R.getDefinition name
      where _ → R.typeError (R.strErr "Not a record type name:" ∷ R.nameErr name ∷ [])
    R.returnTC $ List→ΣFormat $ List.map (λ { (R.arg _ name) → name }) fs
  getRecordΣFormat r@(_) = R.typeError $ R.strErr "Not a record definition: " ∷ R.termErr r ∷ []

  inferTypeNormalised : R.Name → R.TC R.Type
  inferTypeNormalised name = do
    ty ← R.inferType (R.def name [])
    R.normalise ty

  -- Given the name of a record type, return the ΣFormat of the corresponding right-associated Σ-type
  recordName→ΣFormat : (recordName : R.Name) → R.TC ΣFormat
  recordName→ΣFormat recordName = do
    (R.record-type _ fs) ← R.getDefinition recordName
      where _ → R.typeError (R.strErr "Not a record type name:" ∷ R.nameErr recordName ∷ [])
    R.returnTC $ List→ΣFormat $ List.map (λ { (R.arg _ name) → name }) fs

  recordIsoΣTermMacro : (record-term : R.Term) → (hole : R.Term) → R.TC Unit
  recordIsoΣTermMacro record-term hole = do
    σ ← getRecordΣFormat record-term
    R.unify (recordIsoΣTerm σ) hole


  equivΣMacro : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Iso A B → R.Term → R.TC Unit
  equivΣMacro isoΣ hole = strictEquivMacro (isoΣ .fun) (isoΣ .inv) hole <|> isoToEquivMacro
    where
      isoToEquivMacro : R.TC Unit
      isoToEquivMacro = do
        `isoΣ ← R.quoteTC isoΣ
        R.unify (R.def (quote isoToEquiv) (`isoΣ v∷ [])) hole

record RecordToΣ {ℓ} (R : Type ℓ) {S : Type ℓ} : Type (ℓ-suc ℓ) where
  constructor toΣ
  field
    isoΣ : Iso R S
    @(tactic equivΣMacro isoΣ) {equivΣ} : R ≃ S
  
defineRecordToΣ' : (id-name : R.Name) (iso-term : R.Term) → R.TC Unit
defineRecordToΣ' id-name iso-term =
  R.defineFun id-name
    $ R.clause [] (R.proj (quote RecordToΣ.isoΣ) v∷ []) iso-term
      ∷ []

defineRecordToΣ : (id-name record-name : R.Name) → R.TC Unit
defineRecordToΣ id-name record-name = do
  σ ← recordName→ΣFormat record-name
  defineRecordToΣ' id-name $ recordIsoΣTerm σ
  
declareRecordToΣ' : (id-name record-name : R.Name) (σ : ΣFormat) → R.TC Unit
declareRecordToΣ' id-name record-name σ = do
  record-type ← inferTypeNormalised record-name
  decl-type ← underPi record-type $ makeRecordToΣTele []
  R.declareDef (iarg id-name) decl-type
  where
    σTy : R.Type
    σTy = ΣFormat→Ty σ

    makeRecordToΣTele : (params : List (R.Arg R.Type)) → R.Telescope → R.Type → R.TC R.Term
    makeRecordToΣTele params ((name , pi-arg@(R.arg arg-inf _)) ∷ tele) ty = do
      let var = R.arg arg-inf (v (List.length params))
      decl ← makeRecordToΣTele (var ∷ params) tele ty
      R.returnTC $ R.pi (hideArg pi-arg) (R.abs name decl)
    makeRecordToΣTele params [] = λ where
      (R.agda-sort _) → R.returnTC $ R.def (quote RecordToΣ) (R.def record-name params v∷ σTy hω∷ [])
      ty@(_) →  R.typeError
        $ R.strErr "Failed to declare RecordToΣ instance: '"
        ∷ R.nameErr record-name
        ∷ R.strErr "' is not a parametrized record.\n"
        ∷ R.strErr "Expected a sort, got '"
        ∷ R.termErr ty
        ∷ R.strErr "'"
        ∷ []

deriveRecordToΣ : (id-name record-name : R.Name) → R.TC Unit
deriveRecordToΣ id-name record-name = do
  σ ← recordName→ΣFormat record-name
  declareRecordToΣ' id-name record-name σ
  defineRecordToΣ' id-name $ recordIsoΣTerm σ

open RecordToΣ ⦃...⦄

infix 1.5 _asΣ
_asΣ : ∀ {ℓ} (R : Type ℓ) {S : Type ℓ} → ⦃ RecordToΣ R {S} ⦄ → Type ℓ
_asΣ R {S = S} = S

_IsoΣ : ∀ {ℓ} (R : Type ℓ) {S : Type ℓ} → ⦃ RecordToΣ R {S} ⦄ → Iso R S
R IsoΣ = isoΣ

_≃Σ : ∀ {ℓ} (R : Type ℓ) {S : Type ℓ} → ⦃ RecordToΣ R {S} ⦄ → R ≃ S
R ≃Σ = equivΣ

cast→Σ : ∀ {ℓ} {R : Type ℓ} {S : Type ℓ} → ⦃ RecordToΣ R {S} ⦄ → R → S
cast→Σ = isoΣ .fun

cast←Σ : ∀ {ℓ} {R : Type ℓ} {S : Type ℓ} → ⦃ RecordToΣ R {S} ⦄ → S → R
cast←Σ = isoΣ .inv

recordIsOfHLevel : ∀ {ℓ} {R S : Type ℓ} → ⦃ RecordToΣ R {S} ⦄ → (n : HLevel) → isOfHLevel n S → isOfHLevel n R
recordIsOfHLevel n = isOfHLevelRetractFromIso n isoΣ
