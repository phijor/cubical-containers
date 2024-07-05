module GpdCont.Test where
open import GpdCont.RecordEquiv
open import GpdCont.Prelude

open import Agda.Builtin.Unit
open import Agda.Builtin.List

record Foo : Type where
  field
    bar : Unit
    baz : List Unit

unquoteDecl FooToΣ = deriveRecordToΣ FooToΣ (quote Foo)

_ : (Foo asΣ) ≡ Σ Unit λ _ → List Unit
_ = refl

record Bar (a0 : Unit) (a1 : Foo) : Type where
  no-eta-equality
  field
    frob : Foo

-- TODO: Fix visibility in derived telescope
unquoteDecl BarToΣ = deriveRecordToΣ BarToΣ (quote Bar)
