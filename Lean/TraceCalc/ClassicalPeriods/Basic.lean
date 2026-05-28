import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

open CategoryTheory

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Mathlib-facing alias for a categorical functor in the classical period lane. -/
abbrev ClassicalFunctor
    (C : Type u) (D : Type v) [Category.{w} C] [Category.{x} D] := C ⥤ D

/-- Shared scalar context for a classical Betti/de Rham comparison package. -/
structure ClassicalComparisonContext where
  BaseField : Type u
  ScalarField : Type v
  [instBaseField : Field BaseField]
  [instScalarField : Field ScalarField]
  [instCharZero : CharZero BaseField]
  [instAlgebra : Algebra BaseField ScalarField]

attribute [instance]
  ClassicalComparisonContext.instBaseField
  ClassicalComparisonContext.instScalarField
  ClassicalComparisonContext.instCharZero
  ClassicalComparisonContext.instAlgebra

/-- Canonical scalar-extension map `v ↦ 1 ⊗ v` for the base/scalar field pair of `ctx`. -/
noncomputable def canonicalTensorScalarExtensionMap
    {ctx : ClassicalComparisonContext.{u, v}}
    (V : Type*) [AddCommGroup V] [Module ctx.BaseField V] :
    V →ₗ[ctx.BaseField] TensorProduct ctx.BaseField ctx.ScalarField V :=
  (LinearMap.rTensor V (Algebra.linearMap ctx.BaseField ctx.ScalarField)).comp
    (TensorProduct.lid ctx.BaseField V).symm.toLinearMap

/-- The canonical scalar-extension map `v ↦ 1 ⊗ v` is injective for a field extension.

This is the concrete algebraic fact used to remove the last extra hypotheses from
the coarse period-faithfulness theorem: tensoring the injective algebra map
`BaseField → ScalarField` with a vector space preserves injectivity, and the
left-unit tensor equivalence is itself injective. -/
theorem canonicalTensorScalarExtensionMap_injective
    {ctx : ClassicalComparisonContext.{u, v}}
    (V : Type*) [AddCommGroup V] [Module ctx.BaseField V] :
    Function.Injective (canonicalTensorScalarExtensionMap (ctx := ctx) V) := by
  letI : Module.Free ctx.BaseField V := Module.Free.of_divisionRing ctx.BaseField V
  letI : Module.Flat ctx.BaseField V := Module.Flat.of_free (R := ctx.BaseField) (M := V)
  have hAlgebraLinearMap :
      Function.Injective (Algebra.linearMap ctx.BaseField ctx.ScalarField) := by
    simpa using
      (NoZeroSMulDivisors.algebraMap_injective ctx.BaseField ctx.ScalarField)
  have hTensor :
      Function.Injective
        (LinearMap.rTensor V (Algebra.linearMap ctx.BaseField ctx.ScalarField)) :=
    Module.Flat.rTensor_preserves_injective_linearMap
      (M := V)
      (Algebra.linearMap ctx.BaseField ctx.ScalarField)
      hAlgebraLinearMap
  exact hTensor.comp (TensorProduct.lid ctx.BaseField V).symm.injective

/-- Concrete tensor/base-change model for one Betti/de Rham comparison package. -/
structure ComparisonTensorScalarExtensionData
    {ctx : ClassicalComparisonContext.{u, v}}
    (BettiCarrier : Type w)
    (DeRhamCarrier : Type x)
    (BettiOverScalar : Type y)
    (DeRhamOverScalar : Type z)
    [AddCommGroup BettiCarrier]
    [AddCommGroup DeRhamCarrier]
    [AddCommGroup BettiOverScalar]
    [AddCommGroup DeRhamOverScalar]
    [Module ctx.BaseField BettiCarrier]
    [Module ctx.BaseField DeRhamCarrier]
    [Module ctx.ScalarField BettiOverScalar]
    [Module ctx.ScalarField DeRhamOverScalar]
    [Module ctx.BaseField BettiOverScalar]
    [Module ctx.BaseField DeRhamOverScalar]
    (extendBetti : BettiCarrier →ₗ[ctx.BaseField] BettiOverScalar)
    (extendDeRham : DeRhamCarrier →ₗ[ctx.BaseField] DeRhamOverScalar) where
  bettiTensorModel :
    TensorProduct ctx.BaseField ctx.ScalarField BettiCarrier ≃ₗ[ctx.BaseField]
      BettiOverScalar
  deRhamTensorModel :
    TensorProduct ctx.BaseField ctx.ScalarField DeRhamCarrier ≃ₗ[ctx.BaseField]
      DeRhamOverScalar
  extendBetti_eq_tensorScalarExtension :
    extendBetti =
      bettiTensorModel.toLinearMap.comp
        (canonicalTensorScalarExtensionMap
          (ctx := ctx)
          BettiCarrier)
  extendDeRham_eq_tensorScalarExtension :
    extendDeRham =
      deRhamTensorModel.toLinearMap.comp
        (canonicalTensorScalarExtensionMap
          (ctx := ctx)
          DeRhamCarrier)

/-- Object-level classical structured comparison data. -/
structure ClassicalStructuredComparisonObject
    (ctx : ClassicalComparisonContext.{u, v}) where
  BettiCarrier : Type w
  DeRhamCarrier : Type x
  BettiOverScalar : Type y
  DeRhamOverScalar : Type z
  [instBettiAddCommGroup : AddCommGroup BettiCarrier]
  [instDeRhamAddCommGroup : AddCommGroup DeRhamCarrier]
  [instBettiOverScalarAddCommGroup : AddCommGroup BettiOverScalar]
  [instDeRhamOverScalarAddCommGroup : AddCommGroup DeRhamOverScalar]
  [instBettiModule : Module ctx.BaseField BettiCarrier]
  [instDeRhamModule : Module ctx.BaseField DeRhamCarrier]
  [instBettiOverScalarModule : Module ctx.ScalarField BettiOverScalar]
  [instDeRhamOverScalarModule : Module ctx.ScalarField DeRhamOverScalar]
  [instBettiOverScalarRestrictModule : Module ctx.BaseField BettiOverScalar]
  [instDeRhamOverScalarRestrictModule : Module ctx.BaseField DeRhamOverScalar]
  extendBetti : BettiCarrier →ₗ[ctx.BaseField] BettiOverScalar
  extendDeRham : DeRhamCarrier →ₗ[ctx.BaseField] DeRhamOverScalar
  comparisonIso : DeRhamOverScalar ≃ₗ[ctx.ScalarField] BettiOverScalar
  tensorScalarExtensionData :
    ComparisonTensorScalarExtensionData
      (ctx := ctx)
      BettiCarrier
      DeRhamCarrier
      BettiOverScalar
      DeRhamOverScalar
      extendBetti
      extendDeRham
  ScalarExtensionWitness : Type _
  scalarExtensionWitness : ScalarExtensionWitness
  comparisonNaturalityTarget : Prop
  comparisonBaseChangeCompatibility : Prop

attribute [instance]
  ClassicalStructuredComparisonObject.instBettiAddCommGroup
  ClassicalStructuredComparisonObject.instDeRhamAddCommGroup
  ClassicalStructuredComparisonObject.instBettiOverScalarAddCommGroup
  ClassicalStructuredComparisonObject.instDeRhamOverScalarAddCommGroup
  ClassicalStructuredComparisonObject.instBettiModule
  ClassicalStructuredComparisonObject.instDeRhamModule
  ClassicalStructuredComparisonObject.instBettiOverScalarModule
  ClassicalStructuredComparisonObject.instDeRhamOverScalarModule
  ClassicalStructuredComparisonObject.instBettiOverScalarRestrictModule
  ClassicalStructuredComparisonObject.instDeRhamOverScalarRestrictModule

namespace ClassicalStructuredComparisonObject

/-- The Betti scalar-extension map of a concrete structured comparison object is injective. -/
theorem extendBetti_injective
    {ctx : ClassicalComparisonContext.{u, v}}
    (object : ClassicalStructuredComparisonObject ctx) :
    Function.Injective object.extendBetti := by
  rw [object.tensorScalarExtensionData.extendBetti_eq_tensorScalarExtension]
  exact (LinearEquiv.injective object.tensorScalarExtensionData.bettiTensorModel).comp
    (canonicalTensorScalarExtensionMap_injective (ctx := ctx) object.BettiCarrier)

/-- The de Rham scalar-extension map of a concrete structured comparison object is injective. -/
theorem extendDeRham_injective
    {ctx : ClassicalComparisonContext.{u, v}}
    (object : ClassicalStructuredComparisonObject ctx) :
    Function.Injective object.extendDeRham := by
  rw [object.tensorScalarExtensionData.extendDeRham_eq_tensorScalarExtension]
  exact (LinearEquiv.injective object.tensorScalarExtensionData.deRhamTensorModel).comp
    (canonicalTensorScalarExtensionMap_injective (ctx := ctx) object.DeRhamCarrier)

end ClassicalStructuredComparisonObject

/-- Concrete tensor/base-change model for one structured comparison object. -/
abbrev StructuredComparisonTensorScalarExtensionData
    {ctx : ClassicalComparisonContext.{u, v}}
    (object : ClassicalStructuredComparisonObject ctx) :=
  ComparisonTensorScalarExtensionData
    (ctx := ctx)
    object.BettiCarrier
    object.DeRhamCarrier
    object.BettiOverScalar
    object.DeRhamOverScalar
    object.extendBetti
    object.extendDeRham

/-- Morphism-level structured comparison datum. -/
structure ClassicalStructuredComparisonMorphism
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : ClassicalStructuredComparisonObject ctx) where
  bettiMap : source.BettiCarrier →ₗ[ctx.BaseField] target.BettiCarrier
  deRhamMap : source.DeRhamCarrier →ₗ[ctx.BaseField] target.DeRhamCarrier
  bettiMapOverScalar : source.BettiOverScalar →ₗ[ctx.ScalarField] target.BettiOverScalar
  deRhamMapOverScalar : source.DeRhamOverScalar →ₗ[ctx.ScalarField] target.DeRhamOverScalar
  /-- The scalar extension of `bettiMap` agrees with `bettiMapOverScalar` after scalar extension.
  This is the naturality square: `bettiMapOverScalar ∘ extendBetti = extendBetti ∘ bettiMap`. -/
  bettiExtensionCompatibility :
    ∀ (x : source.BettiCarrier),
      bettiMapOverScalar (source.extendBetti x) = target.extendBetti (bettiMap x)
  /-- The scalar extension of `deRhamMap` agrees with `deRhamMapOverScalar` after scalar extension.
  This is the naturality square: `deRhamMapOverScalar ∘ extendDeRham = extendDeRham ∘ deRhamMap`. -/
  deRhamExtensionCompatibility :
    ∀ (x : source.DeRhamCarrier),
      deRhamMapOverScalar (source.extendDeRham x) = target.extendDeRham (deRhamMap x)
  comparisonSquareCommutes :
    target.comparisonIso.toLinearMap.comp deRhamMapOverScalar =
      bettiMapOverScalar.comp source.comparisonIso.toLinearMap

namespace ClassicalStructuredComparisonMorphism

/-- The manuscript's basis-free period datum attached to a morphism comparison package. -/
def basisFreePeriodMap
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (morphism : ClassicalStructuredComparisonMorphism source target) :
    source.DeRhamOverScalar →ₗ[ctx.ScalarField] target.BettiOverScalar :=
  target.comparisonIso.toLinearMap.comp morphism.deRhamMapOverScalar

/-- Betti-side presentation of the same basis-free period datum. -/
def basisFreePeriodMapViaBetti
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (morphism : ClassicalStructuredComparisonMorphism source target) :
    source.DeRhamOverScalar →ₗ[ctx.ScalarField] target.BettiOverScalar :=
  morphism.bettiMapOverScalar.comp source.comparisonIso.toLinearMap

theorem basisFreePeriodMap_agrees
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (morphism : ClassicalStructuredComparisonMorphism source target) :
    morphism.basisFreePeriodMap = morphism.basisFreePeriodMapViaBetti :=
  morphism.comparisonSquareCommutes

/-
TEX ref: `our_paper_draft.tex`, near Corollary `cor:internal-period-faithfulness`.
Paper role: over-scalar reflection — basis-free period map determines de Rham scalar-extended map.
Lean status: PROVED (real proof via comparisonIso cancellation).
Scope: classical algebraic stratum only (fixed source/target comparison objects over BaseField).
The full paper corollary claims unconditional faithfulness for all T_can morphisms;
that stronger claim is NOT proved here and requires the full reconstruction machinery.
-/
/-- For fixed source/target comparison objects, the basis-free period map determines the de Rham
scalar-extended realization map. -/
theorem deRhamMapOverScalar_eq_of_basisFreePeriodMap_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (left right : ClassicalStructuredComparisonMorphism source target)
    (hBasis : left.basisFreePeriodMap = right.basisFreePeriodMap) :
    left.deRhamMapOverScalar = right.deRhamMapOverScalar := by
  have hComp := congrArg (fun m => target.comparisonIso.symm.toLinearMap.comp m) hBasis
  simpa [ClassicalStructuredComparisonMorphism.basisFreePeriodMap] using hComp

/-
TEX ref: `our_paper_draft.tex`, near Corollary `cor:internal-period-faithfulness`.
Paper role: over-scalar reflection — basis-free period map determines Betti scalar-extended map.
Lean status: PROVED (real proof via comparisonIso and basisFreePeriodMapViaBetti cancellation).
-/
/-- For fixed source/target comparison objects, the basis-free period map also determines the
Betti scalar-extended realization map. -/
theorem bettiMapOverScalar_eq_of_basisFreePeriodMap_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (left right : ClassicalStructuredComparisonMorphism source target)
    (hBasis : left.basisFreePeriodMap = right.basisFreePeriodMap) :
    left.bettiMapOverScalar = right.bettiMapOverScalar := by
  have hViaBetti : left.basisFreePeriodMapViaBetti = right.basisFreePeriodMapViaBetti := by
    simpa [left.basisFreePeriodMap_agrees, right.basisFreePeriodMap_agrees] using hBasis
  have hComp := congrArg (fun m => m.comp source.comparisonIso.symm.toLinearMap) hViaBetti
  simpa [ClassicalStructuredComparisonMorphism.basisFreePeriodMapViaBetti] using hComp

/-
TEX ref: `our_paper_draft.tex`, supporting the statement of `thm:classical-coarse-period-consequence`.
Paper role: algebraic morphism-equality lemma — four map equalities imply morphism equality.
Lean status: PROVED (structural case analysis; Prop fields closed by proof irrelevance).
-/
/-- Once the four realization maps agree, the full structured comparison morphism agrees. The
remaining fields live in `Prop`, so proof irrelevance closes them. -/
theorem eq_of_map_fields_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (left right : ClassicalStructuredComparisonMorphism source target)
    (hBetti : left.bettiMap = right.bettiMap)
    (hDeRham : left.deRhamMap = right.deRhamMap)
    (hBettiScalar : left.bettiMapOverScalar = right.bettiMapOverScalar)
    (hDeRhamScalar : left.deRhamMapOverScalar = right.deRhamMapOverScalar) :
    left = right := by
  cases left; cases right
  cases hBetti; cases hDeRham; cases hBettiScalar; cases hDeRhamScalar
  -- All 4 map fields are now equalized. The remaining fields
  -- (bettiExtensionCompatibility, deRhamExtensionCompatibility, comparisonSquareCommutes)
  -- are proof terms of the same Prop on both sides. Close by proof irrelevance.
  simp [proof_irrel]

end ClassicalStructuredComparisonMorphism

/-- Sigma-packaged morphism-level comparison datum used by theorem targets. -/
abbrev SomeStructuredComparisonMorphism (ctx : ClassicalComparisonContext.{u, v}) :=
  Σ source : ClassicalStructuredComparisonObject ctx,
    Σ target : ClassicalStructuredComparisonObject ctx,
      ClassicalStructuredComparisonMorphism source target

/-- Canonical packer into the sigma-packaged structured comparison surface. -/
def packStructuredComparisonMorphism
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : ClassicalStructuredComparisonObject ctx)
    (morphism : ClassicalStructuredComparisonMorphism source target) :
    SomeStructuredComparisonMorphism ctx :=
  ⟨source, target, morphism⟩

namespace SomeStructuredComparisonMorphism

/-- Source comparison object of a sigma-packaged comparison morphism. -/
def sourceObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeStructuredComparisonMorphism ctx) : ClassicalStructuredComparisonObject ctx :=
  datum.1

/-- Target comparison object of a sigma-packaged comparison morphism. -/
def targetObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeStructuredComparisonMorphism ctx) : ClassicalStructuredComparisonObject ctx :=
  datum.2.1

/-- Underlying morphism package of a sigma-packaged comparison morphism. -/
def morphismDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeStructuredComparisonMorphism ctx) :
    ClassicalStructuredComparisonMorphism datum.sourceObject datum.targetObject :=
  datum.2.2

/-- Basis-free period datum of a sigma-packaged comparison morphism. -/
def basisFreePeriodMap
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeStructuredComparisonMorphism ctx) :
    datum.sourceObject.DeRhamOverScalar →ₗ[ctx.ScalarField] datum.targetObject.BettiOverScalar :=
  datum.morphismDatum.basisFreePeriodMap

end SomeStructuredComparisonMorphism

/-- Equality notion for structured comparison data. -/
structure StructuredComparisonEquality (ctx : ClassicalComparisonContext.{u, v}) where
  relates : SomeStructuredComparisonMorphism ctx → SomeStructuredComparisonMorphism ctx → Prop
  reflexiveTarget : Prop
  symmetricTarget : Prop
  transitiveTarget : Prop

/-- Scalar shadow extracted from richer structured or framed period data. -/
structure ScalarPeriodShadow (α : Type u) where
  ScalarCarrier : Type v
  shadowOf : α → ScalarCarrier
  equalityRelation : ScalarCarrier → ScalarCarrier → Prop
  ShadowTransportData : Type w
  shadowTransportData : ShadowTransportData
  scalarExtractionSound : Prop
  equalityCompatibleWithExtraction : Prop

/-- Equality package for the scalar shadow relation. -/
structure ScalarShadowEquality (α : Type u) (shadow : ScalarPeriodShadow α) where
  reflexiveTarget : Prop
  symmetricTarget : Prop
  transitiveTarget : Prop

end ClassicalPeriods
end TraceCalc