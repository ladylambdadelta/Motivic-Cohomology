import TraceCalc.ClassicalPeriods.Tomography

open CategoryTheory

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Scalar value extracted from a basis-free period map by a vector/covector probe. -/
def vectorCovectorProbeValue
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (morphism : ClassicalStructuredComparisonMorphism source target)
    (probe : source.DeRhamOverScalar ×
      (target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField)) :
    ctx.ScalarField :=
  probe.2 (morphism.basisFreePeriodMap probe.1)

/-- Agreement of all vector/covector probes for a fixed source/target comparison pair. -/
def VectorCovectorProbeAgreement
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (left right : ClassicalStructuredComparisonMorphism source target) : Prop :=
  ∀ probe : source.DeRhamOverScalar ×
      (target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField),
    vectorCovectorProbeValue left probe = vectorCovectorProbeValue right probe

/-- First concrete tomography theorem target: vector/covector probes determine the basis-free
period map for a fixed source/target pair. -/
structure BasisFreePeriodMapExtensionality
    (ctx : ClassicalComparisonContext.{u, v}) where
  theoremTarget :
    ∀ {source target : ClassicalStructuredComparisonObject ctx}
      (left right : ClassicalStructuredComparisonMorphism source target),
      VectorCovectorProbeAgreement left right →
        left.basisFreePeriodMap = right.basisFreePeriodMap

/-- Same-typed separating probe family for the basis-free period map. This is the fixed-source /
fixed-target finite-dimensional theorem package below the sigma-packed tomography core. -/
structure SeparatingProbeFamily
    (ctx : ClassicalComparisonContext.{u, v}) where
  ProbeIndex :
    (source target : ClassicalStructuredComparisonObject ctx) → Type w
  probeValue :
    ∀ (source target : ClassicalStructuredComparisonObject ctx),
      ProbeIndex source target →
        ClassicalStructuredComparisonMorphism source target →
          ctx.ScalarField
  separatesBasisFreePeriodMap :
    ∀ (source target : ClassicalStructuredComparisonObject ctx)
      (left right : ClassicalStructuredComparisonMorphism source target),
      (∀ probe : ProbeIndex source target,
        probeValue source target probe left = probeValue source target probe right) →
          left.basisFreePeriodMap = right.basisFreePeriodMap

/-- Finite-dimensional tomography content is packaged here as the point-separation principle on
all linear functionals of the target Betti fiber. The manuscript justifies this by finite
-dimensionality; Lean records the exact separation law needed by the proof. -/
structure PointSeparationForTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (target : ClassicalStructuredComparisonObject ctx) where
  theoremTarget :
    ∀ (left right : target.BettiOverScalar),
      (∀ covector : target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField,
        covector left = covector right) →
          left = right

structure FiniteDimensionalProbeSeparation
    (ctx : ClassicalComparisonContext.{u, v}) where
  pointSeparation :
    ∀ (target : ClassicalStructuredComparisonObject ctx),
      PointSeparationForTarget target
  finiteDimensionalTomographyTarget : Prop

def FiniteDimensionalProbeSeparation.pointSeparationAt
    {ctx : ClassicalComparisonContext.{u, v}}
    (_separation : FiniteDimensionalProbeSeparation ctx)
    (target : ClassicalStructuredComparisonObject ctx) :
    target.BettiOverScalar → target.BettiOverScalar → Prop :=
  fun left right =>
    ∀ covector : target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField,
      covector left = covector right

/-- The manuscript's finite-dimensionality burden is recorded explicitly as a
Prop field on the point-separation package. -/
def FiniteDimensionalProbeSeparation.finiteDimensionalityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (separation : FiniteDimensionalProbeSeparation ctx) : Prop :=
  separation.finiteDimensionalTomographyTarget

/-- The first honest reconstruction content below the sigma-packed tomography core: for fixed
source and target comparison objects, the basis-free period map determines the scalar-extended
realization maps. -/
structure OverScalarBasisFreeReconstruction
    (ctx : ClassicalComparisonContext.{u, v}) where
  theoremTarget :
    ∀ {source target : ClassicalStructuredComparisonObject ctx}
      (left right : ClassicalStructuredComparisonMorphism source target),
      left.basisFreePeriodMap = right.basisFreePeriodMap →
        left.deRhamMapOverScalar = right.deRhamMapOverScalar ∧
          left.bettiMapOverScalar = right.bettiMapOverScalar

/-- The remaining fieldwise reconstruction burden: descend from equality of the scalar-extended
realization maps back to equality of the underlying Betti/de Rham maps. This is the exact missing
input corresponding to the manuscript's faithful-flatness descent step. -/
structure BaseRealizationReconstruction
    (ctx : ClassicalComparisonContext.{u, v})
    (source target : ClassicalStructuredComparisonObject ctx) where
/-- Statement: basis-free period map equality implies the base-field maps agree.
    Extension-compatibility fields (now proof-type) are equal by proof irrelevance
    once the map fields agree; they are not listed as separate conjuncts. -/
    theoremTarget :
      ∀ (left right : ClassicalStructuredComparisonMorphism source target),
        left.basisFreePeriodMap = right.basisFreePeriodMap →
          left.deRhamMap = right.deRhamMap ∧ left.bettiMap = right.bettiMap

/-- Fixed-object packed-comparison reconstruction: once the underlying Betti/de Rham maps are also
recovered, equality of the full structured comparison morphism follows. -/
structure FixedObjectPackedComparisonReconstruction
    (ctx : ClassicalComparisonContext.{u, v})
    (source target : ClassicalStructuredComparisonObject ctx) where
  theoremTarget :
    ∀ (left right : ClassicalStructuredComparisonMorphism source target),
      left.basisFreePeriodMap = right.basisFreePeriodMap →
        left = right

/-- Fieldwise agreement for the packed structured comparison package at fixed source and target.

The object endpoints are explicit parameters of the ambient theorem, so the agreement fields only
need to record the basis-free datum together with the morphism-level components that survive after
packing into `SomeStructuredComparisonMorphism`. -/
structure PackedComparisonFieldwiseAgreement
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
    (left right : ClassicalStructuredComparisonMorphism source target) where
  basisFreePeriodMapEq : left.basisFreePeriodMap = right.basisFreePeriodMap
  bettiMapEq : left.bettiMap = right.bettiMap
  deRhamMapEq : left.deRhamMap = right.deRhamMap
  bettiMapOverScalarEq : left.bettiMapOverScalar = right.bettiMapOverScalar
  deRhamMapOverScalarEq : left.deRhamMapOverScalar = right.deRhamMapOverScalar
  -- Extension-compatibility fields omitted: proof-type fields whose equality
  -- follows from proof irrelevance once the map fields agree.

/-- If the packed fields agree at a fixed source/target pair, the sigma-packed comparison data
agrees as well. This isolates the final packaging step from the geometric reconstruction burden. -/
structure PackedComparisonFieldwiseExtensionality
    (ctx : ClassicalComparisonContext.{u, v})
    (source target : ClassicalStructuredComparisonObject ctx) where
  theoremTarget :
    ∀ (left right : ClassicalStructuredComparisonMorphism source target),
      PackedComparisonFieldwiseAgreement left right →
        packStructuredComparisonMorphism source target left =
          packStructuredComparisonMorphism source target right

/-- The sigma-packed comparison surface is canonically fieldwise extensional once the fixed
source/target morphism package is extensional. -/
def canonicalPackedComparisonFieldwiseExtensionality
    (ctx : ClassicalComparisonContext.{u, v})
    (source target : ClassicalStructuredComparisonObject ctx) :
    PackedComparisonFieldwiseExtensionality ctx source target where
  theoremTarget := by
    intro left right hFields
    have hMorphism : left = right :=
      ClassicalStructuredComparisonMorphism.eq_of_map_fields_eq
        left
        right
        hFields.bettiMapEq
        hFields.deRhamMapEq
        hFields.bettiMapOverScalarEq
        hFields.deRhamMapOverScalarEq
    exact congrArg
      (fun morphism => packStructuredComparisonMorphism source target morphism)
      hMorphism

/-- Phase 8 assembly theorem: once the basis-free period map reconstructs the fieldwise fixed
source/target data, fieldwise extensionality upgrades that information to literal packed equality.
-/
theorem packedComparisonEquality_of_basisFreePeriodMapEquality
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject ctx}
  (fieldwise : PackedComparisonFieldwiseExtensionality ctx source target)
  (reconstruction : BaseRealizationReconstruction ctx source target)
    (left right : ClassicalStructuredComparisonMorphism source target)
    (hBasis : left.basisFreePeriodMap = right.basisFreePeriodMap) :
    packStructuredComparisonMorphism source target left =
      packStructuredComparisonMorphism source target right := by
  have hOverScalarDeRham :=
    left.deRhamMapOverScalar_eq_of_basisFreePeriodMap_eq right hBasis
  have hOverScalarBetti :=
    left.bettiMapOverScalar_eq_of_basisFreePeriodMap_eq right hBasis
  cases reconstruction with
  | mk theoremTarget =>
      have hBase :
          left.deRhamMap = right.deRhamMap ∧ left.bettiMap = right.bettiMap := by
        simpa using theoremTarget left right hBasis
      have hFields : PackedComparisonFieldwiseAgreement left right := {
        basisFreePeriodMapEq := hBasis
        bettiMapEq := hBase.2
        deRhamMapEq := hBase.1
        bettiMapOverScalarEq := hOverScalarBetti
        deRhamMapOverScalarEq := hOverScalarDeRham
      }
      exact fieldwise.theoremTarget left right hFields


/-- The scalar-extended realization maps are already reconstructible from the basis-free period
map in the current API. -/
def canonicalOverScalarBasisFreeReconstruction
    (ctx : ClassicalComparisonContext.{u, v}) :
    OverScalarBasisFreeReconstruction ctx where
  theoremTarget := by
    intro source target left right hBasis
    exact ⟨
      left.deRhamMapOverScalar_eq_of_basisFreePeriodMap_eq right hBasis,
      left.bettiMapOverScalar_eq_of_basisFreePeriodMap_eq right hBasis
    ⟩

/-- Vector/covector probes for a fixed source/target pair. -/
def vectorCovectorSeparatingProbeFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (separation : FiniteDimensionalProbeSeparation ctx) :
    SeparatingProbeFamily ctx where
  ProbeIndex := fun source target =>
    source.DeRhamOverScalar ×
      (target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField)
  probeValue := fun _ _ probe morphism =>
    vectorCovectorProbeValue morphism probe
  separatesBasisFreePeriodMap := by
    intro source target left right hProbe
    change ∀ probe : source.DeRhamOverScalar ×
        (target.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField),
      vectorCovectorProbeValue left probe = vectorCovectorProbeValue right probe at hProbe
    ext vector
    have hPoint : PointSeparationForTarget target := separation.pointSeparation target
    refine hPoint.theoremTarget
      (left := left.basisFreePeriodMap vector)
      (right := right.basisFreePeriodMap vector)
      ?_
    intro covector
    simpa [vectorCovectorProbeValue] using hProbe (vector, covector)

end ClassicalPeriods
end TraceCalc
