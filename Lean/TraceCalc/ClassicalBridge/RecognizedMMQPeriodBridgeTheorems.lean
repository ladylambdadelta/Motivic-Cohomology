import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basic
import TraceCalc.ClassicalBridge.RecognizedMMQPeriodTargetSkeleton
import TraceCalc.ClassicalPeriods.PeriodMatrix
import TraceCalc.MotivicRecognition.PeriodFaithfulnessProviderProofs

universe u v w x y z

namespace TraceCalc
namespace ClassicalBridge

open ClassicalPeriods
open MotivicRecognition
open LayerB.RealObjects

variable
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {normalization : NormalizationPackageTarget internal}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    {comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical}
    {canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence}
    {normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence}
    {transportedNormalization :
      TransportedNormalizationIsMotivicTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport}
    {normTStructure : NormTStructureTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization}
    {heartRecognition : HeartRecognitionTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization normTStructure}

/-- Basis-free equality layer on the recognized `MM(Q)` image.

This is the smallest reconstruction-facing ingredient currently needed from the basis-free layer:
one chosen basis-free equality relation together with the theorem that literal equality of
basis-free period maps on recognized morphisms implies that relation. -/
structure RecognizedMMQBasisFreeSeparation
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  basisFreeEquality : BasisFreePeriodMapEquality ctx
  basisFreeEquality_of_packedComparison_eq :
    ∀ left right : SomeStructuredComparisonMorphism ctx,
      left = right → basisFreeEquality.relates left right
  basisFreeEquality_of_basisFreePeriodMap_eq :
    ∀ {M N : target.MixedMotivesQ} (f g : target.MixedMotivesQHom M N),
      (target.morphismComparisonOf f).basisFreePeriodMap =
          (target.morphismComparisonOf g).basisFreePeriodMap →
        basisFreeEquality.relates
          (target.packedMorphismComparisonOf f)
          (target.packedMorphismComparisonOf g)

/-- Precise fixed-object reconstruction primitive on the recognized `MM(Q)` image.

Its only role is to supply the `BaseRealizationReconstruction` input required by the existing
`LinearTomography` reconstruction theorem. -/
structure RecognizedMMQBaseRealizationReconstructionOnImage
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  theoremTarget :
    ∀ {M N : target.MixedMotivesQ},
      BaseRealizationReconstruction ctx
        (target.objectComparisonOf M)
        (target.objectComparisonOf N)

/-- Injectivity of the scalar-extension maps on the recognized image.

This is the exact extra hypothesis needed by the existing injective-extension faithfulness theorem
to produce fixed-object base realization reconstruction.

In manuscript terms, this is the faithful-flatness/descent gate: if two Betti or de Rham
base-field maps become equal after scalar extension on the recognized `MM(Q)` image, then they
were already equal before scalar extension. No existing bridge in this file derives these
injectivity statements from weaker comparison/base-change fields.

At the current abstraction level, `objectComparisonOf` only exposes arbitrary `BaseField` /
`ScalarField` carriers together with opaque linear maps `extendBetti` and `extendDeRham`; it does
not identify them definitionally with a concrete scalar-extension construction such as
`v ↦ v ⊗ 1` over `ℚ → ℂ`. So a faithful-flatness/mathlib adapter cannot be applied here without a
more concrete scalar-extension bridge upstream. -/
structure RecognizedMMQInjectiveExtensionsOnImage
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  extendBetti_injective :
    ∀ (M : target.MixedMotivesQ),
      Function.Injective (target.objectComparisonOf M).extendBetti
  extendDeRham_injective :
    ∀ (M : target.MixedMotivesQ),
      Function.Injective (target.objectComparisonOf M).extendDeRham

/-- The canonical tensor scalar-extension map is injective because tensoring the injective
base-field inclusion `BaseField → ScalarField` with a `BaseField`-vector space preserves
injectivity. -/
theorem canonicalTensorScalarExtensionMap_injective
    (V : Type*) [AddCommGroup V] [Module ctx.BaseField V] :
    Function.Injective (canonicalTensorScalarExtensionMap (ctx := ctx) V) := by
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

/-- Concrete tensor/base-change model for the recognized-image scalar-extension maps. -/
structure RecognizedMMQTensorScalarExtensionOnImage
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  bettiTensorModel :
    ∀ (M : target.MixedMotivesQ),
      TensorProduct ctx.BaseField ctx.ScalarField (target.objectComparisonOf M).BettiCarrier ≃ₗ[ctx.BaseField]
        (target.objectComparisonOf M).BettiOverScalar
  deRhamTensorModel :
    ∀ (M : target.MixedMotivesQ),
      TensorProduct ctx.BaseField ctx.ScalarField (target.objectComparisonOf M).DeRhamCarrier ≃ₗ[ctx.BaseField]
        (target.objectComparisonOf M).DeRhamOverScalar
  extendBetti_eq_tensorScalarExtension :
    ∀ (M : target.MixedMotivesQ),
      (target.objectComparisonOf M).extendBetti =
        (bettiTensorModel M).toLinearMap.comp
          (canonicalTensorScalarExtensionMap
            (ctx := ctx)
            (target.objectComparisonOf M).BettiCarrier)
  extendDeRham_eq_tensorScalarExtension :
    ∀ (M : target.MixedMotivesQ),
      (target.objectComparisonOf M).extendDeRham =
        (deRhamTensorModel M).toLinearMap.comp
          (canonicalTensorScalarExtensionMap
            (ctx := ctx)
            (target.objectComparisonOf M).DeRhamCarrier)

/-- The recognized comparison objects now carry their tensor/base-change models objectwise, so
the bridge-side tensor scalar-extension package can be assembled directly from
`target.objectComparisonOf`. -/
def recognizedMMQTensorScalarExtensionOnImage_of_objectComparisonTensorData
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    RecognizedMMQTensorScalarExtensionOnImage target where
  bettiTensorModel := fun M =>
    (target.objectComparisonOf M).tensorScalarExtensionData.bettiTensorModel
  deRhamTensorModel := fun M =>
    (target.objectComparisonOf M).tensorScalarExtensionData.deRhamTensorModel
  extendBetti_eq_tensorScalarExtension := fun M =>
    (target.objectComparisonOf M).tensorScalarExtensionData.extendBetti_eq_tensorScalarExtension
  extendDeRham_eq_tensorScalarExtension := fun M =>
    (target.objectComparisonOf M).tensorScalarExtensionData.extendDeRham_eq_tensorScalarExtension

/-- Proof-relevant provenance for scalar-extension descent on the recognized image.

The downstream descent route still accepts an abstract witness package, but it can now be filled by
the concrete tensor/base-change models carried on `target.objectComparisonOf`. -/
structure RecognizedMMQScalarExtensionDescentProvenanceOnImage
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  BettiScalarExtensionWitness : target.MixedMotivesQ → Type w
  DeRhamScalarExtensionWitness : target.MixedMotivesQ → Type x
  bettiWitness : ∀ (M : target.MixedMotivesQ), BettiScalarExtensionWitness M
  deRhamWitness : ∀ (M : target.MixedMotivesQ), DeRhamScalarExtensionWitness M
  bettiExtensionMapIsScalarExtension :
    ∀ (M : target.MixedMotivesQ), BettiScalarExtensionWitness M → Prop
  deRhamExtensionMapIsScalarExtension :
    ∀ (M : target.MixedMotivesQ), DeRhamScalarExtensionWitness M → Prop
  constructionSummary : String

/-- Faithful scalar-extension theorem package on the recognized image.

Mathematically this records the intended descent statement: for finite-dimensional `Q`-vector
spaces, scalar extension along `Q → C` is faithful, so the canonical scalar-extension maps used by
the Betti/de Rham comparison objects are injective. At the current abstraction level we carry the
theorem through explicit objectwise witnesses rather than a concrete tensor-product model. -/
structure RecognizedMMQFaithfulScalarExtensionOnImage
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  provenance : RecognizedMMQScalarExtensionDescentProvenanceOnImage target
  bettiExtensionInjectiveByFaithfulScalarExtension :
    ∀ (M : target.MixedMotivesQ),
      provenance.BettiScalarExtensionWitness M →
        Function.Injective (target.objectComparisonOf M).extendBetti
  deRhamExtensionInjectiveByFaithfulScalarExtension :
    ∀ (M : target.MixedMotivesQ),
      provenance.DeRhamScalarExtensionWitness M →
        Function.Injective (target.objectComparisonOf M).extendDeRham

/-- Proof-relevant scalar-extension injectivity witness on the recognized image.

This is the preferred bridge-level provider for the faithful-flatness/descent gate. It records the
Betti/de Rham injectivity theorems together with provenance tying them to scalar extension, rather
than leaving `RecognizedMMQInjectiveExtensionsOnImage` as a bare primitive theorem surface. -/
structure RecognizedMMQScalarExtensionInjectivityWitnessOnImage
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  faithfulScalarExtension : RecognizedMMQFaithfulScalarExtensionOnImage target
  injective_extendBetti :
    ∀ (M : target.MixedMotivesQ),
      Function.Injective (target.objectComparisonOf M).extendBetti
  injective_extendDeRham :
    ∀ (M : target.MixedMotivesQ),
      Function.Injective (target.objectComparisonOf M).extendDeRham

/-- Derive the high-level injectivity witness from the faithful scalar-extension theorem package. -/
def injectivityWitness_of_faithfulScalarExtension
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (faithfulScalarExtension : RecognizedMMQFaithfulScalarExtensionOnImage target) :
    RecognizedMMQScalarExtensionInjectivityWitnessOnImage target where
  faithfulScalarExtension := faithfulScalarExtension
  injective_extendBetti := fun M =>
    faithfulScalarExtension.bettiExtensionInjectiveByFaithfulScalarExtension
      M
      (faithfulScalarExtension.provenance.bettiWitness M)
  injective_extendDeRham := fun M =>
    faithfulScalarExtension.deRhamExtensionInjectiveByFaithfulScalarExtension
      M
      (faithfulScalarExtension.provenance.deRhamWitness M)

/-- Forget the proof-relevant scalar-extension witness down to the exact injective-extension gate
consumed by the existing basis-free reconstruction chain. -/
def recognizedMMQInjectiveExtensionsOnImage_of_scalarExtensionWitness
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (scalarWitness : RecognizedMMQScalarExtensionInjectivityWitnessOnImage target) :
    RecognizedMMQInjectiveExtensionsOnImage target where
  extendBetti_injective := scalarWitness.injective_extendBetti
  extendDeRham_injective := scalarWitness.injective_extendDeRham

/-- Build the recognized-image injective-extension gate directly from the faithful
scalar-extension theorem package. -/
def recognizedMMQInjectiveExtensionsOnImage_of_faithfulScalarExtension
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (faithfulScalarExtension : RecognizedMMQFaithfulScalarExtensionOnImage target) :
    RecognizedMMQInjectiveExtensionsOnImage target :=
  recognizedMMQInjectiveExtensionsOnImage_of_scalarExtensionWitness
    target
    (injectivityWitness_of_faithfulScalarExtension target faithfulScalarExtension)

/-- Concrete tensor/base-change data yields scalar-extension provenance with actual comparison
against the canonical map `v ↦ 1 ⊗ v`. -/
def recognizedMMQScalarExtensionDescentProvenanceOnImage_of_tensorScalarExtension
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (tensorScalarExtension : RecognizedMMQTensorScalarExtensionOnImage target) :
    RecognizedMMQScalarExtensionDescentProvenanceOnImage target where
  BettiScalarExtensionWitness := fun _ => PUnit
  DeRhamScalarExtensionWitness := fun _ => PUnit
  bettiWitness := fun _ => PUnit.unit
  deRhamWitness := fun _ => PUnit.unit
  bettiExtensionMapIsScalarExtension := fun M _ =>
    (target.objectComparisonOf M).extendBetti =
      (tensorScalarExtension.bettiTensorModel M).toLinearMap.comp
        (canonicalTensorScalarExtensionMap
          (ctx := ctx)
          (target.objectComparisonOf M).BettiCarrier)
  deRhamExtensionMapIsScalarExtension := fun M _ =>
    (target.objectComparisonOf M).extendDeRham =
      (tensorScalarExtension.deRhamTensorModel M).toLinearMap.comp
        (canonicalTensorScalarExtensionMap
          (ctx := ctx)
          (target.objectComparisonOf M).DeRhamCarrier)
  constructionSummary :=
    "objectwise tensor/base-change model: extend maps identified with canonical v ↦ 1 ⊗ v up to BaseField-linear equivalence"

/-- A concrete tensor/base-change model yields the faithful scalar-extension theorem package
on the recognized image. -/
def recognizedMMQFaithfulScalarExtensionOnImage_of_tensorScalarExtension
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (tensorScalarExtension : RecognizedMMQTensorScalarExtensionOnImage target) :
    RecognizedMMQFaithfulScalarExtensionOnImage target where
  provenance :=
    recognizedMMQScalarExtensionDescentProvenanceOnImage_of_tensorScalarExtension
      (ctx := ctx)
      target
      tensorScalarExtension
  bettiExtensionInjectiveByFaithfulScalarExtension := by
    intro M _
    have hCanonical :=
      canonicalTensorScalarExtensionMap_injective
        (ctx := ctx)
        (target.objectComparisonOf M).BettiCarrier
    have hModel : Function.Injective (tensorScalarExtension.bettiTensorModel M).toLinearMap :=
      (tensorScalarExtension.bettiTensorModel M).injective
    rw [tensorScalarExtension.extendBetti_eq_tensorScalarExtension M]
    exact hModel.comp hCanonical
  deRhamExtensionInjectiveByFaithfulScalarExtension := by
    intro M _
    have hCanonical :=
      canonicalTensorScalarExtensionMap_injective
        (ctx := ctx)
        (target.objectComparisonOf M).DeRhamCarrier
    have hModel : Function.Injective (tensorScalarExtension.deRhamTensorModel M).toLinearMap :=
      (tensorScalarExtension.deRhamTensorModel M).injective
    rw [tensorScalarExtension.extendDeRham_eq_tensorScalarExtension M]
    exact hModel.comp hCanonical

/-- The concrete tensor/base-change model yields the bridge-level injectivity witness. -/
def recognizedMMQScalarExtensionInjectivityWitnessOnImage_of_tensorScalarExtension
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (tensorScalarExtension : RecognizedMMQTensorScalarExtensionOnImage target) :
    RecognizedMMQScalarExtensionInjectivityWitnessOnImage target :=
  injectivityWitness_of_faithfulScalarExtension
    target
    (recognizedMMQFaithfulScalarExtensionOnImage_of_tensorScalarExtension
      (ctx := ctx)
      target
      tensorScalarExtension)

/-- The concrete tensor/base-change model yields the recognized-image injective-extension gate. -/
def recognizedMMQInjectiveExtensionsOnImage_of_tensorScalarExtension
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (tensorScalarExtension : RecognizedMMQTensorScalarExtensionOnImage target) :
    RecognizedMMQInjectiveExtensionsOnImage target :=
  recognizedMMQInjectiveExtensionsOnImage_of_faithfulScalarExtension
    target
    (recognizedMMQFaithfulScalarExtensionOnImage_of_tensorScalarExtension
      (ctx := ctx)
      target
      tensorScalarExtension)

/-- The object-level tensor/base-change models directly yield the recognized-image faithful
scalar-extension theorem package. -/
def recognizedMMQFaithfulScalarExtensionOnImage_of_objectComparisonTensorData
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    RecognizedMMQFaithfulScalarExtensionOnImage target :=
  recognizedMMQFaithfulScalarExtensionOnImage_of_tensorScalarExtension
    (ctx := ctx)
    target
    (recognizedMMQTensorScalarExtensionOnImage_of_objectComparisonTensorData
      (ctx := ctx)
      target)

/-- The object-level tensor/base-change models directly yield the recognized-image
scalar-extension injectivity witness package. -/
def recognizedMMQScalarExtensionInjectivityWitnessOnImage_of_objectComparisonTensorData
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    RecognizedMMQScalarExtensionInjectivityWitnessOnImage target :=
  recognizedMMQScalarExtensionInjectivityWitnessOnImage_of_tensorScalarExtension
    (ctx := ctx)
    target
    (recognizedMMQTensorScalarExtensionOnImage_of_objectComparisonTensorData
      (ctx := ctx)
      target)

/-- The object-level tensor/base-change models directly yield the recognized-image
injective-extension gate. -/
def recognizedMMQInjectiveExtensionsOnImage_of_objectComparisonTensorData
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    RecognizedMMQInjectiveExtensionsOnImage target :=
  recognizedMMQInjectiveExtensionsOnImage_of_tensorScalarExtension
    (ctx := ctx)
    target
    (recognizedMMQTensorScalarExtensionOnImage_of_objectComparisonTensorData
      (ctx := ctx)
      target)

/-- Canonical basis-free equality on the recognized image, given by literal packed equality. -/
def recognizedMMQDefinitionalBasisFreeEquality
    (_target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    BasisFreePeriodMapEquality ctx where
  relates := fun left right => left = right
  reflexiveTarget := ∀ (a : ctx.ScalarField), a = a
  symmetricTarget :=
    ∀ a b : ctx.ScalarField, a = b → b = a
  transitiveTarget :=
    ∀ a b c : ctx.ScalarField, a = b → b = c → a = c

/-- Existing injective-extension faithfulness theorem, restricted to the recognized image, yields
the fixed-object `BaseRealizationReconstruction` package needed by `LinearTomography`. -/
def recognizedMMQBaseRealizationReconstruction
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (injectiveExtensions : RecognizedMMQInjectiveExtensionsOnImage target) :
    RecognizedMMQBaseRealizationReconstructionOnImage target where
  theoremTarget := by
    intro M N
    refine {
      theoremTarget := ?_
    }
    intro left right hBasis
    have hMorphism : left = right :=
      internal_period_faithfulness_of_injective_extensions_bridge
        (target.objectComparisonOf M)
        (target.objectComparisonOf N)
        left
        right
        (injectiveExtensions.extendBetti_injective N)
        (injectiveExtensions.extendDeRham_injective N)
        hBasis
    exact ⟨congrArg ClassicalStructuredComparisonMorphism.deRhamMap hMorphism,
      congrArg ClassicalStructuredComparisonMorphism.bettiMap hMorphism⟩

/-- Existing fixed-object reconstruction data from `LinearTomography` upgrades the chosen
basis-free relation on the recognized image to a full `RecognizedMMQBasisFreeSeparation`.

This is the precise adapter from the classical tomography/reconstruction layer to the first
recognized-image bridge ingredient. -/
def RecognizedMMQBasisFreeSeparation.ofBaseRealizationReconstruction
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (basisFreeEquality : BasisFreePeriodMapEquality ctx)
    (basisFreeEquality_of_packedComparison_eq :
      ∀ left right : SomeStructuredComparisonMorphism ctx,
        left = right → basisFreeEquality.relates left right)
    (baseReconstruction :
      ∀ {M N : target.MixedMotivesQ},
        BaseRealizationReconstruction ctx
          (target.objectComparisonOf M)
          (target.objectComparisonOf N)) :
    RecognizedMMQBasisFreeSeparation target where
  basisFreeEquality := basisFreeEquality
  basisFreeEquality_of_packedComparison_eq := basisFreeEquality_of_packedComparison_eq
  basisFreeEquality_of_basisFreePeriodMap_eq := by
    intro M N f g hBasis
    have hPacked :
        target.packedMorphismComparisonOf f =
          target.packedMorphismComparisonOf g :=
      packedComparisonEquality_of_basisFreePeriodMapEquality
        (canonicalPackedComparisonFieldwiseExtensionality
          ctx
          (target.objectComparisonOf M)
          (target.objectComparisonOf N))
        (baseReconstruction (M := M) (N := N))
        (target.morphismComparisonOf f)
        (target.morphismComparisonOf g)
        hBasis
    exact basisFreeEquality_of_packedComparison_eq _ _ hPacked

/-- Period-evaluation data sitting above one chosen basis-free equality layer.

This is kept separate from `RecognizedMMQBasisFreeSeparation` because basis-free evaluation is not
needed to state or consume the reconstruction boundary itself. -/
structure RecognizedMMQBasisFreeEvaluationData
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (basisFreeSeparation : RecognizedMMQBasisFreeSeparation target) where
  periodEvaluation : SomeStructuredComparisonMorphism ctx → ctx.ScalarField
  evaluationRespectsBasisFree :
    RecognizedMMQPeriodTargetSkeleton.classicalPeriodEvaluationIsBasisFreeTarget
      (ctx := ctx) periodEvaluation basisFreeSeparation.basisFreeEquality

/-- Repackage the basis-free evaluation data as the existing bucket-C evaluation obligation. -/
def basisFreeEvaluationObligation_of_basisFreeEvaluationData
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (basisFreeSeparation : RecognizedMMQBasisFreeSeparation target)
    (evaluationData : RecognizedMMQBasisFreeEvaluationData target basisFreeSeparation) :
    RecognizedMMQPeriodTargetSkeleton.RecognizedMMQBasisFreeEvaluationObligation
      (ctx := ctx) where
  periodEvaluation := evaluationData.periodEvaluation
  basisFreeEquality := basisFreeSeparation.basisFreeEquality
  theoremTarget := evaluationData.evaluationRespectsBasisFree

/-- Reconstruction bridge from basis-free equality to equality of packed structured comparison
data on the recognized image. -/
structure RecognizedMMQReconstructionFromBasisFree
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (basisFreeSeparation : RecognizedMMQBasisFreeSeparation target) where
  theoremTarget :
    ∀ {M N : target.MixedMotivesQ} (f g : target.MixedMotivesQHom M N),
      basisFreeSeparation.basisFreeEquality.relates
        (target.packedMorphismComparisonOf f)
        (target.packedMorphismComparisonOf g) →
      target.packedMorphismComparisonOf f = target.packedMorphismComparisonOf g

/-- Derive the existing reconstruction obligation from the basis-free bridge data. -/
def reconstructionObligation_of_basisFreeSeparation
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (basisFreeSeparation : RecognizedMMQBasisFreeSeparation target)
    (reconstruction : RecognizedMMQReconstructionFromBasisFree target basisFreeSeparation) :
    RecognizedMMQPeriodTargetSkeleton.RecognizedMMQReconstructionObligation
      (ctx := ctx) target where
  theoremTarget := by
    intro M N f g hBasis
    exact reconstruction.theoremTarget f g
      (basisFreeSeparation.basisFreeEquality_of_basisFreePeriodMap_eq f g hBasis)

/-- Canonical basis-free separation on the recognized image, derived from the precise fixed-object
base reconstruction primitive. -/
def basisFreeSeparation_of_recognizedBaseRealizationReconstruction
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (baseReconstruction : RecognizedMMQBaseRealizationReconstructionOnImage target) :
    RecognizedMMQBasisFreeSeparation target :=
  RecognizedMMQBasisFreeSeparation.ofBaseRealizationReconstruction
    target
    (recognizedMMQDefinitionalBasisFreeEquality target)
    (fun _ _ h => h)
    baseReconstruction.theoremTarget

/-- Short canonical name for the basis-free separation layer once fixed-object base realization
reconstruction has been supplied on the recognized image. -/
def recognizedMMQBasisFreeSeparation
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (baseReconstruction : RecognizedMMQBaseRealizationReconstructionOnImage target) :
    RecognizedMMQBasisFreeSeparation target :=
  basisFreeSeparation_of_recognizedBaseRealizationReconstruction target baseReconstruction

/-- For the canonical definitional basis-free equality on the recognized image, reconstruction from
basis-free equality to packed equality is immediate. -/
def recognizedMMQReconstructionFromBasisFree
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (baseReconstruction : RecognizedMMQBaseRealizationReconstructionOnImage target) :
    RecognizedMMQReconstructionFromBasisFree target
      (recognizedMMQBasisFreeSeparation target baseReconstruction) where
  theoremTarget := by
    intro M N f g hBasis
    change target.packedMorphismComparisonOf f = target.packedMorphismComparisonOf g at hBasis
    exact hBasis

/-- The recognized reconstruction obligation follows through the existing basis-free bridge once
fixed-object base realization reconstruction has been supplied on the recognized image. -/
def recognizedMMQReconstructionObligation
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (baseReconstruction : RecognizedMMQBaseRealizationReconstructionOnImage target) :
    RecognizedMMQPeriodTargetSkeleton.RecognizedMMQReconstructionObligation
      (ctx := ctx) target :=
  reconstructionObligation_of_basisFreeSeparation
    target
    (recognizedMMQBasisFreeSeparation target baseReconstruction)
    (recognizedMMQReconstructionFromBasisFree target baseReconstruction)

/-- The faithful-flatness/scalar-extension witness directly yields fixed-object base realization
reconstruction on the recognized image. -/
def recognizedMMQBaseRealizationReconstruction_of_scalarExtensionWitness
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (scalarWitness : RecognizedMMQScalarExtensionInjectivityWitnessOnImage target) :
    RecognizedMMQBaseRealizationReconstructionOnImage target :=
  recognizedMMQBaseRealizationReconstruction
    target
    (recognizedMMQInjectiveExtensionsOnImage_of_scalarExtensionWitness target scalarWitness)

/-- The object-level tensor/base-change models directly yield fixed-object base realization
reconstruction on the recognized image. -/
def recognizedMMQBaseRealizationReconstruction_of_objectComparisonTensorData
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    RecognizedMMQBaseRealizationReconstructionOnImage target :=
  recognizedMMQBaseRealizationReconstruction
    target
    (recognizedMMQInjectiveExtensionsOnImage_of_objectComparisonTensorData
      (ctx := ctx)
      target)

/-- The scalar-extension witness closes the canonical basis-free separation layer on the
recognized image. -/
def recognizedMMQBasisFreeSeparation_of_scalarExtensionWitness
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (scalarWitness : RecognizedMMQScalarExtensionInjectivityWitnessOnImage target) :
    RecognizedMMQBasisFreeSeparation target :=
  recognizedMMQBasisFreeSeparation
    target
    (recognizedMMQBaseRealizationReconstruction_of_scalarExtensionWitness target scalarWitness)

/-- The object-level tensor/base-change models directly close the canonical basis-free separation
layer on the recognized image. -/
def recognizedMMQBasisFreeSeparation_of_objectComparisonTensorData
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    RecognizedMMQBasisFreeSeparation target :=
  recognizedMMQBasisFreeSeparation
    target
    (recognizedMMQBaseRealizationReconstruction_of_objectComparisonTensorData
      (ctx := ctx)
      target)

/-- The scalar-extension witness closes the recognized reconstruction obligation through the
existing basis-free reconstruction route. -/
def recognizedMMQReconstructionObligation_of_scalarExtensionWitness
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (scalarWitness : RecognizedMMQScalarExtensionInjectivityWitnessOnImage target) :
    RecognizedMMQPeriodTargetSkeleton.RecognizedMMQReconstructionObligation
      (ctx := ctx) target :=
  recognizedMMQReconstructionObligation
    target
    (recognizedMMQBaseRealizationReconstruction_of_scalarExtensionWitness target scalarWitness)

/-- The object-level tensor/base-change models directly close the recognized reconstruction
obligation through the existing basis-free reconstruction route. -/
def recognizedMMQReconstructionObligation_of_objectComparisonTensorData
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    RecognizedMMQPeriodTargetSkeleton.RecognizedMMQReconstructionObligation
      (ctx := ctx) target :=
  recognizedMMQReconstructionObligation
    target
    (recognizedMMQBaseRealizationReconstruction_of_objectComparisonTensorData
      (ctx := ctx)
      target)

/-- The faithful scalar-extension theorem package directly yields fixed-object base realization
reconstruction on the recognized image. -/
def recognizedMMQBaseRealizationReconstruction_of_faithfulScalarExtension
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (faithfulScalarExtension : RecognizedMMQFaithfulScalarExtensionOnImage target) :
    RecognizedMMQBaseRealizationReconstructionOnImage target :=
  recognizedMMQBaseRealizationReconstruction
    target
    (recognizedMMQInjectiveExtensionsOnImage_of_faithfulScalarExtension
      target faithfulScalarExtension)

/-- The faithful scalar-extension theorem package closes the canonical basis-free separation layer
on the recognized image. -/
def recognizedMMQBasisFreeSeparation_of_faithfulScalarExtension
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (faithfulScalarExtension : RecognizedMMQFaithfulScalarExtensionOnImage target) :
    RecognizedMMQBasisFreeSeparation target :=
  recognizedMMQBasisFreeSeparation
    target
    (recognizedMMQBaseRealizationReconstruction_of_faithfulScalarExtension
      target faithfulScalarExtension)

/-- The faithful scalar-extension theorem package closes the recognized reconstruction obligation
through the existing basis-free reconstruction route. -/
def recognizedMMQReconstructionObligation_of_faithfulScalarExtension
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (faithfulScalarExtension : RecognizedMMQFaithfulScalarExtensionOnImage target) :
    RecognizedMMQPeriodTargetSkeleton.RecognizedMMQReconstructionObligation
      (ctx := ctx) target :=
  recognizedMMQReconstructionObligation
    target
    (recognizedMMQBaseRealizationReconstruction_of_faithfulScalarExtension
      target faithfulScalarExtension)

/-- Packed structured-comparison equality reconstructs the underlying recognized `MM(Q)` morphism.
-/
structure RecognizedMMQMorphismReconstructionFromPackedComparison
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  theoremTarget : target.morphismReconstructionDataTarget

/-- Repackage packed-comparison reconstruction as the existing bucket-C morphism reconstruction
obligation. -/
def morphismReconstructionObligation_of_packedComparison
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (morphismReconstruction :
      RecognizedMMQMorphismReconstructionFromPackedComparison target) :
    RecognizedMMQPeriodTargetSkeleton.RecognizedMMQMorphismReconstructionObligation
      (ctx := ctx) target where
  theoremTarget := morphismReconstruction.theoremTarget

/-- Comparison between the abstract structured-comparison relation and literal equality on the
recognized image. This is the bridge needed to derive theorem targets from packed-comparison
reconstruction rather than reproving them independently. -/
structure RecognizedMMQStructuredComparisonForwardOnRecognizedImage
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  structuredEq_of_packedComparison_eq :
    ∀ {M N : target.MixedMotivesQ} (f g : target.MixedMotivesQHom M N),
      target.packedMorphismComparisonOf f = target.packedMorphismComparisonOf g →
        structuredEq.relates
          (target.packedMorphismComparisonOf f)
          (target.packedMorphismComparisonOf g)

/-- Literal packed-comparison equality reflected from the abstract structured-comparison relation
on the recognized image. This is the exact ingredient needed for the structured-faithfulness
route. -/
structure RecognizedMMQPackedComparisonExtensionalityOnRecognizedImage
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  packedComparison_eq_of_structuredEq :
    ∀ {M N : target.MixedMotivesQ} (f g : target.MixedMotivesQHom M N),
      structuredEq.relates
          (target.packedMorphismComparisonOf f)
          (target.packedMorphismComparisonOf g) →
        target.packedMorphismComparisonOf f = target.packedMorphismComparisonOf g

/-- Build recognized-image packed-comparison extensionality directly from the selected classical
comparison layer when that layer is already known to reflect literal equality of sigma-packaged
comparison data. -/
def RecognizedMMQPackedComparisonExtensionalityOnRecognizedImage.ofPackedComparisonReflection
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (packedComparison_eq_of_structuredEq :
      ∀ left right : SomeStructuredComparisonMorphism ctx,
        structuredEq.relates left right → left = right) :
    RecognizedMMQPackedComparisonExtensionalityOnRecognizedImage target where
  packedComparison_eq_of_structuredEq := by
    intro M N f g hStructured
    exact packedComparison_eq_of_structuredEq
      (target.packedMorphismComparisonOf f)
      (target.packedMorphismComparisonOf g)
      hStructured

/-- Concrete conservativity theorem for the literal packed-comparison equality layer used by the
Layer D classical comparison package. This is the non-generic recognized-image theorem: if the
selected `structuredEq` is literally packed comparison equality, then structured comparison
equality reflects packed comparison equality on recognized `MM(Q)` morphisms. -/
def RecognizedMMQPackedComparisonExtensionalityOnRecognizedImage.ofLiteralPackedEquality
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (hStructuredEq : structuredEq = LayerD.literalPackedStructuredComparisonEquality ctx) :
    RecognizedMMQPackedComparisonExtensionalityOnRecognizedImage target :=
  RecognizedMMQPackedComparisonExtensionalityOnRecognizedImage.ofPackedComparisonReflection
    target
    (by
      intro left right hStructured
      simpa [hStructuredEq] using hStructured)

/-- Build the forward recognized-image comparison bridge from any chosen basis-free equality layer
whose theorem surface already reflects the abstract structured-comparison relation. -/
def RecognizedMMQStructuredComparisonForwardOnRecognizedImage.ofBasisFreeReflection
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (basisFreeSeparation : RecognizedMMQBasisFreeSeparation target)
    (basisFreeReflection :
      BasisFreePeriodMapReflectsStructuredComparison
        ctx
        basisFreeSeparation.basisFreeEquality
        structuredEq) :
    RecognizedMMQStructuredComparisonForwardOnRecognizedImage target where
  structuredEq_of_packedComparison_eq := by
    intro M N f g hPacked
    exact basisFreeReflection.theoremTarget
      (target.packedMorphismComparisonOf f)
      (target.packedMorphismComparisonOf g)
      (basisFreeSeparation.basisFreeEquality_of_packedComparison_eq
        (target.packedMorphismComparisonOf f)
        (target.packedMorphismComparisonOf g)
        hPacked)

structure RecognizedMMQStructuredComparisonOnRecognizedImage
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  structuredEq_of_packedComparison_eq :
    ∀ {M N : target.MixedMotivesQ} (f g : target.MixedMotivesQHom M N),
      target.packedMorphismComparisonOf f = target.packedMorphismComparisonOf g →
        structuredEq.relates
          (target.packedMorphismComparisonOf f)
          (target.packedMorphismComparisonOf g)
  packedComparison_eq_of_structuredEq :
    ∀ {M N : target.MixedMotivesQ} (f g : target.MixedMotivesQHom M N),
      structuredEq.relates
          (target.packedMorphismComparisonOf f)
          (target.packedMorphismComparisonOf g) →
        target.packedMorphismComparisonOf f = target.packedMorphismComparisonOf g

/-- Forget the converse direction when only packed-comparison equality needs to be promoted to the
abstract structured-comparison relation. -/
def RecognizedMMQStructuredComparisonOnRecognizedImage.forward
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (relationOnImage : RecognizedMMQStructuredComparisonOnRecognizedImage target) :
    RecognizedMMQStructuredComparisonForwardOnRecognizedImage target where
  structuredEq_of_packedComparison_eq := relationOnImage.structuredEq_of_packedComparison_eq

/-- Forget the forward direction when only structured-comparison extensionality is needed. -/
def RecognizedMMQStructuredComparisonOnRecognizedImage.extensionality
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (relationOnImage : RecognizedMMQStructuredComparisonOnRecognizedImage target) :
    RecognizedMMQPackedComparisonExtensionalityOnRecognizedImage target where
  packedComparison_eq_of_structuredEq := relationOnImage.packedComparison_eq_of_structuredEq

/-- Structured faithfulness is derived from packed-comparison reconstruction plus the comparison
between the abstract equality relation and literal equality on the recognized image. -/
def RecognizedMMQStructuredFaithfulnessFromMorphismReconstruction
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (relationOnImage : RecognizedMMQPackedComparisonExtensionalityOnRecognizedImage target)
    (morphismReconstruction :
      RecognizedMMQMorphismReconstructionFromPackedComparison target) :
    RecognizedMMQPeriodTargetSkeleton.RecognizedMMQStructuredFaithfulnessObligation
      (ctx := ctx) target where
  theoremTarget := by
    intro M N f g hStructured
    exact morphismReconstruction.theoremTarget f g
      (relationOnImage.packedComparison_eq_of_structuredEq f g hStructured)

/-- Scalar separation on the recognized image, phrased relative to one chosen basis-free equality
layer. This is the precise scalar ingredient needed before scalar reflection can be derived. -/
structure RecognizedMMQScalarSeparationOnImage
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (basisFreeSeparation : RecognizedMMQBasisFreeSeparation target) where
  scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism ctx)
  scalarShadowEquality :
    ScalarShadowEquality (SomeStructuredComparisonMorphism ctx) scalarShadow
  basisFreeEquality_of_scalarShadow_eq :
    ∀ {M N : target.MixedMotivesQ} (f g : target.MixedMotivesQHom M N),
      scalarShadow.equalityRelation
        (scalarShadow.shadowOf (target.packedMorphismComparisonOf f))
        (scalarShadow.shadowOf (target.packedMorphismComparisonOf g)) →
      basisFreeSeparation.basisFreeEquality.relates
        (target.packedMorphismComparisonOf f)
        (target.packedMorphismComparisonOf g)

/-- Exact scalar theorem surface on the recognized image for the literal-packed lane:
equality of scalar shadows determines literal packed structured-comparison equality. -/
structure RecognizedMMQScalarShadowExtensionalityOnImage
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism ctx)
  scalarShadowEquality :
    ScalarShadowEquality (SomeStructuredComparisonMorphism ctx) scalarShadow
  packedComparison_eq_of_scalarShadow_eq :
    ∀ {M N : target.MixedMotivesQ} (f g : target.MixedMotivesQHom M N),
      scalarShadow.equalityRelation
        (scalarShadow.shadowOf (target.packedMorphismComparisonOf f))
        (scalarShadow.shadowOf (target.packedMorphismComparisonOf g)) →
      target.packedMorphismComparisonOf f = target.packedMorphismComparisonOf g

/-- A global Betti scalar-extension faithfulness theorem can be restricted to the recognized image
once a basis-free equality layer is chosen. This makes the relation between the old scalar theorem
surface and the new scalar-separation ingredient explicit instead of implicit. -/
def RecognizedMMQScalarSeparationOnImage.ofBettiScalarExtensionFaithfulness
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (basisFreeSeparation : RecognizedMMQBasisFreeSeparation target)
    (scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism ctx))
    (scalarShadowEquality : ScalarShadowEquality (SomeStructuredComparisonMorphism ctx) scalarShadow)
    (bettiFaithfulness :
      RecognizedMMQPeriodTargetSkeleton.bettiScalarExtensionFaithfulnessTarget
        (ctx := ctx) scalarShadow) :
    RecognizedMMQScalarSeparationOnImage target basisFreeSeparation where
  scalarShadow := scalarShadow
  scalarShadowEquality := scalarShadowEquality
  basisFreeEquality_of_scalarShadow_eq := by
    intro M N f g hScalar
    have hPacked :
        target.packedMorphismComparisonOf f =
          target.packedMorphismComparisonOf g :=
      bettiFaithfulness
        (target.packedMorphismComparisonOf f)
        (target.packedMorphismComparisonOf g)
        hScalar
    exact basisFreeSeparation.basisFreeEquality_of_packedComparison_eq
      _ _ hPacked

/-- Scalar reflection is derived from scalar separation on the recognized image, basis-free
reconstruction, and the comparison between literal packed equality and the abstract structured
comparison relation. -/
def RecognizedMMQScalarReflectionFromBasisFreeSeparation
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (basisFreeSeparation : RecognizedMMQBasisFreeSeparation target)
    (reconstruction : RecognizedMMQReconstructionFromBasisFree target basisFreeSeparation)
    (relationOnImage : RecognizedMMQStructuredComparisonForwardOnRecognizedImage target)
    (scalarSeparation : RecognizedMMQScalarSeparationOnImage target basisFreeSeparation) :
    RecognizedMMQPeriodTargetSkeleton.RecognizedMMQScalarReflectionObligation
      (ctx := ctx) target where
  scalarShadow := scalarSeparation.scalarShadow
  scalarShadowEquality := scalarSeparation.scalarShadowEquality
  theoremTarget := by
    intro M N f g hScalar
    have hBasis :=
      scalarSeparation.basisFreeEquality_of_scalarShadow_eq f g hScalar
    have hPacked := reconstruction.theoremTarget f g hBasis
    exact relationOnImage.structuredEq_of_packedComparison_eq f g hPacked

/-- Convert a direct literal-packed scalar-shadow theorem into the existing scalar-reflection
obligation by passing through the chosen structured-comparison relation on the recognized image. -/
def scalarReflection_of_scalarShadowExtensionality
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (relationOnImage : RecognizedMMQStructuredComparisonForwardOnRecognizedImage target)
    (scalarExtensionality : RecognizedMMQScalarShadowExtensionalityOnImage target) :
    RecognizedMMQPeriodTargetSkeleton.RecognizedMMQScalarReflectionObligation
      (ctx := ctx) target where
  scalarShadow := scalarExtensionality.scalarShadow
  scalarShadowEquality := scalarExtensionality.scalarShadowEquality
  theoremTarget := by
    intro M N f g hScalar
    have hPacked :=
      scalarExtensionality.packedComparison_eq_of_scalarShadow_eq f g hScalar
    exact relationOnImage.structuredEq_of_packedComparison_eq f g hPacked

/-- When the recognized comparison layer is fixed to literal packed equality, any scalar
reflection theorem immediately yields the direct scalar-shadow extensionality statement used by
the final period-conjecture boundary. -/
def RecognizedMMQScalarShadowExtensionalityOnImage.ofScalarReflection
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (scalarReflection :
      RecognizedMMQPeriodTargetSkeleton.RecognizedMMQScalarReflectionObligation
        (ctx := ctx) target)
    (hStructuredEq : structuredEq = LayerD.literalPackedStructuredComparisonEquality ctx) :
    RecognizedMMQScalarShadowExtensionalityOnImage target where
  scalarShadow := scalarReflection.scalarShadow
  scalarShadowEquality := scalarReflection.scalarShadowEquality
  packedComparison_eq_of_scalarShadow_eq := by
    intro M N f g hScalar
    have hStructured := scalarReflection.theoremTarget f g hScalar
    simpa [hStructuredEq] using hStructured

/-- Framed matrix-coefficient separation for the canonical framed-period system.

The theorem target is intentionally stated on the full admissible frame family
exposed by the recognized framed system. A single arbitrary frame value is not
assumed to be separating; the separation statement requires agreement across
all canonical frame indices on the source and target sides. -/
structure RecognizedMMQFramedMatrixCoefficientSeparation
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  packedComparison_eq_of_frameShadow_eq :
    ∀ {M N : target.MixedMotivesQ}
      (f g : target.MixedMotivesQHom M N),
      (∀ probe : target.ProbeIndex,
          target.framedCoordinateFamilyOf f probe = target.framedCoordinateFamilyOf g probe) →
        target.packedMorphismComparisonOf f = target.packedMorphismComparisonOf g

/-- Framed-shadow extensionality on the recognized image.

This is a theorem-level rename of `RecognizedMMQFramedMatrixCoefficientSeparation`: equality of
the canonical framed-shadow family determines literal packed comparison equality. The old theorem
surface remains available for compatibility. -/
structure RecognizedMMQFramedShadowExtensionalityOnImage
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  packedComparison_eq_of_framedShadow_eq :
    ∀ {M N : target.MixedMotivesQ}
      (f g : target.MixedMotivesQHom M N),
      (∀ probe : target.ProbeIndex,
          target.framedCoordinateFamilyOf f probe = target.framedCoordinateFamilyOf g probe) →
        target.packedMorphismComparisonOf f = target.packedMorphismComparisonOf g

/-- When the recognized comparison layer is fixed to literal packed equality, any framed
reflection theorem immediately yields the direct framed-shadow extensionality statement used by
the final period-conjecture boundary. -/
def RecognizedMMQFramedShadowExtensionalityOnImage.ofFramedReflection
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (framedReflection :
      RecognizedMMQPeriodTargetSkeleton.RecognizedMMQFramedReflectionObligation
        (ctx := ctx) target)
    (hStructuredEq : structuredEq = LayerD.literalPackedStructuredComparisonEquality ctx) :
    RecognizedMMQFramedShadowExtensionalityOnImage target where
  packedComparison_eq_of_framedShadow_eq := by
    intro M N f g hShadowFamily
    have hStructured := framedReflection.theoremTarget f g hShadowFamily
    simpa [hStructuredEq] using hStructured

/-- Exact theorem surface on the recognized image for the conservativity lane:
literal packed structured-comparison equality determines motivic morphism equality. -/
abbrev RecognizedMMQLiteralPackedComparisonReflectsMorphismEqualityOnImage
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :=
  RecognizedMMQMorphismReconstructionFromPackedComparison target

/-- Convert the legacy matrix-coefficient theorem surface to the clearer framed-shadow
extensionality name. -/
def framedShadowExtensionality_of_matrixCoefficientSeparation
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (framedSeparation : RecognizedMMQFramedMatrixCoefficientSeparation target) :
    RecognizedMMQFramedShadowExtensionalityOnImage target where
  packedComparison_eq_of_framedShadow_eq :=
    framedSeparation.packedComparison_eq_of_frameShadow_eq

/-- Convert the clearer framed-shadow extensionality theorem surface back to the legacy
matrix-coefficient name for compatibility. -/
def matrixCoefficientSeparation_of_framedShadowExtensionality
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (framedExtensionality : RecognizedMMQFramedShadowExtensionalityOnImage target) :
    RecognizedMMQFramedMatrixCoefficientSeparation target where
  packedComparison_eq_of_frameShadow_eq :=
    framedExtensionality.packedComparison_eq_of_framedShadow_eq

/-- Framed reflection is derived from framed-shadow extensionality plus the comparison between
literal packed equality and the abstract structured-comparison relation. -/
def RecognizedMMQFramedReflectionFromShadowExtensionality
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (relationOnImage : RecognizedMMQStructuredComparisonForwardOnRecognizedImage target)
    (framedExtensionality : RecognizedMMQFramedShadowExtensionalityOnImage target) :
    RecognizedMMQPeriodTargetSkeleton.RecognizedMMQFramedReflectionObligation
      (ctx := ctx) target where
  theoremTarget := by
    intro M N f g hShadowFamily
    have hPacked :=
      framedExtensionality.packedComparison_eq_of_framedShadow_eq
        f g hShadowFamily
    exact relationOnImage.structuredEq_of_packedComparison_eq f g hPacked

/-- Framed reflection is derived from matrix-coefficient separation plus the comparison between
literal packed equality and the abstract structured-comparison relation. -/
def RecognizedMMQFramedReflectionFromMatrixCoefficientSeparation
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (relationOnImage : RecognizedMMQStructuredComparisonForwardOnRecognizedImage target)
    (framedSeparation : RecognizedMMQFramedMatrixCoefficientSeparation target) :
    RecognizedMMQPeriodTargetSkeleton.RecognizedMMQFramedReflectionObligation
      (ctx := ctx) target where
  theoremTarget :=
    (RecognizedMMQFramedReflectionFromShadowExtensionality
      target
      relationOnImage
      (framedShadowExtensionality_of_matrixCoefficientSeparation target framedSeparation)).theoremTarget

end ClassicalBridge
end TraceCalc