import TraceCalc.ClassicalPeriods.ReverseMath
import TraceCalc.ClassicalPeriods.Examples
import TraceCalc.ClassicalPeriods.FramedPeriodsConcrete
import TraceCalc.ClassicalPeriods.GeometricLocalization
import TraceCalc.ClassicalPeriods.GeometricRealizations
import TraceCalc.ClassicalPeriods.ComparisonBoundaryRecovery
import TraceCalc.LayerB.RealObjects.InternalManuscriptTargets

open CategoryTheory

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Lower scalar-realization data for deriving scalar-shadow reflection.  The function field is
kept under an explicitly named realization package rather than on the final target record, so the
target is not itself a theorem-smuggling container. -/
structure ScalarToStructuredReflectionData
    (Context : ClassicalComparisonContext)
    (MotiveCategory : Type u) [Category MotiveCategory]
    (objectComparison : MotiveCategory → ClassicalStructuredComparisonObject Context)
    (morphismStructuredComparison :
      {X Y : MotiveCategory} → (f : X ⟶ Y) →
        ClassicalStructuredComparisonMorphism (objectComparison X) (objectComparison Y))
    (structuredComparisonEquality : StructuredComparisonEquality Context)
    (scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism Context)) where
  scalarRealizationData : Prop
  comparisonData : Prop
  reconstructionData : Prop
  theoremFromData :
    ∀ {X Y : MotiveCategory} (f g : X ⟶ Y),
      scalarShadow.equalityRelation
        (scalarShadow.shadowOf
          (packStructuredComparisonMorphism
            (objectComparison X)
            (objectComparison Y)
            (morphismStructuredComparison f)))
        (scalarShadow.shadowOf
          (packStructuredComparisonMorphism
            (objectComparison X)
            (objectComparison Y)
            (morphismStructuredComparison g))) →
      structuredComparisonEquality.relates
        (packStructuredComparisonMorphism
          (objectComparison X)
          (objectComparison Y)
          (morphismStructuredComparison f))
        (packStructuredComparisonMorphism
          (objectComparison X)
          (objectComparison Y)
          (morphismStructuredComparison g))

/-- Lower recognition/reconstruction data for deriving structured-comparison faithfulness. -/
structure StructuredComparisonFaithfulnessData
    (Context : ClassicalComparisonContext)
    (MotiveCategory : Type u) [Category MotiveCategory]
    (objectComparison : MotiveCategory → ClassicalStructuredComparisonObject Context)
    (morphismStructuredComparison :
      {X Y : MotiveCategory} → (f : X ⟶ Y) →
        ClassicalStructuredComparisonMorphism (objectComparison X) (objectComparison Y))
    (structuredComparisonEquality : StructuredComparisonEquality Context) where
  classicalRecognitionData : Prop
  morphismReconstructionData : Prop
  structuredTransportData : Prop
  theoremFromData :
    ∀ {X Y : MotiveCategory} (f g : X ⟶ Y),
      structuredComparisonEquality.relates
        (packStructuredComparisonMorphism
          (objectComparison X)
          (objectComparison Y)
          (morphismStructuredComparison f))
        (packStructuredComparisonMorphism
          (objectComparison X)
          (objectComparison Y)
          (morphismStructuredComparison g)) →
        f = g

/-- Classical Grothendieck period-faithfulness target stated against mathlib-facing categorical
and linear-algebraic interfaces.

The manuscript's hard statement is morphism-level: equality of basis-free period shadows should
force equality of the corresponding motivic morphisms. The object assignment is retained so the
morphism datum can be expressed as a structured comparison package between the source and target
fibers of a motive morphism. -/
structure ClassicalGrothendieckPeriodFaithfulnessTarget where
  Context : ClassicalComparisonContext
  MotiveCategory : Type u
  [instMotiveCategory : Category MotiveCategory]
  BettiCategory : Type v
  DeRhamCategory : Type w
  [instBettiCategory : Category BettiCategory]
  [instDeRhamCategory : Category DeRhamCategory]
  BettiRealization : MotiveCategory ⥤ BettiCategory
  DeRhamRealization : MotiveCategory ⥤ DeRhamCategory
  objectComparison : MotiveCategory → ClassicalStructuredComparisonObject Context
  morphismStructuredComparison :
    {X Y : MotiveCategory} → (f : X ⟶ Y) →
      ClassicalStructuredComparisonMorphism (objectComparison X) (objectComparison Y)
  structuredComparisonEquality : StructuredComparisonEquality Context
  scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism Context)
  scalarShadowEquality : ScalarShadowEquality (SomeStructuredComparisonMorphism Context) scalarShadow
  classicalPeriodEvaluationIsBasisFree : Prop
  bettiScalarExtensionFaithfulnessTarget : Prop
  scalarToStructuredReflectionData :
    ScalarToStructuredReflectionData
      Context
      MotiveCategory
      objectComparison
      morphismStructuredComparison
      structuredComparisonEquality
      scalarShadow
  structuredComparisonFaithfulnessData :
    StructuredComparisonFaithfulnessData
      Context
      MotiveCategory
      objectComparison
      morphismStructuredComparison
      structuredComparisonEquality

attribute [instance]
  ClassicalGrothendieckPeriodFaithfulnessTarget.instMotiveCategory
  ClassicalGrothendieckPeriodFaithfulnessTarget.instBettiCategory
  ClassicalGrothendieckPeriodFaithfulnessTarget.instDeRhamCategory

namespace ClassicalGrothendieckPeriodFaithfulnessTarget

/-- Sigma-package the morphism comparison datum attached to a motive morphism. -/
def packedMorphismComparison
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w})
    {X Y : target.MotiveCategory} (f : X ⟶ Y) : SomeStructuredComparisonMorphism target.Context :=
  ⟨target.objectComparison X, target.objectComparison Y, target.morphismStructuredComparison f⟩

/-- Basis-free period datum attached to a motive morphism. -/
def basisFreePeriodDatum
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w})
    {X Y : target.MotiveCategory} (f : X ⟶ Y) :=
  (target.packedMorphismComparison f).basisFreePeriodMap

/-- Scalar shadow of the basis-free period datum attached to a motive morphism. -/
def scalarShadowOf
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w})
    {X Y : target.MotiveCategory} (f : X ⟶ Y) : target.scalarShadow.ScalarCarrier :=
  target.scalarShadow.shadowOf (target.packedMorphismComparison f)

/-- Structured comparison version of the classical period conjecture. -/
def structuredPeriodFaithfulnessStatement
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.MotiveCategory} (f g : X ⟶ Y),
    target.structuredComparisonEquality.relates
      (target.packedMorphismComparison f)
      (target.packedMorphismComparison g) →
    f = g

/-- Named reflection theorem target: scalar-shadow equality should recover structured comparison
equality. In the manuscript this is the coarse-scalar descent step below the basis-free datum. -/
def ScalarShadowReflectsStructuredComparisonTarget
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.MotiveCategory} (f g : X ⟶ Y),
    target.scalarShadow.equalityRelation (target.scalarShadowOf f) (target.scalarShadowOf g) →
      target.structuredComparisonEquality.relates
        (target.packedMorphismComparison f)
        (target.packedMorphismComparison g)

/-- Intermediate theorem target matching the manuscript's `per(f)` layer. -/
def BasisFreePeriodMapEqualityStatement
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w})
    (basisEq : BasisFreePeriodMapEquality target.Context) : Prop :=
  ∀ {X Y : target.MotiveCategory} (f g : X ⟶ Y),
    basisEq.relates
      (target.packedMorphismComparison f)
      (target.packedMorphismComparison g)

/-- Phase 8 reconstruction wall: equality of basis-free period maps should already recover literal
equality of the packed structured comparison package attached to a fixed motive source/target
pair. This is the exact `per(f) -> Percmp(f)` theorem surface before any abstract equality
relation is applied. -/
def PackedMorphismComparisonEqualityStatement
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.MotiveCategory} (f g : X ⟶ Y),
    target.basisFreePeriodDatum f = target.basisFreePeriodDatum g →
      target.packedMorphismComparison f = target.packedMorphismComparison g

/-- Scalar-shadow equality descends to the basis-free period layer. -/
def ScalarShadowReflectsBasisFreePeriodMapStatement
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w})
    (basisEq : BasisFreePeriodMapEquality target.Context) : Prop :=
  ∀ {X Y : target.MotiveCategory} (f g : X ⟶ Y),
    target.scalarShadow.equalityRelation (target.scalarShadowOf f) (target.scalarShadowOf g) →
      basisEq.relates
        (target.packedMorphismComparison f)
        (target.packedMorphismComparison g)

/-- Named reflection theorem target: structured comparison equality is the hard faithfulness core
immediately above motivic morphism equality. -/
def StructuredComparisonFaithfulnessTarget
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) : Prop :=
  target.structuredPeriodFaithfulnessStatement

/-- Derived scalar-shadow reflection theorem, projected from lower scalar realization data. -/
def scalarEqualityReflectsStructuredComparison
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) :
    target.ScalarShadowReflectsStructuredComparisonTarget :=
  target.scalarToStructuredReflectionData.theoremFromData

/-- Derived structured-comparison faithfulness theorem, projected from lower recognition data. -/
def structuredComparisonReflectsMorphismEquality
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) :
    target.StructuredComparisonFaithfulnessTarget :=
  target.structuredComparisonFaithfulnessData.theoremFromData

/-- Final classical theorem target: equality in the scalar period shadow reflects equality of the
corresponding motivic morphisms. -/
def faithfulnessStatement
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.MotiveCategory} (f g : X ⟶ Y),
    target.scalarShadow.equalityRelation (target.scalarShadowOf f) (target.scalarShadowOf g) →
      f = g

theorem faithfulnessStatement_of_reflection
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) :
    target.faithfulnessStatement := by
  intro X Y f g hScalar
  exact target.structuredComparisonReflectsMorphismEquality f g
    (target.scalarEqualityReflectsStructuredComparison f g hScalar)

/-- Structured comparison equality already implies the intermediate structured theorem target. -/
theorem structuredPeriodFaithfulnessStatement_of_reflection
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) :
    target.structuredPeriodFaithfulnessStatement :=
  target.structuredComparisonReflectsMorphismEquality

/-- Pointwise soundness of the scalar shadow used in the final target. -/
def scalarShadowSoundness
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) :
    ScalarShadowSoundness
      target.MotiveCategory
      target.Context
      (fun {X Y} (f : X ⟶ Y) => target.packedMorphismComparison f)
      target.scalarShadow
      (fun {X Y} (f : X ⟶ Y) => target.scalarShadowOf f) where
  theoremTarget := by
    intro X Y f
    rfl

/-- Basis-free reflection stage isolating the manuscript's `per(f)` layer from the full
structured comparison package `Percmp(f)`. -/
structure BasisFreePeriodReflectionStage
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) where
  basisFreePeriodMapEquality : BasisFreePeriodMapEquality target.Context
  scalarShadowReflectsBasisFree :
    target.ScalarShadowReflectsBasisFreePeriodMapStatement basisFreePeriodMapEquality
  basisFreeReflectsStructured :
    BasisFreePeriodMapReflectsStructuredComparison
      target.Context
      basisFreePeriodMapEquality
      target.structuredComparisonEquality

theorem BasisFreePeriodReflectionStage.toStructuredComparisonReflectionTarget
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w})
    (stage : BasisFreePeriodReflectionStage target) :
    target.ScalarShadowReflectsStructuredComparisonTarget := by
  intro X Y f g hScalar
  exact stage.basisFreeReflectsStructured.theoremTarget
    (target.packedMorphismComparison f)
    (target.packedMorphismComparison g)
    (stage.scalarShadowReflectsBasisFree f g hScalar)

/-- Cheap sanity tomography core: probe equality is definitionally packed structured comparison
equality, so tomography is tautological. -/
def tautologicalTomographyCore
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) :
    ClassicalPeriodTomographyCore target.Context target.structuredComparisonEquality :=
  ClassicalPeriods.tautologicalTomographyCore target.Context target.structuredComparisonEquality

/-- Cheap sanity probe family: the single probe is the packed structured comparison datum itself. -/
def tautologicalProbeFamily
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) :
    ScalarProbeFamily target.Context :=
  ClassicalPeriods.tautologicalProbeFamily target.Context target.structuredComparisonEquality

/-- Fixed-object reconstruction packages the exact remaining Phase 8 burden at the classical
target level. -/
structure PackedComparisonReconstructionStage
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) where
  fixedObjectReconstruction :
    ∀ (X Y : target.MotiveCategory),
      FixedObjectPackedComparisonReconstruction
        target.Context
        (target.objectComparison X)
        (target.objectComparison Y)

theorem PackedComparisonReconstructionStage.toPackedMorphismComparisonEqualityStatement
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w})
    (stage : PackedComparisonReconstructionStage target) :
    target.PackedMorphismComparisonEqualityStatement := by
  intro X Y f g hBasis
  change
      (target.morphismStructuredComparison f).basisFreePeriodMap =
        (target.morphismStructuredComparison g).basisFreePeriodMap at hBasis
  let left : ClassicalStructuredComparisonMorphism
      (target.objectComparison X) (target.objectComparison Y) :=
    target.morphismStructuredComparison f
  let right : ClassicalStructuredComparisonMorphism
      (target.objectComparison X) (target.objectComparison Y) :=
    target.morphismStructuredComparison g
  have hBasis' : left.basisFreePeriodMap = right.basisFreePeriodMap := by
    simpa using hBasis
  let reconstruction := stage.fixedObjectReconstruction X Y
  have hMorphism : left = right :=
    reconstruction.theoremTarget left right hBasis'
  have hPacked := congrArg
    (fun morphism =>
      packStructuredComparisonMorphism
        (target.objectComparison X)
        (target.objectComparison Y)
        morphism)
    hMorphism
  change
      packStructuredComparisonMorphism
          (target.objectComparison X)
          (target.objectComparison Y)
          (target.morphismStructuredComparison f) =
        packStructuredComparisonMorphism
          (target.objectComparison X)
          (target.objectComparison Y)
          (target.morphismStructuredComparison g)
  simpa [left, right] using hPacked

end ClassicalGrothendieckPeriodFaithfulnessTarget

/-- Lower framed-realization data for deriving framed-shadow reflection to structured comparison. -/
structure FramedToStructuredReflectionData
    (baseTarget : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w})
    (framedPeriodEquality : FramedPeriodEquality baseTarget.Context)
    (framedPeriodShadow : ScalarPeriodShadow (SomeFramedPeriodDatum baseTarget.Context))
    (framedPeriodOf :
      {X Y : baseTarget.MotiveCategory} → (X ⟶ Y) → SomeFramedPeriodDatum baseTarget.Context) where
  framedRealizationData : Prop
  framedComparisonData : Prop
  framedReconstructionData : Prop
  theoremFromData :
    ∀ {X Y : baseTarget.MotiveCategory} (f g : X ⟶ Y),
      framedPeriodShadow.equalityRelation
        (framedPeriodShadow.shadowOf (framedPeriodOf f))
        (framedPeriodShadow.shadowOf (framedPeriodOf g)) →
      baseTarget.structuredComparisonEquality.relates
        (baseTarget.packedMorphismComparison f)
        (baseTarget.packedMorphismComparison g)

/-- Framed-period refinement of the classical target.

The framed lane keeps a separate equality notion for structured comparison objects so the theorem
target can distinguish:
1. framed/scalar period equality,
2. reflection to structured comparison equality,
3. reflection from structured comparison equality to equality of morphisms. -/
structure FramedPeriodConjectureTarget where
  baseTarget : ClassicalGrothendieckPeriodFaithfulnessTarget
  framedPeriodEquality : FramedPeriodEquality baseTarget.Context
  framedPeriodOperations : FramedPeriodOperations baseTarget.Context
  framedPeriodShadow : ScalarPeriodShadow (SomeFramedPeriodDatum baseTarget.Context)
  framedShadowEquality :
    ScalarShadowEquality (SomeFramedPeriodDatum baseTarget.Context) framedPeriodShadow
  framedScalarShadowAlgebra : FramedScalarShadowAlgebra baseTarget.Context framedPeriodShadow
  framedPeriodOperationLaws :
    FramedPeriodOperationLaws
      baseTarget.Context
      framedPeriodOperations
      framedPeriodShadow
      framedScalarShadowAlgebra
  framedPeriodOf :
    {X Y : baseTarget.MotiveCategory} → (X ⟶ Y) → SomeFramedPeriodDatum baseTarget.Context
  framedScalarToBaseScalar :
    framedPeriodShadow.ScalarCarrier → baseTarget.scalarShadow.ScalarCarrier
  framedShadowToBaseShadowCompatible : Prop
  scalarShadow_agrees_with_framedShadow :
    ∀ {X Y : baseTarget.MotiveCategory} (f : X ⟶ Y),
      baseTarget.scalarShadow.equalityRelation
        (baseTarget.scalarShadowOf f)
        (framedScalarToBaseScalar (framedPeriodShadow.shadowOf (framedPeriodOf f)))
  framedPeriodEqualityReflectsShadowEquality : Prop
  scalarShadowReflectsFramedEquality :
    ∀ {X Y : baseTarget.MotiveCategory} (f g : X ⟶ Y),
      framedPeriodShadow.equalityRelation
        (framedPeriodShadow.shadowOf (framedPeriodOf f))
        (framedPeriodShadow.shadowOf (framedPeriodOf g)) →
      framedPeriodEquality.relates (framedPeriodOf f) (framedPeriodOf g)
  framedToStructuredReflectionData :
    FramedToStructuredReflectionData
      baseTarget
      framedPeriodEquality
      framedPeriodShadow
      framedPeriodOf

namespace FramedPeriodConjectureTarget

/-- The framed scalar shadow attached to a motive morphism. -/
def framedShadowOf
    (target : FramedPeriodConjectureTarget.{u, v, w})
    {X Y : target.baseTarget.MotiveCategory} (f : X ⟶ Y) :
    target.framedPeriodShadow.ScalarCarrier :=
  target.framedPeriodShadow.shadowOf (target.framedPeriodOf f)

/-- Equality of framed scalar shadows, viewed as the first level of the equality ladder. -/
def scalarShadowEqualityStatement
    (target : FramedPeriodConjectureTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
    target.framedPeriodShadow.equalityRelation
      (target.framedShadowOf f)
      (target.framedShadowOf g)

/-- Equality of framed witnesses, viewed as the second level of the equality ladder. -/
def framedPeriodEqualityStatement
    (target : FramedPeriodConjectureTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
    target.framedPeriodEquality.relates
      (target.framedPeriodOf f)
      (target.framedPeriodOf g)

/-- Equality of packed structured comparison morphisms, viewed as the third level of the ladder. -/
def structuredComparisonEqualityStatement
    (target : FramedPeriodConjectureTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
    target.baseTarget.structuredComparisonEquality.relates
      (target.baseTarget.packedMorphismComparison f)
      (target.baseTarget.packedMorphismComparison g)

/-- Equality of motive morphisms, viewed as the last level of the equality ladder. -/
def motiveMorphismEqualityStatement
    (target : FramedPeriodConjectureTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
    (definitionalMotiveMorphismEqualityTarget target.baseTarget.MotiveCategory).relates f g

/-- Explicit packaging of the four equality levels that the manuscript distinguishes. -/
def equalityLadder
    (target : FramedPeriodConjectureTarget.{u, v, w}) :
    ClassicalPeriodEqualityLadder
      target.baseTarget.MotiveCategory
      target.baseTarget.Context
      target.framedPeriodShadow
      target.framedPeriodEquality
      target.baseTarget.structuredComparisonEquality
      (definitionalMotiveMorphismEqualityTarget target.baseTarget.MotiveCategory)
      (fun {X Y} (f : X ⟶ Y) => target.framedPeriodOf f)
      (fun {X Y} (f : X ⟶ Y) => target.baseTarget.packedMorphismComparison f) where
  scalarShadowLevel := fun {X Y} (f g : X ⟶ Y) =>
    target.framedPeriodShadow.equalityRelation
      (target.framedShadowOf f)
      (target.framedShadowOf g)
  framedLevel := fun {X Y} (f g : X ⟶ Y) =>
    target.framedPeriodEquality.relates
      (target.framedPeriodOf f)
      (target.framedPeriodOf g)
  structuredLevel := fun {X Y} (f g : X ⟶ Y) =>
    target.baseTarget.structuredComparisonEquality.relates
      (target.baseTarget.packedMorphismComparison f)
      (target.baseTarget.packedMorphismComparison g)
  morphismLevel := fun {X Y} (f g : X ⟶ Y) =>
    (definitionalMotiveMorphismEqualityTarget target.baseTarget.MotiveCategory).relates f g

/-- Pointwise soundness of the framed scalar shadow used in the framed lane. -/
def framedShadowSoundness
    (target : FramedPeriodConjectureTarget.{u, v, w}) :
    FramedShadowSoundness
      target.baseTarget.MotiveCategory
      target.baseTarget.Context
      (fun {X Y} (f : X ⟶ Y) => target.framedPeriodOf f)
      target.framedPeriodShadow
      (fun {X Y} (f : X ⟶ Y) => target.framedShadowOf f) where
  theoremTarget := by
    intro X Y f
    rfl

/-- Pointwise compatibility between the framed scalar shadow and the scalar shadow of the packed
comparison package. -/
def framedToScalarCompatibility
    (target : FramedPeriodConjectureTarget.{u, v, w}) :
    FramedToScalarCompatibility
      target.baseTarget.MotiveCategory
      target.baseTarget.Context
      (fun {X Y} (f : X ⟶ Y) => target.framedPeriodOf f)
      (fun {X Y} (f : X ⟶ Y) => target.baseTarget.packedMorphismComparison f)
      target.framedPeriodShadow
      target.baseTarget.scalarShadow
      target.framedScalarToBaseScalar where
  theoremTarget := target.scalarShadow_agrees_with_framedShadow

/-- Pairwise compatibility needed to transport an equality of base scalar shadows into the framed
shadow relation that feeds the hard reflection core. -/
def baseScalarToFramedShadowStatement
    (target : FramedPeriodConjectureTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
    target.baseTarget.scalarShadow.equalityRelation
      (target.baseTarget.scalarShadowOf f)
      (target.baseTarget.scalarShadowOf g) →
    target.framedPeriodShadow.equalityRelation
      (target.framedShadowOf f)
      (target.framedShadowOf g)

/-- Exact theorem-target burden for scalar shadow to framed-period reflection. -/
def scalarShadowReflectsFramedEqualityStatement
    (target : FramedPeriodConjectureTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
    target.framedPeriodShadow.equalityRelation
      (target.framedShadowOf f)
      (target.framedShadowOf g) →
    target.framedPeriodEquality.relates (target.framedPeriodOf f) (target.framedPeriodOf g)

/-- Exact theorem-target burden carried by the framed-period lane. -/
def reflectionStatement (target : FramedPeriodConjectureTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
    target.framedPeriodShadow.equalityRelation
      (target.framedShadowOf f)
      (target.framedShadowOf g) →
    target.baseTarget.structuredComparisonEquality.relates
      (target.baseTarget.packedMorphismComparison f)
      (target.baseTarget.packedMorphismComparison g)

/-- Derived framed-shadow reflection theorem, projected from lower framed realization data. -/
def framedEqualityReflectsStructuredComparison
    (target : FramedPeriodConjectureTarget.{u, v, w}) :
    target.reflectionStatement :=
  target.framedToStructuredReflectionData.theoremFromData

/-- Hard theorem-target core for the framed lane: scalar shadow equality descends through framed
equality and then back up to structured comparison equality. -/
def scalarShadowReflectsStructuredComparisonStatement
    (target : FramedPeriodConjectureTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
    target.framedPeriodShadow.equalityRelation
      (target.framedShadowOf f)
      (target.framedShadowOf g) →
    target.baseTarget.structuredComparisonEquality.relates
      (target.baseTarget.packedMorphismComparison f)
      (target.baseTarget.packedMorphismComparison g)

/-- Framed version of the classical period-faithfulness target. -/
def faithfulnessStatement (target : FramedPeriodConjectureTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
    target.framedPeriodShadow.equalityRelation
      (target.framedShadowOf f)
      (target.framedShadowOf g) →
    f = g

theorem faithfulnessStatement_of_reflection
    (target : FramedPeriodConjectureTarget.{u, v, w}) :
    target.faithfulnessStatement := by
  intro X Y f g hFramed
  have hStructured :
      target.baseTarget.structuredComparisonEquality.relates
        (target.baseTarget.packedMorphismComparison f)
        (target.baseTarget.packedMorphismComparison g) :=
    target.framedEqualityReflectsStructuredComparison f g hFramed
  exact target.baseTarget.structuredComparisonReflectsMorphismEquality f g
    hStructured

theorem scalarShadowReflectsStructuredComparison_of_reflection
    (target : FramedPeriodConjectureTarget.{u, v, w}) :
    target.scalarShadowReflectsStructuredComparisonStatement :=
  target.framedEqualityReflectsStructuredComparison

end FramedPeriodConjectureTarget

/-- Framed reflection core separating structural transport from the hard reflection burden. -/
structure ClassicalPeriodReflectionCore
    (target : FramedPeriodConjectureTarget.{u, v, w}) where
  scalarShadowReflectsFramed :
    ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
      target.framedPeriodShadow.equalityRelation
        (target.framedShadowOf f)
        (target.framedShadowOf g) →
      target.framedPeriodEquality.relates
        (target.framedPeriodOf f)
        (target.framedPeriodOf g)
  framedEqualityReflectsStructured :
    ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
      target.framedPeriodEquality.relates
        (target.framedPeriodOf f)
        (target.framedPeriodOf g) →
      target.baseTarget.structuredComparisonEquality.relates
        (target.baseTarget.packedMorphismComparison f)
        (target.baseTarget.packedMorphismComparison g)

theorem ClassicalPeriodReflectionCore.toStructuredComparisonReflection
    (target : FramedPeriodConjectureTarget.{u, v, w})
    (core : ClassicalPeriodReflectionCore target) :
    target.scalarShadowReflectsStructuredComparisonStatement := by
  intro X Y f g hScalar
  exact core.framedEqualityReflectsStructured
    f
    g
    (core.scalarShadowReflectsFramed
      f
      g
      hScalar)

/-- Target-specific tomography core: probes determine the basis-free period map, and the basis-free
period map determines the packed structured comparison package. -/
structure ClassicalPeriodTomographyTarget
    (target : FramedPeriodConjectureTarget.{u, v, w}) where
  tomographyCore :
    ClassicalPeriodTomographyCore
      target.baseTarget.Context
      target.baseTarget.structuredComparisonEquality
  probeSoundness :
    ProbeSoundness
      target.baseTarget.MotiveCategory
      target.baseTarget.Context
      tomographyCore.probeFamily
      target.framedPeriodEquality
      (fun {X Y} (f : X ⟶ Y) => target.framedPeriodOf f)
      (fun {X Y} (f : X ⟶ Y) => target.baseTarget.packedMorphismComparison f)

/-- Probe equality on packed comparison morphisms, induced by the target-specific tomography core. -/
def ClassicalPeriodTomographyTarget.probeEqualityStatement
    {target : FramedPeriodConjectureTarget.{u, v, w}}
    (tomography : ClassicalPeriodTomographyTarget target) : Prop :=
  ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
    ProbeEquality
      tomography.tomographyCore.probeFamily
      (target.baseTarget.packedMorphismComparison f)
      (target.baseTarget.packedMorphismComparison g)

/-- Framed-period equality yields tomography probe equality through the packaged probe soundness
input. This exposes the exact interface consumed by the tomography core before reflection. -/
theorem ClassicalPeriodTomographyTarget.probeEquality_of_framedEquality
    {target : FramedPeriodConjectureTarget.{u, v, w}}
    (tomography : ClassicalPeriodTomographyTarget target)
    {X Y : target.baseTarget.MotiveCategory}
    (f g : X ⟶ Y)
    (hFramed :
      target.framedPeriodEquality.relates
        (target.framedPeriodOf f)
        (target.framedPeriodOf g)) :
    ProbeEquality
      tomography.tomographyCore.probeFamily
      (target.baseTarget.packedMorphismComparison f)
      (target.baseTarget.packedMorphismComparison g) :=
  tomography.probeSoundness.theoremTarget f g hFramed

/-- The main tomography consequence at the target level: enough probes recover packed structured
comparison equality. -/
theorem classicalPeriodTomographyTarget_toStructuredComparisonEquality
    (target : FramedPeriodConjectureTarget.{u, v, w})
    (tomography : ClassicalPeriodTomographyTarget target) :
    ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
      ProbeEquality
        tomography.tomographyCore.probeFamily
        (target.baseTarget.packedMorphismComparison f)
        (target.baseTarget.packedMorphismComparison g) →
      target.baseTarget.structuredComparisonEquality.relates
        (target.baseTarget.packedMorphismComparison f)
        (target.baseTarget.packedMorphismComparison g) := by
  intro X Y f g hProbe
  exact tomography.tomographyCore.toStructuredComparisonEquality
    (target.baseTarget.packedMorphismComparison f)
    (target.baseTarget.packedMorphismComparison g)
    hProbe

/-- Framed equality feeds the tomography core and therefore already yields structured comparison
equality before the reflection-core packaging step. -/
theorem ClassicalPeriodTomographyTarget.structuredComparisonEquality_of_framedEquality
    {target : FramedPeriodConjectureTarget.{u, v, w}}
    (tomography : ClassicalPeriodTomographyTarget target)
    {X Y : target.baseTarget.MotiveCategory}
    (f g : X ⟶ Y)
    (hFramed :
      target.framedPeriodEquality.relates
        (target.framedPeriodOf f)
        (target.framedPeriodOf g)) :
    target.baseTarget.structuredComparisonEquality.relates
      (target.baseTarget.packedMorphismComparison f)
      (target.baseTarget.packedMorphismComparison g) :=
  classicalPeriodTomographyTarget_toStructuredComparisonEquality
    target
    tomography
    f
    g
    (tomography.probeEquality_of_framedEquality f g hFramed)

/-- Tomography plus probe soundness assembles into the Phase 5 reflection core. -/
theorem classicalPeriodTomographyCore_toReflectionCore
    (target : FramedPeriodConjectureTarget.{u, v, w})
    (tomography : ClassicalPeriodTomographyTarget target) :
    ClassicalPeriodReflectionCore target := by
  refine {
    scalarShadowReflectsFramed := ?_,
    framedEqualityReflectsStructured := ?_
  }
  · intro X Y f g hScalar
    exact target.scalarShadowReflectsFramedEquality f g hScalar
  · intro X Y f g hFramed
    exact tomography.structuredComparisonEquality_of_framedEquality f g hFramed

/-- Cheap sanity target: tautological packed probes recover the reflection core whenever the
framed reflection step is already packaged. -/
def tautologicalTomographyTarget
    (target : FramedPeriodConjectureTarget.{u, v, w})
    (core : ClassicalPeriodReflectionCore target) :
    ClassicalPeriodTomographyTarget target where
  tomographyCore := target.baseTarget.tautologicalTomographyCore
  probeSoundness := {
    theoremTarget := by
      intro X Y f g hFramed
      intro probe
      cases probe
      exact core.framedEqualityReflectsStructured f g hFramed
  }

/-- Sanity theorem: the tautological tomography package feeds the same reflection core. -/
theorem tautologicalTomography_toReflectionCore
    (target : FramedPeriodConjectureTarget.{u, v, w})
    (core : ClassicalPeriodReflectionCore target) :
    ClassicalPeriodReflectionCore target :=
  core

/-- Faithfulness decomposition exposing the theorem ladder from coarse scalar equality to literal
morphism equality. -/
structure ClassicalPeriodFaithfulnessDecomposition
    (target : FramedPeriodConjectureTarget.{u, v, w}) where
  basisFreeReflection :
    ClassicalGrothendieckPeriodFaithfulnessTarget.BasisFreePeriodReflectionStage
      target.baseTarget
  reflectionCore : ClassicalPeriodReflectionCore target
  scalarShadowSoundnessCore :
    ScalarShadowSoundness
      target.baseTarget.MotiveCategory
      target.baseTarget.Context
      (fun {X Y} (f : X ⟶ Y) => target.baseTarget.packedMorphismComparison f)
      target.baseTarget.scalarShadow
      (fun {X Y} (f : X ⟶ Y) => target.baseTarget.scalarShadowOf f)
  framedShadowSoundnessCore :
    FramedShadowSoundness
      target.baseTarget.MotiveCategory
      target.baseTarget.Context
      (fun {X Y} (f : X ⟶ Y) => target.framedPeriodOf f)
      target.framedPeriodShadow
      (fun {X Y} (f : X ⟶ Y) => target.framedShadowOf f)
  framedToScalarCompatibilityCore :
    FramedToScalarCompatibility
      target.baseTarget.MotiveCategory
      target.baseTarget.Context
      (fun {X Y} (f : X ⟶ Y) => target.framedPeriodOf f)
      (fun {X Y} (f : X ⟶ Y) => target.baseTarget.packedMorphismComparison f)
      target.framedPeriodShadow
      target.baseTarget.scalarShadow
      target.framedScalarToBaseScalar
  scalarFramedCompatibility : target.baseScalarToFramedShadowStatement
  structuredFaithfulness :
    StructuredComparisonFaithfulnessCore
      target.baseTarget.MotiveCategory
      target.baseTarget.Context
      target.baseTarget.structuredComparisonEquality
      (fun {X Y} (f : X ⟶ Y) => target.baseTarget.packedMorphismComparison f)
      (definitionalMotiveMorphismEqualityTarget target.baseTarget.MotiveCategory)

theorem classicalPeriodFaithfulnessDecomposition_toFramedFaithfulnessTarget
  (target : FramedPeriodConjectureTarget.{u, v, w})
  (decomposition : ClassicalPeriodFaithfulnessDecomposition target) :
    target.faithfulnessStatement := by
  intro X Y f g hScalar
  have hStructured :=
    ClassicalPeriodReflectionCore.toStructuredComparisonReflection
      target
      decomposition.reflectionCore
      f
      g
      hScalar
  have hMorphismEq := decomposition.structuredFaithfulness.theoremTarget f g hStructured
  exact hMorphismEq

theorem classicalPeriodFaithfulnessDecomposition_toGrothendieckTarget
    (target : FramedPeriodConjectureTarget.{u, v, w})
    (decomposition : ClassicalPeriodFaithfulnessDecomposition target) :
    target.baseTarget.faithfulnessStatement := by
  intro X Y f g hScalar
  have hFramed := decomposition.scalarFramedCompatibility f g hScalar
  have hStructured :=
    ClassicalPeriodReflectionCore.toStructuredComparisonReflection
      target
      decomposition.reflectionCore
      f
      g
      hFramed
  have hMorphismEq := decomposition.structuredFaithfulness.theoremTarget f g hStructured
  exact hMorphismEq

/-- Exact final classical theorem target. -/
abbrev ClassicalGrothendieckPeriodFaithfulnessStatement :=
  ClassicalGrothendieckPeriodFaithfulnessTarget.faithfulnessStatement

/-- Exact framed-period theorem target. -/
abbrev ClassicalFramedPeriodConjectureStatement :=
  FramedPeriodConjectureTarget.faithfulnessStatement

/-- Stable exported names intended for later bridge consumption. -/
abbrev TargetStructuredComparisonObject (ctx : ClassicalComparisonContext) :=
  ClassicalStructuredComparisonObject ctx
abbrev TargetStructuredComparisonMorphism
    {ctx : ClassicalComparisonContext}
    (source target : ClassicalStructuredComparisonObject ctx) :=
  ClassicalStructuredComparisonMorphism source target
abbrev TargetFramedPeriodDatum
    {ctx : ClassicalComparisonContext}
    {source target : ClassicalStructuredComparisonObject ctx}
    (morphism : ClassicalStructuredComparisonMorphism source target)
    (pairingData : PeriodPairingData morphism) :=
  FramedPeriodDatum morphism pairingData
abbrev TargetScalarShadow (α : Type u) := ScalarPeriodShadow α
abbrev TargetFinalFaithfulnessObject := ClassicalGrothendieckPeriodFaithfulnessTarget

/-- Stable exported name for later bridge consumption of the framed reflection core. -/
abbrev TargetReflectionTheoremObject := FramedPeriodConjectureTarget

/-- Stable exported name for later bridge consumption of the decomposed reflection core. -/
abbrev TargetReflectionCoreObject := ClassicalPeriodReflectionCore

/-- Stable exported name for later bridge consumption of the faithfulness decomposition. -/
abbrev TargetFaithfulnessDecompositionObject := ClassicalPeriodFaithfulnessDecomposition

/-- Stable exported name for later bridge consumption of the reverse-math obligation object. -/
abbrev TargetReverseMathObject := ClassicalPeriodReverseMathObligations

/- Compact alias index for the theorem-target surface already closed inside
`PeriodConjectureTarget.lean`.

This namespace is intentionally small. It exists so future cleanup passes can re-use the current
period-conjecture target surface rather than adding parallel wrappers. -/
namespace PeriodConjectureTargetIndex

/-- Final morphism-level classical target. -/
abbrev BaseFaithfulnessTarget := ClassicalGrothendieckPeriodFaithfulnessTarget

/-- Framed refinement of the classical target. -/
abbrev FramedFaithfulnessTarget := FramedPeriodConjectureTarget

/-- Hard framed reflection core separating shadow reflection from structured faithfulness. -/
abbrev ReflectionCore := ClassicalPeriodReflectionCore

/-- Decomposed final assembly object. -/
abbrev FaithfulnessDecomposition := ClassicalPeriodFaithfulnessDecomposition

/-- Reverse-mathematics registry for the classical lane. -/
abbrev ReverseMathObligations := ClassicalPeriodReverseMathObligations

/-- Exact final classical theorem statement. -/
abbrev BaseFaithfulnessStatement := ClassicalGrothendieckPeriodFaithfulnessStatement

/-- Exact framed classical theorem statement. -/
abbrev FramedFaithfulnessStatement := ClassicalFramedPeriodConjectureStatement

/-- Final classical theorem from the already-packaged reflection target. -/
theorem baseFaithfulness_of_reflection
    (target : BaseFaithfulnessTarget.{u, v, w}) :
    target.faithfulnessStatement :=
  ClassicalGrothendieckPeriodFaithfulnessTarget.faithfulnessStatement_of_reflection target

/-- Final framed theorem from the already-packaged reflection target. -/
theorem framedFaithfulness_of_reflection
    (target : FramedFaithfulnessTarget.{u, v, w}) :
    target.faithfulnessStatement :=
  FramedPeriodConjectureTarget.faithfulnessStatement_of_reflection target

end PeriodConjectureTargetIndex

end ClassicalPeriods
end TraceCalc