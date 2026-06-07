import Boundary.OpenClosedLocalization
import Boundary.TateMotives

/-!
# Tate Stabilization Construction Surface

This file records the canonical Boundary-side construction surface for
Tate/`P1` stabilization above the minimal presentation package.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

namespace Boundary

open CategoryTheory

noncomputable section

/-- Canonical Boundary-side witness data for Tate stabilization: the chosen
composition package together with exactly the ambient categorical instances
needed to construct the canonical Tate datum from the actual motive map
`M(Spec k) ⟶ M(P¹_k)` and its distinguished triangle. The projective-line
owner object and basepoint are now taken from the canonical constructions in
`ProjectiveLineGeometry.lean`, so no separate proof payload is threaded here.
-/
structure BoundaryTateStabilizationWitnessData where
  composition : Boundary.CanonicalCompositionData (k := k)
  a1NisImplementation : CanonicalA1NisLocalizationImplementation composition
  localizationPresentation :
    OpenClosedLocalizationPresentationQ (Boundary.canonicalCategory composition)
  abelianLinearPST : Abelian (LinearPST (Boundary.canonicalCategory composition))
  hasDerivedLinearPST : HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))
  abelianA1Nis : Abelian (canonicalA1NisLocalization composition)
  hasDerivedA1Nis : HasDerivedCategory (canonicalA1NisLocalization composition)

namespace BoundaryTateStabilizationWitnessData

def projectiveLineData
    (witness : BoundaryTateStabilizationWitnessData (k := k)) :
    CanonicalProjectiveLineMotiveConstructionData witness.composition :=
  boundaryProjectiveLineMotiveConstructionData
    (composition := witness.composition)

/-- The canonical projective-line open/closed localization presentation
threaded through the Tate stabilization witness package. -/
def projectiveLineLocalizationPresentation
    (witness : BoundaryTateStabilizationWitnessData (k := k)) :
    OpenClosedLocalizationPresentationQ (Boundary.canonicalCategory witness.composition) :=
  witness.localizationPresentation

/-- The witness-threaded localization presentation is the canonical projective
line localization package. -/
theorem projectiveLineLocalizationPresentation_isCanonical
    (witness : BoundaryTateStabilizationWitnessData (k := k)) :
    witness.projectiveLineLocalizationPresentation =
      boundaryProjectiveLineLocalizationPresentation (k := k) witness.composition :=
  rfl

/-- The canonical Boundary Tate datum determined by the witness environment.
No additional choice is stored here: the datum is reconstructed from the
actual unit-to-`P¹` motive map each time it is needed. -/
def tateDatum
    (witness : BoundaryTateStabilizationWitnessData (k := k)) :
  BoundaryTateObjectConstructionData witness.composition := by
  letI := witness.abelianLinearPST
  letI := witness.hasDerivedLinearPST
  letI := witness.abelianA1Nis
  letI := witness.hasDerivedA1Nis
  letI := witness.a1NisImplementation.sourcePreadditive
  letI := witness.a1NisImplementation.localizedPreadditive
  letI : (canonicalA1NisLocalizationFunctor witness.composition).Additive :=
    canonicalA1NisLocalizationFunctor_additive
      witness.composition witness.a1NisImplementation
  letI : Limits.PreservesFiniteLimits
      (canonicalA1NisLocalizationFunctor witness.composition) :=
    canonicalA1NisLocalizationFunctor_preservesFiniteLimits
      witness.composition witness.a1NisImplementation
  letI : Limits.PreservesFiniteColimits
      (canonicalA1NisLocalizationFunctor witness.composition) :=
    canonicalA1NisLocalizationFunctor_preservesFiniteColimits
      witness.composition witness.a1NisImplementation
  exact Boundary.boundaryCanonicalTateObjectConstructionData
    (composition := witness.composition)

/-- Canonical motive-level comparison data linking the concrete Boundary
projective line, the reduced `P¹` cone object, and the Tate object determined
from it. This is the honest motivic seam behind Boundary-specialized Tate
stabilization. -/
structure CanonicalReducedProjectiveLineTateComparisonDataQ where
  projectiveLineMotive : canonicalEffectiveMotives witness.composition
  reducedProjectiveLineMotive : canonicalEffectiveMotives witness.composition
  tateObject : canonicalEffectiveMotives witness.composition
  unitToProjectiveLineMotive :
    canonicalUnitMotive witness.composition ⟶ projectiveLineMotive
  projectiveLineToReduced :
    projectiveLineMotive ⟶ reducedProjectiveLineMotive
  reducedToShiftedUnit :
    reducedProjectiveLineMotive ⟶
      (shiftFunctor (canonicalEffectiveMotives witness.composition) (1 : ℤ)).obj
        (canonicalUnitMotive witness.composition)
  reducedProjectiveLineConeData :
    ({ obj₁ := canonicalUnitMotive witness.composition
       obj₂ := projectiveLineMotive
       obj₃ := reducedProjectiveLineMotive
       mor₁ := unitToProjectiveLineMotive
       mor₂ := projectiveLineToReduced
       mor₃ := reducedToShiftedUnit } :
        CategoryTheory.Pretriangulated.Triangle
          (canonicalEffectiveMotives witness.composition)) ∈
      distTriang (canonicalEffectiveMotives witness.composition)
  tateObjectShiftedIsoReducedProjectiveLineData :
    Nonempty
      (((shiftFunctor (canonicalEffectiveMotives witness.composition) (2 : ℤ)).obj tateObject) ≅
        reducedProjectiveLineMotive)

/-- The canonical reduced-`P¹`/Tate comparison data extracted from the actual
Boundary Tate datum. -/
def reducedProjectiveLineTateComparisonData
    (witness : BoundaryTateStabilizationWitnessData (k := k)) :
  witness.CanonicalReducedProjectiveLineTateComparisonDataQ := by
  let tateData := witness.tateDatum
  rcases tateData.reducedProjectiveLine_isCone with ⟨projectiveLineToReduced, reducedToShiftedUnit, hTriangle⟩
  refine
    { projectiveLineMotive :=
        boundaryProjectiveLineMotive (composition := witness.composition)
      reducedProjectiveLineMotive := tateData.reducedProjectiveLineMotive
      tateObject := tateData.tateObject
      unitToProjectiveLineMotive :=
        boundaryUnitToProjectiveLineMotive (composition := witness.composition)
      projectiveLineToReduced := projectiveLineToReduced
      reducedToShiftedUnit := reducedToShiftedUnit
      reducedProjectiveLineConeData := hTriangle
      tateObjectShiftedIsoReducedProjectiveLineData :=
        tateData.tateObject_shifted_iso_reducedProjectiveLine }

end BoundaryTateStabilizationWitnessData

/-- The formal twist-by-Tate operation on minimal-presentation generators:
keep the smooth scheme and projector fixed and increment the Tate index by one. -/
def tateTwistShiftGenerator
    {category : SmCorQ (k := k)}
    (generator : MinimalPresentationGeneratorQ category) :
    MinimalPresentationGeneratorQ category where
  scheme := generator.scheme
  projector := generator.projector
  projectorIdempotentTarget := generator.projectorIdempotentTarget
  twist := generator.twist + 1

/-- Proof-relevant comparison between two minimal-presentation generators.
This is the concrete replacement for saying that two stabilization outputs are
"compatible" without specifying how their scheme, projector, and Tate index
align. -/
structure GeneratorComparisonDataQ
    {category : SmCorQ (k := k)}
    (lhs rhs : MinimalPresentationGeneratorQ category) where
  scheme_eq : lhs.scheme = rhs.scheme
  projector_eq : HEq lhs.projector rhs.projector
  twist_eq : lhs.twist = rhs.twist

namespace GeneratorComparisonDataQ

def refl
    {category : SmCorQ (k := k)}
    (generator : MinimalPresentationGeneratorQ category) :
    GeneratorComparisonDataQ generator generator :=
  ⟨rfl, HEq.rfl, rfl⟩

end GeneratorComparisonDataQ

/-- Canonical generator model for the Boundary-side projective line: identity
projector on the honest `P¹_k` object with zero Tate twist. -/
def canonicalProjectiveLineGeneratorModel
    {category : SmCorQ (k := k)}
    (witness : BoundaryTateStabilizationWitnessData (k := k)) :
    MinimalPresentationGeneratorQ category where
  scheme := boundaryProjectiveLineCanonicalObject (k := k)
  projector := 𝟙 _
  projectorIdempotentTarget := by
    letI := SmCorQCat category
    simp
  twist := 0

/-- Canonical generator model for the Boundary Tate object on the current
minimal-presentation surface: the unit scheme with identity projector and one
Tate twist.  This is the generator-level shadow of `Q(1)[2]`. -/
def canonicalTateGeneratorModel
    {category : SmCorQ (k := k)} :
    MinimalPresentationGeneratorQ category where
  scheme := canonicalUnitScheme (k := k)
  projector := 𝟙 _
  projectorIdempotentTarget := by
    letI := SmCorQCat category
    simp
  twist := 1

/-- Data that a chosen minimal-package generator really plays the role of the
canonical Boundary projective line. -/
structure CanonicalProjectiveLineGeneratorDataQ
    {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category)
    (witness : BoundaryTateStabilizationWitnessData (k := k))
    (idx : package.GeneratorIndex) where
  comparison :
    GeneratorComparisonDataQ
      (package.generator idx)
      (canonicalProjectiveLineGeneratorModel (category := category) witness)

/-- Data that a chosen minimal-package generator really plays the role of the
canonical Boundary Tate generator. -/
structure CanonicalTateGeneratorDataQ
    {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category)
    (idx : package.GeneratorIndex) where
  comparison :
    GeneratorComparisonDataQ
      (package.generator idx)
      (canonicalTateGeneratorModel (category := category) (k := k))

/-- Canonical comparison between the designated Boundary `P¹` generator and the
designated Boundary Tate generator, tied to the motive-level reduced-`P¹`/Tate
comparison extracted from the actual distinguished triangle. -/
structure CanonicalBoundaryTateP1ComparisonDataQ
    {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category)
    (witness : BoundaryTateStabilizationWitnessData (k := k))
    (tateGenerator p1Generator : package.GeneratorIndex) where
  motiveComparisonData : witness.CanonicalReducedProjectiveLineTateComparisonDataQ
  tateGeneratorData : CanonicalTateGeneratorDataQ package tateGenerator
  p1GeneratorData : CanonicalProjectiveLineGeneratorDataQ package witness p1Generator

/-- Concrete canonical comparison between stabilization by the Tate generator
and stabilization by the `P¹`/reduced-`P¹` route on one minimal generator.
Both outputs are required to realize the same one-step Tate-twist shift of the
input generator. -/
structure CanonicalBoundaryStabilizationComparisonDataQ
    {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category)
    (witness : BoundaryTateStabilizationWitnessData (k := k))
    (tateGenerator p1Generator : package.GeneratorIndex)
    (stabilizeWithTate stabilizeWithP1 :
      package.GeneratorIndex → package.GeneratorIndex)
    (idx : package.GeneratorIndex) where
  canonicalTateP1ComparisonData :
    CanonicalBoundaryTateP1ComparisonDataQ package witness tateGenerator p1Generator
  tateShiftComparison :
    GeneratorComparisonDataQ
      (package.generator (stabilizeWithTate idx))
      (tateTwistShiftGenerator (package.generator idx))
  p1ShiftComparison :
    GeneratorComparisonDataQ
      (package.generator (stabilizeWithP1 idx))
      (tateTwistShiftGenerator (package.generator idx))

/-- Tate stabilization target surface specialized to the canonical Boundary-side
Tate data coming from the concrete projective line and its chosen basepoint. -/
structure BoundaryTateStabilizationPresentationQ
    (category : SmCorQ (k := k))
    (package : MinimalPresentationPackageQ category) where
  /-- Canonical correspondence-level tensor owner inherited from the minimal
  package closure. -/
  canonicalExternalProduct :
    FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k) :=
      package.closure.canonicalExternalProduct
  witnessData : BoundaryTateStabilizationWitnessData (k := k)
  tateGenerator : package.GeneratorIndex
  p1Generator : package.GeneratorIndex
  stabilizeWithTate : package.GeneratorIndex → package.GeneratorIndex
  stabilizeWithP1 : package.GeneratorIndex → package.GeneratorIndex
  tateObjectData : CanonicalTateGeneratorDataQ package tateGenerator
  p1ObjectData :
    CanonicalProjectiveLineGeneratorDataQ package witnessData p1Generator
  canonicalTateP1ComparisonData :
    CanonicalBoundaryTateP1ComparisonDataQ package witnessData tateGenerator p1Generator
  stabilizationComparisonData :
    ∀ idx : package.GeneratorIndex,
      CanonicalBoundaryStabilizationComparisonDataQ
        package witnessData tateGenerator p1Generator stabilizeWithTate stabilizeWithP1 idx

namespace BoundaryTateStabilizationPresentationQ

/-- The canonical witness-free Tate datum attached to a stabilization
presentation is the owner-level Tate datum constructed directly from the
composition package. Downstream code should prefer this theorem-shaped API
over threading witness records. -/
def canonicalTateDatum
    {category : SmCorQ (k := k)}
    {package : MinimalPresentationPackageQ category}
    (presentation : BoundaryTateStabilizationPresentationQ (k := k) category package) :
  BoundaryTateObjectConstructionData (k := k)
      presentation.witnessData.composition :=
  Boundary.boundaryCanonicalTateObjectConstructionData
    (composition := presentation.witnessData.composition)

end BoundaryTateStabilizationPresentationQ

end

end Boundary
