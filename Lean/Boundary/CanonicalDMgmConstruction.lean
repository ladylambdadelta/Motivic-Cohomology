import Boundary.DMgm
import Boundary.InternalPresentationPackage

/-!
# Canonical DMgm Input Surface

This file records the canonical Boundary-side input data consumed by the
classical `DM_gm(Q)_Q` construction layer.

Boundary also has a formal geometric-motives stabilization surface in
`Boundary.GeometricMotives`. This file intentionally remains input-only: it
exports effective presentation data, reduced-`P¹`/Tate object data, and
canonical stabilization input expected by downstream classical interfaces.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

namespace Boundary

noncomputable section

/-- Canonical effective motivic presentation exported by Boundary.
This is the effective geometric input consumed later by the classical
`DM_gm(Q)_Q` construction. -/
structure CanonicalEffectiveMotivicPresentationQ
    (category : SmCorQ (k := k))
    where
  internalPresentation : BoundaryInternalPresentationPackageQ category
  localizingMorphisms : LocalizingMorphismPresentationQ category :=
    internalPresentation.constructionData.localizingMorphisms
  rawLocalizationConstruction : RawZigzagLocalizationConstructionQ category :=
    internalPresentation.constructionData.rawLocalizationConstruction
  effectiveClosureData : MinimalPresentationClosureQ :=
    internalPresentation.constructionData.exactEnvelopeData.closureData
  canonicalExternalProductData :
    FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k) :=
      internalPresentation.constructionData.exactEnvelopeData.canonicalExternalProductData

namespace CanonicalEffectiveMotivicPresentationQ

/-- Canonical correspondence-level external-product owner exported by the
effective presentation package. -/
abbrev canonicalExternalProduct
    {category : SmCorQ (k := k)}
    (presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category) :
    FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k) :=
  presentation.canonicalExternalProductData

@[simp] theorem canonicalExternalProduct_eq_data
    {category : SmCorQ (k := k)}
    (presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category) :
    presentation.canonicalExternalProduct = presentation.canonicalExternalProductData :=
  rfl

end CanonicalEffectiveMotivicPresentationQ

/-- Canonical Boundary-side Tate object data exported to the classical motives
layer. The reduced-`P¹`/Tate identification is already constructed at the
effective level and is packaged here as input, not as a `DM_gm` target. -/
structure CanonicalTateObjectDataQ
    (category : SmCorQ (k := k))
    (presentation : CanonicalEffectiveMotivicPresentationQ category) where
  witnessData : BoundaryTateStabilizationWitnessData (k := k)
  motiveComparisonData : witnessData.CanonicalReducedProjectiveLineTateComparisonDataQ
  tateGenerator : presentation.internalPresentation.stabilization.tateGenerator
  p1Generator : presentation.internalPresentation.stabilization.p1Generator
  tateGeneratorData :
    CanonicalTateGeneratorDataQ presentation.internalPresentation.minimal tateGenerator
  p1GeneratorData :
    CanonicalProjectiveLineGeneratorDataQ
      presentation.internalPresentation.minimal witnessData p1Generator

/-- Canonical Boundary-side stabilization input for the classical Tate
inversion step. This remains purely input data: effective presentation,
Tate object data, and the canonical stabilization action on generators. -/
structure CanonicalTateStabilizationInputQ
    (category : SmCorQ (k := k))
    (presentation : CanonicalEffectiveMotivicPresentationQ category) where
  canonicalExternalProduct :
    FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k) :=
      presentation.canonicalExternalProduct
  tateObjectData : CanonicalTateObjectDataQ category presentation
  stabilizationComparisonData :
    ∀ idx : presentation.internalPresentation.minimal.GeneratorIndex,
      presentation.internalPresentation.stabilization.stabilizationComparisonData idx

namespace CanonicalTateStabilizationInputQ

/-- DMgm-facing name for the owner theorem that the effective-motives
localization inverts degree-zero images of canonical `A¹`/Nis local
equivalences. Product-stability theorems identify Tate-stabilized primitive
generators with maps in this class before this theorem is applied. -/
abbrev localizationCompatibility :=
  @canonicalEffectiveMotivesLocalizationFunctor_map_degreeZero_isIso_of_localEquivalence

@[simp] theorem localizationCompatibility_eq_canonical :
    localizationCompatibility (k := k) =
      @canonicalEffectiveMotivesLocalizationFunctor_map_degreeZero_isIso_of_localEquivalence k _ _ :=
  rfl

abbrev composition
    {category : SmCorQ (k := k)}
    {presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category}
    (input : CanonicalTateStabilizationInputQ (k := k) category presentation) :=
  input.tateObjectData.witnessData.composition

abbrev composition
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :=
  input.tateStabilizationInput.tateObjectData.witnessData.composition

/-- The effective Tate object carried by a classical stabilization input is the
owner-level Boundary Tate object for the witness composition. -/
abbrev effectiveTateObject
    {category : SmCorQ (k := k)}
    {presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category}
    (input : CanonicalTateStabilizationInputQ (k := k) category presentation) :
    canonicalEffectiveMotives input.composition :=
  boundaryEffectiveTateObject
    (composition := input.composition)

/-- Canonical owner-level Tate datum for a classical stabilization input.
This is the theorem-shaped surface downstream code should prefer over the
witness field. -/
abbrev canonicalTateDatum
    {category : SmCorQ (k := k)}
    {presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category}
    (input : CanonicalTateStabilizationInputQ (k := k) category presentation) :=
  input.effectiveTateObject

@[simp] theorem canonicalTateDatum_eq_tateObjectData_tateDatum
    {category : SmCorQ (k := k)}
    {presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category}
    (input : CanonicalTateStabilizationInputQ (k := k) category presentation) :
    input.canonicalTateDatum = input.effectiveTateObject :=
  rfl

@[simp] theorem effectiveTateObject_eq_boundaryEffectiveTateObject
    {category : SmCorQ (k := k)}
    {presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category}
    (input : CanonicalTateStabilizationInputQ (k := k) category presentation) :
    input.effectiveTateObject =
      boundaryEffectiveTateObject
        (composition := input.composition) :=
  rfl

/-- The reduced projective-line motive carried by a classical stabilization
input is the owner-level reduced `P¹` motive for the witness composition. -/
abbrev reducedProjectiveLineMotive
    {category : SmCorQ (k := k)}
    {presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category}
    (input : CanonicalTateStabilizationInputQ (k := k) category presentation) :
    canonicalEffectiveMotives input.composition :=
  boundaryReducedProjectiveLineMotive
    (composition := input.composition)

/-- Canonical owner-level reduced projective-line motive datum exposed without
the witness record as the primary surface. -/
abbrev canonicalReducedProjectiveLineMotive
    {category : SmCorQ (k := k)}
    {presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category}
    (input : CanonicalTateStabilizationInputQ (k := k) category presentation) :=
  input.reducedProjectiveLineMotive

@[simp] theorem canonicalReducedProjectiveLineMotive_eq_reducedProjectiveLineMotive
    {category : SmCorQ (k := k)}
    {presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category}
    (input : CanonicalTateStabilizationInputQ (k := k) category presentation) :
    input.canonicalReducedProjectiveLineMotive = input.reducedProjectiveLineMotive :=
  rfl

@[simp] theorem reducedProjectiveLineMotive_eq_boundaryReducedProjectiveLineMotive
    {category : SmCorQ (k := k)}
    {presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category}
    (input : CanonicalTateStabilizationInputQ (k := k) category presentation) :
    input.reducedProjectiveLineMotive =
      boundaryReducedProjectiveLineMotive (composition := input.composition) :=
  rfl

/-- The shifted-Tate/reduced-`P¹` identification consumed by stabilization,
routed through the owner theorem rather than through presentation fields. -/
theorem effectiveTateObject_shifted_iso_reducedProjectiveLine
    {category : SmCorQ (k := k)}
    {presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category}
    (input : CanonicalTateStabilizationInputQ (k := k) category presentation) :
    Nonempty
      (((shiftFunctor
          (canonicalEffectiveMotives input.composition)
          (2 : ℤ)).obj
          (effectiveTateObject input)) ≅
        reducedProjectiveLineMotive input) :=
  boundaryEffectiveTateObject_shifted_iso_reducedProjectiveLine
    (composition := input.composition)

/-- The reduced-`P¹` cone theorem consumed by stabilization, routed through
the owner theorem rather than through presentation fields. -/
theorem reducedProjectiveLineMotive_isCone
    {category : SmCorQ (k := k)}
    {presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category}
    (input : CanonicalTateStabilizationInputQ (k := k) category presentation) :
    ∃ (projectiveLineToReduced :
          boundaryProjectiveLineMotive
              (composition := input.composition) ⟶
            reducedProjectiveLineMotive input)
        (reducedToShiftedUnit :
          reducedProjectiveLineMotive input ⟶
            (shiftFunctor
              (canonicalEffectiveMotives input.composition)
              (1 : ℤ)).obj
              (canonicalUnitMotive input.composition)),
      ({ obj₁ := canonicalUnitMotive input.composition
         obj₂ := boundaryProjectiveLineMotive
            (composition := input.composition)
         obj₃ := reducedProjectiveLineMotive input
         mor₁ := boundaryUnitToProjectiveLineMotive
            (composition := input.composition)
         mor₂ := projectiveLineToReduced
         mor₃ := reducedToShiftedUnit } :
          CategoryTheory.Pretriangulated.Triangle
            (canonicalEffectiveMotives input.composition)) ∈
        distTriang (canonicalEffectiveMotives input.composition) :=
  boundaryReducedProjectiveLineMotive_isCone
    (composition := input.composition)

/-- The classical stabilization input consumes the owner-level DMgm universal
property built from the projective-geometric Tate object. -/
abbrev dmgmUniversalProperty
    {category : SmCorQ (k := k)}
    {presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category}
    (input : CanonicalTateStabilizationInputQ (k := k) category presentation) :
    VoevodskyDMgmTateStabilizationUniversalProperty
      (composition := input.composition) :=
  VoevodskyDMgmTateStabilizationUniversalProperty.canonical
    (composition := input.composition)

@[simp] theorem dmgmUniversalProperty_eq_canonical
    {category : SmCorQ (k := k)}
    {presentation : CanonicalEffectiveMotivicPresentationQ (k := k) category}
    (input : CanonicalTateStabilizationInputQ (k := k) category presentation) :
    input.dmgmUniversalProperty =
      VoevodskyDMgmTateStabilizationUniversalProperty.canonical
        (composition := input.composition) :=
  rfl

end CanonicalTateStabilizationInputQ

end

end Boundary
