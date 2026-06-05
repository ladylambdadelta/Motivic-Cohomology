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

end CanonicalTateStabilizationInputQ

end

end Boundary
