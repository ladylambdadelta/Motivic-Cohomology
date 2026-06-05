import Boundary.CanonicalDMgmConstruction

/-!
# Boundary DMgm Input Surface

This file exports the canonical Boundary-side input package consumed by the
classical `DM_gm(Q)_Q` construction layer.

Boundary has a formal geometric-motives stabilization surface in
`Boundary.GeometricMotives`; this module intentionally exposes the separate
input bundle used by downstream classical recognition APIs.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

namespace Boundary

noncomputable section


/-- Final Boundary-side input bundle for the classical `DM_gm(Q)_Q`
construction. Boundary exports the effective presentation and canonical
Tate-stabilization input expected by the classical recognition layer. -/
structure CanonicalDMgmInputDataQ (category : SmCorQ (k := k)) where
  effectivePresentation : CanonicalEffectiveMotivicPresentationQ category
  tateStabilizationInput :
    CanonicalTateStabilizationInputQ category effectivePresentation

namespace CanonicalDMgmInputDataQ

abbrev internalPresentation
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :=
  input.effectivePresentation.internalPresentation

abbrev motiveOf
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :=
  input.tateStabilizationInput.tateObjectData.motiveComparisonData.tateObject

abbrev reducedProjectiveLineMotive
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :=
  input.tateStabilizationInput.tateObjectData.motiveComparisonData.reducedProjectiveLineMotive

/-- Canonical theorem-surface alias for localization compatibility, proved in
the effective-motives owner layer. -/
abbrev localizationCompatibility :=
  CanonicalTateStabilizationInputQ.localizationCompatibility

abbrev canonicalExternalProduct
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :=
  input.tateStabilizationInput.canonicalExternalProduct

/-- Canonical theorem-surface alias for tensor input data at the correspondence
layer used by downstream Tate-action consumers. -/
abbrev boundaryCanonicalTensorInput
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :=
  input.canonicalExternalProduct

/-- Canonical theorem-surface alias for the Boundary DMgm input package. -/
abbrev boundaryCanonicalDMgmInput
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :=
  input

/-- Project the canonical Boundary input to the pair of the effective
presentation data and the Tate-stabilization input needed by the classical
motives layer. -/
def toPresentationAndStabilization
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :
    CanonicalEffectiveMotivicPresentationQ category ×
      CanonicalTateStabilizationInputQ category input.effectivePresentation :=
  (input.effectivePresentation,
    input.tateStabilizationInput)

end CanonicalDMgmInputDataQ

end

end Boundary
