import Boundary.TateStabilization

/-!
# Internal Presentation Package

This file bundles the source-side minimal package, derived localization, Tate
stabilization, and envelope exactness into the internal presentation package
used downstream by the canonical `DM_gm(Q)_Q` construction route.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

namespace Boundary

noncomputable section

/-- Exact-envelope construction data above the current internal presentation
surface. The minimal package already carries the closure operations used in the
envelope stage, so the internal package records that closure data directly
together with the canonical localization and stabilization inputs. -/
structure InternalEnvelopeConstructionDataQ
    (category : SmCorQ (k := k))
    (minimal : MinimalPresentationPackageQ category)
    (localization : OpenClosedLocalizationPresentationQ category)
    (stabilization : BoundaryTateStabilizationPresentationQ category minimal) where
  localizingMorphisms : LocalizingMorphismPresentationQ category :=
    minimal.toLocalizingMorphisms
  rawLocalizationConstruction : RawZigzagLocalizationConstructionQ category :=
    minimal.rawZigzagLocalizationConstruction
  localizationData : OpenClosedLocalizationPresentationQ category := localization
  stabilizationData : BoundaryTateStabilizationPresentationQ category minimal := stabilization
  closureData : MinimalPresentationClosureQ := minimal.closure
  canonicalExternalProductData :
    FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k) :=
      minimal.closure.canonicalExternalProduct

/-- Canonical Boundary-side internal construction data threading the chosen
minimal package, open/closed localization, and canonical Tate stabilization
together with its internal exact-envelope data. -/
structure CanonicalBoundaryInternalConstructionDataQ
    (category : SmCorQ (k := k))
    (minimal : MinimalPresentationPackageQ category)
    (localization : OpenClosedLocalizationPresentationQ category)
    (stabilization : BoundaryTateStabilizationPresentationQ category minimal) where
  localizingMorphisms : LocalizingMorphismPresentationQ category :=
    minimal.toLocalizingMorphisms
  rawLocalizationConstruction : RawZigzagLocalizationConstructionQ category :=
    minimal.rawZigzagLocalizationConstruction
  canonicalStabilizationData :
    ∀ idx : minimal.GeneratorIndex,
      stabilization.stabilizationComparisonData idx
  canonicalExternalProductData :
    FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k) :=
      minimal.closure.canonicalExternalProduct
  exactEnvelopeData :
    InternalEnvelopeConstructionDataQ
      category minimal localization stabilization

/-- Boundary-side internal presentation package specialized to the canonical
Tate-stabilization route coming from the concrete projective line and its
chosen basepoint. This is the Boundary-facing package that feeds the canonical
DMgm construction layer. -/
structure BoundaryInternalPresentationPackageQ (category : SmCorQ (k := k)) where
  minimal : MinimalPresentationPackageQ category
  localization : OpenClosedLocalizationPresentationQ category
  stabilization : BoundaryTateStabilizationPresentationQ category minimal
  constructionData :
    CanonicalBoundaryInternalConstructionDataQ category minimal localization stabilization

end

end Boundary
