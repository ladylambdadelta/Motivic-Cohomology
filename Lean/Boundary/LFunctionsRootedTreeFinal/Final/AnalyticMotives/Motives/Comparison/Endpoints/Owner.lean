import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.BoundedDescent.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Descent.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Source.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Target.Summary.Owner

/-!
# Comparison endpoints

This file records the two categories and endpoint functors used by the analytic
comparison with Boundary `DMgm`: the source is the stable analytic Verdier
quotient, and the target is the existing Boundary `DMgm` construction.
-/

universe u

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable [FiniteCorrespondence.CanonicalExternalProductFamily (k := k)]
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- Endpoint statement: the analytic source is the stable analytic Verdier
quotient. -/
theorem TraceAnalyticMotiveComparison.source_eq_stableVerdierQuotient :
    TraceAnalyticDMgmComparisonSource =
      TraceAnalyticStableMotiveCategory :=
  rfl

/-- Endpoint statement: the analytic source is the stable homotopy comparison
source. -/
theorem TraceAnalyticMotiveComparison.source_eq_stableHomotopyComparisonSource :
    TraceAnalyticDMgmComparisonSource =
      TraceAnalyticStableHomotopyComparisonSource :=
  rfl

/-- Endpoint statement: the comparison-source quotient is the stable analytic
Verdier quotient functor. -/
theorem TraceAnalyticMotiveComparison.sourceQuotientFunctor_eq_stable :
    TraceAnalyticDMgmComparisonSource.quotientFunctor =
      TraceAnalyticStableMotiveCategory.quotientFunctor :=
  rfl

/-- Endpoint statement: the comparison-source quotient is the stable homotopy
comparison quotient functor. -/
theorem TraceAnalyticMotiveComparison.sourceQuotientFunctor_eq_stableHomotopy :
    TraceAnalyticDMgmComparisonSource.quotientFunctor =
      TraceAnalyticStableHomotopyComparisonSource.quotientFunctor :=
  rfl

/-- Endpoint statement: the concrete target is the parent Boundary `DMgm`
alias. -/
theorem TraceAnalyticMotiveComparison.target_eq_parentDMgm :
    TraceAnalyticDMgmComparisonTarget (composition := composition) =
      Boundary.DMgmQ_Q (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget_eq_parentDMgm
    (composition := composition)

/-- Endpoint statement: the concrete target is the Voevodsky-style Boundary
`DMgm` construction. -/
theorem TraceAnalyticMotiveComparison.target_eq_VoevodskyDMgm :
    TraceAnalyticDMgmComparisonTarget (composition := composition) =
      Boundary.VoevodskyDMgmQ_Q (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget_eq_VoevodskyDMgm
    (composition := composition)

/-- Endpoint statement: the concrete target is formal stabilization at the
projective-geometric Tate object. -/
theorem TraceAnalyticMotiveComparison.target_eq_projectiveGeometricTateStabilization :
    TraceAnalyticDMgmComparisonTarget (composition := composition) =
      Boundary.boundaryMotivesOfProjectiveGeometricTateObject
        (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget_eq_projectiveGeometricTateStabilization
    (composition := composition)

/-- Endpoint statement: the target effective embedding is the parent Boundary
`DMgm` effective embedding. -/
theorem TraceAnalyticMotiveComparison.targetEffectiveEmbedding_eq_parent :
    TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
        (composition := composition) =
      Boundary.VoevodskyDMgmEffectiveEmbedding
        (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget.effectiveEmbedding_eq_parent
    (composition := composition)

/-- Endpoint statement: the target Tate-shift equivalence is the parent
Boundary `DMgm` Tate-shift equivalence. -/
theorem TraceAnalyticMotiveComparison.targetTateShiftEquivalence_eq_parent :
    TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
        (composition := composition) =
      Boundary.VoevodskyDMgmTateShiftEquivalence
        (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_eq_parent
    (composition := composition)

/-- Endpoint statement: the source distinguished triangles are exactly the
stable analytic distinguished triangles. -/
theorem TraceAnalyticMotiveComparison.sourceDistinguishedTriangles_eq_stable :
    TraceAnalyticDMgmComparisonSource.distinguishedTriangles =
      TraceAnalyticStableMotiveCategory.distinguishedTriangles :=
  rfl

/-- Endpoint statement: the source distinguished triangles are exactly the
stable homotopy comparison distinguished triangles. -/
theorem TraceAnalyticMotiveComparison.sourceDistinguishedTriangles_eq_stableHomotopy :
    TraceAnalyticDMgmComparisonSource.distinguishedTriangles =
      TraceAnalyticStableHomotopyComparisonSource.distinguishedTriangles :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
