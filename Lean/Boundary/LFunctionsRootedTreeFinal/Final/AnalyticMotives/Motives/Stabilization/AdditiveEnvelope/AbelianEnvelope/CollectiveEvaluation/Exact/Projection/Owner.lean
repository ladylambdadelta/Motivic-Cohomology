import Mathlib.CategoryTheory.Abelian.Exact
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.CollectiveEvaluation.Projection.Owner

/-!
# Coordinate exactness from collective exactness

This file projects exactness of short complexes in the collective
probe-evaluation target to exactness at each analytic additive probe.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveAbelianEnvelope

/-- Exactness in the collective probe-evaluation target implies exactness after
projecting to any probe coordinate. -/
theorem collectiveTarget_projection_exact
    (probe : TraceAnalyticAdditiveCategoryObject)
    {shortComplex :
      ShortComplex
        TraceAnalyticAdditiveAbelianEnvelope.CollectiveEvaluationTarget}
    (hexact : shortComplex.Exact) :
    (shortComplex.map
      (TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluationProjection
        probe)).Exact :=
  hexact.map
    (TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluationProjection
      probe)

end TraceAnalyticAdditiveAbelianEnvelope

end AnalyticMotives
end LFunctions
end Boundary
