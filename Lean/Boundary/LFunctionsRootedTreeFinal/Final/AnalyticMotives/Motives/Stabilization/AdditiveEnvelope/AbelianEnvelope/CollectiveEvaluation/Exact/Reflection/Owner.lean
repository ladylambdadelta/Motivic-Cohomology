import Mathlib.CategoryTheory.Abelian.Exact
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.CollectiveEvaluation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Exact.Owner

/-!
# Exactness reflection along collective probe evaluation

This file reflects exactness of short complexes in the analytic abelian
envelope from exactness after collective probe evaluation.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveAbelianEnvelope

/-- If the collective probe-evaluated short complex is exact in the product of
probe-value Q-module categories, then the original short complex in the
analytic abelian envelope is exact. -/
theorem exact_of_collectiveEvaluation_exact
    (shortComplex : ShortComplex TraceAnalyticAdditiveAbelianEnvelope)
    (hexact :
      (shortComplex.map
        TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluation).Exact) :
    TraceAnalyticAdditiveAbelianEnvelope.exact shortComplex :=
  letI :
      TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluation.Faithful :=
    TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluationFaithful
  Functor.reflects_exact_of_faithful
    TraceAnalyticAdditiveAbelianEnvelope.collectiveEvaluation
    shortComplex
    hexact

end TraceAnalyticAdditiveAbelianEnvelope

end AnalyticMotives
end LFunctions
end Boundary
