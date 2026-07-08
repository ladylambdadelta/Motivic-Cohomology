import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Exact.Owner

/-!
# Evaluation of exact short complexes in the analytic abelian envelope

Exactness in the analytic presheaf abelian envelope maps to exactness after
evaluation at any analytic additive probe.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveAbelianEnvelope

/-- Evaluation at an analytic additive probe sends exact short complexes in the
analytic abelian envelope to exact short complexes of Q-modules. -/
theorem evaluation_exact
    (probe : TraceAnalyticAdditiveCategoryObject)
    {shortComplex : ShortComplex TraceAnalyticAdditiveAbelianEnvelope}
    (hexact :
      TraceAnalyticAdditiveAbelianEnvelope.exact shortComplex) :
    (shortComplex.map
      (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)).Exact :=
  hexact.map
    (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)

/-- Evaluation at an analytic additive probe sends short exact complexes in the
analytic abelian envelope to exact short complexes of Q-modules. -/
theorem evaluation_shortExact_exact
    (probe : TraceAnalyticAdditiveCategoryObject)
    {shortComplex : ShortComplex TraceAnalyticAdditiveAbelianEnvelope}
    (hshortExact :
      TraceAnalyticAdditiveAbelianEnvelope.shortExact shortComplex) :
    (shortComplex.map
      (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)).Exact :=
  TraceAnalyticAdditiveAbelianEnvelope.evaluation_exact
    probe
    (TraceAnalyticAdditiveAbelianEnvelope.shortExact_exact hshortExact)

/-- Evaluation at an analytic additive probe sends short exact complexes in the
analytic abelian envelope to short exact complexes of Q-modules. -/
theorem evaluation_shortExact
    (probe : TraceAnalyticAdditiveCategoryObject)
    {shortComplex : ShortComplex TraceAnalyticAdditiveAbelianEnvelope}
    (hshortExact :
      TraceAnalyticAdditiveAbelianEnvelope.shortExact shortComplex) :
    (shortComplex.map
      (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)).ShortExact :=
  hshortExact.map_of_exact
    (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)

end TraceAnalyticAdditiveAbelianEnvelope

end AnalyticMotives
end LFunctions
end Boundary
