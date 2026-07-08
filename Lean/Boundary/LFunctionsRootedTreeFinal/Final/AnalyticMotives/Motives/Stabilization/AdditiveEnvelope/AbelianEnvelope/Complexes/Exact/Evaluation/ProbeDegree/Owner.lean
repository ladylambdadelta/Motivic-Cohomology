import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Complexes.Exact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Exact.Evaluation.Owner

/-!
# Probe-degree evaluation of short exact abelian-envelope cochain complexes

Short exactness of cochain complexes in the analytic abelian envelope becomes
short exactness after evaluating first at a cochain degree and then at an
analytic additive probe.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAbelianCochainComplex

/-- An exact short complex of analytic abelian cochain complexes remains exact
after degree evaluation and analytic probe evaluation. -/
theorem exact_probeDegreeEvaluation
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    {shortComplex : ShortComplex TraceAnalyticAbelianCochainComplex}
    (hexact :
      TraceAnalyticAbelianCochainComplex.exact shortComplex) :
    ((shortComplex.map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        degree)).map
      (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)).Exact :=
  TraceAnalyticAdditiveAbelianEnvelope.evaluation_exact
    probe
    ((TraceAnalyticAbelianCochainComplex.exact_iff_degreewise_exact
      shortComplex).mp hexact degree)

/-- A short exact short complex of analytic abelian cochain complexes remains
short exact after degree evaluation and analytic probe evaluation. -/
theorem shortExact_probeDegreeEvaluation
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    {shortComplex : ShortComplex TraceAnalyticAbelianCochainComplex}
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact shortComplex) :
    ((shortComplex.map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        degree)).map
      (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)).ShortExact :=
  TraceAnalyticAdditiveAbelianEnvelope.evaluation_shortExact
    probe
    ((TraceAnalyticAbelianCochainComplex.shortExact_iff_degreewise_shortExact
      shortComplex).mp hshortExact degree)

/-- A short exact short complex of analytic abelian cochain complexes remains
exact after degree evaluation and analytic probe evaluation. -/
theorem shortExact_probeDegreeEvaluation_exact
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    {shortComplex : ShortComplex TraceAnalyticAbelianCochainComplex}
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact shortComplex) :
    ((shortComplex.map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        degree)).map
      (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)).Exact :=
  (TraceAnalyticAbelianCochainComplex.shortExact_probeDegreeEvaluation
    probe
    degree
    hshortExact).exact

end TraceAnalyticAbelianCochainComplex

end AnalyticMotives
end LFunctions
end Boundary
