import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Exactness.Comparison.Transport.Contravariant.Owner

/-!
# Paired Yoneda exactness for explicit truncation short complexes

This file packages the covariant and contravariant Yoneda exactness statements
for the explicit hand-built chosen truncation short complex.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives
namespace TraceAnalyticMotivicTStructure

namespace YonedaTruncationRepresentative

/-- The explicit chosen truncation short complex is exact after both
covariant and contravariant preadditive Yoneda probes. -/
theorem yonedaExact_pair
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    (representative.shortComplex.map
        (preadditiveCoyoneda.obj leftProbe)).Exact ∧
      (representative.shortComplex.op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  And.intro
    (representative.coyonedaShortComplex_exact leftProbe)
    (representative.yonedaShortComplex_exact rightProbe)

/-- Normalized adjacent cut-`1` paired Yoneda exactness for the explicit
chosen truncation short complex. -/
theorem normalized_yonedaExact_pair
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    (representative.shortComplex.map
        (preadditiveCoyoneda.obj leftProbe)).Exact ∧
      (representative.shortComplex.op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  And.intro
    (representative.normalized_coyonedaShortComplex_exact leftProbe)
    (representative.normalized_yonedaShortComplex_exact rightProbe)

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
