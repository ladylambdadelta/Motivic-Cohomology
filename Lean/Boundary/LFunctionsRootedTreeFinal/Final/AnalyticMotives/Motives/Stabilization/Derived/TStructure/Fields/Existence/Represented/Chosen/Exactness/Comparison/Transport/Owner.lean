import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Exactness.Comparison.Owner

/-!
# Exactness transport to the explicit chosen truncation short complex

This file transports covariant Yoneda exactness from the canonical
distinguished short complex to the explicit hand-built chosen truncation short
complex along their componentwise isomorphism.
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

/-- Covariant preadditive Yoneda exactness for the explicit chosen truncation
short complex, transported from the canonical distinguished short complex. -/
theorem coyonedaShortComplex_exact
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object)
    (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ) :
    (representative.shortComplex.map
      (preadditiveCoyoneda.obj probe)).Exact :=
  ShortComplex.exact_of_iso
    (((preadditiveCoyoneda.obj probe).mapShortComplex.mapIso
      representative.shortComplexIsoDistinguishedShortComplex).symm)
    (representative.coyonedaDistinguishedShortComplex_exact probe)

/-- Covariant preadditive Yoneda exactness for the normalized adjacent
cut-`1` explicit chosen truncation short complex. -/
theorem normalized_coyonedaShortComplex_exact
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ) :
    (representative.shortComplex.map
      (preadditiveCoyoneda.obj probe)).Exact :=
  representative.coyonedaShortComplex_exact probe

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
