import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Components.Owner

/-!
# Off-lower-tail upper inverse component normal form

This file records the component calculation behind the off-lower-tail splitting:
on a nonboundary upper-tail degree, the restricted-core upper projection is the
inverse of Mathlib's nonboundary truncation isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- On a nonboundary analytic upper-tail degree, the restricted-core upper
projection component is the inverse nonboundary truncation isomorphism. -/
theorem additiveTruncGEProjectionCoreComponent_of_not_boundary
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (hboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    TraceAnalyticMotivicTStructure.additiveTruncGEProjectionCoreComponent
        cut
        complex
        tail =
      (_root_.HomologicalComplex.truncGE'XIso
        complex
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
        rfl
        hboundary).inv :=
  TraceAnalyticMotivicTStructure
    .truncGEProjectionCoreComponent_of_not_boundary
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
      complex
      tail
      hboundary

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
