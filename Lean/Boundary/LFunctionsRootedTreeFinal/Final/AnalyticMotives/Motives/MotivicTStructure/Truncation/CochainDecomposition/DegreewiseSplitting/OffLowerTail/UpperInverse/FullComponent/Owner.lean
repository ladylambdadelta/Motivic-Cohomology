import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Components.Owner

/-!
# Off-lower-tail full upper projection component normal form

This file records the full degreewise component calculation used by the
off-lower-tail splitting: on a nonboundary upper-tail degree, the upper
projection component is the inverse of Mathlib's nonboundary truncation
isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- On a nonboundary analytic upper-tail degree, the full upper projection
component is the inverse nonboundary truncation isomorphism. -/
theorem additiveTruncGEProjectionComponent_of_not_boundary
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
        some tail)
    (hboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    TraceAnalyticMotivicTStructure.additiveTruncGEProjectionComponent
        cut
        complex
        degree =
      (_root_.HomologicalComplex.truncGEXIso
        complex
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
        (ComplexShape.Embedding.f_eq_of_r_eq_some
          (e := TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
          htail)
        hboundary).inv :=
  TraceAnalyticMotivicTStructure
    .truncGEProjectionComponent_of_not_boundary
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
      complex
      degree
      tail
      htail
      hboundary

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
