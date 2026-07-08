import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Normalized.Exactness.Owner

/-!
# Certificate for the normalized truncation exact sequence

This file bundles the vertex identifications, map projections, and paired
Yoneda exactness of the normalized explicit chosen truncation short complex.
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

/-- The normalized explicit truncation short complex is the concrete
`≤ 0` aisle-to-object-to-`≥ 1` coaisle sequence, and it is exact under both
covariant and contravariant preadditive Yoneda probes. -/
theorem normalized_exactSequence_certificate
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    representative.shortComplex.X₁ =
        (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion 0).obj
          representative.lowerAisleObjectZero ∧
      representative.shortComplex.X₂ = object ∧
        representative.shortComplex.X₃ =
          (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion 1).obj
            representative.upperCoaisleObjectOne ∧
          representative.shortComplex.f = representative.firstMap ∧
            representative.shortComplex.g = representative.secondMap ∧
              (representative.shortComplex.map
                  (preadditiveCoyoneda.obj leftProbe)).Exact ∧
                (representative.shortComplex.op.map
                  (preadditiveYoneda.obj rightProbe)).Exact :=
  let vertex₁ := representative.normalized_shortComplex_X₁_inclusion
  let vertex₂ := representative.normalized_shortComplex_X₂_object
  let vertex₃ := representative.normalized_shortComplex_X₃_inclusion
  let map₁ := representative.shortComplex_f
  let map₂ := representative.shortComplex_g
  let exactPair :=
    representative.normalized_subcategoryVertex_yonedaExact_pair
      leftProbe
      rightProbe
  And.intro
    vertex₁
    (And.intro
      vertex₂
      (And.intro
        vertex₃
        (And.intro
          map₁
          (And.intro
            map₂
            exactPair))))

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
