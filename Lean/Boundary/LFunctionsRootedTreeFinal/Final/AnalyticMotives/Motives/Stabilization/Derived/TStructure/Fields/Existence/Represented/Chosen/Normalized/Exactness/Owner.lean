import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Normalized.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Exactness.Comparison.Transport.Paired.Owner

/-!
# Normalized exactness with aisle and coaisle vertices

This file rewrites the normalized cut-`1` chosen truncation short complex so
its first and third vertices are expressed through the concrete `≤ 0` aisle
and `≥ 1` coaisle objects.
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

/-- The first vertex of the normalized explicit truncation short complex is
the inclusion of the normalized lower aisle object. -/
theorem normalized_shortComplex_X₁_inclusion
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object) :
    representative.shortComplex.X₁ =
      (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion 0).obj
        representative.lowerAisleObjectZero :=
  Eq.trans
    representative.shortComplex_X₁
    (Eq.symm representative.lowerAisleObjectZero_inclusion)

/-- The middle vertex of the normalized explicit truncation short complex is
the represented object. -/
theorem normalized_shortComplex_X₂_object
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object) :
    representative.shortComplex.X₂ = object :=
  representative.shortComplex_X₂

/-- The third vertex of the normalized explicit truncation short complex is
the inclusion of the normalized upper coaisle object. -/
theorem normalized_shortComplex_X₃_inclusion
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object) :
    representative.shortComplex.X₃ =
      (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion 1).obj
        representative.upperCoaisleObjectOne :=
  Eq.trans
    representative.shortComplex_X₃
    (Eq.symm representative.upperCoaisleObjectOne_inclusion)

/-- The normalized explicit truncation short complex has paired Yoneda
exactness with its first and third vertices identified as the concrete aisle
and coaisle inclusions. -/
theorem normalized_subcategoryVertex_yonedaExact_pair
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
  representative.normalized_yonedaExact_pair leftProbe rightProbe

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
