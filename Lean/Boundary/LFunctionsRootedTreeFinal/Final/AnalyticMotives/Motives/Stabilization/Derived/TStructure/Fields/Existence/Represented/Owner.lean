import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Owner

/-!
# Mathlib-shape represented truncation existence

This file records the represented-object truncation theorem in the exact field
shape used by Mathlib's `TStructure.exists_triangle_zero_one`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives
namespace TraceAnalyticMotivicTStructure

/-- Objects carrying a concrete Yoneda truncation representative at cut `1`
have the adjacent truncation triangle in the exact Mathlib
`exists_triangle_zero_one` field shape. -/
theorem derivedTStructure_exists_triangle_zero_one_of_yonedaRepresentative
    (object : TraceAnalyticDerivedMotiveCategory)
    (representativeExists :
      TraceAnalyticMotivicTStructure
        .HasYonedaTruncationRepresentative 1 object) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .derivedTStructure_hasYonedaTruncationRepresentative_exists_triangle_zero_one_fieldShape
      object
      representativeExists

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
