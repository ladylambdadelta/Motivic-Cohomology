import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Preimage.FieldShape.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.RepresentedComposite.Owner

/-!
# Current proved Mathlib field fragments

This file records the currently proved field-level fragments of the derived
analytic motivic t-structure: adjacent monotonicity, arbitrary-object
truncation existence through the canonical cochain preimage, and the
represented truncation composite in the `zero'`-field source/target shape.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The currently proved adjacent monotonicity fields for the derived
analytic t-structure predicates. -/
theorem current_tStructure_monotonicity_fields :
    TraceAnalyticDerivedMotiveCategory.tStructureLE 0 ≤
        TraceAnalyticDerivedMotiveCategory.tStructureLE 1 ∧
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1 ≤
        TraceAnalyticDerivedMotiveCategory.tStructureGE 0 :=
  And.intro
    TraceAnalyticDerivedMotiveCategory.tStructureLE_zero_le
    TraceAnalyticDerivedMotiveCategory.tStructureGE_one_le

/-- The currently proved arbitrary-object truncation existence field, in the
exact binder shape used by Mathlib's `TStructure.exists_triangle_zero_one`.
-/
theorem current_exists_triangle_zero_one_field
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .derivedTStructure_cochainPreimage_exists_triangle_zero_one_fieldShape
      object
      hshortExact

end TraceAnalyticDerivedMotiveCategory

namespace TraceAnalyticMotivicTStructure

namespace RepresentedTruncationObject

/-- The currently proved represented-object orthogonality fragment: the
chosen lower-to-upper truncation composite is zero in the source/target
membership shape expected by Mathlib's `TStructure.zero'` field. -/
theorem current_represented_zero_field
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.firstMap ≫ object.secondMap = 0 :=
  object.firstMap_secondMap_eq_zero_tStructure_field

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
