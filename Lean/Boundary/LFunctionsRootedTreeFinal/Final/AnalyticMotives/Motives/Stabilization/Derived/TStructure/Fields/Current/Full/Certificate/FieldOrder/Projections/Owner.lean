import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Full.Certificate.FieldOrder.Owner

/-!
# Projections from the current field-order certificate

This file exposes the individual constructor-order fields from the current
t-structure-facing certificate.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

namespace RepresentedTruncationObject

/-- The field-order certificate gives adjacent monotonicity of the analytic
aisle predicate. -/
theorem current_constructor_order_tStructureLE_zero_le
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    TraceAnalyticDerivedMotiveCategory.tStructureLE 0 ≤
      TraceAnalyticDerivedMotiveCategory.tStructureLE 1 :=
  (represented.current_full_constructor_order_certificate
    object
    hshortExact).left

/-- The field-order certificate gives adjacent monotonicity of the analytic
coaisle predicate. -/
theorem current_constructor_order_tStructureGE_one_le
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    TraceAnalyticDerivedMotiveCategory.tStructureGE 1 ≤
      TraceAnalyticDerivedMotiveCategory.tStructureGE 0 :=
  (represented.current_full_constructor_order_certificate
    object
    hshortExact).right.left

/-- The field-order certificate gives adjacent truncation triangle
existence. -/
theorem current_constructor_order_truncation_triangle
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
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
  (represented.current_full_constructor_order_certificate
    object
    hshortExact).right.right.left

/-- The field-order certificate gives represented-object orthogonality. -/
theorem current_constructor_order_represented_firstMap_secondMap
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    represented.firstMap ≫ represented.secondMap = 0 :=
  (represented.current_full_constructor_order_certificate
    object
    hshortExact).right.right.right

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
