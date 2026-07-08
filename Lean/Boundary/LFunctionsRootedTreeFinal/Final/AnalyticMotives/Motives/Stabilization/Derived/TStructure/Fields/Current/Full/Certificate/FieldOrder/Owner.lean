import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Full.Projections.Fields.Owner

/-!
# Constructor-order current t-structure field certificate

This file records the currently proved adjacent t-structure-facing fields in
the order consumed by the eventual owner-level t-structure constructor.
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

/-- The current adjacent t-structure-facing fields in constructor order:
aisle monotonicity, coaisle monotonicity, adjacent truncation triangle
existence, and represented-object orthogonality. -/
theorem current_full_constructor_order_certificate
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
        TraceAnalyticDerivedMotiveCategory.tStructureLE 1 ∧
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1 ≤
          TraceAnalyticDerivedMotiveCategory.tStructureGE 0 ∧
        (∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory) ∧
          represented.firstMap ≫ represented.secondMap = 0 :=
  And.intro
    (represented.current_full_tStructureLE_zero_le object hshortExact)
    (And.intro
      (represented.current_full_tStructureGE_one_le object hshortExact)
      (And.intro
        (represented.current_full_truncation_triangle object hshortExact)
        (represented.current_full_represented_firstMap_secondMap
          object
          hshortExact)))

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
