import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Representatives.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Transport.Owner

/-!
# Transport formulas for heart representatives

This file records reflexive pointwise-equality transport formulas for exact
shifted bounded heart representative objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The reflexive pointwise-equality lift fixes exact-degree heart
representatives. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_liftOfPointwiseEq_refl
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.liftOfPointwiseEq
        (TraceAnalyticMotivicTStructure.Heart.inclusion degree)
        (fun object => Eq.refl object.object)).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
        complex
        degree :=
  rfl

/-- The reflexive pointwise-equality lift fixes translated exact-degree heart
representatives. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_liftOfPointwiseEq_refl
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.liftOfPointwiseEq
        (TraceAnalyticMotivicTStructure.Heart.inclusion (degree + shift))
        (fun object => Eq.refl object.object)).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
          shift
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
        shift
        complex
        degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
