import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Monotone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Transport.Owner

/-!
# Transport formulas for window representatives

This file records reflexive pointwise-equality transport formulas for shifted
bounded window representative objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The reflexive pointwise-equality lift fixes shifted bounded window
representatives. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBounded_liftOfPointwiseEq_refl
    {lower upper : ℤ}
    (degree : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
        (TraceAnalyticMotivicTStructure.Window.inclusion lower upper)
        (fun object => Eq.refl object.object)).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
          degree
          lower_le_degree
          degree_le_upper
          complex) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
        degree
        lower_le_degree
        degree_le_upper
        complex :=
  rfl

/-- The reflexive pointwise-equality lift fixes singleton-window
representatives. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_liftOfPointwiseEq_refl
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
        (TraceAnalyticMotivicTStructure.Window.inclusion degree degree)
        (fun object => Eq.refl object.object)).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
        complex
        degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
