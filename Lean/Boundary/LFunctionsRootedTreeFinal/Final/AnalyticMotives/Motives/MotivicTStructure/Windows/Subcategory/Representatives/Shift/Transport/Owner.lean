import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Transport.Owner

/-!
# Transport formulas for translated window representatives

This file records reflexive pointwise-equality transport formulas for
translated shifted bounded window representative objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The reflexive pointwise-equality lift fixes translated shifted bounded
window representatives. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight_liftOfPointwiseEq_refl
    {lower upper : ℤ}
    (degree shift : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
        (TraceAnalyticMotivicTStructure.Window.inclusion
          (lower + shift)
          (upper + shift))
        (fun object => Eq.refl object.object)).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight
          degree
          shift
          lower_le_degree
          degree_le_upper
          complex) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight
        degree
        shift
        lower_le_degree
        degree_le_upper
        complex :=
  rfl

/-- The reflexive pointwise-equality lift fixes translated singleton-window
representatives. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight_liftOfPointwiseEq_refl
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
        (TraceAnalyticMotivicTStructure.Window.inclusion
          (degree + shift)
          (degree + shift))
        (fun object => Eq.refl object.object)).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
          shift
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
        shift
        complex
        degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
