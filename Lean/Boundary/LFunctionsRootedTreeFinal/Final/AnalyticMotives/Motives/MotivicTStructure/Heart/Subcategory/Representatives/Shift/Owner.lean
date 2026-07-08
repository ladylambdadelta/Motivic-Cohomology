import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Representatives.Transport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Owner

/-!
# Shift formulas for heart representative constructors

This file records how translated exact-degree heart representatives interact
with the diagonal-window bridge.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Sending a translated exact-degree heart representative to the diagonal
window gives the translated singleton-window representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toDiagonalWindow
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow
        (degree + shift)).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
          shift
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
        shift
        complex
        degree :=
  rfl

/-- Sending a translated singleton-window representative to the heart gives
the translated exact-degree heart representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight_diagonalToHeart
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.diagonalToHeart
        (degree + shift)).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
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
