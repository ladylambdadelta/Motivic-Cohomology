import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Diagonal.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Owner

/-!
# Representative formulas for singleton heart-to-window intervals

This file records the representative-level specialization of heart-to-window
interval functors to diagonal singleton windows.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Sending an exact-degree heart representative through the singleton
heart-to-window interval gives the singleton-window representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow_self
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toWindow
        (lower := degree)
        (center := degree)
        (upper := degree)
        le_rfl
        le_rfl).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
        complex
        degree :=
  rfl

/-- Sending a translated exact-degree heart representative through the
singleton heart-to-window interval gives the translated singleton-window
representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow_self
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toWindow
        (lower := degree + shift)
        (center := degree + shift)
        (upper := degree + shift)
        le_rfl
        le_rfl).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
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
