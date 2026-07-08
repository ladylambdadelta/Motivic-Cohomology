import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Diagonal.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Diagonal.Representatives.Owner

/-!
# Round-trip formulas for singleton heart-to-window representatives

This file records that exact-degree heart representatives are fixed by the
singleton heart-to-window functor followed by the diagonal-window-to-heart
functor.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- An exact-degree heart representative is fixed by singleton
heart-to-window followed by diagonal-window-to-heart. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow_self_diagonalToHeart
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.diagonalToHeart degree).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          (lower := degree)
          (center := degree)
          (upper := degree)
          le_rfl
          le_rfl).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
        complex
        degree :=
  rfl

/-- A translated exact-degree heart representative is fixed by singleton
heart-to-window followed by diagonal-window-to-heart. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow_self_diagonalToHeart
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.diagonalToHeart
        (degree + shift)).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          (lower := degree + shift)
          (center := degree + shift)
          (upper := degree + shift)
          le_rfl
          le_rfl).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
        shift
        complex
        degree :=
  rfl

/-- A singleton-window representative is fixed by diagonal-window-to-heart
followed by singleton heart-to-window. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_diagonalToHeart_toWindow_self
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
        ((TraceAnalyticMotivicTStructure.Window.diagonalToHeart degree).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
        complex
        degree :=
  rfl

/-- A translated singleton-window representative is fixed by
diagonal-window-to-heart followed by singleton heart-to-window. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight_diagonalToHeart_toWindow_self
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
        ((TraceAnalyticMotivicTStructure.Window.diagonalToHeart
          (degree + shift)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
        shift
        complex
        degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
