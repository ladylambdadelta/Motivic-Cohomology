import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Diagonal.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Owner

/-!
# Projection formulas for shifted bounded heart representatives

This file records how exact-degree shifted bounded heart representatives map to
aisle, coaisle, and diagonal-window representatives.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Projecting an exact-degree heart representative to the aisle gives the
exact-degree aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toAisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toAisle degree).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting an exact-degree heart representative to the coaisle gives the
exact-degree coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toCoaisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toCoaisle degree).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- Sending an exact-degree heart representative to the diagonal window gives
the singleton-window representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toDiagonalWindow
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow degree).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
        complex
        degree :=
  rfl

/-- Sending a singleton-window representative to the heart gives the
exact-degree heart representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_diagonalToHeart
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.diagonalToHeart degree).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
        complex
        degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
