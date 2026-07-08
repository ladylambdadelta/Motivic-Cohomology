import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Owner

/-!
# Projection formulas for shifted bounded window representatives

This file records how shifted bounded window representative objects project to
the corresponding aisle and coaisle representative objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Projecting a shifted bounded window representative to its upper aisle gives
the shifted bounded aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBounded_toAisle
    {lower upper : ℤ}
    (degree : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle lower upper).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
          degree
          lower_le_degree
          degree_le_upper
          complex) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        upper
        complex
        degree
        degree_le_upper :=
  rfl

/-- Projecting a shifted bounded window representative to its lower coaisle
gives the shifted bounded coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBounded_toCoaisle
    {lower upper : ℤ}
    (degree : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle lower upper).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
          degree
          lower_le_degree
          degree_le_upper
          complex) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        lower
        complex
        degree
        lower_le_degree :=
  rfl

/-- Projecting a singleton shifted bounded window representative to its aisle
gives the exact-degree aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_toAisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.toAisle degree degree).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting a singleton shifted bounded window representative to its
coaisle gives the exact-degree coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_toCoaisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle degree degree).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
