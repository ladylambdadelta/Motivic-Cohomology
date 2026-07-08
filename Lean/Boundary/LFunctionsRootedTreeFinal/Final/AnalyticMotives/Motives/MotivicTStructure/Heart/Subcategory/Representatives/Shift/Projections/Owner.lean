import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Representatives.Shift.Owner

/-!
# Projection formulas for translated heart representative constructors

This file records how translated exact-degree heart representatives project to
translated aisle and coaisle representative objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Projecting a translated exact-degree heart representative to the aisle gives
the translated exact-degree aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toAisle
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toAisle
        (degree + shift)).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
          shift
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
        degree
        shift
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting a translated exact-degree heart representative to the coaisle
gives the translated exact-degree coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toCoaisle
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toCoaisle
        (degree + shift)).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
          shift
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
        degree
        shift
        complex
        degree
        le_rfl :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
