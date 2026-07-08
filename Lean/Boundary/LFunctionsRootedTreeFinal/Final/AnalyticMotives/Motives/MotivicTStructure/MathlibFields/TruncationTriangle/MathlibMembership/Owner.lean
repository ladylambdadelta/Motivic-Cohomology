import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSource.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.TruncationTriangle.BoundedRepresentative.Owner

/-!
# Truncation triangles for Mathlib-facing bounded membership

This file connects the Mathlib-facing aisle and coaisle predicates to the
concrete bounded-source truncation theorem.  The global
`exists_triangle_zero_one` field is then reduced to the remaining
bounded-generation statement for the analytic comparison source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- A Mathlib-facing `LE` object has the concrete truncation triangle supplied
by its bounded-source representative. -/
theorem exists_triangle_zero_one_of_mathlibLE
    (truncationCut membershipCut : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.mathlibLE membershipCut object)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
    (coneComparison :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        IsIso
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap
              truncationCut
              complex.complex)) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticMotivicTStructure.mathlibLE 0 lower ∧
        TraceAnalyticMotivicTStructure.mathlibGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .boundedStableObject_exists_triangle_zero_one
      truncationCut
      (TraceAnalyticMotivicTStructure
        .boundedStableObject_of_mathlibLE membershipCut membership)
      homology
      coneComparison

/-- A Mathlib-facing `GE` object has the concrete truncation triangle supplied
by its bounded-source representative. -/
theorem exists_triangle_zero_one_of_mathlibGE
    (truncationCut membershipCut : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.mathlibGE membershipCut object)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
    (coneComparison :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        IsIso
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap
              truncationCut
              complex.complex)) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticMotivicTStructure.mathlibLE 0 lower ∧
        TraceAnalyticMotivicTStructure.mathlibGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .boundedStableObject_exists_triangle_zero_one
      truncationCut
      (TraceAnalyticMotivicTStructure
        .boundedStableObject_of_mathlibGE membershipCut membership)
      homology
      coneComparison

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
