import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.TruncationTriangle.BoundedRepresentative.Owner

/-!
# Truncation triangles for bounded stable source objects

This file keeps the bounded full subcategory on the actual analytic
comparison-source objects.  The displayed predicates are the Mathlib-facing
aisle and coaisle predicates pulled back along the bounded-source inclusion,
and the triangle theorem is the concrete ambient truncation triangle supplied
by the bounded-source representative calculus.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The Mathlib-facing `LE` predicate pulled back to bounded stable source
objects. -/
abbrev mathlibLE
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    Prop :=
  TraceAnalyticMotivicTStructure.mathlibLE cut object.object

/-- The Mathlib-facing `GE` predicate pulled back to bounded stable source
objects. -/
abbrev mathlibGE
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    Prop :=
  TraceAnalyticMotivicTStructure.mathlibGE cut object.object

/-- Pullback of the Mathlib-facing `LE` predicate agrees with the ambient
predicate on the included object. -/
theorem mathlibLE_iff_ambient
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE cut object ↔
      TraceAnalyticMotivicTStructure.mathlibLE cut object.object :=
  Iff.rfl

/-- Pullback of the Mathlib-facing `GE` predicate agrees with the ambient
predicate on the included object. -/
theorem mathlibGE_iff_ambient
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE cut object ↔
      TraceAnalyticMotivicTStructure.mathlibGE cut object.object :=
  Iff.rfl

/-- Every bounded stable source object has the ambient Mathlib-shaped
truncation triangle. -/
theorem exists_ambient_triangle_zero_one
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable)
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
              cut
              complex.complex)) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticMotivicTStructure.mathlibLE 0 lower ∧
        TraceAnalyticMotivicTStructure.mathlibGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object.object)
            (secondMap : object.object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .boundedStableObject_exists_triangle_zero_one
      cut
      object.membership
      homology
      coneComparison

/-- Every bounded stable source object has the ambient Mathlib-shaped
truncation triangle in the exact field order used by
`TStructure.exists_triangle_zero_one`. -/
theorem exists_ambient_triangle_zero_one_fieldShape
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable)
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
              cut
              complex.complex)) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ : TraceAnalyticMotivicTStructure.mathlibLE 0 lower)
      (_ : TraceAnalyticMotivicTStructure.mathlibGE 1 upper)
      (firstMap : lower ⟶ object.object)
      (secondMap : object.object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .boundedStableObject_exists_triangle_zero_one_fieldShape
      cut
      object.membership
      homology
      coneComparison

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
