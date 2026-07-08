import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Reindexed.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Orthogonality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.TruncationTriangle.BoundedRepresentative.Owner

/-!
# Mathlib t-structure field surface

This file names the concrete fields for Mathlib's `TStructure` record that
have already been proved from the analytic motivic aisle, coaisle, shift,
orthogonality, and bounded truncation-triangle constructions.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The Mathlib-facing `LE` predicate field. -/
abbrev tStructureLE
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource → Prop :=
  TraceAnalyticMotivicTStructure.mathlibLE cut

/-- The Mathlib-facing `GE` predicate field. -/
abbrev tStructureGE
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource → Prop :=
  TraceAnalyticMotivicTStructure.mathlibGE cut

/-- The closed-under-isomorphism field for the Mathlib-facing `LE`
predicate. -/
def tStructureLE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticMotivicTStructure.tStructureLE cut) :=
  TraceAnalyticMotivicTStructure.mathlibLE_closedUnderIsomorphisms cut

/-- The closed-under-isomorphism field for the Mathlib-facing `GE`
predicate. -/
def tStructureGE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticMotivicTStructure.tStructureGE cut) :=
  TraceAnalyticMotivicTStructure.mathlibGE_closedUnderIsomorphisms cut

/-- The Mathlib `LE_shift` field for the analytic motivic predicates. -/
theorem tStructureLE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership : TraceAnalyticMotivicTStructure.tStructureLE n object) :
    TraceAnalyticMotivicTStructure.tStructureLE n' (object⟦a⟧) :=
  TraceAnalyticMotivicTStructure.mathlibLE_shift
    n
    a
    n'
    h
    object
    membership

/-- The Mathlib `GE_shift` field for the analytic motivic predicates. -/
theorem tStructureGE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership : TraceAnalyticMotivicTStructure.tStructureGE n object) :
    TraceAnalyticMotivicTStructure.tStructureGE n' (object⟦a⟧) :=
  TraceAnalyticMotivicTStructure.mathlibGE_shift
    n
    a
    n'
    h
    object
    membership

/-- The Mathlib adjacent monotonicity field for `LE`. -/
theorem tStructureLE_zero_le :
    TraceAnalyticMotivicTStructure.tStructureLE 0 ≤
      TraceAnalyticMotivicTStructure.tStructureLE 1 :=
  TraceAnalyticMotivicTStructure.mathlibLE_zero_le

/-- The Mathlib adjacent monotonicity field for `GE`. -/
theorem tStructureGE_one_le :
    TraceAnalyticMotivicTStructure.tStructureGE 1 ≤
      TraceAnalyticMotivicTStructure.tStructureGE 0 :=
  TraceAnalyticMotivicTStructure.mathlibGE_one_le

/-- A concrete orthogonality field obtained from localization-input numerator
cancellation. -/
theorem tStructure_zero_of_leftFraction_numerator_localizationInput_postcomp_zero
    (leftFraction_numerator_localizationInput_postcomp_zero :
      ∀ {sourceBound targetBound : Nat}
        (sourceComplex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
            sourceBound)
        (sourceDegree : ℤ)
        (targetComplex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
            targetBound)
        (targetDegree : ℤ),
        -0 ≤ sourceDegree →
        targetDegree ≤ -1 →
        (fraction :
          TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
            (TraceAnalyticMotiveComparison
              .sourceShiftedWeightBoundedHomotopyObject
                sourceComplex
                sourceDegree)
            (TraceAnalyticMotiveComparison
              .sourceShiftedWeightBoundedHomotopyObject
                targetComplex
                targetDegree)),
        ∃ input : TraceLocalizationInput,
          ∃ source_eq : fraction.Y' = input.stableSource,
            fraction.f ≫ (eqToHom source_eq ≫ input.stableMap) = 0)
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.tStructureLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.tStructureGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure
    .mathlib_zero_of_leftFraction_numerator_localizationInput_postcomp_zero
      leftFraction_numerator_localizationInput_postcomp_zero
      hom
      source_mem
      target_mem

/-- The Mathlib truncation-triangle field for a bounded stable source object,
using the concrete normalized cochain-decomposition triangle at cut `0`. -/
theorem tStructure_exists_triangle_zero_one_of_boundedStableObject
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
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
              0
              complex.complex)) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticMotivicTStructure.tStructureLE 0 lower ∧
        TraceAnalyticMotivicTStructure.tStructureGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure.boundedStableObject_exists_triangle_zero_one
    0
    membership
    homology
    coneComparison

/-- The Mathlib truncation-triangle field for a bounded stable source object,
in the exact field order used by `TStructure.exists_triangle_zero_one`. -/
theorem tStructure_exists_triangle_zero_one_of_boundedStableObject_fieldShape
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
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
              0
              complex.complex)) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ : TraceAnalyticMotivicTStructure.tStructureLE 0 lower)
      (_ : TraceAnalyticMotivicTStructure.tStructureGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .boundedStableObject_exists_triangle_zero_one_fieldShape
      0
      membership
      homology
      coneComparison

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
