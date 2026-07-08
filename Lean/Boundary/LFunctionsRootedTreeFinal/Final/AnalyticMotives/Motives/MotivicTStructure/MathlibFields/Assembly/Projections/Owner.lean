import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Assembly.Owner

/-!
# Projections from the global-input Mathlib t-structure assembly

This file exposes the concrete Mathlib record fields supplied by
`tStructureOfGlobalAnalyticInputs`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

section GlobalAnalyticInputs

variable
    (allBoundedStable :
      ∀ object : TraceAnalyticDMgmComparisonSource,
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
              complex.complex))
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

/-- The global-input assembly supplies Mathlib's `LE` iso-closure field. -/
theorem tStructureOfGlobalAnalyticInputs_LE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticMotivicTStructure
        .tStructureOfGlobalAnalyticInputs
          allBoundedStable
          homology
          coneComparison
          leftFraction_numerator_localizationInput_postcomp_zero).LE
        cut) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfGlobalAnalyticInputs
      allBoundedStable
      homology
      coneComparison
      leftFraction_numerator_localizationInput_postcomp_zero)
    .LE_closedUnderIsomorphisms
      cut

/-- The global-input assembly supplies Mathlib's `GE` iso-closure field. -/
theorem tStructureOfGlobalAnalyticInputs_GE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticMotivicTStructure
        .tStructureOfGlobalAnalyticInputs
          allBoundedStable
          homology
          coneComparison
          leftFraction_numerator_localizationInput_postcomp_zero).GE
        cut) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfGlobalAnalyticInputs
      allBoundedStable
      homology
      coneComparison
      leftFraction_numerator_localizationInput_postcomp_zero)
    .GE_closedUnderIsomorphisms
      cut

/-- The global-input assembly supplies Mathlib's `LE_shift` field. -/
theorem tStructureOfGlobalAnalyticInputs_LE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      (TraceAnalyticMotivicTStructure
        .tStructureOfGlobalAnalyticInputs
          allBoundedStable
          homology
          coneComparison
          leftFraction_numerator_localizationInput_postcomp_zero).LE
        n
        object) :
    (TraceAnalyticMotivicTStructure
      .tStructureOfGlobalAnalyticInputs
        allBoundedStable
        homology
        coneComparison
        leftFraction_numerator_localizationInput_postcomp_zero).LE
      n'
      (object⟦a⟧) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfGlobalAnalyticInputs
      allBoundedStable
      homology
      coneComparison
      leftFraction_numerator_localizationInput_postcomp_zero).LE_shift
    n
    a
    n'
    h
    object
    membership

/-- The global-input assembly supplies Mathlib's `GE_shift` field. -/
theorem tStructureOfGlobalAnalyticInputs_GE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      (TraceAnalyticMotivicTStructure
        .tStructureOfGlobalAnalyticInputs
          allBoundedStable
          homology
          coneComparison
          leftFraction_numerator_localizationInput_postcomp_zero).GE
        n
        object) :
    (TraceAnalyticMotivicTStructure
      .tStructureOfGlobalAnalyticInputs
        allBoundedStable
        homology
        coneComparison
        leftFraction_numerator_localizationInput_postcomp_zero).GE
      n'
      (object⟦a⟧) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfGlobalAnalyticInputs
      allBoundedStable
      homology
      coneComparison
      leftFraction_numerator_localizationInput_postcomp_zero).GE_shift
    n
    a
    n'
    h
    object
    membership

/-- The global-input assembly supplies Mathlib's adjacent `LE` monotonicity
field. -/
theorem tStructureOfGlobalAnalyticInputs_LE_zero_le :
    (TraceAnalyticMotivicTStructure
      .tStructureOfGlobalAnalyticInputs
        allBoundedStable
        homology
        coneComparison
        leftFraction_numerator_localizationInput_postcomp_zero).LE 0 ≤
      (TraceAnalyticMotivicTStructure
        .tStructureOfGlobalAnalyticInputs
          allBoundedStable
          homology
          coneComparison
          leftFraction_numerator_localizationInput_postcomp_zero).LE 1 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfGlobalAnalyticInputs
      allBoundedStable
      homology
      coneComparison
      leftFraction_numerator_localizationInput_postcomp_zero).LE_zero_le

/-- The global-input assembly supplies Mathlib's adjacent `GE` monotonicity
field. -/
theorem tStructureOfGlobalAnalyticInputs_GE_one_le :
    (TraceAnalyticMotivicTStructure
      .tStructureOfGlobalAnalyticInputs
        allBoundedStable
        homology
        coneComparison
        leftFraction_numerator_localizationInput_postcomp_zero).GE 1 ≤
      (TraceAnalyticMotivicTStructure
        .tStructureOfGlobalAnalyticInputs
          allBoundedStable
          homology
          coneComparison
          leftFraction_numerator_localizationInput_postcomp_zero).GE 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfGlobalAnalyticInputs
      allBoundedStable
      homology
      coneComparison
      leftFraction_numerator_localizationInput_postcomp_zero).GE_one_le

/-- The global-input assembly supplies Mathlib's orthogonality field. -/
theorem tStructureOfGlobalAnalyticInputs_zero
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfGlobalAnalyticInputs
          allBoundedStable
          homology
          coneComparison
          leftFraction_numerator_localizationInput_postcomp_zero).LE
        0
        source)
    (target_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfGlobalAnalyticInputs
          allBoundedStable
          homology
          coneComparison
          leftFraction_numerator_localizationInput_postcomp_zero).GE
        1
        target) :
    hom = 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfGlobalAnalyticInputs
      allBoundedStable
      homology
      coneComparison
      leftFraction_numerator_localizationInput_postcomp_zero).zero'
    hom
    source_mem
    target_mem

/-- The global-input assembly supplies Mathlib's truncation-triangle existence
field in the exact constructor order. -/
theorem tStructureOfGlobalAnalyticInputs_exists_triangle_zero_one
    (object : TraceAnalyticDMgmComparisonSource) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ :
        (TraceAnalyticMotivicTStructure
          .tStructureOfGlobalAnalyticInputs
            allBoundedStable
            homology
            coneComparison
            leftFraction_numerator_localizationInput_postcomp_zero).LE
          0
          lower)
      (_ :
        (TraceAnalyticMotivicTStructure
          .tStructureOfGlobalAnalyticInputs
            allBoundedStable
            homology
            coneComparison
            leftFraction_numerator_localizationInput_postcomp_zero).GE
          1
          upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfGlobalAnalyticInputs
      allBoundedStable
      homology
      coneComparison
      leftFraction_numerator_localizationInput_postcomp_zero)
    .exists_triangle_zero_one
      object

end GlobalAnalyticInputs

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
