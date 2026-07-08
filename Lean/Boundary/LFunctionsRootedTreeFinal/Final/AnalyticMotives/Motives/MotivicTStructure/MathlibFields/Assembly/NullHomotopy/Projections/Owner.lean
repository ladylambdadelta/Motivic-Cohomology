import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Assembly.NullHomotopy.Owner

/-!
# Projections from the null-homotopy Mathlib t-structure assembly

This file exposes the concrete Mathlib record fields supplied by
`tStructureOfNullHomotopicIdentity`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

section NullHomotopyInputs

variable
    (allBoundedStable :
      ∀ object : TraceAnalyticDMgmComparisonSource,
        TraceAnalyticDMgmComparisonSource.boundedStableObject object)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∃ hom :
          ∀ i j,
            (ComplexShape.up ℤ).Rel j i →
              (CochainComplex.mappingCone
                (TraceAnalyticMotivicTStructure
                  .additiveNormalizedConeComparisonCochainMap
                    0
                    complex.complex)).X i ⟶
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      0
                      complex.complex)).X j,
          𝟙
              (CochainComplex.mappingCone
                (TraceAnalyticMotivicTStructure
                  .additiveNormalizedConeComparisonCochainMap
                    0
                    complex.complex)) =
            _root_.HomologicalComplex.nullHomotopicMap' hom)
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

/-- The null-homotopy assembly supplies Mathlib's `LE` iso-closure field. -/
theorem tStructureOfNullHomotopicIdentity_LE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentity
          allBoundedStable
          homology
          nullHomotopicIdentity
          leftFraction_numerator_localizationInput_postcomp_zero).LE
        cut) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentity
      allBoundedStable
      homology
      nullHomotopicIdentity
      leftFraction_numerator_localizationInput_postcomp_zero)
    .LE_closedUnderIsomorphisms
      cut

/-- The null-homotopy assembly supplies Mathlib's `GE` iso-closure field. -/
theorem tStructureOfNullHomotopicIdentity_GE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentity
          allBoundedStable
          homology
          nullHomotopicIdentity
          leftFraction_numerator_localizationInput_postcomp_zero).GE
        cut) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentity
      allBoundedStable
      homology
      nullHomotopicIdentity
      leftFraction_numerator_localizationInput_postcomp_zero)
    .GE_closedUnderIsomorphisms
      cut

/-- The null-homotopy assembly supplies Mathlib's `LE_shift` field. -/
theorem tStructureOfNullHomotopicIdentity_LE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentity
          allBoundedStable
          homology
          nullHomotopicIdentity
          leftFraction_numerator_localizationInput_postcomp_zero).LE
        n
        object) :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentity
        allBoundedStable
        homology
        nullHomotopicIdentity
        leftFraction_numerator_localizationInput_postcomp_zero).LE
      n'
      (object⟦a⟧) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentity
      allBoundedStable
      homology
      nullHomotopicIdentity
      leftFraction_numerator_localizationInput_postcomp_zero).LE_shift
    n
    a
    n'
    h
    object
    membership

/-- The null-homotopy assembly supplies Mathlib's `GE_shift` field. -/
theorem tStructureOfNullHomotopicIdentity_GE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentity
          allBoundedStable
          homology
          nullHomotopicIdentity
          leftFraction_numerator_localizationInput_postcomp_zero).GE
        n
        object) :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentity
        allBoundedStable
        homology
        nullHomotopicIdentity
        leftFraction_numerator_localizationInput_postcomp_zero).GE
      n'
      (object⟦a⟧) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentity
      allBoundedStable
      homology
      nullHomotopicIdentity
      leftFraction_numerator_localizationInput_postcomp_zero).GE_shift
    n
    a
    n'
    h
    object
    membership

/-- The null-homotopy assembly supplies Mathlib's adjacent `LE` monotonicity
field. -/
theorem tStructureOfNullHomotopicIdentity_LE_zero_le :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentity
        allBoundedStable
        homology
        nullHomotopicIdentity
        leftFraction_numerator_localizationInput_postcomp_zero).LE 0 ≤
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentity
          allBoundedStable
          homology
          nullHomotopicIdentity
          leftFraction_numerator_localizationInput_postcomp_zero).LE 1 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentity
      allBoundedStable
      homology
      nullHomotopicIdentity
      leftFraction_numerator_localizationInput_postcomp_zero).LE_zero_le

/-- The null-homotopy assembly supplies Mathlib's adjacent `GE` monotonicity
field. -/
theorem tStructureOfNullHomotopicIdentity_GE_one_le :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentity
        allBoundedStable
        homology
        nullHomotopicIdentity
        leftFraction_numerator_localizationInput_postcomp_zero).GE 1 ≤
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentity
          allBoundedStable
          homology
          nullHomotopicIdentity
          leftFraction_numerator_localizationInput_postcomp_zero).GE 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentity
      allBoundedStable
      homology
      nullHomotopicIdentity
      leftFraction_numerator_localizationInput_postcomp_zero).GE_one_le

/-- The null-homotopy assembly supplies Mathlib's orthogonality field. -/
theorem tStructureOfNullHomotopicIdentity_zero
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentity
          allBoundedStable
          homology
          nullHomotopicIdentity
          leftFraction_numerator_localizationInput_postcomp_zero).LE
        0
        source)
    (target_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentity
          allBoundedStable
          homology
          nullHomotopicIdentity
          leftFraction_numerator_localizationInput_postcomp_zero).GE
        1
        target) :
    hom = 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentity
      allBoundedStable
      homology
      nullHomotopicIdentity
      leftFraction_numerator_localizationInput_postcomp_zero).zero'
    hom
    source_mem
    target_mem

/-- The null-homotopy assembly supplies Mathlib's adjacent truncation-triangle
field. -/
theorem tStructureOfNullHomotopicIdentity_exists_triangle_zero_one
    (object : TraceAnalyticDMgmComparisonSource) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ :
        (TraceAnalyticMotivicTStructure
          .tStructureOfNullHomotopicIdentity
            allBoundedStable
            homology
            nullHomotopicIdentity
            leftFraction_numerator_localizationInput_postcomp_zero).LE
          0
          lower)
      (_ :
        (TraceAnalyticMotivicTStructure
          .tStructureOfNullHomotopicIdentity
            allBoundedStable
            homology
            nullHomotopicIdentity
            leftFraction_numerator_localizationInput_postcomp_zero).GE
          1
          upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentity
      allBoundedStable
      homology
      nullHomotopicIdentity
      leftFraction_numerator_localizationInput_postcomp_zero)
    .exists_triangle_zero_one
      object

end NullHomotopyInputs

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
