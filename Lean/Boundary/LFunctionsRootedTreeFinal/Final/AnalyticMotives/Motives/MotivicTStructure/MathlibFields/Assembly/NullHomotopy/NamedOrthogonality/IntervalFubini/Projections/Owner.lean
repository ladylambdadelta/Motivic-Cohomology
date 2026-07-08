import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Assembly.NullHomotopy.NamedOrthogonality.IntervalFubini.Owner

/-!
# Projections from the Interval-Fubini Mathlib t-structure assembly

This file exposes the concrete Mathlib record fields supplied by
`tStructureOfNullHomotopicIdentityAndIntervalFubini`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

section IntervalFubiniInputs

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
    (intervalFubini_zero :
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
        ∃ inputSource : QTraceExpression,
          ∃ inputTarget : QTraceExpression,
            ∃ source_eq :
              fraction.Y' =
                TraceLocalizationInput.intervalFubini_stableSource
                  inputSource
                  inputTarget,
              fraction.f ≫
                  (eqToHom source_eq ≫
                    TraceLocalizationInput.intervalFubini_stableMap
                      inputSource
                      inputTarget) =
                0)

/-- The Interval-Fubini assembly supplies Mathlib's `LE` iso-closure field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalFubini_LE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalFubini
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalFubini_zero).LE
        cut) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalFubini
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalFubini_zero)
    .LE_closedUnderIsomorphisms
      cut

/-- The Interval-Fubini assembly supplies Mathlib's `GE` iso-closure field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalFubini_GE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalFubini
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalFubini_zero).GE
        cut) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalFubini
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalFubini_zero)
    .GE_closedUnderIsomorphisms
      cut

/-- The Interval-Fubini assembly supplies Mathlib's `LE_shift` field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalFubini_LE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalFubini
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalFubini_zero).LE
        n
        object) :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndIntervalFubini
        allBoundedStable
        homology
        nullHomotopicIdentity
        intervalFubini_zero).LE
      n'
      (object⟦a⟧) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalFubini
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalFubini_zero).LE_shift
    n
    a
    n'
    h
    object
    membership

/-- The Interval-Fubini assembly supplies Mathlib's `GE_shift` field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalFubini_GE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalFubini
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalFubini_zero).GE
        n
        object) :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndIntervalFubini
        allBoundedStable
        homology
        nullHomotopicIdentity
        intervalFubini_zero).GE
      n'
      (object⟦a⟧) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalFubini
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalFubini_zero).GE_shift
    n
    a
    n'
    h
    object
    membership

/-- The Interval-Fubini assembly supplies Mathlib's adjacent `LE`
monotonicity field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalFubini_LE_zero_le :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndIntervalFubini
        allBoundedStable
        homology
        nullHomotopicIdentity
        intervalFubini_zero).LE 0 ≤
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalFubini
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalFubini_zero).LE 1 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalFubini
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalFubini_zero).LE_zero_le

/-- The Interval-Fubini assembly supplies Mathlib's adjacent `GE`
monotonicity field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalFubini_GE_one_le :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndIntervalFubini
        allBoundedStable
        homology
        nullHomotopicIdentity
        intervalFubini_zero).GE 1 ≤
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalFubini
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalFubini_zero).GE 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalFubini
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalFubini_zero).GE_one_le

/-- The Interval-Fubini assembly supplies Mathlib's orthogonality field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalFubini_zero
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalFubini
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalFubini_zero).LE
        0
        source)
    (target_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalFubini
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalFubini_zero).GE
        1
        target) :
    hom = 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalFubini
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalFubini_zero).zero'
    hom
    source_mem
    target_mem

/-- The Interval-Fubini assembly supplies Mathlib's adjacent truncation-triangle
field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalFubini_exists_triangle_zero_one
    (object : TraceAnalyticDMgmComparisonSource) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ :
        (TraceAnalyticMotivicTStructure
          .tStructureOfNullHomotopicIdentityAndIntervalFubini
            allBoundedStable
            homology
            nullHomotopicIdentity
            intervalFubini_zero).LE
          0
          lower)
      (_ :
        (TraceAnalyticMotivicTStructure
          .tStructureOfNullHomotopicIdentityAndIntervalFubini
            allBoundedStable
            homology
            nullHomotopicIdentity
            intervalFubini_zero).GE
          1
          upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalFubini
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalFubini_zero)
    .exists_triangle_zero_one
      object

end IntervalFubiniInputs

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
