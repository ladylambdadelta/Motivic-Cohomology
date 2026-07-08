import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Assembly.NullHomotopy.NamedOrthogonality.IntervalStokes.Owner

/-!
# Projections from the Interval-Stokes Mathlib t-structure assembly

This file exposes the concrete Mathlib record fields supplied by
`tStructureOfNullHomotopicIdentityAndIntervalStokes`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

section IntervalStokesInputs

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
    (intervalStokes_zero :
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
                TraceLocalizationInput.intervalStokes_stableSource
                  inputSource
                  inputTarget,
              fraction.f ≫
                  (eqToHom source_eq ≫
                    TraceLocalizationInput.intervalStokes_stableMap
                      inputSource
                      inputTarget) =
                0)

/-- The Interval-Stokes assembly supplies Mathlib's `LE` iso-closure field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalStokes_LE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalStokes
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalStokes_zero).LE
        cut) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalStokes
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalStokes_zero)
    .LE_closedUnderIsomorphisms
      cut

/-- The Interval-Stokes assembly supplies Mathlib's `GE` iso-closure field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalStokes_GE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalStokes
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalStokes_zero).GE
        cut) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalStokes
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalStokes_zero)
    .GE_closedUnderIsomorphisms
      cut

/-- The Interval-Stokes assembly supplies Mathlib's `LE_shift` field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalStokes_LE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalStokes
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalStokes_zero).LE
        n
        object) :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndIntervalStokes
        allBoundedStable
        homology
        nullHomotopicIdentity
        intervalStokes_zero).LE
      n'
      (object⟦a⟧) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalStokes
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalStokes_zero).LE_shift
    n
    a
    n'
    h
    object
    membership

/-- The Interval-Stokes assembly supplies Mathlib's `GE_shift` field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalStokes_GE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalStokes
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalStokes_zero).GE
        n
        object) :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndIntervalStokes
        allBoundedStable
        homology
        nullHomotopicIdentity
        intervalStokes_zero).GE
      n'
      (object⟦a⟧) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalStokes
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalStokes_zero).GE_shift
    n
    a
    n'
    h
    object
    membership

/-- The Interval-Stokes assembly supplies Mathlib's adjacent `LE`
monotonicity field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalStokes_LE_zero_le :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndIntervalStokes
        allBoundedStable
        homology
        nullHomotopicIdentity
        intervalStokes_zero).LE 0 ≤
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalStokes
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalStokes_zero).LE 1 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalStokes
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalStokes_zero).LE_zero_le

/-- The Interval-Stokes assembly supplies Mathlib's adjacent `GE`
monotonicity field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalStokes_GE_one_le :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndIntervalStokes
        allBoundedStable
        homology
        nullHomotopicIdentity
        intervalStokes_zero).GE 1 ≤
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalStokes
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalStokes_zero).GE 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalStokes
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalStokes_zero).GE_one_le

/-- The Interval-Stokes assembly supplies Mathlib's orthogonality field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalStokes_zero
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalStokes
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalStokes_zero).LE
        0
        source)
    (target_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndIntervalStokes
          allBoundedStable
          homology
          nullHomotopicIdentity
          intervalStokes_zero).GE
        1
        target) :
    hom = 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalStokes
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalStokes_zero).zero'
    hom
    source_mem
    target_mem

/-- The Interval-Stokes assembly supplies Mathlib's adjacent truncation-triangle
field. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalStokes_exists_triangle_zero_one
    (object : TraceAnalyticDMgmComparisonSource) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ :
        (TraceAnalyticMotivicTStructure
          .tStructureOfNullHomotopicIdentityAndIntervalStokes
            allBoundedStable
            homology
            nullHomotopicIdentity
            intervalStokes_zero).LE
          0
          lower)
      (_ :
        (TraceAnalyticMotivicTStructure
          .tStructureOfNullHomotopicIdentityAndIntervalStokes
            allBoundedStable
            homology
            nullHomotopicIdentity
            intervalStokes_zero).GE
          1
          upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalStokes
      allBoundedStable
      homology
      nullHomotopicIdentity
      intervalStokes_zero)
    .exists_triangle_zero_one
      object

end IntervalStokesInputs

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
