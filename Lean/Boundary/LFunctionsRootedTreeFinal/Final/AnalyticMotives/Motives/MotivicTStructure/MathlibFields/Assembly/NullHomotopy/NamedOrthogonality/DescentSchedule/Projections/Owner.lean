import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Assembly.NullHomotopy.NamedOrthogonality.DescentSchedule.Owner

/-!
# Projections from the descent-schedule Mathlib t-structure assembly

This file exposes the concrete Mathlib record fields supplied by
`tStructureOfNullHomotopicIdentityAndDescentSchedule`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

section DescentScheduleInputs

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
    (descentSchedule_zero :
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
                TraceLocalizationInput.descentSchedule_stableSource
                  inputSource
                  inputTarget,
              fraction.f ≫
                  (eqToHom source_eq ≫
                    TraceLocalizationInput.descentSchedule_stableMap
                      inputSource
                      inputTarget) =
                0)

/-- The descent-schedule assembly supplies Mathlib's `LE` iso-closure
field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentSchedule_LE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentSchedule
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentSchedule_zero).LE
        cut) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentSchedule
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentSchedule_zero)
    .LE_closedUnderIsomorphisms
      cut

/-- The descent-schedule assembly supplies Mathlib's `GE` iso-closure
field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentSchedule_GE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentSchedule
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentSchedule_zero).GE
        cut) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentSchedule
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentSchedule_zero)
    .GE_closedUnderIsomorphisms
      cut

/-- The descent-schedule assembly supplies Mathlib's `LE_shift` field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentSchedule_LE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentSchedule
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentSchedule_zero).LE
        n
        object) :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndDescentSchedule
        allBoundedStable
        homology
        nullHomotopicIdentity
        descentSchedule_zero).LE
      n'
      (object⟦a⟧) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentSchedule
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentSchedule_zero).LE_shift
    n
    a
    n'
    h
    object
    membership

/-- The descent-schedule assembly supplies Mathlib's `GE_shift` field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentSchedule_GE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentSchedule
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentSchedule_zero).GE
        n
        object) :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndDescentSchedule
        allBoundedStable
        homology
        nullHomotopicIdentity
        descentSchedule_zero).GE
      n'
      (object⟦a⟧) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentSchedule
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentSchedule_zero).GE_shift
    n
    a
    n'
    h
    object
    membership

/-- The descent-schedule assembly supplies Mathlib's adjacent `LE`
monotonicity field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentSchedule_LE_zero_le :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndDescentSchedule
        allBoundedStable
        homology
        nullHomotopicIdentity
        descentSchedule_zero).LE 0 ≤
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentSchedule
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentSchedule_zero).LE 1 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentSchedule
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentSchedule_zero).LE_zero_le

/-- The descent-schedule assembly supplies Mathlib's adjacent `GE`
monotonicity field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentSchedule_GE_one_le :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndDescentSchedule
        allBoundedStable
        homology
        nullHomotopicIdentity
        descentSchedule_zero).GE 1 ≤
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentSchedule
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentSchedule_zero).GE 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentSchedule
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentSchedule_zero).GE_one_le

/-- The descent-schedule assembly supplies Mathlib's orthogonality field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentSchedule_zero
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentSchedule
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentSchedule_zero).LE
        0
        source)
    (target_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentSchedule
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentSchedule_zero).GE
        1
        target) :
    hom = 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentSchedule
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentSchedule_zero).zero'
    hom
    source_mem
    target_mem

/-- The descent-schedule assembly supplies Mathlib's adjacent truncation-triangle
field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentSchedule_exists_triangle_zero_one
    (object : TraceAnalyticDMgmComparisonSource) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ :
        (TraceAnalyticMotivicTStructure
          .tStructureOfNullHomotopicIdentityAndDescentSchedule
            allBoundedStable
            homology
            nullHomotopicIdentity
            descentSchedule_zero).LE
          0
          lower)
      (_ :
        (TraceAnalyticMotivicTStructure
          .tStructureOfNullHomotopicIdentityAndDescentSchedule
            allBoundedStable
            homology
            nullHomotopicIdentity
            descentSchedule_zero).GE
          1
          upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentSchedule
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentSchedule_zero)
    .exists_triangle_zero_one
      object

end DescentScheduleInputs

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
