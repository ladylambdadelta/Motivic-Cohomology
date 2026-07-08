import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Assembly.NullHomotopy.NamedOrthogonality.DescentChannel.Owner

/-!
# Projections from the descent-channel Mathlib t-structure assembly

This file exposes the concrete Mathlib record fields supplied by
`tStructureOfNullHomotopicIdentityAndDescentChannel`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

section DescentChannelInputs

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
    (descentChannel_zero :
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
                TraceLocalizationInput.descentChannel_stableSource
                  inputSource
                  inputTarget,
              fraction.f ≫
                  (eqToHom source_eq ≫
                    TraceLocalizationInput.descentChannel_stableMap
                      inputSource
                      inputTarget) =
                0)

/-- The descent-channel assembly supplies Mathlib's `LE` iso-closure field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentChannel_LE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentChannel
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentChannel_zero).LE
        cut) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentChannel
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentChannel_zero)
    .LE_closedUnderIsomorphisms
      cut

/-- The descent-channel assembly supplies Mathlib's `GE` iso-closure field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentChannel_GE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentChannel
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentChannel_zero).GE
        cut) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentChannel
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentChannel_zero)
    .GE_closedUnderIsomorphisms
      cut

/-- The descent-channel assembly supplies Mathlib's `LE_shift` field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentChannel_LE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentChannel
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentChannel_zero).LE
        n
        object) :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndDescentChannel
        allBoundedStable
        homology
        nullHomotopicIdentity
        descentChannel_zero).LE
      n'
      (object⟦a⟧) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentChannel
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentChannel_zero).LE_shift
    n
    a
    n'
    h
    object
    membership

/-- The descent-channel assembly supplies Mathlib's `GE_shift` field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentChannel_GE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentChannel
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentChannel_zero).GE
        n
        object) :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndDescentChannel
        allBoundedStable
        homology
        nullHomotopicIdentity
        descentChannel_zero).GE
      n'
      (object⟦a⟧) :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentChannel
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentChannel_zero).GE_shift
    n
    a
    n'
    h
    object
    membership

/-- The descent-channel assembly supplies Mathlib's adjacent `LE`
monotonicity field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentChannel_LE_zero_le :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndDescentChannel
        allBoundedStable
        homology
        nullHomotopicIdentity
        descentChannel_zero).LE 0 ≤
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentChannel
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentChannel_zero).LE 1 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentChannel
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentChannel_zero).LE_zero_le

/-- The descent-channel assembly supplies Mathlib's adjacent `GE`
monotonicity field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentChannel_GE_one_le :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndDescentChannel
        allBoundedStable
        homology
        nullHomotopicIdentity
        descentChannel_zero).GE 1 ≤
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentChannel
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentChannel_zero).GE 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentChannel
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentChannel_zero).GE_one_le

/-- The descent-channel assembly supplies Mathlib's orthogonality field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentChannel_zero
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentChannel
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentChannel_zero).LE
        0
        source)
    (target_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentChannel
          allBoundedStable
          homology
          nullHomotopicIdentity
          descentChannel_zero).GE
        1
        target) :
    hom = 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentChannel
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentChannel_zero).zero'
    hom
    source_mem
    target_mem

/-- The descent-channel assembly supplies Mathlib's adjacent truncation-triangle
field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentChannel_exists_triangle_zero_one
    (object : TraceAnalyticDMgmComparisonSource) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ :
        (TraceAnalyticMotivicTStructure
          .tStructureOfNullHomotopicIdentityAndDescentChannel
            allBoundedStable
            homology
            nullHomotopicIdentity
            descentChannel_zero).LE
          0
          lower)
      (_ :
        (TraceAnalyticMotivicTStructure
          .tStructureOfNullHomotopicIdentityAndDescentChannel
            allBoundedStable
            homology
            nullHomotopicIdentity
            descentChannel_zero).GE
          1
          upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentChannel
      allBoundedStable
      homology
      nullHomotopicIdentity
      descentChannel_zero)
    .exists_triangle_zero_one
      object

end DescentChannelInputs

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
