import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Assembly.NullHomotopy.NamedOrthogonality.DescentChannel.HomologyDischarged.Owner

/-!
# Projections from the homology-discharged descent-channel assembly

This file exposes the orthogonality and truncation-triangle fields supplied by
the descent-channel null-homotopy t-structure assembly after cochain homology
has been discharged from the abelian-envelope theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

section HomologyDischargedDescentChannelInputs

variable
    (allBoundedStable :
      ∀ object : TraceAnalyticDMgmComparisonSource,
        TraceAnalyticDMgmComparisonSource.boundedStableObject object)
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

/-- The homology-discharged descent-channel assembly supplies Mathlib's
orthogonality field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentChannelHomologyDischarged_zero
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentChannelHomologyDischarged
          allBoundedStable
          nullHomotopicIdentity
          descentChannel_zero).LE
        0
        source)
    (target_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityAndDescentChannelHomologyDischarged
          allBoundedStable
          nullHomotopicIdentity
          descentChannel_zero).GE
        1
        target) :
    hom = 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentChannelHomologyDischarged
      allBoundedStable
      nullHomotopicIdentity
      descentChannel_zero).zero'
    hom
    source_mem
    target_mem

/-- The homology-discharged descent-channel assembly supplies Mathlib's
adjacent truncation-triangle field. -/
theorem tStructureOfNullHomotopicIdentityAndDescentChannelHomologyDischarged_exists_triangle_zero_one
    (object : TraceAnalyticDMgmComparisonSource) :
    ∃ (left middle right : TraceAnalyticDMgmComparisonSource)
      (first : left ⟶ middle)
      (second : middle ⟶ right)
      (third : right ⟶ left⟦(1 : ℤ)⟧),
      middle = object ∧
        (TraceAnalyticMotivicTStructure
          .tStructureOfNullHomotopicIdentityAndDescentChannelHomologyDischarged
            allBoundedStable
            nullHomotopicIdentity
            descentChannel_zero).LE
          0
          left ∧
        (TraceAnalyticMotivicTStructure
          .tStructureOfNullHomotopicIdentityAndDescentChannelHomologyDischarged
            allBoundedStable
            nullHomotopicIdentity
            descentChannel_zero).GE
          1
          right ∧
        Pretriangulated.Triangle.mk first second third ∈ distTriang
          TraceAnalyticDMgmComparisonSource :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndDescentChannelHomologyDischarged
      allBoundedStable
      nullHomotopicIdentity
      descentChannel_zero)
    .exists_triangle_zero_one
      object

end HomologyDischargedDescentChannelInputs

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
