import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.TStructureFields.Orthogonality.Owner

/-!
# Descent orthogonality fields on the degreewise bounded stable source

This file restricts the named descent analytic orthogonality reductions from
the ambient comparison source to the degreewise bounded stable source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Descent-channel numerator cancellation gives the orthogonality field on
the degreewise bounded stable source. -/
theorem tStructure_zero_of_descentChannel
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
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureGE 1 target) :
    hom = 0 :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .tStructure_zero_of_ambient_zero
      (fun hom source_mem target_mem =>
        TraceAnalyticMotivicTStructure
          .mathlib_zero_of_leftFraction_numerator_descentChannel_postcomp_zero
            descentChannel_zero
            hom
            source_mem
            target_mem)
      hom
      source_mem
      target_mem

/-- Descent-refinement numerator cancellation gives the orthogonality field on
the degreewise bounded stable source. -/
theorem tStructure_zero_of_descentRefinement
    (descentRefinement_zero :
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
                TraceLocalizationInput.descentRefinement_stableSource
                  inputSource
                  inputTarget,
              fraction.f ≫
                  (eqToHom source_eq ≫
                    TraceLocalizationInput.descentRefinement_stableMap
                      inputSource
                      inputTarget) =
                0)
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureGE 1 target) :
    hom = 0 :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .tStructure_zero_of_ambient_zero
      (fun hom source_mem target_mem =>
        TraceAnalyticMotivicTStructure
          .mathlib_zero_of_leftFraction_numerator_descentRefinement_postcomp_zero
            descentRefinement_zero
            hom
            source_mem
            target_mem)
      hom
      source_mem
      target_mem

/-- Descent-schedule numerator cancellation gives the orthogonality field on
the degreewise bounded stable source. -/
theorem tStructure_zero_of_descentSchedule
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
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureGE 1 target) :
    hom = 0 :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .tStructure_zero_of_ambient_zero
      (fun hom source_mem target_mem =>
        TraceAnalyticMotivicTStructure
          .mathlib_zero_of_leftFraction_numerator_descentSchedule_postcomp_zero
            descentSchedule_zero
            hom
            source_mem
            target_mem)
      hom
      source_mem
      target_mem

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
