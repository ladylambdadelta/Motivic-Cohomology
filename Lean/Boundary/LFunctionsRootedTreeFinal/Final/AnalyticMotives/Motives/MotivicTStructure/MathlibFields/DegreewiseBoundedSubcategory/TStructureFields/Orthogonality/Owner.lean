import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.TStructureFields.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Orthogonality.Named.Owner

/-!
# Orthogonality fields on the degreewise bounded stable source

This file restricts the named analytic orthogonality reductions from the
ambient comparison source to the degreewise bounded stable source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Interval-Stokes numerator cancellation gives the orthogonality field on
the degreewise bounded stable source. -/
theorem tStructure_zero_of_intervalStokes
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
          .mathlib_zero_of_leftFraction_numerator_intervalStokes_postcomp_zero
            intervalStokes_zero
            hom
            source_mem
            target_mem)
      hom
      source_mem
      target_mem

/-- Interval-Fubini numerator cancellation gives the orthogonality field on
the degreewise bounded stable source. -/
theorem tStructure_zero_of_intervalFubini
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
          .mathlib_zero_of_leftFraction_numerator_intervalFubini_postcomp_zero
            intervalFubini_zero
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
