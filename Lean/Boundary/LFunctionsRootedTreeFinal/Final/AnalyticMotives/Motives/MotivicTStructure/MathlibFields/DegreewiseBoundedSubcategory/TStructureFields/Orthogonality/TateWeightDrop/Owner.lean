import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.TStructureFields.Orthogonality.Owner

/-!
# Tate weight-drop orthogonality field on the degreewise bounded stable source

This file restricts the named Tate weight-drop analytic orthogonality
reduction from the ambient comparison source to the degreewise bounded stable
source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Tate weight-drop numerator cancellation gives the orthogonality field on
the degreewise bounded stable source. -/
theorem tStructure_zero_of_tateWeightDrop
    (tateWeightDrop_zero :
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
                TraceLocalizationInput.tateWeightDrop_stableSource
                  inputSource
                  inputTarget,
              fraction.f ≫
                  (eqToHom source_eq ≫
                    TraceLocalizationInput.tateWeightDrop_stableMap
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
          .mathlib_zero_of_leftFraction_numerator_tateWeightDrop_postcomp_zero
            tateWeightDrop_zero
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
