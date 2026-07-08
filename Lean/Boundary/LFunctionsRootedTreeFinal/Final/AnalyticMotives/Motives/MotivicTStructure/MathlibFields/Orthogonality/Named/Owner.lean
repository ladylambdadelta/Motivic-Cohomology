import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Orthogonality.Owner

/-!
# Mathlib-facing named analytic-generator orthogonality reductions

This file exposes direct Mathlib `TStructure.zero'` reduction theorems for the
six named analytic localization inputs.  Each theorem consumes the named
shifted-bounded cancellation criterion and routes it through the existing
orthogonality owner chain.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Descent-channel numerator cancellation implies the Mathlib-facing
orthogonality field from `LE 0` to `GE 1`. -/
theorem mathlib_zero_of_leftFraction_numerator_descentChannel_postcomp_zero
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
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_shiftedBounded_zero
    (TraceAnalyticMotivicTStructure
      .shiftedBounded_zero_of_leftFraction_numerator_descentChannel_postcomp_zero
        descentChannel_zero)
    hom
    source_mem
    target_mem

/-- Descent-refinement numerator cancellation implies the Mathlib-facing
orthogonality field from `LE 0` to `GE 1`. -/
theorem mathlib_zero_of_leftFraction_numerator_descentRefinement_postcomp_zero
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
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_shiftedBounded_zero
    (TraceAnalyticMotivicTStructure
      .shiftedBounded_zero_of_leftFraction_numerator_descentRefinement_postcomp_zero
        descentRefinement_zero)
    hom
    source_mem
    target_mem

/-- Descent-schedule numerator cancellation implies the Mathlib-facing
orthogonality field from `LE 0` to `GE 1`. -/
theorem mathlib_zero_of_leftFraction_numerator_descentSchedule_postcomp_zero
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
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_shiftedBounded_zero
    (TraceAnalyticMotivicTStructure
      .shiftedBounded_zero_of_leftFraction_numerator_descentSchedule_postcomp_zero
        descentSchedule_zero)
    hom
    source_mem
    target_mem

/-- Interval-Stokes numerator cancellation implies the Mathlib-facing
orthogonality field from `LE 0` to `GE 1`. -/
theorem mathlib_zero_of_leftFraction_numerator_intervalStokes_postcomp_zero
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
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_shiftedBounded_zero
    (TraceAnalyticMotivicTStructure
      .shiftedBounded_zero_of_leftFraction_numerator_intervalStokes_postcomp_zero
        intervalStokes_zero)
    hom
    source_mem
    target_mem

/-- Interval-Fubini numerator cancellation implies the Mathlib-facing
orthogonality field from `LE 0` to `GE 1`. -/
theorem mathlib_zero_of_leftFraction_numerator_intervalFubini_postcomp_zero
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
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_shiftedBounded_zero
    (TraceAnalyticMotivicTStructure
      .shiftedBounded_zero_of_leftFraction_numerator_intervalFubini_postcomp_zero
        intervalFubini_zero)
    hom
    source_mem
    target_mem

/-- Tate-weight-drop numerator cancellation implies the Mathlib-facing
orthogonality field from `LE 0` to `GE 1`. -/
theorem mathlib_zero_of_leftFraction_numerator_tateWeightDrop_postcomp_zero
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
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_shiftedBounded_zero
    (TraceAnalyticMotivicTStructure
      .shiftedBounded_zero_of_leftFraction_numerator_tateWeightDrop_postcomp_zero
        tateWeightDrop_zero)
    hom
    source_mem
    target_mem

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
