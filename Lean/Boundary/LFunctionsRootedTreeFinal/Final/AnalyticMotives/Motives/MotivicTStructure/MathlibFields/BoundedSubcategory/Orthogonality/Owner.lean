import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Monotonicity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Fields.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Orthogonality.Named.Owner

/-!
# Orthogonality on the bounded stable source

The bounded stable source is a full subcategory of the analytic comparison
source.  Orthogonality for the bounded-source predicates is therefore the
ambient Mathlib-facing orthogonality theorem applied to the same underlying
ambient morphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- Ambient orthogonality restricts to orthogonality on the bounded stable
source. -/
theorem zero_of_ambient_zero
    (ambient_zero :
      ∀ {source target : TraceAnalyticDMgmComparisonSource}
        (hom : source ⟶ target),
        TraceAnalyticMotivicTStructure.mathlibLE 0 source →
        TraceAnalyticMotivicTStructure.mathlibGE 1 target →
        hom = 0)
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 target) :
    hom = 0 :=
  ambient_zero hom source_mem target_mem

/-- Localization-input numerator cancellation gives bounded-source
orthogonality from `LE 0` to `GE 1`. -/
theorem zero_of_leftFraction_numerator_localizationInput_postcomp_zero
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
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.zero_of_ambient_zero
    (fun hom source_mem target_mem =>
      TraceAnalyticMotivicTStructure
        .mathlib_zero_of_leftFraction_numerator_localizationInput_postcomp_zero
          leftFraction_numerator_localizationInput_postcomp_zero
          hom
          source_mem
          target_mem)
    hom
    source_mem
    target_mem

/-- Descent-channel numerator cancellation gives bounded-source
orthogonality from `LE 0` to `GE 1`. -/
theorem zero_of_leftFraction_numerator_descentChannel_postcomp_zero
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
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.zero_of_ambient_zero
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

/-- Descent-refinement numerator cancellation gives bounded-source
orthogonality from `LE 0` to `GE 1`. -/
theorem zero_of_leftFraction_numerator_descentRefinement_postcomp_zero
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
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.zero_of_ambient_zero
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

/-- Descent-schedule numerator cancellation gives bounded-source
orthogonality from `LE 0` to `GE 1`. -/
theorem zero_of_leftFraction_numerator_descentSchedule_postcomp_zero
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
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.zero_of_ambient_zero
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

/-- Interval-Stokes numerator cancellation gives bounded-source orthogonality
from `LE 0` to `GE 1`. -/
theorem zero_of_leftFraction_numerator_intervalStokes_postcomp_zero
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
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.zero_of_ambient_zero
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

/-- Interval-Fubini numerator cancellation gives bounded-source orthogonality
from `LE 0` to `GE 1`. -/
theorem zero_of_leftFraction_numerator_intervalFubini_postcomp_zero
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
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.zero_of_ambient_zero
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

/-- Tate-weight-drop numerator cancellation gives bounded-source orthogonality
from `LE 0` to `GE 1`. -/
theorem zero_of_leftFraction_numerator_tateWeightDrop_postcomp_zero
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
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.zero_of_ambient_zero
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

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
