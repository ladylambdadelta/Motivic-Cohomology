import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Orthogonality.Fractions.Owner

/-!
# Named localization-input reductions for shifted-bounded orthogonality

This file specializes the shifted-bounded orthogonality reduction to each of
the six concrete analytic localization inputs.  The theorems here are
dependency-ordered wrappers over the generic `TraceLocalizationInput` criterion.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Descent-channel numerator cancellation implies shifted-bounded endpoint
vanishing. -/
theorem shiftedBounded_zero_of_leftFraction_numerator_descentChannel_postcomp_zero
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
    {sourceBound targetBound : Nat}
    (sourceComplex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy sourceBound)
    (sourceDegree : ℤ)
    (targetComplex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy targetBound)
    (targetDegree : ℤ)
    (sourceDegree_mem : -0 ≤ sourceDegree)
    (targetDegree_mem : targetDegree ≤ -1)
    (hom :
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          sourceComplex
          sourceDegree ⟶
        TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          targetComplex
          targetDegree) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure
    .shiftedBounded_zero_of_leftFraction_numerator_localizationInput_postcomp_zero
      (fun sourceComplex sourceDegree targetComplex targetDegree
          sourceDegree_mem targetDegree_mem fraction =>
        Exists.elim
          (descentChannel_zero
            sourceComplex
            sourceDegree
            targetComplex
            targetDegree
            sourceDegree_mem
            targetDegree_mem
            fraction)
          (fun inputSource inputSourceData =>
            Exists.elim
              inputSourceData
              (fun inputTarget inputTargetData =>
                Exists.elim
                  inputTargetData
                  (fun source_eq numerator_zero =>
                    Exists.intro
                      (TraceLocalizationInput.descentChannel
                        inputSource
                        inputTarget)
                      (Exists.intro source_eq numerator_zero)))))
      sourceComplex
      sourceDegree
      targetComplex
      targetDegree
      sourceDegree_mem
      targetDegree_mem
      hom

/-- Descent-refinement numerator cancellation implies shifted-bounded endpoint
vanishing. -/
theorem shiftedBounded_zero_of_leftFraction_numerator_descentRefinement_postcomp_zero
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
    {sourceBound targetBound : Nat}
    (sourceComplex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy sourceBound)
    (sourceDegree : ℤ)
    (targetComplex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy targetBound)
    (targetDegree : ℤ)
    (sourceDegree_mem : -0 ≤ sourceDegree)
    (targetDegree_mem : targetDegree ≤ -1)
    (hom :
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          sourceComplex
          sourceDegree ⟶
        TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          targetComplex
          targetDegree) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure
    .shiftedBounded_zero_of_leftFraction_numerator_localizationInput_postcomp_zero
      (fun sourceComplex sourceDegree targetComplex targetDegree
          sourceDegree_mem targetDegree_mem fraction =>
        Exists.elim
          (descentRefinement_zero
            sourceComplex
            sourceDegree
            targetComplex
            targetDegree
            sourceDegree_mem
            targetDegree_mem
            fraction)
          (fun inputSource inputSourceData =>
            Exists.elim
              inputSourceData
              (fun inputTarget inputTargetData =>
                Exists.elim
                  inputTargetData
                  (fun source_eq numerator_zero =>
                    Exists.intro
                      (TraceLocalizationInput.descentRefinement
                        inputSource
                        inputTarget)
                      (Exists.intro source_eq numerator_zero)))))
      sourceComplex
      sourceDegree
      targetComplex
      targetDegree
      sourceDegree_mem
      targetDegree_mem
      hom

/-- Descent-schedule numerator cancellation implies shifted-bounded endpoint
vanishing. -/
theorem shiftedBounded_zero_of_leftFraction_numerator_descentSchedule_postcomp_zero
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
    {sourceBound targetBound : Nat}
    (sourceComplex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy sourceBound)
    (sourceDegree : ℤ)
    (targetComplex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy targetBound)
    (targetDegree : ℤ)
    (sourceDegree_mem : -0 ≤ sourceDegree)
    (targetDegree_mem : targetDegree ≤ -1)
    (hom :
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          sourceComplex
          sourceDegree ⟶
        TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          targetComplex
          targetDegree) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure
    .shiftedBounded_zero_of_leftFraction_numerator_localizationInput_postcomp_zero
      (fun sourceComplex sourceDegree targetComplex targetDegree
          sourceDegree_mem targetDegree_mem fraction =>
        Exists.elim
          (descentSchedule_zero
            sourceComplex
            sourceDegree
            targetComplex
            targetDegree
            sourceDegree_mem
            targetDegree_mem
            fraction)
          (fun inputSource inputSourceData =>
            Exists.elim
              inputSourceData
              (fun inputTarget inputTargetData =>
                Exists.elim
                  inputTargetData
                  (fun source_eq numerator_zero =>
                    Exists.intro
                      (TraceLocalizationInput.descentSchedule
                        inputSource
                        inputTarget)
                      (Exists.intro source_eq numerator_zero)))))
      sourceComplex
      sourceDegree
      targetComplex
      targetDegree
      sourceDegree_mem
      targetDegree_mem
      hom

/-- Interval-Stokes numerator cancellation implies shifted-bounded endpoint
vanishing. -/
theorem shiftedBounded_zero_of_leftFraction_numerator_intervalStokes_postcomp_zero
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
    {sourceBound targetBound : Nat}
    (sourceComplex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy sourceBound)
    (sourceDegree : ℤ)
    (targetComplex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy targetBound)
    (targetDegree : ℤ)
    (sourceDegree_mem : -0 ≤ sourceDegree)
    (targetDegree_mem : targetDegree ≤ -1)
    (hom :
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          sourceComplex
          sourceDegree ⟶
        TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          targetComplex
          targetDegree) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure
    .shiftedBounded_zero_of_leftFraction_numerator_localizationInput_postcomp_zero
      (fun sourceComplex sourceDegree targetComplex targetDegree
          sourceDegree_mem targetDegree_mem fraction =>
        Exists.elim
          (intervalStokes_zero
            sourceComplex
            sourceDegree
            targetComplex
            targetDegree
            sourceDegree_mem
            targetDegree_mem
            fraction)
          (fun inputSource inputSourceData =>
            Exists.elim
              inputSourceData
              (fun inputTarget inputTargetData =>
                Exists.elim
                  inputTargetData
                  (fun source_eq numerator_zero =>
                    Exists.intro
                      (TraceLocalizationInput.intervalStokes
                        inputSource
                        inputTarget)
                      (Exists.intro source_eq numerator_zero)))))
      sourceComplex
      sourceDegree
      targetComplex
      targetDegree
      sourceDegree_mem
      targetDegree_mem
      hom

/-- Interval-Fubini numerator cancellation implies shifted-bounded endpoint
vanishing. -/
theorem shiftedBounded_zero_of_leftFraction_numerator_intervalFubini_postcomp_zero
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
    {sourceBound targetBound : Nat}
    (sourceComplex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy sourceBound)
    (sourceDegree : ℤ)
    (targetComplex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy targetBound)
    (targetDegree : ℤ)
    (sourceDegree_mem : -0 ≤ sourceDegree)
    (targetDegree_mem : targetDegree ≤ -1)
    (hom :
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          sourceComplex
          sourceDegree ⟶
        TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          targetComplex
          targetDegree) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure
    .shiftedBounded_zero_of_leftFraction_numerator_localizationInput_postcomp_zero
      (fun sourceComplex sourceDegree targetComplex targetDegree
          sourceDegree_mem targetDegree_mem fraction =>
        Exists.elim
          (intervalFubini_zero
            sourceComplex
            sourceDegree
            targetComplex
            targetDegree
            sourceDegree_mem
            targetDegree_mem
            fraction)
          (fun inputSource inputSourceData =>
            Exists.elim
              inputSourceData
              (fun inputTarget inputTargetData =>
                Exists.elim
                  inputTargetData
                  (fun source_eq numerator_zero =>
                    Exists.intro
                      (TraceLocalizationInput.intervalFubini
                        inputSource
                        inputTarget)
                      (Exists.intro source_eq numerator_zero)))))
      sourceComplex
      sourceDegree
      targetComplex
      targetDegree
      sourceDegree_mem
      targetDegree_mem
      hom

/-- Tate-weight-drop numerator cancellation implies shifted-bounded endpoint
vanishing. -/
theorem shiftedBounded_zero_of_leftFraction_numerator_tateWeightDrop_postcomp_zero
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
    {sourceBound targetBound : Nat}
    (sourceComplex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy sourceBound)
    (sourceDegree : ℤ)
    (targetComplex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy targetBound)
    (targetDegree : ℤ)
    (sourceDegree_mem : -0 ≤ sourceDegree)
    (targetDegree_mem : targetDegree ≤ -1)
    (hom :
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          sourceComplex
          sourceDegree ⟶
        TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          targetComplex
          targetDegree) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure
    .shiftedBounded_zero_of_leftFraction_numerator_localizationInput_postcomp_zero
      (fun sourceComplex sourceDegree targetComplex targetDegree
          sourceDegree_mem targetDegree_mem fraction =>
        Exists.elim
          (tateWeightDrop_zero
            sourceComplex
            sourceDegree
            targetComplex
            targetDegree
            sourceDegree_mem
            targetDegree_mem
            fraction)
          (fun inputSource inputSourceData =>
            Exists.elim
              inputSourceData
              (fun inputTarget inputTargetData =>
                Exists.elim
                  inputTargetData
                  (fun source_eq numerator_zero =>
                    Exists.intro
                      (TraceLocalizationInput.tateWeightDrop
                        inputSource
                        inputTarget)
                      (Exists.intro source_eq numerator_zero)))))
      sourceComplex
      sourceDegree
      targetComplex
      targetDegree
      sourceDegree_mem
      targetDegree_mem
      hom

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
