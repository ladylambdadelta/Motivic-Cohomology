import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Orthogonality.ShiftedBounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Orthogonality.Fractions.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Orthogonality.Fractions.Named.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Orthogonality.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Orthogonality.IsoClosure.Owner

/-!
# Mathlib-facing orthogonality reductions

This file composes the representative unpacking and iso-closure transport
layers for the Mathlib `TStructure.zero'` field.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Shifted-bounded endpoint vanishing implies the Mathlib-facing
orthogonality field from `LE 0` to `GE 1`. -/
theorem mathlib_zero_of_shiftedBounded_zero
    (shiftedBounded_zero :
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
        (endpointHom :
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            sourceComplex
            sourceDegree ⟶
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            targetComplex
            targetDegree) →
        endpointHom = 0)
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_representative_zero
    (fun hom sourceRepresentative_mem targetRepresentative_mem =>
      TraceAnalyticMotivicTStructure
        .representative_zero_of_shiftedBounded_zero
          shiftedBounded_zero
          hom
          sourceRepresentative_mem
          targetRepresentative_mem)
    hom
    source_mem
    target_mem

/-- Common-bound shifted-bounded endpoint vanishing implies the Mathlib-facing
orthogonality field from `LE 0` to `GE 1`. -/
theorem mathlib_zero_of_commonBound_shiftedBounded_zero
    (commonBound_zero :
      ∀ {bound : Nat}
        (sourceComplex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
        (sourceDegree : ℤ)
        (targetComplex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
        (targetDegree : ℤ),
        -0 ≤ sourceDegree →
        targetDegree ≤ -1 →
        (endpointHom :
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            sourceComplex
            sourceDegree ⟶
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            targetComplex
            targetDegree) →
        endpointHom = 0)
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_shiftedBounded_zero
    (TraceAnalyticMotivicTStructure
      .shiftedBounded_zero_of_commonBound_zero commonBound_zero)
    hom
    source_mem
    target_mem

/-- Analytic Verdier-roof endpoint vanishing implies the Mathlib-facing
orthogonality field from `LE 0` to `GE 1`. -/
theorem mathlib_zero_of_leftFraction_zero
    (leftFraction_zero :
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
        fraction.map
            TraceAnalyticDMgmComparisonSource.quotientFunctor
            (CategoryTheory.Localization.inverts
              TraceAnalyticDMgmComparisonSource.quotientFunctor
              TraceAnalyticStableNullSubcategory.invertedMorphisms) =
          0)
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_shiftedBounded_zero
    (TraceAnalyticMotivicTStructure
      .shiftedBounded_zero_of_leftFraction_zero leftFraction_zero)
    hom
    source_mem
    target_mem

/-- Analytic Verdier-roof numerator vanishing implies the Mathlib-facing
orthogonality field from `LE 0` to `GE 1`. -/
theorem mathlib_zero_of_leftFraction_numerator_zero
    (leftFraction_numerator_zero :
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
        TraceAnalyticDMgmComparisonSource.quotientFunctor.map fraction.f =
          (0 :
            TraceAnalyticDMgmComparisonSource.quotientFunctor.obj
                (TraceAnalyticMotiveComparison
                  .sourceShiftedWeightBoundedHomotopyObject
                    sourceComplex
                    sourceDegree) ⟶
              TraceAnalyticDMgmComparisonSource.quotientFunctor.obj
                fraction.Y'))
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_shiftedBounded_zero
    (TraceAnalyticMotivicTStructure
      .shiftedBounded_zero_of_leftFraction_numerator_zero
        leftFraction_numerator_zero)
    hom
    source_mem
    target_mem

/-- Analytic Verdier-roof numerator postcomposition vanishing implies the
Mathlib-facing orthogonality field from `LE 0` to `GE 1`. -/
theorem mathlib_zero_of_leftFraction_numerator_postcomp_zero
    (leftFraction_numerator_postcomp_zero :
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
        ∃ postTarget : TraceAnalyticAdditiveHomotopyCategory,
          ∃ post : fraction.Y' ⟶ postTarget,
            ∃ post_inverted :
              TraceAnalyticStableNullSubcategory.invertedMorphisms post,
              fraction.f ≫ post = 0)
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_shiftedBounded_zero
    (TraceAnalyticMotivicTStructure
      .shiftedBounded_zero_of_leftFraction_numerator_postcomp_zero
        leftFraction_numerator_postcomp_zero)
    hom
    source_mem
    target_mem

/-- Analytic Verdier-roof numerator null-cone postcomposition vanishing implies
the Mathlib-facing orthogonality field from `LE 0` to `GE 1`. -/
theorem mathlib_zero_of_leftFraction_numerator_nullCone_postcomp_zero
    (leftFraction_numerator_nullCone_postcomp_zero :
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
        ∃ postTarget : TraceAnalyticAdditiveHomotopyCategory,
          ∃ postCone : TraceAnalyticAdditiveHomotopyCategory,
            ∃ post : fraction.Y' ⟶ postTarget,
              ∃ postConeMap : postTarget ⟶ postCone,
                ∃ postBoundary : postCone ⟶ fraction.Y'⟦(1 : ℤ)⟧,
                  ∃ distinguished :
                    Triangle.mk post postConeMap postBoundary ∈
                      TraceAnalyticAdditiveHomotopyCategory
                        .distinguishedTriangles,
                    ∃ postCone_null :
                      TraceAnalyticStableNullSubcategory.P postCone,
                      fraction.f ≫ post = 0)
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_shiftedBounded_zero
    (TraceAnalyticMotivicTStructure
      .shiftedBounded_zero_of_leftFraction_numerator_nullCone_postcomp_zero
        leftFraction_numerator_nullCone_postcomp_zero)
    hom
    source_mem
    target_mem

/-- Stable acyclic-generator numerator cancellation implies the Mathlib-facing
orthogonality field from `LE 0` to `GE 1`. -/
theorem mathlib_zero_of_leftFraction_numerator_generator_postcomp_zero
    (leftFraction_numerator_generator_postcomp_zero :
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
        ∃ generator : TraceAnalyticStableAcyclicGenerator,
          ∃ source_eq : fraction.Y' = generator.source,
            fraction.f ≫ (eqToHom source_eq ≫ generator.firstMap) = 0)
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_shiftedBounded_zero
    (TraceAnalyticMotivicTStructure
      .shiftedBounded_zero_of_leftFraction_numerator_generator_postcomp_zero
        leftFraction_numerator_generator_postcomp_zero)
    hom
    source_mem
    target_mem

/-- Localization-input numerator cancellation implies the Mathlib-facing
orthogonality field from `LE 0` to `GE 1`. -/
theorem mathlib_zero_of_leftFraction_numerator_localizationInput_postcomp_zero
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
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  TraceAnalyticMotivicTStructure.mathlib_zero_of_shiftedBounded_zero
    (TraceAnalyticMotivicTStructure
      .shiftedBounded_zero_of_leftFraction_numerator_localizationInput_postcomp_zero
        leftFraction_numerator_localizationInput_postcomp_zero)
    hom
    source_mem
    target_mem

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
