import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Fractions.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.Owner

/-!
# Fraction reduction for shifted-bounded orthogonality

The Mathlib `TStructure.zero'` field quantifies over arbitrary morphisms in
the stable analytic comparison source.  The stable source is a Verdier
localization, so such morphisms are represented by concrete analytic
left fractions.  This file reduces shifted-bounded endpoint vanishing to
vanishing of those Verdier roof representatives.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- To prove shifted-bounded endpoint vanishing in the stable comparison
source, it is enough to prove it for every analytic Verdier left fraction
between the shifted bounded homotopy representatives. -/
theorem shiftedBounded_zero_of_leftFraction_zero
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
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.exists_leftFraction hom)
    (fun fraction hom_eq_fraction =>
      Eq.trans
        hom_eq_fraction
        (leftFraction_zero
          sourceComplex
          sourceDegree
          targetComplex
          targetDegree
          sourceDegree_mem
          targetDegree_mem
          fraction))

/-- To prove shifted-bounded endpoint vanishing, it is enough to prove that
the localized numerator of every analytic Verdier left fraction between the
shifted bounded homotopy representatives is zero. -/
theorem shiftedBounded_zero_of_leftFraction_numerator_zero
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
    .shiftedBounded_zero_of_leftFraction_zero
      (fun sourceComplex sourceDegree targetComplex targetDegree
          sourceDegree_mem targetDegree_mem fraction =>
        TraceAnalyticDMgmComparisonSource
          .leftFraction_map_eq_zero_of_numerator_zero
            fraction
            (leftFraction_numerator_zero
              sourceComplex
              sourceDegree
              targetComplex
              targetDegree
              sourceDegree_mem
              targetDegree_mem
              fraction))
      sourceComplex
      sourceDegree
      targetComplex
      targetDegree
      sourceDegree_mem
      targetDegree_mem
      hom

/-- To prove shifted-bounded endpoint vanishing, it is enough to prove that
the numerator of every analytic Verdier left fraction becomes zero after
postcomposition by another analytic Verdier-inverted morphism. -/
theorem shiftedBounded_zero_of_leftFraction_numerator_postcomp_zero
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
    .shiftedBounded_zero_of_leftFraction_zero
      (fun sourceComplex sourceDegree targetComplex targetDegree
          sourceDegree_mem targetDegree_mem fraction =>
        TraceAnalyticDMgmComparisonSource
          .leftFraction_map_eq_zero_of_numerator_postcomp_zero
            fraction
            (leftFraction_numerator_postcomp_zero
              sourceComplex
              sourceDegree
              targetComplex
              targetDegree
              sourceDegree_mem
              targetDegree_mem
              fraction))
      sourceComplex
      sourceDegree
      targetComplex
      targetDegree
      sourceDegree_mem
      targetDegree_mem
      hom

/-- To prove shifted-bounded endpoint vanishing, it is enough to prove that
the numerator of every analytic Verdier left fraction is killed by
postcomposition with the first map of a distinguished triangle whose cone is
stable-null. -/
theorem shiftedBounded_zero_of_leftFraction_numerator_nullCone_postcomp_zero
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
    .shiftedBounded_zero_of_leftFraction_zero
      (fun sourceComplex sourceDegree targetComplex targetDegree
          sourceDegree_mem targetDegree_mem fraction =>
        Exists.elim
          (leftFraction_numerator_nullCone_postcomp_zero
            sourceComplex
            sourceDegree
            targetComplex
            targetDegree
            sourceDegree_mem
            targetDegree_mem
            fraction)
          (fun postTarget postTargetData =>
            Exists.elim
              postTargetData
              (fun postCone postConeData =>
                Exists.elim
                  postConeData
                  (fun post postData =>
                    Exists.elim
                      postData
                      (fun postConeMap postConeMapData =>
                        Exists.elim
                          postConeMapData
                          (fun postBoundary postBoundaryData =>
                            Exists.elim
                              postBoundaryData
                              (fun distinguished distinguishedData =>
                                Exists.elim
                                  distinguishedData
                                  (fun postCone_null numerator_post_zero =>
                                    TraceAnalyticDMgmComparisonSource
                                      .leftFraction_map_eq_zero_of_numerator_nullCone_postcomp_zero
                                        fraction
                                        postTarget
                                        postCone
                                        post
                                        postConeMap
                                        postBoundary
                                        distinguished
                                        postCone_null
                                        numerator_post_zero))))))))
      sourceComplex
      sourceDegree
      targetComplex
      targetDegree
      sourceDegree_mem
      targetDegree_mem
      hom

/-- To prove shifted-bounded endpoint vanishing, it is enough to prove that
the numerator of every analytic Verdier left fraction is killed by a stable
acyclic generator first map, after identifying the numerator target with the
generator source. -/
theorem shiftedBounded_zero_of_leftFraction_numerator_generator_postcomp_zero
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
    .shiftedBounded_zero_of_leftFraction_zero
      (fun sourceComplex sourceDegree targetComplex targetDegree
          sourceDegree_mem targetDegree_mem fraction =>
        Exists.elim
          (leftFraction_numerator_generator_postcomp_zero
            sourceComplex
            sourceDegree
            targetComplex
            targetDegree
            sourceDegree_mem
            targetDegree_mem
            fraction)
          (fun generator generatorData =>
            Exists.elim
              generatorData
              (fun source_eq numerator_generator_zero =>
                TraceAnalyticDMgmComparisonSource
                  .leftFraction_map_eq_zero_of_numerator_generator_postcomp_zero
                    fraction
                    generator
                    source_eq
                    numerator_generator_zero)))
      sourceComplex
      sourceDegree
      targetComplex
      targetDegree
      sourceDegree_mem
      targetDegree_mem
      hom

/-- To prove shifted-bounded endpoint vanishing, it is enough to prove that
the numerator of every analytic Verdier left fraction is killed by the stable
map of a concrete analytic localization input, after identifying the numerator
target with that input's stable source. -/
theorem shiftedBounded_zero_of_leftFraction_numerator_localizationInput_postcomp_zero
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
    .shiftedBounded_zero_of_leftFraction_zero
      (fun sourceComplex sourceDegree targetComplex targetDegree
          sourceDegree_mem targetDegree_mem fraction =>
        Exists.elim
          (leftFraction_numerator_localizationInput_postcomp_zero
            sourceComplex
            sourceDegree
            targetComplex
            targetDegree
            sourceDegree_mem
            targetDegree_mem
            fraction)
          (fun input inputData =>
            Exists.elim
              inputData
              (fun source_eq numerator_input_zero =>
                TraceAnalyticDMgmComparisonSource
                  .leftFraction_map_eq_zero_of_numerator_localizationInput_postcomp_zero
                    fraction
                    input
                    source_eq
                    numerator_input_zero)))
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
