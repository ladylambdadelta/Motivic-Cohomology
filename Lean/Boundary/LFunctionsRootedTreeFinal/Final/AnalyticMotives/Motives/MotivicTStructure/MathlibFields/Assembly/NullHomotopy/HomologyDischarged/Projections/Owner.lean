import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Assembly.NullHomotopy.HomologyDischarged.Owner

/-!
# Projections from the homology-discharged null-homotopy assembly

This file exposes the orthogonality and truncation-triangle fields supplied by
the null-homotopy t-structure assembly after cochain homology has been
discharged from the abelian-envelope theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

section HomologyDischargedNullHomotopyInputs

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

/-- The homology-discharged null-homotopy assembly supplies Mathlib's
orthogonality field. -/
theorem tStructureOfNullHomotopicIdentityHomologyDischarged_zero
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityHomologyDischarged
          allBoundedStable
          nullHomotopicIdentity
          leftFraction_numerator_localizationInput_postcomp_zero).LE
        0
        source)
    (target_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfNullHomotopicIdentityHomologyDischarged
          allBoundedStable
          nullHomotopicIdentity
          leftFraction_numerator_localizationInput_postcomp_zero).GE
        1
        target) :
    hom = 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityHomologyDischarged
      allBoundedStable
      nullHomotopicIdentity
      leftFraction_numerator_localizationInput_postcomp_zero).zero'
    hom
    source_mem
    target_mem

/-- The homology-discharged null-homotopy assembly supplies Mathlib's
adjacent truncation-triangle field. -/
theorem tStructureOfNullHomotopicIdentityHomologyDischarged_exists_triangle_zero_one
    (object : TraceAnalyticDMgmComparisonSource) :
    ∃ (left middle right : TraceAnalyticDMgmComparisonSource)
      (first : left ⟶ middle)
      (second : middle ⟶ right)
      (third : right ⟶ left⟦(1 : ℤ)⟧),
      middle = object ∧
        (TraceAnalyticMotivicTStructure
          .tStructureOfNullHomotopicIdentityHomologyDischarged
            allBoundedStable
            nullHomotopicIdentity
            leftFraction_numerator_localizationInput_postcomp_zero).LE
          0
          left ∧
        (TraceAnalyticMotivicTStructure
          .tStructureOfNullHomotopicIdentityHomologyDischarged
            allBoundedStable
            nullHomotopicIdentity
            leftFraction_numerator_localizationInput_postcomp_zero).GE
          1
          right ∧
        Pretriangulated.Triangle.mk first second third ∈ distTriang
          TraceAnalyticDMgmComparisonSource :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityHomologyDischarged
      allBoundedStable
      nullHomotopicIdentity
      leftFraction_numerator_localizationInput_postcomp_zero)
    .exists_triangle_zero_one
      object

end HomologyDischargedNullHomotopyInputs

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
