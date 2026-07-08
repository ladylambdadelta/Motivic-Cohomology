import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Assembly.HomologyDischarged.Owner

/-!
# Projections from the homology-discharged t-structure assembly

This file exposes the main record fields of
`tStructureOfHomologyDischargedInputs`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

section Inputs

variable
    (allBoundedStable :
      ∀ object : TraceAnalyticDMgmComparisonSource,
        TraceAnalyticDMgmComparisonSource.boundedStableObject object)
    (coneComparison :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        IsIso
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap
              0
              complex.complex))
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

/-- Projection to the orthogonality field of the homology-discharged
assembly. -/
theorem tStructureOfHomologyDischargedInputs_zero'
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfHomologyDischargedInputs
          allBoundedStable
          coneComparison
          leftFraction_numerator_localizationInput_postcomp_zero).LE
        0
        source)
    (target_mem :
      (TraceAnalyticMotivicTStructure
        .tStructureOfHomologyDischargedInputs
          allBoundedStable
          coneComparison
          leftFraction_numerator_localizationInput_postcomp_zero).GE
        1
        target) :
    hom = 0 :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfHomologyDischargedInputs
      allBoundedStable
      coneComparison
      leftFraction_numerator_localizationInput_postcomp_zero)
    .zero'
      hom
      source_mem
      target_mem

/-- Projection to the truncation-triangle existence field of the
homology-discharged assembly. -/
theorem tStructureOfHomologyDischargedInputs_exists_triangle_zero_one
    (object : TraceAnalyticDMgmComparisonSource) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ :
        (TraceAnalyticMotivicTStructure
          .tStructureOfHomologyDischargedInputs
            allBoundedStable
            coneComparison
            leftFraction_numerator_localizationInput_postcomp_zero).LE
          0
          lower)
      (_ :
        (TraceAnalyticMotivicTStructure
          .tStructureOfHomologyDischargedInputs
            allBoundedStable
            coneComparison
            leftFraction_numerator_localizationInput_postcomp_zero).GE
          1
          upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  (TraceAnalyticMotivicTStructure
    .tStructureOfHomologyDischargedInputs
      allBoundedStable
      coneComparison
      leftFraction_numerator_localizationInput_postcomp_zero)
    .exists_triangle_zero_one
      object

end Inputs

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
