import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Assembly.HomologyDischarged.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Assembly.NullHomotopy.NamedOrthogonality.IntervalStokes.Owner

/-!
# Interval-Stokes assembly with homology discharged

This file removes the cochain-homology input from the Interval-Stokes
null-homotopy route to Mathlib's `TStructure` record.  The homology objects are
supplied by the abelian-envelope cochain-complex theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace TraceAnalyticMotivicTStructure

/-- Assemble the analytic motivic Mathlib `TStructure` from global boundedness,
null-homotopic cone identities, and Interval-Stokes numerator cancellation,
with cochain homology supplied by the abelian-envelope owner theorem. -/
def tStructureOfNullHomotopicIdentityAndIntervalStokesHomologyDischarged
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
                0) :
    TStructure TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticMotivicTStructure
    .tStructureOfNullHomotopicIdentityAndIntervalStokes
      allBoundedStable
      (fun complex =>
        TraceAnalyticMotivicTStructure
          .sourceComplexWeightBoundedBy_hasHomology complex)
      nullHomotopicIdentity
      intervalStokes_zero

/-- The homology-discharged Interval-Stokes assembly has the analytic motivic
`LE` predicate. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalStokesHomologyDischarged_LE
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
                0) :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndIntervalStokesHomologyDischarged
        allBoundedStable
        nullHomotopicIdentity
        intervalStokes_zero).LE =
      TraceAnalyticMotivicTStructure.tStructureLE :=
  rfl

/-- The homology-discharged Interval-Stokes assembly has the analytic motivic
`GE` predicate. -/
theorem tStructureOfNullHomotopicIdentityAndIntervalStokesHomologyDischarged_GE
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
                0) :
    (TraceAnalyticMotivicTStructure
      .tStructureOfNullHomotopicIdentityAndIntervalStokesHomologyDischarged
        allBoundedStable
        nullHomotopicIdentity
        intervalStokes_zero).GE =
      TraceAnalyticMotivicTStructure.tStructureGE :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
