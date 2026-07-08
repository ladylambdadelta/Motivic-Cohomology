import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.TruncationTriangle.MathlibMembership.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Fields.ConeComparison.ContractibleCone.NullHomotopy.Owner

/-!
# Null-homotopy truncation triangles from Mathlib-facing membership

This file specializes the Mathlib-facing `LE` and `GE` membership truncation
theorems to the null-homotopic identity criterion for the normalized
cone-comparison field.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- A Mathlib-facing `LE` object has the ambient truncation triangle once the
normalized cone-to-upper mapping cones have null-homotopic identities. -/
theorem exists_triangle_zero_one_of_mathlibLE_of_nullHomotopicIdentity
    (membershipCut : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.mathlibLE membershipCut object)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
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
            _root_.HomologicalComplex.nullHomotopicMap' hom) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticMotivicTStructure.mathlibLE 0 lower ∧
        TraceAnalyticMotivicTStructure.mathlibGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .tStructure_exists_triangle_zero_one_of_boundedStableObject_of_nullHomotopicIdentity
      (TraceAnalyticMotivicTStructure
        .boundedStableObject_of_mathlibLE
          membershipCut
          membership)
      homology
      nullHomotopicIdentity

/-- A Mathlib-facing `GE` object has the ambient truncation triangle once the
normalized cone-to-upper mapping cones have null-homotopic identities. -/
theorem exists_triangle_zero_one_of_mathlibGE_of_nullHomotopicIdentity
    (membershipCut : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.mathlibGE membershipCut object)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
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
            _root_.HomologicalComplex.nullHomotopicMap' hom) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticMotivicTStructure.mathlibLE 0 lower ∧
        TraceAnalyticMotivicTStructure.mathlibGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .tStructure_exists_triangle_zero_one_of_boundedStableObject_of_nullHomotopicIdentity
      (TraceAnalyticMotivicTStructure
        .boundedStableObject_of_mathlibGE
          membershipCut
          membership)
      homology
      nullHomotopicIdentity

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
