import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.IsIso.ContractibleCone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Fields.Owner

/-!
# Contractible-cone field for Mathlib truncation triangles

This file exposes the concrete route from a contracting homotopy of the
mapping cone of the normalized cone-to-upper map to the stable
cone-comparison isomorphism used by the Mathlib-facing truncation triangle
field.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- A contracting homotopy for every normalized cone-to-upper mapping cone
supplies the stable cone-comparison isomorphism family used by the
bounded-source truncation field. -/
theorem tStructure_coneComparison_of_contractibleCone
    (cut : ℤ)
    (contractibleCone :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        Nonempty
          (Homotopy
            (𝟙
              (CochainComplex.mappingCone
                (TraceAnalyticMotivicTStructure
                  .additiveNormalizedConeComparisonCochainMap
                    cut
                    complex.complex)))
            0))
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex.complex) :=
  TraceAnalyticMotivicTStructure
    .stableNormalizedConeComparisonMap_isIso_of_contractibleCone
      cut
      complex.complex
      (contractibleCone complex)

/-- At Mathlib cut `0`, contracting homotopies supply the exact
cone-comparison family required by the bounded-source truncation field. -/
theorem tStructure_cutZero_coneComparison_of_contractibleCone
    (contractibleCone :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        Nonempty
          (Homotopy
            (𝟙
              (CochainComplex.mappingCone
                (TraceAnalyticMotivicTStructure
                  .additiveNormalizedConeComparisonCochainMap
                    0
                    complex.complex)))
            0))
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        0
        complex.complex) :=
  TraceAnalyticMotivicTStructure.tStructure_coneComparison_of_contractibleCone
    0
    contractibleCone
    complex

/-- The bounded-source truncation field can be invoked using contracting
homotopies of the normalized cone-to-upper mapping cones. -/
theorem tStructure_exists_triangle_zero_one_of_boundedStableObject_of_contractibleCone
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
    (contractibleCone :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        Nonempty
          (Homotopy
            (𝟙
              (CochainComplex.mappingCone
                (TraceAnalyticMotivicTStructure
                  .additiveNormalizedConeComparisonCochainMap
                    0
                    complex.complex)))
            0)) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticMotivicTStructure.tStructureLE 0 lower ∧
        TraceAnalyticMotivicTStructure.tStructureGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            CategoryTheory.Pretriangulated.Triangle.mk
                firstMap
                secondMap
                connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .tStructure_exists_triangle_zero_one_of_boundedStableObject
      membership
      homology
      (fun complex =>
        TraceAnalyticMotivicTStructure
          .tStructure_cutZero_coneComparison_of_contractibleCone
            contractibleCone
            complex)

/-- The bounded-source truncation field, in Mathlib field order, follows from
contracting homotopies of the normalized cone-to-upper mapping cones. -/
theorem tStructure_exists_triangle_zero_one_fieldShape_of_contractibleCone
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
    (contractibleCone :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        Nonempty
          (Homotopy
            (𝟙
              (CochainComplex.mappingCone
                (TraceAnalyticMotivicTStructure
                  .additiveNormalizedConeComparisonCochainMap
                    0
                    complex.complex)))
            0)) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ : TraceAnalyticMotivicTStructure.tStructureLE 0 lower)
      (_ : TraceAnalyticMotivicTStructure.tStructureGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      CategoryTheory.Pretriangulated.Triangle.mk
          firstMap
          secondMap
          connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .tStructure_exists_triangle_zero_one_of_boundedStableObject_fieldShape
      membership
      homology
      (fun complex =>
        TraceAnalyticMotivicTStructure
          .tStructure_cutZero_coneComparison_of_contractibleCone
            contractibleCone
            complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
