import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.IsIso.ContractibleCone.NullHomotopy.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Fields.ConeComparison.ContractibleCone.Owner

/-!
# Null-homotopic identity criterion for the cone-comparison field

This file specializes Mathlib's general `nullHomotopy'` constructor to the
normalized cone-to-upper mapping cone.  It is the concrete shape of the
contracting-homotopy data needed by the Mathlib-facing truncation field.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- If the identity on a cochain complex is a null-homotopic map assembled from
adjacent-degree homotopy components, then the complex is contractible. -/
theorem contractible_of_identity_eq_nullHomotopicMap
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hom :
      ∀ i j,
        (ComplexShape.up ℤ).Rel j i →
          complex.X i ⟶ complex.X j)
    (identity_eq :
      𝟙 complex =
        _root_.HomologicalComplex.nullHomotopicMap' hom) :
    Nonempty (Homotopy (𝟙 complex) 0) :=
  TraceAnalyticMotivicTStructure
    .cochainComplex_contractible_of_identity_eq_nullHomotopicMap
      complex
      hom
      identity_eq

/-- The normalized cone-to-upper mapping cone is contractible once its identity
is expressed as a null-homotopic map from explicit adjacent-degree homotopy
components. -/
theorem normalizedConeComparison_contractible_of_identity_eq_nullHomotopicMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hom :
      ∀ i j,
        (ComplexShape.up ℤ).Rel j i →
          (CochainComplex.mappingCone
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap cut complex)).X i ⟶
            (CochainComplex.mappingCone
              (TraceAnalyticMotivicTStructure
                .additiveNormalizedConeComparisonCochainMap cut complex)).X j)
    (identity_eq :
      𝟙
          (CochainComplex.mappingCone
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap cut complex)) =
        _root_.HomologicalComplex.nullHomotopicMap' hom) :
    Nonempty
      (Homotopy
        (𝟙
          (CochainComplex.mappingCone
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap cut complex)))
        0) :=
  TraceAnalyticMotivicTStructure.contractible_of_identity_eq_nullHomotopicMap
    (CochainComplex.mappingCone
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex))
    hom
    identity_eq

/-- Null-homotopic identity presentations supply the stable cone-comparison
isomorphism family used by the bounded-source truncation field. -/
theorem tStructure_coneComparison_of_nullHomotopicIdentity
    (cut : ℤ)
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
                    cut
                    complex.complex)).X i ⟶
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      cut
                      complex.complex)).X j,
          𝟙
              (CochainComplex.mappingCone
                (TraceAnalyticMotivicTStructure
                  .additiveNormalizedConeComparisonCochainMap
                    cut
                    complex.complex)) =
            _root_.HomologicalComplex.nullHomotopicMap' hom)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex.complex) :=
  Exists.elim
    (nullHomotopicIdentity complex)
    (fun hom identity_eq =>
      TraceAnalyticMotivicTStructure
        .stableNormalizedConeComparisonMap_isIso_of_identity_eq_nullHomotopicMap
          cut
          complex.complex
          hom
          identity_eq)

/-- At Mathlib cut `0`, null-homotopic identity presentations supply the exact
cone-comparison family required by the bounded-source truncation field. -/
theorem tStructure_cutZero_coneComparison_of_nullHomotopicIdentity
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
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        0
        complex.complex) :=
  TraceAnalyticMotivicTStructure
    .tStructure_coneComparison_of_nullHomotopicIdentity
      0
      nullHomotopicIdentity
      complex

/-- The bounded-source truncation field follows from null-homotopic identity
presentations of the normalized cone-to-upper mapping cones. -/
theorem tStructure_exists_triangle_zero_one_of_boundedStableObject_of_nullHomotopicIdentity
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
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
          .tStructure_cutZero_coneComparison_of_nullHomotopicIdentity
            nullHomotopicIdentity
            complex)

/-- The bounded-source truncation field, in Mathlib field order, follows from
null-homotopic identity presentations of the normalized cone-to-upper mapping
cones. -/
theorem tStructure_exists_triangle_zero_one_fieldShape_of_nullHomotopicIdentity
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
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
          .tStructure_cutZero_coneComparison_of_nullHomotopicIdentity
            nullHomotopicIdentity
            complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
