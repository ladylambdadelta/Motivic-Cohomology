import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Assembly.ContractibleCone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.IsIso.ContractibleCone.NullHomotopy.Owner

/-!
# Support t-structure from null-homotopic cone identities

This file specializes the contractible-cone support t-structure constructor to
explicit adjacent-degree null-homotopies of the identities on the normalized
cone-comparison mapping cones.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Null-homotopic identity presentations of the normalized cone-comparison
mapping cones supply the stable cone-comparison isomorphism family used by the
support truncation field. -/
theorem supportConeComparison_of_nullHomotopicIdentity
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          ∃ hom :
            ∀ i j,
              (ComplexShape.up ℤ).Rel j i →
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)).X i ⟶
                  (CochainComplex.mappingCone
                    (TraceAnalyticMotivicTStructure
                      .additiveNormalizedConeComparisonCochainMap
                        1
                        complex)).X j,
            𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)) =
              _root_.HomologicalComplex.nullHomotopicMap' hom)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree] :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        1
        complex) :=
  Exists.elim
    (nullHomotopicIdentity complex bounded)
    (fun hom identity_eq =>
      TraceAnalyticMotivicTStructure
        .stableNormalizedConeComparisonMap_isIso_of_identity_eq_nullHomotopicMap
          1
          complex
          hom
          identity_eq)

/-- The support-based motivic t-structure assembled from explicit
null-homotopic identity presentations of the normalized cone-comparison mapping
cones. -/
def supportTStructureOfNullHomotopicIdentity
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          ∃ hom :
            ∀ i j,
              (ComplexShape.up ℤ).Rel j i →
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)).X i ⟶
                  (CochainComplex.mappingCone
                    (TraceAnalyticMotivicTStructure
                      .additiveNormalizedConeComparisonCochainMap
                        1
                        complex)).X j,
            𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)) =
              _root_.HomologicalComplex.nullHomotopicMap' hom) :
    TStructure TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfConeComparison
      (fun complex bounded =>
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportConeComparison_of_nullHomotopicIdentity
            nullHomotopicIdentity
            complex
            bounded)

/-- The null-homotopy support t-structure has the support `LE` predicate. -/
theorem supportTStructureOfNullHomotopicIdentity_LE
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          ∃ hom :
            ∀ i j,
              (ComplexShape.up ℤ).Rel j i →
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)).X i ⟶
                  (CochainComplex.mappingCone
                    (TraceAnalyticMotivicTStructure
                      .additiveNormalizedConeComparisonCochainMap
                        1
                        complex)).X j,
            𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)) =
              _root_.HomologicalComplex.nullHomotopicMap' hom) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfNullHomotopicIdentity nullHomotopicIdentity).LE =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE :=
  rfl

/-- The null-homotopy support t-structure has the support `GE` predicate. -/
theorem supportTStructureOfNullHomotopicIdentity_GE
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          ∃ hom :
            ∀ i j,
              (ComplexShape.up ℤ).Rel j i →
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)).X i ⟶
                  (CochainComplex.mappingCone
                    (TraceAnalyticMotivicTStructure
                      .additiveNormalizedConeComparisonCochainMap
                        1
                        complex)).X j,
            𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)) =
              _root_.HomologicalComplex.nullHomotopicMap' hom) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfNullHomotopicIdentity nullHomotopicIdentity).GE =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE :=
  rfl

/-- The null-homotopy support t-structure has the proved support
orthogonality field. -/
theorem supportTStructureOfNullHomotopicIdentity_zero
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          ∃ hom :
            ∀ i j,
              (ComplexShape.up ℤ).Rel j i →
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)).X i ⟶
                  (CochainComplex.mappingCone
                    (TraceAnalyticMotivicTStructure
                      .additiveNormalizedConeComparisonCochainMap
                        1
                        complex)).X j,
            𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)) =
              _root_.HomologicalComplex.nullHomotopicMap' hom)
    {source target : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfNullHomotopicIdentity
          nullHomotopicIdentity).LE
          0
          source)
    (target_mem :
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfNullHomotopicIdentity
          nullHomotopicIdentity).GE
          1
          target) :
    hom = 0 :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfNullHomotopicIdentity nullHomotopicIdentity).zero'
      hom
      source_mem
      target_mem

/-- The null-homotopy support t-structure has the adjacent `LE` monotonicity
field. -/
theorem supportTStructureOfNullHomotopicIdentity_LE_zero_le
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          ∃ hom :
            ∀ i j,
              (ComplexShape.up ℤ).Rel j i →
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)).X i ⟶
                  (CochainComplex.mappingCone
                    (TraceAnalyticMotivicTStructure
                      .additiveNormalizedConeComparisonCochainMap
                        1
                        complex)).X j,
            𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)) =
              _root_.HomologicalComplex.nullHomotopicMap' hom) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfNullHomotopicIdentity
        nullHomotopicIdentity).LE 0 ≤
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfNullHomotopicIdentity
          nullHomotopicIdentity).LE 1 :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfNullHomotopicIdentity nullHomotopicIdentity)
      .LE_zero_le

/-- The null-homotopy support t-structure has the adjacent `GE` monotonicity
field. -/
theorem supportTStructureOfNullHomotopicIdentity_GE_one_le
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          ∃ hom :
            ∀ i j,
              (ComplexShape.up ℤ).Rel j i →
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)).X i ⟶
                  (CochainComplex.mappingCone
                    (TraceAnalyticMotivicTStructure
                      .additiveNormalizedConeComparisonCochainMap
                        1
                        complex)).X j,
            𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)) =
              _root_.HomologicalComplex.nullHomotopicMap' hom) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfNullHomotopicIdentity
        nullHomotopicIdentity).GE 1 ≤
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfNullHomotopicIdentity
          nullHomotopicIdentity).GE 0 :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfNullHomotopicIdentity nullHomotopicIdentity)
      .GE_one_le

/-- The null-homotopy support t-structure has the zero-one truncation triangle
field. -/
theorem supportTStructureOfNullHomotopicIdentity_exists_triangle_zero_one
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          ∃ hom :
            ∀ i j,
              (ComplexShape.up ℤ).Rel j i →
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)).X i ⟶
                  (CochainComplex.mappingCone
                    (TraceAnalyticMotivicTStructure
                      .additiveNormalizedConeComparisonCochainMap
                        1
                        complex)).X j,
            𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)) =
              _root_.HomologicalComplex.nullHomotopicMap' hom)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
      (_ :
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportTStructureOfNullHomotopicIdentity
            nullHomotopicIdentity).LE 0 lower)
      (_ :
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportTStructureOfNullHomotopicIdentity
            nullHomotopicIdentity).GE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .distinguishedTriangles :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfNullHomotopicIdentity nullHomotopicIdentity)
      .exists_triangle_zero_one
        object

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
