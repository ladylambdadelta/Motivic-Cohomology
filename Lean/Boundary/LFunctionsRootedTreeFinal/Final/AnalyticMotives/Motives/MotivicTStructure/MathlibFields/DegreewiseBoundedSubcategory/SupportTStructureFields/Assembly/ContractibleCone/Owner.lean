import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Assembly.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.IsIso.ContractibleCone.Owner

/-!
# Support t-structure from contractible cone comparisons

This file gives the support t-structure constructor whose analytic input is a
contracting homotopy for the mapping cone of each normalized cone-to-upper
cochain map, in the same degreewise iso-closure bounded representative shape
used by the support truncation field.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Contractible normalized cone-comparison mapping cones supply the stable
cone-comparison isomorphism family used by the support truncation field. -/
theorem supportConeComparison_of_contractibleCone
    (contractibleCone :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          Nonempty
            (Homotopy
              (𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)))
              0))
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
  TraceAnalyticMotivicTStructure
    .stableNormalizedConeComparisonMap_isIso_of_contractibleCone
      1
      complex
      (contractibleCone complex bounded)

/-- The support-based motivic t-structure assembled from concrete contracting
homotopies of the normalized cone-comparison mapping cones. -/
def supportTStructureOfContractibleCone
    (contractibleCone :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          Nonempty
            (Homotopy
              (𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)))
              0)) :
    TStructure TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfConeComparison
      (fun complex bounded =>
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportConeComparison_of_contractibleCone
            contractibleCone
            complex
            bounded)

/-- The contractible-cone support t-structure has the support `LE` predicate. -/
theorem supportTStructureOfContractibleCone_LE
    (contractibleCone :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          Nonempty
            (Homotopy
              (𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)))
              0)) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfContractibleCone contractibleCone).LE =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE :=
  rfl

/-- The contractible-cone support t-structure has the support `GE` predicate. -/
theorem supportTStructureOfContractibleCone_GE
    (contractibleCone :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          Nonempty
            (Homotopy
              (𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)))
              0)) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfContractibleCone contractibleCone).GE =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE :=
  rfl

/-- The contractible-cone support t-structure has the proved support
orthogonality field. -/
theorem supportTStructureOfContractibleCone_zero
    (contractibleCone :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          Nonempty
            (Homotopy
              (𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)))
              0))
    {source target : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfContractibleCone contractibleCone).LE
          0
          source)
    (target_mem :
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfContractibleCone contractibleCone).GE
          1
          target) :
    hom = 0 :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfContractibleCone contractibleCone).zero'
      hom
      source_mem
      target_mem

/-- The contractible-cone support t-structure has the adjacent `LE`
monotonicity field. -/
theorem supportTStructureOfContractibleCone_LE_zero_le
    (contractibleCone :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          Nonempty
            (Homotopy
              (𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)))
              0)) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfContractibleCone contractibleCone).LE 0 ≤
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfContractibleCone contractibleCone).LE 1 :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfContractibleCone contractibleCone).LE_zero_le

/-- The contractible-cone support t-structure has the adjacent `GE`
monotonicity field. -/
theorem supportTStructureOfContractibleCone_GE_one_le
    (contractibleCone :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          Nonempty
            (Homotopy
              (𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)))
              0)) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfContractibleCone contractibleCone).GE 1 ≤
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfContractibleCone contractibleCone).GE 0 :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfContractibleCone contractibleCone).GE_one_le

/-- The contractible-cone support t-structure has the zero-one truncation
triangle field. -/
theorem supportTStructureOfContractibleCone_exists_triangle_zero_one
    (contractibleCone :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          Nonempty
            (Homotopy
              (𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)))
              0))
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
      (_ :
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportTStructureOfContractibleCone contractibleCone).LE 0 lower)
      (_ :
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportTStructureOfContractibleCone contractibleCone).GE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .distinguishedTriangles :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfContractibleCone contractibleCone)
      .exists_triangle_zero_one
        object

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
