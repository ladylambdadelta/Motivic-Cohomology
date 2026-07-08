import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Assembly.ContractibleCone.Owner

/-!
# Projections from the contractible-cone support t-structure

This file exposes the remaining Mathlib `TStructure` fields of the
contractible-cone support assembly.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The contractible-cone support t-structure supplies the `LE`
closed-under-isomorphism field. -/
theorem supportTStructureOfContractibleCone_LE_closedUnderIsomorphisms
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
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfContractibleCone contractibleCone).LE cut) :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfContractibleCone contractibleCone)
      .LE_closedUnderIsomorphisms
        cut

/-- The contractible-cone support t-structure supplies the `GE`
closed-under-isomorphism field. -/
theorem supportTStructureOfContractibleCone_GE_closedUnderIsomorphisms
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
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfContractibleCone contractibleCone).GE cut) :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfContractibleCone contractibleCone)
      .GE_closedUnderIsomorphisms
        cut

/-- The contractible-cone support t-structure supplies the `LE_shift` field. -/
theorem supportTStructureOfContractibleCone_LE_shift
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
    (sourceCut shift targetCut : ℤ)
    (cut_eq : shift + targetCut = sourceCut)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (membership :
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfContractibleCone contractibleCone).LE
          sourceCut
          object) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfContractibleCone contractibleCone).LE
        targetCut
        (object⟦shift⟧) :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfContractibleCone contractibleCone).LE_shift
      sourceCut
      shift
      targetCut
      cut_eq
      object
      membership

/-- The contractible-cone support t-structure supplies the `GE_shift` field. -/
theorem supportTStructureOfContractibleCone_GE_shift
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
    (sourceCut shift targetCut : ℤ)
    (cut_eq : shift + targetCut = sourceCut)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (membership :
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfContractibleCone contractibleCone).GE
          sourceCut
          object) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfContractibleCone contractibleCone).GE
        targetCut
        (object⟦shift⟧) :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfContractibleCone contractibleCone).GE_shift
      sourceCut
      shift
      targetCut
      cut_eq
      object
      membership

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
