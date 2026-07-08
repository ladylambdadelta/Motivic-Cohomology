import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Assembly.Owner

/-!
# Projections from the support-based t-structure assembly

This file exposes the major Mathlib `TStructure` fields of the assembled
support t-structure under stable analytic names, so downstream heart and
transport code can consume the proved fields directly.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The assembled support t-structure has the proved support `LE`
isomorphism-closure field. -/
def supportTStructureOfConeComparison_LE_closedUnderIsomorphisms
    (coneComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .stableNormalizedConeComparisonMap 1 complex)) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfConeComparison coneComparison).LE :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfConeComparison coneComparison).LE_closedUnderIsomorphisms

/-- The assembled support t-structure has the proved support `GE`
isomorphism-closure field. -/
def supportTStructureOfConeComparison_GE_closedUnderIsomorphisms
    (coneComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .stableNormalizedConeComparisonMap 1 complex)) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfConeComparison coneComparison).GE :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfConeComparison coneComparison).GE_closedUnderIsomorphisms

/-- The assembled support t-structure has the proved `LE` shift field. -/
theorem supportTStructureOfConeComparison_LE_shift
    (coneComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .stableNormalizedConeComparisonMap 1 complex))
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (membership :
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfConeComparison coneComparison).LE n object) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfConeComparison coneComparison).LE n' (object⟦a⟧) :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfConeComparison coneComparison).LE_shift
      n
      a
      n'
      h
      object
      membership

/-- The assembled support t-structure has the proved `GE` shift field. -/
theorem supportTStructureOfConeComparison_GE_shift
    (coneComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .stableNormalizedConeComparisonMap 1 complex))
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (membership :
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfConeComparison coneComparison).GE n object) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfConeComparison coneComparison).GE n' (object⟦a⟧) :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfConeComparison coneComparison).GE_shift
      n
      a
      n'
      h
      object
      membership

/-- The assembled support t-structure has the proved support orthogonality
field. -/
theorem supportTStructureOfConeComparison_zero
    (coneComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .stableNormalizedConeComparisonMap 1 complex))
    {source target : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfConeComparison coneComparison).LE
          0
          source)
    (target_mem :
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfConeComparison coneComparison).GE
          1
          target) :
    hom = 0 :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfConeComparison coneComparison).zero'
      hom
      source_mem
      target_mem

/-- The assembled support t-structure has the proved adjacent `LE`
monotonicity field. -/
theorem supportTStructureOfConeComparison_LE_zero_le
    (coneComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .stableNormalizedConeComparisonMap 1 complex)) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfConeComparison coneComparison).LE 0 ≤
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfConeComparison coneComparison).LE 1 :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfConeComparison coneComparison).LE_zero_le

/-- The assembled support t-structure has the proved adjacent `GE`
monotonicity field. -/
theorem supportTStructureOfConeComparison_GE_one_le
    (coneComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .stableNormalizedConeComparisonMap 1 complex)) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfConeComparison coneComparison).GE 1 ≤
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfConeComparison coneComparison).GE 0 :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfConeComparison coneComparison).GE_one_le

/-- The assembled support t-structure has the proved zero-one truncation
triangle field. -/
theorem supportTStructureOfConeComparison_exists_triangle_zero_one
    (coneComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .stableNormalizedConeComparisonMap 1 complex))
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
      (_ :
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportTStructureOfConeComparison coneComparison).LE 0 lower)
      (_ :
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportTStructureOfConeComparison coneComparison).GE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .distinguishedTriangles :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfConeComparison coneComparison)
      .exists_triangle_zero_one
        object

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
