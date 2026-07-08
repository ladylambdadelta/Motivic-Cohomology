import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportPredicates.Owner

/-!
# Iso-closed support predicates for the degreewise bounded source

The concrete support predicates are representative statements.  This file
passes them through Mathlib's iso-closure operation, which is the closure
condition required by `TStructure`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Iso-closed ambient lower-tail support predicate. -/
abbrev supportedLEIsoClosedAmbient
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource → Prop :=
  CategoryTheory.isoClosure
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedLEAmbient cut)

/-- Iso-closed ambient upper-tail support predicate. -/
abbrev supportedGEIsoClosedAmbient
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource → Prop :=
  CategoryTheory.isoClosure
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedGEAmbient cut)

/-- Iso-closed lower-tail support on the degreewise bounded source. -/
abbrev supportedLEIsoClosed
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    Prop :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportedLEIsoClosedAmbient cut object.object

/-- Iso-closed upper-tail support on the degreewise bounded source. -/
abbrev supportedGEIsoClosed
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    Prop :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportedGEIsoClosedAmbient cut object.object

/-- Concrete lower-tail support maps to its iso-closed predicate. -/
theorem supportedLEAmbient_le_supportedLEIsoClosedAmbient
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEAmbient cut ≤
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEIsoClosedAmbient cut :=
  CategoryTheory.le_isoClosure
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedLEAmbient cut)

/-- Concrete upper-tail support maps to its iso-closed predicate. -/
theorem supportedGEAmbient_le_supportedGEIsoClosedAmbient
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEAmbient cut ≤
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEIsoClosedAmbient cut :=
  CategoryTheory.le_isoClosure
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedGEAmbient cut)

/-- The lower stable truncation vertex belongs to the iso-closed lower-tail
support predicate. -/
theorem stableTruncLE_mem_supportedLEIsoClosedAmbient
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedLEIsoClosedAmbient
        cut
        (TraceAnalyticMotivicTStructure.stableTruncLE cut complex) :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportedLEAmbient_le_supportedLEIsoClosedAmbient
      cut
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .stableTruncLE_mem_supportedLEAmbient cut complex bounded)

/-- The upper stable truncation vertex belongs to the iso-closed upper-tail
support predicate. -/
theorem stableTruncGE_mem_supportedGEIsoClosedAmbient
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedGEIsoClosedAmbient
        cut
        (TraceAnalyticMotivicTStructure.stableTruncGE cut complex) :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportedGEAmbient_le_supportedGEIsoClosedAmbient
      cut
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .stableTruncGE_mem_supportedGEAmbient cut complex bounded)

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
