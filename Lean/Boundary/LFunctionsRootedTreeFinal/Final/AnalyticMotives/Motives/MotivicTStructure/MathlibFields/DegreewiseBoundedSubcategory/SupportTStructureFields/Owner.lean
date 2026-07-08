import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportPredicates.IsoClosure.Owner

/-!
# Support-based t-structure field predicates

This file names the support-based `LE` and `GE` predicates on the degreewise
bounded stable source and proves their isomorphism-closure fields.  These are
the predicates supplied by concrete lower-tail and upper-tail analytic cochain
representatives, closed under stable equivalence.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Support-based `LE` predicate on the degreewise bounded stable source. -/
abbrev supportTStructureLE
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    Prop :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportedLEIsoClosed cut object

/-- Support-based `GE` predicate on the degreewise bounded stable source. -/
abbrev supportTStructureGE
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    Prop :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportedGEIsoClosed cut object

/-- The support-based `LE` predicate is definitionally the ambient iso-closed
lower-tail support predicate on the included object. -/
theorem supportTStructureLE_iff_ambient
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE cut object ↔
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEIsoClosedAmbient cut object.object :=
  Iff.rfl

/-- The support-based `GE` predicate is definitionally the ambient iso-closed
upper-tail support predicate on the included object. -/
theorem supportTStructureGE_iff_ambient
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE cut object ↔
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEIsoClosedAmbient cut object.object :=
  Iff.rfl

/-- The support-based `LE` predicate is closed under isomorphisms in the
degreewise bounded stable source. -/
def supportTStructureLE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE cut) where
  of_iso :=
    fun iso sourceMembership =>
      CategoryTheory.ClosedUnderIsomorphisms.of_iso
        ((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .inclusion).mapIso iso)
        sourceMembership

/-- The support-based `GE` predicate is closed under isomorphisms in the
degreewise bounded stable source. -/
def supportTStructureGE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE cut) where
  of_iso :=
    fun iso sourceMembership =>
      CategoryTheory.ClosedUnderIsomorphisms.of_iso
        ((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .inclusion).mapIso iso)
        sourceMembership

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
