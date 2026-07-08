import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Fields.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Shift.Owner

/-!
# T-structure fields on the degreewise bounded stable source

This file pulls the ambient Mathlib-facing analytic aisle and coaisle
predicates back to the degreewise bounded stable full subcategory, and proves
the non-truncation t-structure fields there.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Mathlib-facing `LE` predicate restricted to the degreewise bounded stable
source. -/
abbrev tStructureLE
    (cut : ℤ)
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    Prop :=
  TraceAnalyticMotivicTStructure.tStructureLE cut object.object

/-- Mathlib-facing `GE` predicate restricted to the degreewise bounded stable
source. -/
abbrev tStructureGE
    (cut : ℤ)
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    Prop :=
  TraceAnalyticMotivicTStructure.tStructureGE cut object.object

/-- The restricted `LE` predicate is exactly the ambient `LE` predicate on the
included object. -/
theorem tStructureLE_iff_ambient
    (cut : ℤ)
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureLE cut object ↔
      TraceAnalyticMotivicTStructure.tStructureLE cut object.object :=
  Iff.rfl

/-- The restricted `GE` predicate is exactly the ambient `GE` predicate on the
included object. -/
theorem tStructureGE_iff_ambient
    (cut : ℤ)
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureGE cut object ↔
      TraceAnalyticMotivicTStructure.tStructureGE cut object.object :=
  Iff.rfl

/-- The degreewise bounded `LE` predicate is closed under isomorphisms. -/
def tStructureLE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureLE cut) where
  of_iso :=
    fun iso source_mem =>
      CategoryTheory.ClosedUnderIsomorphisms.of_iso
        ((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .inclusion).mapIso iso)
        source_mem

/-- The degreewise bounded `GE` predicate is closed under isomorphisms. -/
def tStructureGE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureGE cut) where
  of_iso :=
    fun iso source_mem =>
      CategoryTheory.ClosedUnderIsomorphisms.of_iso
        ((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .inclusion).mapIso iso)
        source_mem

/-- The degreewise bounded `LE` predicates are monotone in the displayed cut. -/
theorem tStructureLE_monotone :
    Monotone
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureLE :=
  fun lower upper cut_le object membership =>
    TraceAnalyticMotivicTStructure.mathlibLE_monotone
      cut_le
      object.object
      membership

/-- The degreewise bounded `GE` predicates are antitone in the displayed cut. -/
theorem tStructureGE_antitone :
    Antitone
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureGE :=
  fun lower upper cut_le object membership =>
    TraceAnalyticMotivicTStructure.mathlibGE_antitone
      cut_le
      object.object
      membership

/-- The degreewise bounded adjacent `LE` monotonicity field. -/
theorem tStructureLE_zero_le :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureLE 0 ≤
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureLE 1 :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .tStructureLE_monotone
    (zero_le_one : (0 : ℤ) ≤ 1)

/-- The degreewise bounded adjacent `GE` monotonicity field. -/
theorem tStructureGE_one_le :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureGE 1 ≤
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureGE 0 :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .tStructureGE_antitone
    (zero_le_one : (0 : ℤ) ≤ 1)

/-- The degreewise bounded `LE` shift field inherited from the ambient
analytic motivic t-structure field. -/
theorem tStructureLE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (membership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureLE n object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .tStructureLE n'
        (object⟦a⟧) :=
  TraceAnalyticMotivicTStructure.tStructureLE_shift
    n
    a
    n'
    h
    object.object
    membership

/-- The degreewise bounded `GE` shift field inherited from the ambient
analytic motivic t-structure field. -/
theorem tStructureGE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (membership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureGE n object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .tStructureGE n'
        (object⟦a⟧) :=
  TraceAnalyticMotivicTStructure.tStructureGE_shift
    n
    a
    n'
    h
    object.object
    membership

/-- Ambient orthogonality restricts to the degreewise bounded stable source. -/
theorem tStructure_zero_of_ambient_zero
    (ambient_zero :
      ∀ {source target : TraceAnalyticDMgmComparisonSource}
        (hom : source ⟶ target),
        TraceAnalyticMotivicTStructure.tStructureLE 0 source →
        TraceAnalyticMotivicTStructure.tStructureGE 1 target →
        hom = 0)
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .tStructureGE 1 target) :
    hom = 0 :=
  ambient_zero hom source_mem target_mem

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
