import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Reindexed.Owner

/-!
# Bounded-source support of Mathlib-facing predicates

The Mathlib-facing analytic t-structure predicates are iso-closures of
bounded-representative predicates.  This file proves that every object in one
of those predicates lies in the bounded stable analytic comparison source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Iso-closed concrete aisle membership implies bounded stable source
membership. -/
theorem boundedStableObject_of_aisleLEIsoClosed
    (cut : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.aisleLEIsoClosed cut object) :
    TraceAnalyticDMgmComparisonSource.boundedStableObject object :=
  Exists.elim
    membership
    (fun representative representativeData =>
      Exists.elim
        representativeData
        (fun representativeMembership representativeIso =>
          Nonempty.elim
            representativeIso
            (fun iso =>
              CategoryTheory.mem_of_iso
                (P := TraceAnalyticDMgmComparisonSource.boundedStableObject)
                iso.symm
                (TraceAnalyticDMgmComparisonSource
                  .boundedStableObject_of_aisleLE
                    cut
                    representativeMembership))))

/-- Iso-closed concrete coaisle membership implies bounded stable source
membership. -/
theorem boundedStableObject_of_coaisleGEIsoClosed
    (cut : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.coaisleGEIsoClosed cut object) :
    TraceAnalyticDMgmComparisonSource.boundedStableObject object :=
  Exists.elim
    membership
    (fun representative representativeData =>
      Exists.elim
        representativeData
        (fun representativeMembership representativeIso =>
          Nonempty.elim
            representativeIso
            (fun iso =>
              CategoryTheory.mem_of_iso
                (P := TraceAnalyticDMgmComparisonSource.boundedStableObject)
                iso.symm
                (TraceAnalyticDMgmComparisonSource
                  .boundedStableObject_of_coaisleGE
                    cut
                    representativeMembership))))

/-- Mathlib-facing `LE` membership implies bounded stable source membership. -/
theorem boundedStableObject_of_mathlibLE
    (cut : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.mathlibLE cut object) :
    TraceAnalyticDMgmComparisonSource.boundedStableObject object :=
  TraceAnalyticMotivicTStructure.boundedStableObject_of_coaisleGEIsoClosed
    (-cut)
    membership

/-- Mathlib-facing `GE` membership implies bounded stable source membership. -/
theorem boundedStableObject_of_mathlibGE
    (cut : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.mathlibGE cut object) :
    TraceAnalyticDMgmComparisonSource.boundedStableObject object :=
  TraceAnalyticMotivicTStructure.boundedStableObject_of_aisleLEIsoClosed
    (-cut)
    membership

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
