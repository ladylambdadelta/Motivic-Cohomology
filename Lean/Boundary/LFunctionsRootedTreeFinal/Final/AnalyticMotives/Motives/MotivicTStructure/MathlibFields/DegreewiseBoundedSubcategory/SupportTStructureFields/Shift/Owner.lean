import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportPredicates.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Owner

/-!
# Shift fields for the support-based t-structure predicates

This file lifts concrete support-shift closure to Mathlib's `LE_shift` and
`GE_shift` fields on the degreewise bounded stable source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Iso-closed ambient lower-tail support is stable under ambient shifts. -/
theorem supportedLEIsoClosedAmbient_shift
    (sourceCut shift targetCut : ℤ)
    (cut_eq : shift + targetCut = sourceCut)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEIsoClosedAmbient sourceCut object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedLEIsoClosedAmbient targetCut (object⟦shift⟧) :=
  Exists.elim
    membership
    (fun representative representativeData =>
      Exists.elim
        representativeData
        (fun representativeMembership representativeIsoData =>
          Nonempty.elim
            representativeIsoData
            (fun representativeIso =>
              let shiftedRepresentativeMembership :
                  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                    .supportedLEIsoClosedAmbient
                      targetCut
                      (representative⟦shift⟧) :=
                TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                  .supportedLEAmbient_shift
                    sourceCut
                    shift
                    targetCut
                    cut_eq
                    representative
                    representativeMembership
              CategoryTheory.mem_of_iso
                (P := TraceAnalyticDMgmComparisonSource
                  .DegreewiseBoundedStable
                  .supportedLEIsoClosedAmbient targetCut)
                ((CategoryTheory.shiftFunctor
                  TraceAnalyticDMgmComparisonSource
                  shift).mapIso representativeIso).symm
                shiftedRepresentativeMembership)))

/-- Iso-closed ambient upper-tail support is stable under ambient shifts. -/
theorem supportedGEIsoClosedAmbient_shift
    (sourceCut shift targetCut : ℤ)
    (cut_eq : shift + targetCut = sourceCut)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEIsoClosedAmbient sourceCut object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedGEIsoClosedAmbient targetCut (object⟦shift⟧) :=
  Exists.elim
    membership
    (fun representative representativeData =>
      Exists.elim
        representativeData
        (fun representativeMembership representativeIsoData =>
          Nonempty.elim
            representativeIsoData
            (fun representativeIso =>
              let shiftedRepresentativeMembership :
                  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                    .supportedGEIsoClosedAmbient
                      targetCut
                      (representative⟦shift⟧) :=
                TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                  .supportedGEAmbient_shift
                    sourceCut
                    shift
                    targetCut
                    cut_eq
                    representative
                    representativeMembership
              CategoryTheory.mem_of_iso
                (P := TraceAnalyticDMgmComparisonSource
                  .DegreewiseBoundedStable
                  .supportedGEIsoClosedAmbient targetCut)
                ((CategoryTheory.shiftFunctor
                  TraceAnalyticDMgmComparisonSource
                  shift).mapIso representativeIso).symm
                shiftedRepresentativeMembership)))

/-- The support-based `LE_shift` field. -/
theorem supportTStructureLE_shift
    (sourceCut shift targetCut : ℤ)
    (cut_eq : shift + targetCut = sourceCut)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (membership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE sourceCut object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureLE targetCut (object⟦shift⟧) :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportedLEIsoClosedAmbient_shift
      sourceCut
      shift
      targetCut
      cut_eq
      object.object
      membership

/-- The support-based `GE_shift` field. -/
theorem supportTStructureGE_shift
    (sourceCut shift targetCut : ℤ)
    (cut_eq : shift + targetCut = sourceCut)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (membership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE sourceCut object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE targetCut (object⟦shift⟧) :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportedGEIsoClosedAmbient_shift
      sourceCut
      shift
      targetCut
      cut_eq
      object.object
      membership

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
