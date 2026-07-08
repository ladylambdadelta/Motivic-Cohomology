import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.RelationWitnesses.Add.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.RelationWitnesses.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.RelationWitnesses.Smul.Payload.Owner

/-!
# Public typed hom relation witnesses

This file exposes the data-bearing relation-witness operations for typed
trace-correspondence hom representatives at the top root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes typed hom relation-witness ledgers as raw ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_ledger_eq_raw
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.ledger =
      TraceCorQRelationWitness.ledger witness :=
  TraceCorQHomRelationWitness.ledger_eq_raw
    witness

/-- The top root exposes typed hom relation-witness certificate ledgers as raw ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_certificateLedger_eq_raw
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.certificateLedger =
      TraceCorQRelationWitness.certificateLedger witness :=
  TraceCorQHomRelationWitness.certificateLedger_eq_raw
    witness

/-- The top root exposes typed hom relation-witness imported counts as raw counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_importedRectangleCount_eq_raw
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.importedRectangleCount =
      TraceCorQRelationWitness.importedRectangleCount witness :=
  TraceCorQHomRelationWitness.importedRectangleCount_eq_raw
    witness

/-- The top root exposes typed hom relation-witness imported rectangles as raw rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_importedRectangles_eq_raw
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.importedRectangles =
      TraceCorQRelationWitness.importedRectangles witness :=
  TraceCorQHomRelationWitness.importedRectangles_eq_raw
    witness

/-- The top root exposes typed hom relation-witness bookkeeping as raw bookkeeping. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_traceBookkeepingCount_eq_raw
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.traceBookkeepingCount =
      TraceCorQRelationWitness.traceBookkeepingCount witness :=
  TraceCorQHomRelationWitness.traceBookkeepingCount_eq_raw
    witness

/-- The top root exposes typed hom relation-witness rewrite-step counts as raw counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_rewriteStepCount_eq_raw
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.rewriteStepCount =
      TraceCorQRelationWitness.rewriteStepCount witness :=
  TraceCorQHomRelationWitness.rewriteStepCount_eq_raw
    witness

/-- The top root exposes relation-witness certificate ledgers as ledger certificates. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_certificateLedger_eq_ledger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.certificateLedger =
      witness.ledger.certificateLedger :=
  TraceCorQHomRelationWitness.certificateLedger_eq_ledger
    witness

/-- The top root exposes relation-witness imported counts as ledger counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_importedRectangleCount_eq_ledger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.importedRectangleCount =
      witness.ledger.importedRectangleCount :=
  TraceCorQHomRelationWitness.importedRectangleCount_eq_ledger
    witness

/-- The top root exposes relation-witness imported rectangles as ledger rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_importedRectangles_eq_ledger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.importedRectangles =
      witness.ledger.importedRectangles :=
  TraceCorQHomRelationWitness.importedRectangles_eq_ledger
    witness

/-- The top root exposes relation-witness bookkeeping counts as ledger counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_traceBookkeepingCount_eq_ledger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.traceBookkeepingCount =
      witness.ledger.traceBookkeepingCount :=
  TraceCorQHomRelationWitness.traceBookkeepingCount_eq_ledger
    witness

/-- The top root exposes relation-witness rewrite-step counts as ledger counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_rewriteStepCount_eq_ledger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.rewriteStepCount =
      witness.ledger.rewriteStepCount :=
  TraceCorQHomRelationWitness.rewriteStepCount_eq_ledger
    witness

/-- The top root exposes reflexive relation-witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_refl_certificateLedger
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.refl representative).certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQHomRelationWitness.refl_certificateLedger
    representative

/-- The top root exposes reflexive relation-witness imported counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_refl_importedRectangleCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.refl representative).importedRectangleCount =
      0 :=
  TraceCorQHomRelationWitness.refl_importedRectangleCount
    representative

/-- The top root exposes reflexive relation-witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_refl_importedRectangles
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.refl representative).importedRectangles =
      [] :=
  TraceCorQHomRelationWitness.refl_importedRectangles
    representative

/-- The top root exposes reflexive relation-witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_refl_traceBookkeepingCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.refl representative).traceBookkeepingCount =
      0 :=
  TraceCorQHomRelationWitness.refl_traceBookkeepingCount
    representative

/-- The top root exposes reflexive relation-witness rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_refl_rewriteStepCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.refl representative).rewriteStepCount =
      0 :=
  TraceCorQHomRelationWitness.refl_rewriteStepCount
    representative

/-- The top root exposes symmetric relation-witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_symm_certificateLedger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.symm witness).certificateLedger =
      witness.certificateLedger :=
  TraceCorQHomRelationWitness.symm_certificateLedger
    witness

/-- The top root exposes symmetric relation-witness imported counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_symm_importedRectangleCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.symm witness).importedRectangleCount =
      witness.importedRectangleCount :=
  TraceCorQHomRelationWitness.symm_importedRectangleCount
    witness

/-- The top root exposes symmetric relation-witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_symm_importedRectangles
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.symm witness).importedRectangles =
      witness.importedRectangles :=
  TraceCorQHomRelationWitness.symm_importedRectangles
    witness

/-- The top root exposes symmetric relation-witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_symm_traceBookkeepingCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.symm witness).traceBookkeepingCount =
      witness.traceBookkeepingCount :=
  TraceCorQHomRelationWitness.symm_traceBookkeepingCount
    witness

/-- The top root exposes symmetric relation-witness rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_symm_rewriteStepCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.symm witness).rewriteStepCount =
      witness.rewriteStepCount :=
  TraceCorQHomRelationWitness.symm_rewriteStepCount
    witness

/-- The top root exposes transitive relation-witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_trans_certificateLedger
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelationWitness left middle)
    (second : TraceCorQHomRelationWitness middle right) :
    (TraceCorQHomRelationWitness.trans first second).certificateLedger =
      ResidueChannelCertificateLedger.append
        first.certificateLedger
        second.certificateLedger :=
  TraceCorQHomRelationWitness.trans_certificateLedger
    first
    second

/-- The top root exposes transitive relation-witness imported counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_trans_importedRectangleCount
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelationWitness left middle)
    (second : TraceCorQHomRelationWitness middle right) :
    (TraceCorQHomRelationWitness.trans first second).importedRectangleCount =
      first.importedRectangleCount +
        second.importedRectangleCount :=
  TraceCorQHomRelationWitness.trans_importedRectangleCount
    first
    second

/-- The top root exposes transitive relation-witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_trans_importedRectangles
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelationWitness left middle)
    (second : TraceCorQHomRelationWitness middle right) :
    (TraceCorQHomRelationWitness.trans first second).importedRectangles =
      first.importedRectangles ++
        second.importedRectangles :=
  TraceCorQHomRelationWitness.trans_importedRectangles
    first
    second

/-- The top root exposes transitive relation-witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_trans_traceBookkeepingCount
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelationWitness left middle)
    (second : TraceCorQHomRelationWitness middle right) :
    (TraceCorQHomRelationWitness.trans first second).traceBookkeepingCount =
      first.traceBookkeepingCount +
        second.traceBookkeepingCount :=
  TraceCorQHomRelationWitness.trans_traceBookkeepingCount
    first
    second

/-- The top root exposes transitive relation-witness rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_trans_rewriteStepCount
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelationWitness left middle)
    (second : TraceCorQHomRelationWitness middle right) :
    (TraceCorQHomRelationWitness.trans first second).rewriteStepCount =
      first.rewriteStepCount +
        second.rewriteStepCount :=
  TraceCorQHomRelationWitness.trans_rewriteStepCount
    first
    second

/-- The top root exposes soundness for data-bearing typed hom relation witnesses. -/
theorem AnalyticMotivesRoot.traceCorQHom_soundWitness
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    TraceCorQHom.ofRepresentative left =
      TraceCorQHom.ofRepresentative right :=
  TraceCorQHom.soundWitness
    witness

end AnalyticMotives
end LFunctions
end Boundary
