import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Owner

/-!
# Payload projections for typed hom relation witnesses

This file records direct certificate-ledger payload projections for typed hom
relation witnesses.  The base owner exposes raw-witness and relation-ledger
views; this nested owner gives downstream typed-hom code the certificate-ledger
view directly.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A typed hom relation witness imports exactly the payload counted by its certificate ledger. -/
theorem TraceCorQHomRelationWitness.importedRectangleCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.importedRectangleCount =
      witness.certificateLedger.importedRectangleCount :=
  rfl

/-- A typed hom relation witness exposes the rectangles extracted from its certificate ledger. -/
theorem TraceCorQHomRelationWitness.importedRectangles_eq_certificateLedger_rectangles
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.importedRectangles =
      witness.certificateLedger.importedRectangles :=
  rfl

/-- A typed hom relation witness's bookkeeping payload is counted by its certificate ledger. -/
theorem TraceCorQHomRelationWitness.traceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.traceBookkeepingCount =
      witness.certificateLedger.traceBookkeepingCount :=
  rfl

/-- A typed hom relation witness's rewrite-step payload is counted by its certificate ledger. -/
theorem TraceCorQHomRelationWitness.rewriteStepCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.rewriteStepCount =
      witness.certificateLedger.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
