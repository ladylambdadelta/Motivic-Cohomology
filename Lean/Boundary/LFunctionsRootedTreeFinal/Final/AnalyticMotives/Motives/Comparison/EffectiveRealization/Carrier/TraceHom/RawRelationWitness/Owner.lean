import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.QuotientCandidate.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.RelationClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Ledgers.Owner

/-!
# Raw relation-witness carriers for analytic effective realization

This file exposes concrete raw quotient relation witnesses between
trace-correspondence quotient candidates.  A witness is a relation ledger
together with a finite closure derivation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual raw quotient relation witness. -/
def TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessCarrier
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationWitness left right :=
  witness

/-- The relation ledger carried by a raw quotient relation witness. -/
def TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessLedger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationLedger :=
  witness.ledger

/-- The finite relation-closure derivation carried by a raw witness. -/
def TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessDerivation
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationClosure witness.ledger left right :=
  witness.derivation

/-- The certificate ledger carried by a raw quotient relation witness. -/
def TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessCertificateLedger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    ResidueChannelCertificateLedger :=
  witness.certificateLedger

/-- The imported finite-rectangle count carried by a raw quotient relation witness. -/
def TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessImportedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    Nat :=
  witness.importedRectangleCount

/-- The imported finite rectangles carried by a raw quotient relation witness. -/
def TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessImportedRectangles
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  witness.importedRectangles

/-- The trace-bookkeeping count carried by a raw quotient relation witness. -/
def TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessTraceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    Nat :=
  witness.traceBookkeepingCount

/-- The rewrite-step count carried by a raw quotient relation witness. -/
def TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessRewriteStepCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    Nat :=
  witness.rewriteStepCount

/-- The raw relation-witness carrier is definitionally the supplied witness. -/
theorem TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessCarrier_eq
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessCarrier witness =
      witness :=
  rfl

/-- The raw relation witness carries exactly its relation ledger certificates. -/
theorem TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessCertificateLedger_eq_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessCertificateLedger witness =
      (TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessLedger
        witness).certificateLedger :=
  TraceCorQRelationWitness.certificateLedger_eq_relationLedger
    witness

/-- The raw relation witness imports exactly its relation ledger rectangles. -/
theorem TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessImportedRectangles_eq_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessImportedRectangles witness =
      (TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessLedger
        witness).importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_ledger
    witness

/-- A raw relation witness's imported count is the length of its rectangle list. -/
theorem TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessImportedRectangleCount_eq_length
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessImportedRectangleCount witness =
      (TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessImportedRectangles
        witness).length :=
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    witness

/-- A reflexive raw relation witness carries the empty certificate ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessRefl_certificateLedger
    (candidate : TraceCorQQuotientCandidate) :
    TraceAnalyticEffectiveRealization.traceHomRawRelationWitnessCertificateLedger
      (TraceCorQRelationWitness.refl candidate) =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationWitness.refl_certificateLedger
    candidate

end AnalyticMotives
end LFunctions
end Boundary
