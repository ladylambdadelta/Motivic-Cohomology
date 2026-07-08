import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Basic.Owner

/-!
# Public basic relation-witness certificate facts

This file exposes the basic certificate payload carried by relation witnesses
under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes the analytic certificate ledger carried by a relation witness. -/
def TraceCorQ.relationWitness_certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    ResidueChannelCertificateLedger :=
  TraceCorQRelationWitness.certificateLedger witness

/-- The trace-correspondence root exposes the imported finite-rectangle count of a relation witness. -/
def TraceCorQ.relationWitness_importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    Nat :=
  TraceCorQRelationWitness.importedRectangleCount witness

/-- The trace-correspondence root exposes the imported finite explicit-formula rectangles of a relation witness. -/
def TraceCorQ.relationWitness_importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceCorQRelationWitness.importedRectangles witness

/-- The trace-correspondence root exposes the internal trace-bookkeeping count of a relation witness. -/
def TraceCorQ.relationWitness_traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    Nat :=
  TraceCorQRelationWitness.traceBookkeepingCount witness

/-- The trace-correspondence root exposes the explicit rewrite-step count of a relation witness. -/
def TraceCorQ.relationWitness_rewriteStepCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    Nat :=
  TraceCorQRelationWitness.rewriteStepCount witness

/-- The trace-correspondence root exposes the relation-ledger certificate equality. -/
theorem TraceCorQ.relationWitness_certificateLedger_eq_relationLedger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.certificateLedger =
      witness.ledger.certificateLedger :=
  TraceCorQRelationWitness.certificateLedger_eq_relationLedger witness

/-- The trace-correspondence root exposes the relation-ledger imported-count equality. -/
theorem TraceCorQ.relationWitness_importedRectangleCount_eq_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangleCount =
      witness.ledger.importedRectangleCount :=
  TraceCorQRelationWitness.importedRectangleCount_eq_ledger witness

/-- The trace-correspondence root exposes the relation-ledger imported-rectangle equality. -/
theorem TraceCorQ.relationWitness_importedRectangles_eq_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangles =
      witness.ledger.importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_ledger witness

/-- The trace-correspondence root exposes the imported-count/list-length equality. -/
theorem TraceCorQ.relationWitness_importedRectangleCount_eq_length_importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangleCount =
      witness.importedRectangles.length :=
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    witness

/-- The trace-correspondence root exposes the relation-ledger bookkeeping equality. -/
theorem TraceCorQ.relationWitness_traceBookkeepingCount_eq_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.traceBookkeepingCount =
      witness.ledger.traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger witness

/-- The trace-correspondence root exposes the relation-ledger rewrite-step equality. -/
theorem TraceCorQ.relationWitness_rewriteStepCount_eq_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.rewriteStepCount =
      witness.ledger.rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_ledger witness

/-- The trace-correspondence root exposes the certificate ledger of a witness built from a ledger derivation. -/
theorem TraceCorQ.relationWitness_ofLedgerDerivation_certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).certificateLedger =
      ledger.certificateLedger :=
  TraceCorQRelationWitness.ofLedgerDerivation_certificateLedger
    ledger
    derivation

/-- The trace-correspondence root exposes the imported count of a witness built from a ledger derivation. -/
theorem TraceCorQ.relationWitness_ofLedgerDerivation_importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).importedRectangleCount =
      ledger.importedRectangleCount :=
  TraceCorQRelationWitness.ofLedgerDerivation_importedRectangleCount
    ledger
    derivation

/-- The trace-correspondence root exposes the imported rectangles of a witness built from a ledger derivation. -/
theorem TraceCorQ.relationWitness_ofLedgerDerivation_importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).importedRectangles =
      ledger.importedRectangles :=
  TraceCorQRelationWitness.ofLedgerDerivation_importedRectangles
    ledger
    derivation

/-- The trace-correspondence root exposes the bookkeeping count of a witness built from a ledger derivation. -/
theorem TraceCorQ.relationWitness_ofLedgerDerivation_traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  TraceCorQRelationWitness.ofLedgerDerivation_traceBookkeepingCount
    ledger
    derivation

/-- The trace-correspondence root exposes the rewrite-step count of a witness built from a ledger derivation. -/
theorem TraceCorQ.relationWitness_ofLedgerDerivation_rewriteStepCount
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).rewriteStepCount =
      ledger.rewriteStepCount :=
  TraceCorQRelationWitness.ofLedgerDerivation_rewriteStepCount
    ledger
    derivation

/-- The trace-correspondence root exposes the empty certificate ledger of a reflexive witness. -/
theorem TraceCorQ.relationWitness_refl_certificateLedger
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationWitness.refl_certificateLedger candidate

/-- The trace-correspondence root exposes the zero imported count of a reflexive witness. -/
theorem TraceCorQ.relationWitness_refl_importedRectangleCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).importedRectangleCount =
      0 :=
  TraceCorQRelationWitness.refl_importedRectangleCount candidate

/-- The trace-correspondence root exposes the empty imported rectangle list of a reflexive witness. -/
theorem TraceCorQ.relationWitness_refl_importedRectangles
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).importedRectangles =
      [] :=
  TraceCorQRelationWitness.refl_importedRectangles candidate

/-- The trace-correspondence root exposes the zero bookkeeping count of a reflexive witness. -/
theorem TraceCorQ.relationWitness_refl_traceBookkeepingCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).traceBookkeepingCount =
      0 :=
  TraceCorQRelationWitness.refl_traceBookkeepingCount candidate

/-- The trace-correspondence root exposes the zero rewrite-step count of a reflexive witness. -/
theorem TraceCorQ.relationWitness_refl_rewriteStepCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).rewriteStepCount =
      0 :=
  TraceCorQRelationWitness.refl_rewriteStepCount candidate

/-- The trace-correspondence root exposes preservation of certificate ledgers under symmetry. -/
theorem TraceCorQ.relationWitness_symm_certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).certificateLedger =
      witness.certificateLedger :=
  TraceCorQRelationWitness.symm_certificateLedger witness

/-- The trace-correspondence root exposes preservation of imported counts under symmetry. -/
theorem TraceCorQ.relationWitness_symm_importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).importedRectangleCount =
      witness.importedRectangleCount :=
  TraceCorQRelationWitness.symm_importedRectangleCount witness

/-- The trace-correspondence root exposes preservation of imported rectangles under symmetry. -/
theorem TraceCorQ.relationWitness_symm_importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).importedRectangles =
      witness.importedRectangles :=
  TraceCorQRelationWitness.symm_importedRectangles witness

/-- The trace-correspondence root exposes preservation of bookkeeping counts under symmetry. -/
theorem TraceCorQ.relationWitness_symm_traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).traceBookkeepingCount =
      witness.traceBookkeepingCount :=
  TraceCorQRelationWitness.symm_traceBookkeepingCount witness

/-- The trace-correspondence root exposes preservation of rewrite-step counts under symmetry. -/
theorem TraceCorQ.relationWitness_symm_rewriteStepCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).rewriteStepCount =
      witness.rewriteStepCount :=
  TraceCorQRelationWitness.symm_rewriteStepCount witness

/-- The trace-correspondence root exposes append of certificate ledgers under transitivity. -/
theorem TraceCorQ.relationWitness_trans_certificateLedger
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).certificateLedger =
      ResidueChannelCertificateLedger.append
        first.certificateLedger
        second.certificateLedger :=
  TraceCorQRelationWitness.trans_certificateLedger first second

/-- The trace-correspondence root exposes addition of imported counts under transitivity. -/
theorem TraceCorQ.relationWitness_trans_importedRectangleCount
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).importedRectangleCount =
      first.importedRectangleCount +
        second.importedRectangleCount :=
  TraceCorQRelationWitness.trans_importedRectangleCount first second

/-- The trace-correspondence root exposes concatenation of imported rectangles under transitivity. -/
theorem TraceCorQ.relationWitness_trans_importedRectangles
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).importedRectangles =
      first.importedRectangles ++
        second.importedRectangles :=
  TraceCorQRelationWitness.trans_importedRectangles first second

/-- The trace-correspondence root exposes addition of bookkeeping counts under transitivity. -/
theorem TraceCorQ.relationWitness_trans_traceBookkeepingCount
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).traceBookkeepingCount =
      first.traceBookkeepingCount +
        second.traceBookkeepingCount :=
  TraceCorQRelationWitness.trans_traceBookkeepingCount first second

/-- The trace-correspondence root exposes addition of rewrite-step counts under transitivity. -/
theorem TraceCorQ.relationWitness_trans_rewriteStepCount
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).rewriteStepCount =
      first.rewriteStepCount +
        second.rewriteStepCount :=
  TraceCorQRelationWitness.trans_rewriteStepCount first second

end AnalyticMotives
end LFunctions
end Boundary
