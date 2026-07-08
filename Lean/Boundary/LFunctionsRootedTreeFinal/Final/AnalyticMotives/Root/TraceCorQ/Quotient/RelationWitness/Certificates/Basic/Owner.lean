import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Certificates.Basic.Owner

/-!
# Top-root basic relation-witness certificate facts

This file exposes the concrete certificate payload carried by basic
relation-witness constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the analytic certificate ledger carried by a relation witness. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    ResidueChannelCertificateLedger :=
  TraceCorQ.relationWitness_certificateLedger witness

/-- The top root exposes the imported finite-rectangle count of a relation witness. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    Nat :=
  TraceCorQ.relationWitness_importedRectangleCount witness

/-- The top root exposes the imported finite explicit-formula rectangles of a relation witness. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceCorQ.relationWitness_importedRectangles witness

/-- The top root exposes the internal trace-bookkeeping count of a relation witness. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    Nat :=
  TraceCorQ.relationWitness_traceBookkeepingCount witness

/-- The top root exposes the explicit rewrite-step count of a relation witness. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_rewriteStepCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    Nat :=
  TraceCorQ.relationWitness_rewriteStepCount witness

/-- The top root exposes the relation-ledger certificate equality. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_certificateLedger_eq_relationLedger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.certificateLedger =
      witness.ledger.certificateLedger :=
  TraceCorQ.relationWitness_certificateLedger_eq_relationLedger witness

/-- The top root exposes the relation-ledger imported-count equality. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_importedRectangleCount_eq_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangleCount =
      witness.ledger.importedRectangleCount :=
  TraceCorQ.relationWitness_importedRectangleCount_eq_ledger witness

/-- The top root exposes the relation-ledger imported-rectangle equality. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_importedRectangles_eq_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangles =
      witness.ledger.importedRectangles :=
  TraceCorQ.relationWitness_importedRectangles_eq_ledger witness

/-- The top root exposes the imported-count/list-length equality. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_importedRectangleCount_eq_length_importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangleCount =
      witness.importedRectangles.length :=
  TraceCorQ.relationWitness_importedRectangleCount_eq_length_importedRectangles
    witness

/-- The top root exposes the relation-ledger bookkeeping equality. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_traceBookkeepingCount_eq_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.traceBookkeepingCount =
      witness.ledger.traceBookkeepingCount :=
  TraceCorQ.relationWitness_traceBookkeepingCount_eq_ledger witness

/-- The top root exposes the relation-ledger rewrite-step equality. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_rewriteStepCount_eq_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.rewriteStepCount =
      witness.ledger.rewriteStepCount :=
  TraceCorQ.relationWitness_rewriteStepCount_eq_ledger witness

/-- The top root exposes the certificate ledger of a witness built from a ledger derivation. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_ofLedgerDerivation_certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).certificateLedger =
      ledger.certificateLedger :=
  TraceCorQ.relationWitness_ofLedgerDerivation_certificateLedger
    ledger
    derivation

/-- The top root exposes the imported count of a witness built from a ledger derivation. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_ofLedgerDerivation_importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).importedRectangleCount =
      ledger.importedRectangleCount :=
  TraceCorQ.relationWitness_ofLedgerDerivation_importedRectangleCount
    ledger
    derivation

/-- The top root exposes the imported rectangles of a witness built from a ledger derivation. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_ofLedgerDerivation_importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).importedRectangles =
      ledger.importedRectangles :=
  TraceCorQ.relationWitness_ofLedgerDerivation_importedRectangles
    ledger
    derivation

/-- The top root exposes the bookkeeping count of a witness built from a ledger derivation. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_ofLedgerDerivation_traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  TraceCorQ.relationWitness_ofLedgerDerivation_traceBookkeepingCount
    ledger
    derivation

/-- The top root exposes the rewrite-step count of a witness built from a ledger derivation. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_ofLedgerDerivation_rewriteStepCount
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).rewriteStepCount =
      ledger.rewriteStepCount :=
  TraceCorQ.relationWitness_ofLedgerDerivation_rewriteStepCount
    ledger
    derivation

/-- The top root exposes the empty certificate ledger of a reflexive witness. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_refl_certificateLedger
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQ.relationWitness_refl_certificateLedger candidate

/-- The top root exposes the zero imported count of a reflexive witness. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_refl_importedRectangleCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).importedRectangleCount =
      0 :=
  TraceCorQ.relationWitness_refl_importedRectangleCount candidate

/-- The top root exposes the empty imported rectangle list of a reflexive witness. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_refl_importedRectangles
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).importedRectangles =
      [] :=
  TraceCorQ.relationWitness_refl_importedRectangles candidate

/-- The top root exposes the zero bookkeeping count of a reflexive witness. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_refl_traceBookkeepingCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).traceBookkeepingCount =
      0 :=
  TraceCorQ.relationWitness_refl_traceBookkeepingCount candidate

/-- The top root exposes the zero rewrite-step count of a reflexive witness. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_refl_rewriteStepCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).rewriteStepCount =
      0 :=
  TraceCorQ.relationWitness_refl_rewriteStepCount candidate

/-- The top root exposes preservation of certificate ledgers under symmetry. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_symm_certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).certificateLedger =
      witness.certificateLedger :=
  TraceCorQ.relationWitness_symm_certificateLedger witness

/-- The top root exposes preservation of imported counts under symmetry. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_symm_importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).importedRectangleCount =
      witness.importedRectangleCount :=
  TraceCorQ.relationWitness_symm_importedRectangleCount witness

/-- The top root exposes preservation of imported rectangles under symmetry. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_symm_importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).importedRectangles =
      witness.importedRectangles :=
  TraceCorQ.relationWitness_symm_importedRectangles witness

/-- The top root exposes preservation of bookkeeping counts under symmetry. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_symm_traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).traceBookkeepingCount =
      witness.traceBookkeepingCount :=
  TraceCorQ.relationWitness_symm_traceBookkeepingCount witness

/-- The top root exposes preservation of rewrite-step counts under symmetry. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_symm_rewriteStepCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).rewriteStepCount =
      witness.rewriteStepCount :=
  TraceCorQ.relationWitness_symm_rewriteStepCount witness

/-- The top root exposes append of certificate ledgers under transitivity. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_trans_certificateLedger
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).certificateLedger =
      ResidueChannelCertificateLedger.append
        first.certificateLedger
        second.certificateLedger :=
  TraceCorQ.relationWitness_trans_certificateLedger first second

/-- The top root exposes addition of imported counts under transitivity. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_trans_importedRectangleCount
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).importedRectangleCount =
      first.importedRectangleCount +
        second.importedRectangleCount :=
  TraceCorQ.relationWitness_trans_importedRectangleCount first second

/-- The top root exposes concatenation of imported rectangles under transitivity. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_trans_importedRectangles
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).importedRectangles =
      first.importedRectangles ++
        second.importedRectangles :=
  TraceCorQ.relationWitness_trans_importedRectangles first second

/-- The top root exposes addition of bookkeeping counts under transitivity. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_trans_traceBookkeepingCount
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).traceBookkeepingCount =
      first.traceBookkeepingCount +
        second.traceBookkeepingCount :=
  TraceCorQ.relationWitness_trans_traceBookkeepingCount first second

/-- The top root exposes addition of rewrite-step counts under transitivity. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_trans_rewriteStepCount
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).rewriteStepCount =
      first.rewriteStepCount +
        second.rewriteStepCount :=
  TraceCorQ.relationWitness_trans_rewriteStepCount first second

end AnalyticMotives
end LFunctions
end Boundary
