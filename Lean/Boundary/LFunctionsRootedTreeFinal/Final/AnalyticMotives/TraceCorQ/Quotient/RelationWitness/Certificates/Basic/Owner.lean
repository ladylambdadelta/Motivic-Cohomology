import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Owner

/-!
# Basic certificate ledgers for relation witnesses

This file records the analytic certificates carried by concrete quotient
relation witnesses under the basic constructors: ledger derivation, reflexivity,
symmetry, and transitivity.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic certificate ledger carried by a concrete relation witness. -/
def TraceCorQRelationWitness.certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    ResidueChannelCertificateLedger :=
  witness.ledger.certificateLedger

/-- The imported finite-rectangle payload carried by a concrete relation witness. -/
def TraceCorQRelationWitness.importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    Nat :=
  witness.certificateLedger.importedRectangleCount

/-- The imported finite explicit-formula rectangles carried by a concrete relation witness. -/
def TraceCorQRelationWitness.importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  witness.certificateLedger.importedRectangles

/-- The internal trace-bookkeeping payload carried by a concrete relation witness. -/
def TraceCorQRelationWitness.traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    Nat :=
  witness.certificateLedger.traceBookkeepingCount

/-- The explicit rewrite-step payload carried by a concrete relation witness. -/
def TraceCorQRelationWitness.rewriteStepCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    Nat :=
  witness.certificateLedger.rewriteStepCount

/-- A relation witness carries exactly the certificate ledger of its relation ledger. -/
theorem TraceCorQRelationWitness.certificateLedger_eq_relationLedger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.certificateLedger =
      witness.ledger.certificateLedger :=
  rfl

/-- A relation witness imports exactly the finite-rectangle payload of its relation ledger. -/
theorem TraceCorQRelationWitness.importedRectangleCount_eq_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangleCount =
      witness.ledger.importedRectangleCount :=
  rfl

/-- A relation witness exposes exactly the imported rectangles of its relation ledger. -/
theorem TraceCorQRelationWitness.importedRectangles_eq_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangles =
      witness.ledger.importedRectangles :=
  rfl

/-- A relation witness's imported-rectangle count is the length of its rectangle list. -/
theorem TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangleCount =
      witness.importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    witness.certificateLedger

/-- A relation witness keeps exactly the bookkeeping payload of its relation ledger. -/
theorem TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.traceBookkeepingCount =
      witness.ledger.traceBookkeepingCount :=
  rfl

/-- A relation witness keeps exactly the rewrite-step payload of its relation ledger. -/
theorem TraceCorQRelationWitness.rewriteStepCount_eq_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.rewriteStepCount =
      witness.ledger.rewriteStepCount :=
  rfl

/-- A witness built from a ledger carries that ledger's certificates. -/
theorem TraceCorQRelationWitness.ofLedgerDerivation_certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).certificateLedger =
      ledger.certificateLedger :=
  TraceCorQRelationWitness.certificateLedger_eq_relationLedger
    (TraceCorQRelationWitness.ofLedgerDerivation ledger derivation)

/-- A witness built from a ledger carries that ledger's imported payload. -/
theorem TraceCorQRelationWitness.ofLedgerDerivation_importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).importedRectangleCount =
      ledger.importedRectangleCount :=
  TraceCorQRelationWitness.importedRectangleCount_eq_ledger
    (TraceCorQRelationWitness.ofLedgerDerivation ledger derivation)

/-- A witness built from a ledger exposes that ledger's imported rectangles. -/
theorem TraceCorQRelationWitness.ofLedgerDerivation_importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).importedRectangles =
      ledger.importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_ledger
    (TraceCorQRelationWitness.ofLedgerDerivation ledger derivation)

/-- A witness built from a ledger carries that ledger's bookkeeping payload. -/
theorem TraceCorQRelationWitness.ofLedgerDerivation_traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger
    (TraceCorQRelationWitness.ofLedgerDerivation ledger derivation)

/-- A witness built from a ledger carries that ledger's rewrite-step payload. -/
theorem TraceCorQRelationWitness.ofLedgerDerivation_rewriteStepCount
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).rewriteStepCount =
      ledger.rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_ledger
    (TraceCorQRelationWitness.ofLedgerDerivation ledger derivation)

/-- Reflexive witnesses carry the empty certificate ledger. -/
theorem TraceCorQRelationWitness.refl_certificateLedger
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationLedger.empty_certificateLedger

/-- Reflexive witnesses carry no imported finite-rectangle payload. -/
theorem TraceCorQRelationWitness.refl_importedRectangleCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).importedRectangleCount =
      0 :=
  TraceCorQRelationLedger.empty_importedRectangleCount

/-- Reflexive witnesses expose no imported finite explicit-formula rectangles. -/
theorem TraceCorQRelationWitness.refl_importedRectangles
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).importedRectangles =
      [] :=
  TraceCorQRelationLedger.empty_importedRectangles

/-- Reflexive witnesses carry no internal trace-bookkeeping payload. -/
theorem TraceCorQRelationWitness.refl_traceBookkeepingCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).traceBookkeepingCount =
      0 :=
  TraceCorQRelationLedger.empty_traceBookkeepingCount

/-- Reflexive witnesses carry no explicit rewrite-step payload. -/
theorem TraceCorQRelationWitness.refl_rewriteStepCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).rewriteStepCount =
      0 :=
  TraceCorQRelationLedger.empty_rewriteStepCount

/-- Symmetry preserves witness certificate ledgers. -/
theorem TraceCorQRelationWitness.symm_certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).certificateLedger =
      witness.certificateLedger :=
  rfl

/-- Symmetry preserves witness imported finite-rectangle payload. -/
theorem TraceCorQRelationWitness.symm_importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).importedRectangleCount =
      witness.importedRectangleCount :=
  rfl

/-- Symmetry preserves witness imported finite explicit-formula rectangles. -/
theorem TraceCorQRelationWitness.symm_importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).importedRectangles =
      witness.importedRectangles :=
  rfl

/-- Symmetry preserves witness internal trace-bookkeeping payload. -/
theorem TraceCorQRelationWitness.symm_traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).traceBookkeepingCount =
      witness.traceBookkeepingCount :=
  rfl

/-- Symmetry preserves witness explicit rewrite-step payload. -/
theorem TraceCorQRelationWitness.symm_rewriteStepCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).rewriteStepCount =
      witness.rewriteStepCount :=
  rfl

/-- Transitivity appends witness certificate ledgers. -/
theorem TraceCorQRelationWitness.trans_certificateLedger
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).certificateLedger =
      ResidueChannelCertificateLedger.append
        first.certificateLedger
        second.certificateLedger :=
  Eq.trans
    (congrArg
      TraceCorQRelationLedger.certificateLedger
      (TraceCorQRelationWitness.trans_ledger first second))
    (TraceCorQRelationLedger.append_certificateLedger
      first.ledger
      second.ledger)

/-- Transitivity adds witness imported finite-rectangle payload. -/
theorem TraceCorQRelationWitness.trans_importedRectangleCount
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).importedRectangleCount =
      first.importedRectangleCount +
        second.importedRectangleCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangleCount
      (TraceCorQRelationWitness.trans_certificateLedger first second))
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      first.certificateLedger
      second.certificateLedger)

/-- Transitivity concatenates witness imported finite explicit-formula rectangles. -/
theorem TraceCorQRelationWitness.trans_importedRectangles
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).importedRectangles =
      first.importedRectangles ++
        second.importedRectangles :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangles
      (TraceCorQRelationWitness.trans_certificateLedger first second))
    (ResidueChannelCertificateLedger.append_importedRectangles
      first.certificateLedger
      second.certificateLedger)

/-- Transitivity adds witness internal trace-bookkeeping payload. -/
theorem TraceCorQRelationWitness.trans_traceBookkeepingCount
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).traceBookkeepingCount =
      first.traceBookkeepingCount +
        second.traceBookkeepingCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.traceBookkeepingCount
      (TraceCorQRelationWitness.trans_certificateLedger first second))
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      first.certificateLedger
      second.certificateLedger)

/-- Transitivity adds witness explicit rewrite-step payload. -/
theorem TraceCorQRelationWitness.trans_rewriteStepCount
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).rewriteStepCount =
      first.rewriteStepCount +
        second.rewriteStepCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.rewriteStepCount
      (TraceCorQRelationWitness.trans_certificateLedger first second))
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      first.certificateLedger
      second.certificateLedger)

end AnalyticMotives
end LFunctions
end Boundary
