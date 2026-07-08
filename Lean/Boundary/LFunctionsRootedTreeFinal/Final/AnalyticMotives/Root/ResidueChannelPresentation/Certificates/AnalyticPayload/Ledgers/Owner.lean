import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.AnalyticPayload.Owner

/-!
# Top-root analytic payload of certificate ledgers

This file exposes folded imported-rectangle and trace-calculus payload
accounting for residue-channel certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes imported rectangle counts for certificate ledgers. -/
def AnalyticMotivesRoot.residueChannelCertificateLedger_importedRectangleCount
    (ledger : ResidueChannelCertificateLedger) :
    Nat :=
  ResidueChannelCertificateLedger.importedRectangleCount ledger

/-- The top root exposes trace-bookkeeping counts for certificate ledgers. -/
def AnalyticMotivesRoot.residueChannelCertificateLedger_traceBookkeepingCount
    (ledger : ResidueChannelCertificateLedger) :
    Nat :=
  ResidueChannelCertificateLedger.traceBookkeepingCount ledger

/-- The top root exposes rewrite-step counts for certificate ledgers. -/
def AnalyticMotivesRoot.residueChannelCertificateLedger_rewriteStepCount
    (ledger : ResidueChannelCertificateLedger) :
    Nat :=
  ResidueChannelCertificateLedger.rewriteStepCount ledger

/-- The top root exposes imported rectangles for certificate ledgers. -/
def AnalyticMotivesRoot.residueChannelCertificateLedger_importedRectangles
    (ledger : ResidueChannelCertificateLedger) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  ResidueChannelCertificateLedger.importedRectangles ledger

/-- The top root exposes empty-ledger imported rectangle counts. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_empty_importedRectangleCount :
    ResidueChannelCertificateLedger.empty.importedRectangleCount =
      0 :=
  ResidueChannelCertificateLedger.empty_importedRectangleCount

/-- The top root exposes empty-ledger imported rectangle lists. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_empty_importedRectangles :
    ResidueChannelCertificateLedger.empty.importedRectangles =
      [] :=
  ResidueChannelCertificateLedger.empty_importedRectangles

/-- The top root exposes empty-ledger bookkeeping counts. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_empty_traceBookkeepingCount :
    ResidueChannelCertificateLedger.empty.traceBookkeepingCount =
      0 :=
  ResidueChannelCertificateLedger.empty_traceBookkeepingCount

/-- The top root exposes empty-ledger rewrite-step counts. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_empty_rewriteStepCount :
    ResidueChannelCertificateLedger.empty.rewriteStepCount =
      0 :=
  ResidueChannelCertificateLedger.empty_rewriteStepCount

/-- The top root exposes cons imported rectangle counts. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_cons_importedRectangleCount
    (atom : ResidueChannelCertificateAtom)
    (ledger : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.cons
      atom
      ledger).importedRectangleCount =
      atom.importedRectangleCount +
        ledger.importedRectangleCount :=
  ResidueChannelCertificateLedger.cons_importedRectangleCount atom ledger

/-- The top root exposes cons imported rectangle lists. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_cons_importedRectangles
    (atom : ResidueChannelCertificateAtom)
    (ledger : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.cons
      atom
      ledger).importedRectangles =
      atom.importedRectangles ++
        ledger.importedRectangles :=
  ResidueChannelCertificateLedger.cons_importedRectangles atom ledger

/-- The top root exposes cons bookkeeping counts. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_cons_traceBookkeepingCount
    (atom : ResidueChannelCertificateAtom)
    (ledger : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.cons
      atom
      ledger).traceBookkeepingCount =
      atom.traceBookkeepingCount +
        ledger.traceBookkeepingCount :=
  ResidueChannelCertificateLedger.cons_traceBookkeepingCount atom ledger

/-- The top root exposes cons rewrite-step counts. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_cons_rewriteStepCount
    (atom : ResidueChannelCertificateAtom)
    (ledger : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.cons
      atom
      ledger).rewriteStepCount =
      atom.rewriteStepCount +
        ledger.rewriteStepCount :=
  ResidueChannelCertificateLedger.cons_rewriteStepCount atom ledger

/-- The top root exposes append imported rectangle counts. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_append_importedRectangleCount
    (first second : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.append
      first
      second).importedRectangleCount =
      first.importedRectangleCount +
        second.importedRectangleCount :=
  ResidueChannelCertificateLedger.append_importedRectangleCount first second

/-- The top root exposes append imported rectangle lists. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_append_importedRectangles
    (first second : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.append
      first
      second).importedRectangles =
      first.importedRectangles ++
        second.importedRectangles :=
  ResidueChannelCertificateLedger.append_importedRectangles first second

/-- The top root exposes imported rectangle count as rectangle-list length. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_importedRectangleCount_eq_length_importedRectangles
    (ledger : ResidueChannelCertificateLedger) :
    ledger.importedRectangleCount =
      ledger.importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    ledger

/-- The top root exposes append bookkeeping counts. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_append_traceBookkeepingCount
    (first second : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.append
      first
      second).traceBookkeepingCount =
      first.traceBookkeepingCount +
        second.traceBookkeepingCount :=
  ResidueChannelCertificateLedger.append_traceBookkeepingCount first second

/-- The top root exposes append rewrite-step counts. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_append_rewriteStepCount
    (first second : ResidueChannelCertificateLedger) :
    (ResidueChannelCertificateLedger.append
      first
      second).rewriteStepCount =
      first.rewriteStepCount +
        second.rewriteStepCount :=
  ResidueChannelCertificateLedger.append_rewriteStepCount first second

end AnalyticMotives
end LFunctions
end Boundary
