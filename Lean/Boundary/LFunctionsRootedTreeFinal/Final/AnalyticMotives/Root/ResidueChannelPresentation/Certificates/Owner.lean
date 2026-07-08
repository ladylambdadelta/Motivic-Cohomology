import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.ResidueChannelPresentation.Certificates.AnalyticPayload.Owner

/-!
# Top-root residue-channel certificate ledgers

This file exposes the finite analytic certificate ledgers attached to
residue-channel presentations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the empty analytic certificate ledger. -/
def AnalyticMotivesRoot.residueChannelCertificateLedger_empty :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.empty

/-- The top root exposes certificate-ledger cons. -/
def AnalyticMotivesRoot.residueChannelCertificateLedger_cons
    (atom : ResidueChannelCertificateAtom)
    (ledger : ResidueChannelCertificateLedger) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.cons atom ledger

/-- The top root exposes singleton analytic certificate ledgers. -/
def AnalyticMotivesRoot.residueChannelCertificateLedger_singleton
    (atom : ResidueChannelCertificateAtom) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.singleton atom

/-- The top root exposes rewrite-path certificate ledgers. -/
def AnalyticMotivesRoot.residueChannelCertificateLedger_ofRewritePath
    (path : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofRewritePath path

/-- The top root exposes certified-coherence-cell certificate ledgers. -/
def AnalyticMotivesRoot.residueChannelCertificateLedger_ofCertifiedCoherenceCell
    (cell : TraceCoherenceCell) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell cell

/-- The top root exposes finite explicit-formula rectangle certificate ledgers. -/
def AnalyticMotivesRoot.residueChannelCertificateLedger_ofExplicitFormulaRectangle
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofExplicitFormulaRectangle rectangle

/-- The top root exposes certificate-ledger append. -/
def AnalyticMotivesRoot.residueChannelCertificateLedger_append
    (first second : ResidueChannelCertificateLedger) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.append first second

/-- The top root exposes left-empty certificate-ledger append. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_empty_append
    (ledger : ResidueChannelCertificateLedger) :
    ResidueChannelCertificateLedger.append
      ResidueChannelCertificateLedger.empty
      ledger =
      ledger :=
  ResidueChannelCertificateLedger.empty_append ledger

/-- The top root exposes certificate-ledger cons as list cons. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_cons_eq_cons
    (atom : ResidueChannelCertificateAtom)
    (ledger : ResidueChannelCertificateLedger) :
    ResidueChannelCertificateLedger.cons atom ledger =
      atom :: ledger :=
  ResidueChannelCertificateLedger.cons_eq_cons atom ledger

/-- The top root exposes singleton ledgers as cons over the empty ledger. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_singleton_eq_cons_empty
    (atom : ResidueChannelCertificateAtom) :
    ResidueChannelCertificateLedger.singleton atom =
      ResidueChannelCertificateLedger.cons
        atom
        ResidueChannelCertificateLedger.empty :=
  ResidueChannelCertificateLedger.singleton_eq_cons_empty atom

/-- The top root exposes rewrite-path ledgers as singletons. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_ofRewritePath_eq_singleton
    (path : TraceRewritePath) :
    ResidueChannelCertificateLedger.ofRewritePath path =
      ResidueChannelCertificateLedger.singleton
        (ResidueChannelCertificateAtom.rewritePath path) :=
  ResidueChannelCertificateLedger.ofRewritePath_eq_singleton path

/-- The top root exposes the source/target/cell layout of a coherence-cell ledger. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_ofCertifiedCoherenceCell_eq_paths_cell
    (cell : TraceCoherenceCell) :
    ResidueChannelCertificateLedger.ofCertifiedCoherenceCell cell =
      ResidueChannelCertificateAtom.rewritePath cell.source ::
        ResidueChannelCertificateAtom.rewritePath cell.target ::
          ResidueChannelCertificateAtom.coherenceCell cell ::
            ResidueChannelCertificateLedger.empty :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_eq_paths_cell
    cell

/-- The top root exposes explicit-formula rectangle ledgers as singletons. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_ofExplicitFormulaRectangle_eq_singleton
    (rectangle :
      ZetaAdmissibleFunction.ExplicitFormulaRectangle) :
    ResidueChannelCertificateLedger.ofExplicitFormulaRectangle rectangle =
      ResidueChannelCertificateLedger.singleton
        (ResidueChannelCertificateAtom.explicitFormulaRectangle rectangle) :=
  ResidueChannelCertificateLedger.ofExplicitFormulaRectangle_eq_singleton
    rectangle

/-- The top root exposes certificate-ledger append as list append. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_append_eq_append
    (first second : ResidueChannelCertificateLedger) :
    ResidueChannelCertificateLedger.append first second =
      first ++ second :=
  ResidueChannelCertificateLedger.append_eq_append first second

/-- The top root exposes right-empty certificate-ledger append. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_append_empty
    (ledger : ResidueChannelCertificateLedger) :
    ResidueChannelCertificateLedger.append
      ledger
      ResidueChannelCertificateLedger.empty =
      ledger :=
  ResidueChannelCertificateLedger.append_empty ledger

/-- The top root exposes associativity of certificate-ledger append. -/
theorem AnalyticMotivesRoot.residueChannelCertificateLedger_append_assoc
    (first second third : ResidueChannelCertificateLedger) :
    ResidueChannelCertificateLedger.append
      (ResidueChannelCertificateLedger.append first second)
      third =
      ResidueChannelCertificateLedger.append
        first
        (ResidueChannelCertificateLedger.append second third) :=
  ResidueChannelCertificateLedger.append_assoc first second third

/-- The top root exposes the certificate root's empty ledger theorem. -/
theorem AnalyticMotivesRoot.residueChannelCertificate_empty_eq_nil :
    ResidueChannelCertificateLedger.empty = [] :=
  ResidueChannelCertificate.empty_eq_nil

/-- The top root exposes the certificate root's singleton theorem. -/
theorem AnalyticMotivesRoot.residueChannelCertificate_singleton_eq_cons_empty
    (atom : ResidueChannelCertificateAtom) :
    ResidueChannelCertificateLedger.singleton atom =
      ResidueChannelCertificateLedger.cons
        atom
        ResidueChannelCertificateLedger.empty :=
  ResidueChannelCertificate.singleton_eq_cons_empty atom

/-- The top root exposes the certificate root's rewrite-path theorem. -/
theorem AnalyticMotivesRoot.residueChannelCertificate_ofRewritePath_eq_singleton
    (path : TraceRewritePath) :
    ResidueChannelCertificateLedger.ofRewritePath path =
      ResidueChannelCertificateLedger.singleton
        (ResidueChannelCertificateAtom.rewritePath path) :=
  ResidueChannelCertificate.ofRewritePath_eq_singleton path

/-- The top root exposes the certificate root's append associativity theorem. -/
theorem AnalyticMotivesRoot.residueChannelCertificate_append_assoc
    (first second third : ResidueChannelCertificateLedger) :
    ResidueChannelCertificateLedger.append
      (ResidueChannelCertificateLedger.append first second)
      third =
      ResidueChannelCertificateLedger.append
        first
        (ResidueChannelCertificateLedger.append second third) :=
  ResidueChannelCertificate.append_assoc first second third

end AnalyticMotives
end LFunctions
end Boundary
