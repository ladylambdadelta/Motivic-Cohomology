import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Coherence.Certificates.Owner

/-!
# Shape facts for named coherence certificate ledgers

This file records that each named coherence certificate ledger consists of the
source rewrite path, target rewrite path, and the named coherence cell.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini coherence certificate ledger records source path, target path, and Fubini cell. -/
theorem TraceCoherenceCell.fubiniCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    TraceCoherenceCell.fubiniCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.fubini source target) ::
            ResidueChannelCertificateLedger.empty :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_eq_paths_cell
    (TraceCoherenceCell.fubini source target)

/-- A schedule-exchange certificate ledger records source path, target path, and cell. -/
theorem TraceCoherenceCell.scheduleExchangeCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    TraceCoherenceCell.scheduleExchangeCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.scheduleExchange source target) ::
            ResidueChannelCertificateLedger.empty :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_eq_paths_cell
    (TraceCoherenceCell.scheduleExchange source target)

/-- A residue-channel certificate ledger records source path, target path, and cell. -/
theorem TraceCoherenceCell.residueChannelCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    TraceCoherenceCell.residueChannelCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.residueChannel source target) ::
            ResidueChannelCertificateLedger.empty :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_eq_paths_cell
    (TraceCoherenceCell.residueChannel source target)

/-- A Stokes-residue certificate ledger records source path, target path, and cell. -/
theorem TraceCoherenceCell.stokesResidueCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    TraceCoherenceCell.stokesResidueCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.stokesResidue source target) ::
            ResidueChannelCertificateLedger.empty :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_eq_paths_cell
    (TraceCoherenceCell.stokesResidue source target)

/-- A refinement certificate ledger records source path, target path, and cell. -/
theorem TraceCoherenceCell.refinementCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    TraceCoherenceCell.refinementCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.refinement source target) ::
            ResidueChannelCertificateLedger.empty :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_eq_paths_cell
    (TraceCoherenceCell.refinement source target)

/-- An associativity certificate ledger records source path, target path, and cell. -/
theorem TraceCoherenceCell.associativityCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    TraceCoherenceCell.associativityCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.associativity source target) ::
            ResidueChannelCertificateLedger.empty :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_eq_paths_cell
    (TraceCoherenceCell.associativity source target)

/-- A left-identity certificate ledger records source path, target path, and cell. -/
theorem TraceCoherenceCell.leftIdentityCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    TraceCoherenceCell.leftIdentityCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.leftIdentity source target) ::
            ResidueChannelCertificateLedger.empty :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_eq_paths_cell
    (TraceCoherenceCell.leftIdentity source target)

/-- A right-identity certificate ledger records source path, target path, and cell. -/
theorem TraceCoherenceCell.rightIdentityCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    TraceCoherenceCell.rightIdentityCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.rightIdentity source target) ::
            ResidueChannelCertificateLedger.empty :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell_eq_paths_cell
    (TraceCoherenceCell.rightIdentity source target)

end AnalyticMotives
end LFunctions
end Boundary
