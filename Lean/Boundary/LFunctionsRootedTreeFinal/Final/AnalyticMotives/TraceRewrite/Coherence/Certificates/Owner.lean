import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.AnalyticPayload.Owner

/-!
# Certificate ledgers for named coherence cells

This file records the certificate ledgers attached to the named higher
coherence cells of the trace computad.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The certificate ledger attached to a Fubini coherence cell. -/
def TraceCoherenceCell.fubiniCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
    (TraceCoherenceCell.fubini source target)

/-- The certificate ledger attached to a schedule-exchange coherence cell. -/
def TraceCoherenceCell.scheduleExchangeCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
    (TraceCoherenceCell.scheduleExchange source target)

/-- The certificate ledger attached to a residue-channel coherence cell. -/
def TraceCoherenceCell.residueChannelCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
    (TraceCoherenceCell.residueChannel source target)

/-- The certificate ledger attached to a Stokes-residue coherence cell. -/
def TraceCoherenceCell.stokesResidueCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
    (TraceCoherenceCell.stokesResidue source target)

/-- The certificate ledger attached to a refinement coherence cell. -/
def TraceCoherenceCell.refinementCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
    (TraceCoherenceCell.refinement source target)

/-- The certificate ledger attached to an associativity coherence cell. -/
def TraceCoherenceCell.associativityCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
    (TraceCoherenceCell.associativity source target)

/-- The certificate ledger attached to a left-identity coherence cell. -/
def TraceCoherenceCell.leftIdentityCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
    (TraceCoherenceCell.leftIdentity source target)

/-- The certificate ledger attached to a right-identity coherence cell. -/
def TraceCoherenceCell.rightIdentityCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
    (TraceCoherenceCell.rightIdentity source target)

/-- A Fubini coherence certificate ledger counts the compared source and target paths. -/
theorem TraceCoherenceCell.fubiniCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.fubiniCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

/-- A schedule-exchange coherence certificate ledger counts the compared paths. -/
theorem TraceCoherenceCell.scheduleExchangeCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.scheduleExchangeCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

/-- A residue-channel coherence certificate ledger counts the compared paths. -/
theorem TraceCoherenceCell.residueChannelCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.residueChannelCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

/-- A Stokes-residue coherence certificate ledger counts the compared paths. -/
theorem TraceCoherenceCell.stokesResidueCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.stokesResidueCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

/-- A refinement coherence certificate ledger counts the compared paths. -/
theorem TraceCoherenceCell.refinementCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.refinementCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

/-- An associativity coherence certificate ledger counts the compared paths. -/
theorem TraceCoherenceCell.associativityCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.associativityCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

/-- A left-identity coherence certificate ledger counts the compared paths. -/
theorem TraceCoherenceCell.leftIdentityCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.leftIdentityCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

/-- A right-identity coherence certificate ledger counts the compared paths. -/
theorem TraceCoherenceCell.rightIdentityCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.rightIdentityCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
