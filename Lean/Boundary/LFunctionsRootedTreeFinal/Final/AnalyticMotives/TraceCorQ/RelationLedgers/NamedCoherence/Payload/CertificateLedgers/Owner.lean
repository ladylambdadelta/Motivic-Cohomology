import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.NamedCoherence.Owner

/-!
# Certificate ledgers for named coherence relation ledgers

This file records certificate-ledger payloads carried by the singleton relation
ledgers generated from named coherence cells.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini relation ledger carries the Fubini coherence certificate ledger. -/
theorem TraceCorQRelationLedger.fubini_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.fubini
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCoherenceCell.fubiniCertificateLedger source target)
        ResidueChannelCertificateLedger.empty :=
  rfl

/-- A schedule-exchange relation ledger carries the schedule-exchange certificate ledger. -/
theorem TraceCorQRelationLedger.scheduleExchange_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.scheduleExchange
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCoherenceCell.scheduleExchangeCertificateLedger source target)
        ResidueChannelCertificateLedger.empty :=
  rfl

/-- A residue-channel relation ledger carries the residue-channel certificate ledger. -/
theorem TraceCorQRelationLedger.residueChannel_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.residueChannel
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCoherenceCell.residueChannelCertificateLedger source target)
        ResidueChannelCertificateLedger.empty :=
  rfl

/-- A Stokes-residue relation ledger carries the Stokes-residue certificate ledger. -/
theorem TraceCorQRelationLedger.stokesResidue_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.stokesResidue
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCoherenceCell.stokesResidueCertificateLedger source target)
        ResidueChannelCertificateLedger.empty :=
  rfl

/-- A refinement relation ledger carries the refinement certificate ledger. -/
theorem TraceCorQRelationLedger.refinement_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.refinement
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCoherenceCell.refinementCertificateLedger source target)
        ResidueChannelCertificateLedger.empty :=
  rfl

/-- An associativity relation ledger carries the associativity certificate ledger. -/
theorem TraceCorQRelationLedger.associativity_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.associativity
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCoherenceCell.associativityCertificateLedger source target)
        ResidueChannelCertificateLedger.empty :=
  rfl

/-- A left-identity relation ledger carries the left-identity certificate ledger. -/
theorem TraceCorQRelationLedger.leftIdentity_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.leftIdentity
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCoherenceCell.leftIdentityCertificateLedger source target)
        ResidueChannelCertificateLedger.empty :=
  rfl

/-- A right-identity relation ledger carries the right-identity certificate ledger. -/
theorem TraceCorQRelationLedger.rightIdentity_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.rightIdentity
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCoherenceCell.rightIdentityCertificateLedger source target)
        ResidueChannelCertificateLedger.empty :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
