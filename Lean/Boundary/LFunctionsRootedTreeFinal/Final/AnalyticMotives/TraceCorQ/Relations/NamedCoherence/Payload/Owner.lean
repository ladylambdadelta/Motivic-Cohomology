import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Relations.NamedCoherence.Owner

/-!
# Named coherence relation payloads

This file exposes the analytic certificate payload carried by named coherence
relation generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini relation generator has the imported-rectangle count of its coherence ledger. -/
theorem TraceCorQRelationGenerator.fubini_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubini
      source
      target
      support).importedRectangleCount =
      (TraceCoherenceCell.fubiniCertificateLedger
        source
        target).importedRectangleCount :=
  rfl

/-- A Fubini relation generator exposes the imported rectangles of its coherence ledger. -/
theorem TraceCorQRelationGenerator.fubini_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubini
      source
      target
      support).importedRectangles =
      (TraceCoherenceCell.fubiniCertificateLedger
        source
        target).importedRectangles :=
  rfl

/-- A Fubini relation generator has the bookkeeping count of its coherence ledger. -/
theorem TraceCorQRelationGenerator.fubini_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubini
      source
      target
      support).traceBookkeepingCount =
      (TraceCoherenceCell.fubiniCertificateLedger
        source
        target).traceBookkeepingCount :=
  rfl

/-- A schedule-exchange relation generator has the imported-rectangle count of its ledger. -/
theorem TraceCorQRelationGenerator.scheduleExchange_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchange
      source
      target
      support).importedRectangleCount =
      (TraceCoherenceCell.scheduleExchangeCertificateLedger
        source
        target).importedRectangleCount :=
  rfl

/-- A schedule-exchange relation generator exposes the imported rectangles of its ledger. -/
theorem TraceCorQRelationGenerator.scheduleExchange_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchange
      source
      target
      support).importedRectangles =
      (TraceCoherenceCell.scheduleExchangeCertificateLedger
        source
        target).importedRectangles :=
  rfl

/-- A schedule-exchange relation generator has the bookkeeping count of its ledger. -/
theorem TraceCorQRelationGenerator.scheduleExchange_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchange
      source
      target
      support).traceBookkeepingCount =
      (TraceCoherenceCell.scheduleExchangeCertificateLedger
        source
        target).traceBookkeepingCount :=
  rfl

/-- A residue-channel relation generator has the imported-rectangle count of its ledger. -/
theorem TraceCorQRelationGenerator.residueChannel_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannel
      source
      target
      support).importedRectangleCount =
      (TraceCoherenceCell.residueChannelCertificateLedger
        source
        target).importedRectangleCount :=
  rfl

/-- A residue-channel relation generator exposes the imported rectangles of its ledger. -/
theorem TraceCorQRelationGenerator.residueChannel_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannel
      source
      target
      support).importedRectangles =
      (TraceCoherenceCell.residueChannelCertificateLedger
        source
        target).importedRectangles :=
  rfl

/-- A residue-channel relation generator has the bookkeeping count of its ledger. -/
theorem TraceCorQRelationGenerator.residueChannel_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannel
      source
      target
      support).traceBookkeepingCount =
      (TraceCoherenceCell.residueChannelCertificateLedger
        source
        target).traceBookkeepingCount :=
  rfl

/-- A Stokes-residue relation generator has the imported-rectangle count of its ledger. -/
theorem TraceCorQRelationGenerator.stokesResidue_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidue
      source
      target
      support).importedRectangleCount =
      (TraceCoherenceCell.stokesResidueCertificateLedger
        source
        target).importedRectangleCount :=
  rfl

/-- A Stokes-residue relation generator exposes the imported rectangles of its ledger. -/
theorem TraceCorQRelationGenerator.stokesResidue_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidue
      source
      target
      support).importedRectangles =
      (TraceCoherenceCell.stokesResidueCertificateLedger
        source
        target).importedRectangles :=
  rfl

/-- A Stokes-residue relation generator has the bookkeeping count of its ledger. -/
theorem TraceCorQRelationGenerator.stokesResidue_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidue
      source
      target
      support).traceBookkeepingCount =
      (TraceCoherenceCell.stokesResidueCertificateLedger
        source
        target).traceBookkeepingCount :=
  rfl

/-- A refinement relation generator has the imported-rectangle count of its ledger. -/
theorem TraceCorQRelationGenerator.refinement_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinement
      source
      target
      support).importedRectangleCount =
      (TraceCoherenceCell.refinementCertificateLedger
        source
        target).importedRectangleCount :=
  rfl

/-- A refinement relation generator exposes the imported rectangles of its ledger. -/
theorem TraceCorQRelationGenerator.refinement_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinement
      source
      target
      support).importedRectangles =
      (TraceCoherenceCell.refinementCertificateLedger
        source
        target).importedRectangles :=
  rfl

/-- A refinement relation generator has the bookkeeping count of its ledger. -/
theorem TraceCorQRelationGenerator.refinement_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinement
      source
      target
      support).traceBookkeepingCount =
      (TraceCoherenceCell.refinementCertificateLedger
        source
        target).traceBookkeepingCount :=
  rfl

/-- An associativity relation generator has the imported-rectangle count of its ledger. -/
theorem TraceCorQRelationGenerator.associativity_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativity
      source
      target
      support).importedRectangleCount =
      (TraceCoherenceCell.associativityCertificateLedger
        source
        target).importedRectangleCount :=
  rfl

/-- An associativity relation generator exposes the imported rectangles of its ledger. -/
theorem TraceCorQRelationGenerator.associativity_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativity
      source
      target
      support).importedRectangles =
      (TraceCoherenceCell.associativityCertificateLedger
        source
        target).importedRectangles :=
  rfl

/-- An associativity relation generator has the bookkeeping count of its ledger. -/
theorem TraceCorQRelationGenerator.associativity_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativity
      source
      target
      support).traceBookkeepingCount =
      (TraceCoherenceCell.associativityCertificateLedger
        source
        target).traceBookkeepingCount :=
  rfl

/-- A left-identity relation generator has the imported-rectangle count of its ledger. -/
theorem TraceCorQRelationGenerator.leftIdentity_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentity
      source
      target
      support).importedRectangleCount =
      (TraceCoherenceCell.leftIdentityCertificateLedger
        source
        target).importedRectangleCount :=
  rfl

/-- A left-identity relation generator exposes the imported rectangles of its ledger. -/
theorem TraceCorQRelationGenerator.leftIdentity_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentity
      source
      target
      support).importedRectangles =
      (TraceCoherenceCell.leftIdentityCertificateLedger
        source
        target).importedRectangles :=
  rfl

/-- A left-identity relation generator has the bookkeeping count of its ledger. -/
theorem TraceCorQRelationGenerator.leftIdentity_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentity
      source
      target
      support).traceBookkeepingCount =
      (TraceCoherenceCell.leftIdentityCertificateLedger
        source
        target).traceBookkeepingCount :=
  rfl

/-- A right-identity relation generator has the imported-rectangle count of its ledger. -/
theorem TraceCorQRelationGenerator.rightIdentity_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentity
      source
      target
      support).importedRectangleCount =
      (TraceCoherenceCell.rightIdentityCertificateLedger
        source
        target).importedRectangleCount :=
  rfl

/-- A right-identity relation generator exposes the imported rectangles of its ledger. -/
theorem TraceCorQRelationGenerator.rightIdentity_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentity
      source
      target
      support).importedRectangles =
      (TraceCoherenceCell.rightIdentityCertificateLedger
        source
        target).importedRectangles :=
  rfl

/-- A right-identity relation generator has the bookkeeping count of its ledger. -/
theorem TraceCorQRelationGenerator.rightIdentity_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentity
      source
      target
      support).traceBookkeepingCount =
      (TraceCoherenceCell.rightIdentityCertificateLedger
        source
        target).traceBookkeepingCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
