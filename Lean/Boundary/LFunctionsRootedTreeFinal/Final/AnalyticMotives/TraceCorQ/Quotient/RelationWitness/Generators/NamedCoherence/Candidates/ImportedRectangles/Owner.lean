import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.CertificateLedgers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.Projections.Owner

/-!
# Imported-rectangle payload for named-coherence support candidates

This file records the imported finite-rectangle payload carried by named
coherence support candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini support candidate splits imported-rectangle count into support and ledger payload. -/
theorem TraceCorQRelationGenerator.fubiniSupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.fubini source target support).importedRectangleCount :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.fubiniSupportCandidate source target support)

/-- A schedule-exchange support candidate splits imported-rectangle count. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.scheduleExchange source target support).importedRectangleCount :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate source target support)

/-- A residue-channel support candidate splits imported-rectangle count. -/
theorem TraceCorQRelationGenerator.residueChannelSupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.residueChannel source target support).importedRectangleCount :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.residueChannelSupportCandidate source target support)

/-- A Stokes-residue support candidate splits imported-rectangle count. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.stokesResidue source target support).importedRectangleCount :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate source target support)

/-- A refinement support candidate splits imported-rectangle count. -/
theorem TraceCorQRelationGenerator.refinementSupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.refinement source target support).importedRectangleCount :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.refinementSupportCandidate source target support)

/-- An associativity support candidate splits imported-rectangle count. -/
theorem TraceCorQRelationGenerator.associativitySupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.associativity source target support).importedRectangleCount :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.associativitySupportCandidate source target support)

/-- A left-identity support candidate splits imported-rectangle count. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.leftIdentity source target support).importedRectangleCount :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate source target support)

/-- A right-identity support candidate splits imported-rectangle count. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.rightIdentity source target support).importedRectangleCount :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate source target support)

/-- A Fubini support candidate splits imported rectangles into support and ledger rectangles. -/
theorem TraceCorQRelationGenerator.fubiniSupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.fubini source target support).importedRectangles :=
  TraceCorQQuotientCandidate.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.fubiniSupportCandidate source target support)

/-- A schedule-exchange support candidate splits imported rectangles. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.scheduleExchange source target support).importedRectangles :=
  TraceCorQQuotientCandidate.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate source target support)

/-- A residue-channel support candidate splits imported rectangles. -/
theorem TraceCorQRelationGenerator.residueChannelSupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.residueChannel source target support).importedRectangles :=
  TraceCorQQuotientCandidate.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.residueChannelSupportCandidate source target support)

/-- A Stokes-residue support candidate splits imported rectangles. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.stokesResidue source target support).importedRectangles :=
  TraceCorQQuotientCandidate.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate source target support)

/-- A refinement support candidate splits imported rectangles. -/
theorem TraceCorQRelationGenerator.refinementSupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.refinement source target support).importedRectangles :=
  TraceCorQQuotientCandidate.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.refinementSupportCandidate source target support)

/-- An associativity support candidate splits imported rectangles. -/
theorem TraceCorQRelationGenerator.associativitySupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.associativity source target support).importedRectangles :=
  TraceCorQQuotientCandidate.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.associativitySupportCandidate source target support)

/-- A left-identity support candidate splits imported rectangles. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.leftIdentity source target support).importedRectangles :=
  TraceCorQQuotientCandidate.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate source target support)

/-- A right-identity support candidate splits imported rectangles. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.rightIdentity source target support).importedRectangles :=
  TraceCorQQuotientCandidate.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate source target support)

end AnalyticMotives
end LFunctions
end Boundary
