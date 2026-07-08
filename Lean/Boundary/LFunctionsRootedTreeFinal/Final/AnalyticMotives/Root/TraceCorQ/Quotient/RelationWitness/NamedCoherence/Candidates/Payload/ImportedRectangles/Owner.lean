import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.ImportedRectangles.Owner

/-!
# Top-root imported rectangles for named-coherence candidates

This file exposes imported finite-rectangle counts and lists carried by
named-coherence support candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes Fubini candidate imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.fubini source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.fubiniSupportCandidate_importedRectangleCount
    source
    target
    support

/-- The top root exposes schedule-exchange candidate imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.scheduleExchange source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_importedRectangleCount
    source
    target
    support

/-- The top root exposes residue-channel candidate imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.residueChannel source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.residueChannelSupportCandidate_importedRectangleCount
    source
    target
    support

/-- The top root exposes Stokes-residue candidate imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.stokesResidue source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.stokesResidueSupportCandidate_importedRectangleCount
    source
    target
    support

/-- The top root exposes refinement candidate imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.refinement source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.refinementSupportCandidate_importedRectangleCount
    source
    target
    support

/-- The top root exposes associativity candidate imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.associativity source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.associativitySupportCandidate_importedRectangleCount
    source
    target
    support

/-- The top root exposes left-identity candidate imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.leftIdentity source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.leftIdentitySupportCandidate_importedRectangleCount
    source
    target
    support

/-- The top root exposes right-identity candidate imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportCandidate_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.rightIdentity source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.rightIdentitySupportCandidate_importedRectangleCount
    source
    target
    support

/-- The top root exposes Fubini candidate imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.fubini source target support).importedRectangles :=
  TraceCorQRelationGenerator.fubiniSupportCandidate_importedRectangles
    source
    target
    support

/-- The top root exposes schedule-exchange candidate imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.scheduleExchange source target support).importedRectangles :=
  TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_importedRectangles
    source
    target
    support

/-- The top root exposes residue-channel candidate imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.residueChannel source target support).importedRectangles :=
  TraceCorQRelationGenerator.residueChannelSupportCandidate_importedRectangles
    source
    target
    support

/-- The top root exposes Stokes-residue candidate imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.stokesResidue source target support).importedRectangles :=
  TraceCorQRelationGenerator.stokesResidueSupportCandidate_importedRectangles
    source
    target
    support

/-- The top root exposes refinement candidate imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.refinement source target support).importedRectangles :=
  TraceCorQRelationGenerator.refinementSupportCandidate_importedRectangles
    source
    target
    support

/-- The top root exposes associativity candidate imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.associativity source target support).importedRectangles :=
  TraceCorQRelationGenerator.associativitySupportCandidate_importedRectangles
    source
    target
    support

/-- The top root exposes left-identity candidate imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.leftIdentity source target support).importedRectangles :=
  TraceCorQRelationGenerator.leftIdentitySupportCandidate_importedRectangles
    source
    target
    support

/-- The top root exposes right-identity candidate imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportCandidate_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.rightIdentity source target support).importedRectangles :=
  TraceCorQRelationGenerator.rightIdentitySupportCandidate_importedRectangles
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
