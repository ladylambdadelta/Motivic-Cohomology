import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.ImportedRectangles.Owner

/-!
# Public named-coherence support-candidate imported rectangles

This file exposes imported-rectangle count and rectangle-list decompositions
for named-coherence support candidates under the `TraceCorQ` aggregate
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes Fubini support-candidate imported counts. -/
theorem TraceCorQ.relationGenerator_fubiniSupportCandidate_importedRectangleCount
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

/-- The trace-correspondence root exposes schedule-exchange support-candidate imported counts. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportCandidate_importedRectangleCount
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

/-- The trace-correspondence root exposes residue-channel support-candidate imported counts. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportCandidate_importedRectangleCount
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

/-- The trace-correspondence root exposes Stokes-residue support-candidate imported counts. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportCandidate_importedRectangleCount
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

/-- The trace-correspondence root exposes refinement support-candidate imported counts. -/
theorem TraceCorQ.relationGenerator_refinementSupportCandidate_importedRectangleCount
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

/-- The trace-correspondence root exposes associativity support-candidate imported counts. -/
theorem TraceCorQ.relationGenerator_associativitySupportCandidate_importedRectangleCount
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

/-- The trace-correspondence root exposes left-identity support-candidate imported counts. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportCandidate_importedRectangleCount
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

/-- The trace-correspondence root exposes right-identity support-candidate imported counts. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportCandidate_importedRectangleCount
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

/-- The trace-correspondence root exposes Fubini support-candidate imported rectangles. -/
theorem TraceCorQ.relationGenerator_fubiniSupportCandidate_importedRectangles
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

/-- The trace-correspondence root exposes schedule-exchange support-candidate imported rectangles. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportCandidate_importedRectangles
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

/-- The trace-correspondence root exposes residue-channel support-candidate imported rectangles. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportCandidate_importedRectangles
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

/-- The trace-correspondence root exposes Stokes-residue support-candidate imported rectangles. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportCandidate_importedRectangles
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

/-- The trace-correspondence root exposes refinement support-candidate imported rectangles. -/
theorem TraceCorQ.relationGenerator_refinementSupportCandidate_importedRectangles
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

/-- The trace-correspondence root exposes associativity support-candidate imported rectangles. -/
theorem TraceCorQ.relationGenerator_associativitySupportCandidate_importedRectangles
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

/-- The trace-correspondence root exposes left-identity support-candidate imported rectangles. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportCandidate_importedRectangles
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

/-- The trace-correspondence root exposes right-identity support-candidate imported rectangles. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportCandidate_importedRectangles
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
