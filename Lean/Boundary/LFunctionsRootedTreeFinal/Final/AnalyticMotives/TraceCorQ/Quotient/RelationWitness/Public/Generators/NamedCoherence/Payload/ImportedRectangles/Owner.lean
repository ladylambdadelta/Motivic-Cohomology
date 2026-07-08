import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Payload.ImportedRectangles.Owner

/-!
# Public named-coherence support-witness imported rectangles

This file exposes imported-rectangle count and rectangle-list projections for
named-coherence support witnesses under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes Fubini support-witness imported counts. -/
theorem TraceCorQ.relationGenerator_fubiniSupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.fubini source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.fubiniSupportWitness_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-witness imported counts. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.scheduleExchange source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.scheduleExchangeSupportWitness_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-witness imported counts. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.residueChannel source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.residueChannelSupportWitness_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-witness imported counts. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.stokesResidue source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.stokesResidueSupportWitness_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-witness imported counts. -/
theorem TraceCorQ.relationGenerator_refinementSupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.refinement source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.refinementSupportWitness_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-witness imported counts. -/
theorem TraceCorQ.relationGenerator_associativitySupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.associativity source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.associativitySupportWitness_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-witness imported counts. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.leftIdentity source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.leftIdentitySupportWitness_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-witness imported counts. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.rightIdentity source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.rightIdentitySupportWitness_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes Fubini support-witness imported rectangles. -/
theorem TraceCorQ.relationGenerator_fubiniSupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.fubini source target support).importedRectangles :=
  TraceCorQRelationGenerator.fubiniSupportWitness_importedRectangles
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-witness imported rectangles. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.scheduleExchange source target support).importedRectangles :=
  TraceCorQRelationGenerator.scheduleExchangeSupportWitness_importedRectangles
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-witness imported rectangles. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.residueChannel source target support).importedRectangles :=
  TraceCorQRelationGenerator.residueChannelSupportWitness_importedRectangles
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-witness imported rectangles. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.stokesResidue source target support).importedRectangles :=
  TraceCorQRelationGenerator.stokesResidueSupportWitness_importedRectangles
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-witness imported rectangles. -/
theorem TraceCorQ.relationGenerator_refinementSupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.refinement source target support).importedRectangles :=
  TraceCorQRelationGenerator.refinementSupportWitness_importedRectangles
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-witness imported rectangles. -/
theorem TraceCorQ.relationGenerator_associativitySupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.associativity source target support).importedRectangles :=
  TraceCorQRelationGenerator.associativitySupportWitness_importedRectangles
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-witness imported rectangles. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.leftIdentity source target support).importedRectangles :=
  TraceCorQRelationGenerator.leftIdentitySupportWitness_importedRectangles
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-witness imported rectangles. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.rightIdentity source target support).importedRectangles :=
  TraceCorQRelationGenerator.rightIdentitySupportWitness_importedRectangles
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
