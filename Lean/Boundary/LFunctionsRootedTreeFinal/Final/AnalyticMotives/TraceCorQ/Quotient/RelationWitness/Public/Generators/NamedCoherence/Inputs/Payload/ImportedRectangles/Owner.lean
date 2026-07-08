import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Payload.ImportedRectangles.Owner

/-!
# Public named-coherence support-input imported rectangles

This file exposes imported-rectangle count and rectangle-list decompositions
for named-coherence support inputs under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes Fubini support-input imported counts. -/
theorem TraceCorQ.relationGenerator_fubiniSupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.fubini source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.fubiniSupportInput_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-input imported counts. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.scheduleExchange source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.scheduleExchangeSupportInput_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-input imported counts. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.residueChannel source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.residueChannelSupportInput_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-input imported counts. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.stokesResidue source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.stokesResidueSupportInput_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-input imported counts. -/
theorem TraceCorQ.relationGenerator_refinementSupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.refinement source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.refinementSupportInput_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-input imported counts. -/
theorem TraceCorQ.relationGenerator_associativitySupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.associativity source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.associativitySupportInput_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-input imported counts. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.leftIdentity source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.leftIdentitySupportInput_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-input imported counts. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.rightIdentity source target support).importedRectangleCount :=
  TraceCorQRelationGenerator.rightIdentitySupportInput_importedRectangleCount
    source
    target
    support

/-- The trace-correspondence root exposes Fubini support-input imported rectangles. -/
theorem TraceCorQ.relationGenerator_fubiniSupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.fubini source target support).importedRectangles :=
  TraceCorQRelationGenerator.fubiniSupportInput_importedRectangles
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-input imported rectangles. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.scheduleExchange source target support).importedRectangles :=
  TraceCorQRelationGenerator.scheduleExchangeSupportInput_importedRectangles
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-input imported rectangles. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.residueChannel source target support).importedRectangles :=
  TraceCorQRelationGenerator.residueChannelSupportInput_importedRectangles
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-input imported rectangles. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.stokesResidue source target support).importedRectangles :=
  TraceCorQRelationGenerator.stokesResidueSupportInput_importedRectangles
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-input imported rectangles. -/
theorem TraceCorQ.relationGenerator_refinementSupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.refinement source target support).importedRectangles :=
  TraceCorQRelationGenerator.refinementSupportInput_importedRectangles
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-input imported rectangles. -/
theorem TraceCorQ.relationGenerator_associativitySupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.associativity source target support).importedRectangles :=
  TraceCorQRelationGenerator.associativitySupportInput_importedRectangles
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-input imported rectangles. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.leftIdentity source target support).importedRectangles :=
  TraceCorQRelationGenerator.leftIdentitySupportInput_importedRectangles
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-input imported rectangles. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.rightIdentity source target support).importedRectangles :=
  TraceCorQRelationGenerator.rightIdentitySupportInput_importedRectangles
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
