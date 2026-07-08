import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Payload.ImportedRectangles.Owner

/-!
# Top-root imported rectangles for named-coherence inputs

This file exposes imported finite-rectangle counts and lists carried by
named-coherence support inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes Fubini input imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportInput_importedRectangleCount
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

/-- The top root exposes schedule-exchange input imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportInput_importedRectangleCount
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

/-- The top root exposes residue-channel input imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportInput_importedRectangleCount
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

/-- The top root exposes Stokes-residue input imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportInput_importedRectangleCount
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

/-- The top root exposes refinement input imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportInput_importedRectangleCount
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

/-- The top root exposes associativity input imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportInput_importedRectangleCount
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

/-- The top root exposes left-identity input imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportInput_importedRectangleCount
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

/-- The top root exposes right-identity input imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportInput_importedRectangleCount
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

/-- The top root exposes Fubini input imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportInput_importedRectangles
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

/-- The top root exposes schedule-exchange input imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportInput_importedRectangles
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

/-- The top root exposes residue-channel input imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportInput_importedRectangles
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

/-- The top root exposes Stokes-residue input imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportInput_importedRectangles
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

/-- The top root exposes refinement input imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportInput_importedRectangles
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

/-- The top root exposes associativity input imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportInput_importedRectangles
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

/-- The top root exposes left-identity input imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportInput_importedRectangles
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

/-- The top root exposes right-identity input imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportInput_importedRectangles
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
