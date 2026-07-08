import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Payload.ImportedRectangles.Owner

/-!
# Top-root imported rectangles for named-coherence witnesses

This file exposes imported finite-rectangle counts and lists carried by
named-coherence quotient-relation witnesses.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes Fubini witness imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportWitness_importedRectangleCount
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

/-- The top root exposes schedule-exchange witness imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportWitness_importedRectangleCount
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

/-- The top root exposes residue-channel witness imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportWitness_importedRectangleCount
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

/-- The top root exposes Stokes-residue witness imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportWitness_importedRectangleCount
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

/-- The top root exposes refinement witness imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportWitness_importedRectangleCount
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

/-- The top root exposes associativity witness imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportWitness_importedRectangleCount
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

/-- The top root exposes left-identity witness imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportWitness_importedRectangleCount
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

/-- The top root exposes right-identity witness imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportWitness_importedRectangleCount
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

/-- The top root exposes Fubini witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportWitness_importedRectangles
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

/-- The top root exposes schedule-exchange witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportWitness_importedRectangles
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

/-- The top root exposes residue-channel witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportWitness_importedRectangles
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

/-- The top root exposes Stokes-residue witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportWitness_importedRectangles
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

/-- The top root exposes refinement witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportWitness_importedRectangles
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

/-- The top root exposes associativity witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportWitness_importedRectangles
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

/-- The top root exposes left-identity witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportWitness_importedRectangles
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

/-- The top root exposes right-identity witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportWitness_importedRectangles
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
