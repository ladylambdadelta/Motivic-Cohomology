import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Payload.Lengths.Owner

/-!
# Public named-coherence support-witness length invariants

This file exposes count-as-length invariants for named-coherence support
witnesses under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes Fubini support-witness count-as-length. -/
theorem TraceCorQ.relationGenerator_fubiniSupportWitness_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.fubiniSupportWitness
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.fubiniSupportWitness_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-witness count-as-length. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportWitness_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.scheduleExchangeSupportWitness
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.scheduleExchangeSupportWitness_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-witness count-as-length. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportWitness_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.residueChannelSupportWitness
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.residueChannelSupportWitness_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-witness count-as-length. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportWitness_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.stokesResidueSupportWitness
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.stokesResidueSupportWitness_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-witness count-as-length. -/
theorem TraceCorQ.relationGenerator_refinementSupportWitness_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.refinementSupportWitness
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.refinementSupportWitness_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-witness count-as-length. -/
theorem TraceCorQ.relationGenerator_associativitySupportWitness_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.associativitySupportWitness
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.associativitySupportWitness_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-witness count-as-length. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportWitness_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.leftIdentitySupportWitness
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.leftIdentitySupportWitness_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-witness count-as-length. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportWitness_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.rightIdentitySupportWitness
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.rightIdentitySupportWitness_importedRectangleCount_eq_length
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
