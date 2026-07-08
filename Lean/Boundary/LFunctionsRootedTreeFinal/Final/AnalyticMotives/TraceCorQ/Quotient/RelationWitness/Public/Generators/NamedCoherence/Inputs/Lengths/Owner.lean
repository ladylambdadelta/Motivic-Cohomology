import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Lengths.Owner

/-!
# Public named-coherence support-input length invariants

This file exposes count-as-length invariants for named-coherence support inputs
under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes Fubini support-input count-as-length. -/
theorem TraceCorQ.relationGenerator_fubiniSupportInput_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.fubiniSupportInput
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.fubiniSupportInput_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-input count-as-length. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportInput_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.scheduleExchangeSupportInput
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.scheduleExchangeSupportInput_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-input count-as-length. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportInput_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.residueChannelSupportInput
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.residueChannelSupportInput_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-input count-as-length. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportInput_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.stokesResidueSupportInput
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.stokesResidueSupportInput_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-input count-as-length. -/
theorem TraceCorQ.relationGenerator_refinementSupportInput_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.refinementSupportInput
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.refinementSupportInput_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-input count-as-length. -/
theorem TraceCorQ.relationGenerator_associativitySupportInput_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.associativitySupportInput
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.associativitySupportInput_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-input count-as-length. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportInput_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.leftIdentitySupportInput
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.leftIdentitySupportInput_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-input count-as-length. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportInput_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.rightIdentitySupportInput
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.rightIdentitySupportInput_importedRectangleCount_eq_length
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
