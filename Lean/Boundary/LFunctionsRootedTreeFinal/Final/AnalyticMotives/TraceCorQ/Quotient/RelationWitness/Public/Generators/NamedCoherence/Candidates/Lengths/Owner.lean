import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.Lengths.Owner

/-!
# Public named-coherence support-candidate length invariants

This file exposes count-as-length invariants for named-coherence support
candidates under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes Fubini support-candidate count-as-length. -/
theorem TraceCorQ.relationGenerator_fubiniSupportCandidate_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.fubiniSupportCandidate
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.fubiniSupportCandidate_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-candidate count-as-length. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportCandidate_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-candidate count-as-length. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportCandidate_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.residueChannelSupportCandidate
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.residueChannelSupportCandidate_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-candidate count-as-length. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportCandidate_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.stokesResidueSupportCandidate
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.stokesResidueSupportCandidate_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-candidate count-as-length. -/
theorem TraceCorQ.relationGenerator_refinementSupportCandidate_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.refinementSupportCandidate
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.refinementSupportCandidate_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-candidate count-as-length. -/
theorem TraceCorQ.relationGenerator_associativitySupportCandidate_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.associativitySupportCandidate
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.associativitySupportCandidate_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-candidate count-as-length. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportCandidate_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.leftIdentitySupportCandidate
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.leftIdentitySupportCandidate_importedRectangleCount_eq_length
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-candidate count-as-length. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportCandidate_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.rightIdentitySupportCandidate
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.rightIdentitySupportCandidate_importedRectangleCount_eq_length
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
