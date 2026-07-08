import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.Lengths.Owner

/-!
# Top-root length invariants for named-coherence candidates

This file exposes count-as-length invariants for named-coherence support
candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes Fubini candidate count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportCandidate_importedRectangleCount_eq_length
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

/-- The top root exposes schedule-exchange candidate count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportCandidate_importedRectangleCount_eq_length
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

/-- The top root exposes residue-channel candidate count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportCandidate_importedRectangleCount_eq_length
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

/-- The top root exposes Stokes-residue candidate count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportCandidate_importedRectangleCount_eq_length
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

/-- The top root exposes refinement candidate count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportCandidate_importedRectangleCount_eq_length
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

/-- The top root exposes associativity candidate count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportCandidate_importedRectangleCount_eq_length
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

/-- The top root exposes left-identity candidate count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportCandidate_importedRectangleCount_eq_length
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

/-- The top root exposes right-identity candidate count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportCandidate_importedRectangleCount_eq_length
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
