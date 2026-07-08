import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Lengths.Owner

/-!
# Top-root length invariants for named-coherence inputs

This file exposes count-as-length invariants for named-coherence support inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes Fubini input count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportInput_importedRectangleCount_eq_length
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

/-- The top root exposes schedule-exchange input count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportInput_importedRectangleCount_eq_length
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

/-- The top root exposes residue-channel input count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportInput_importedRectangleCount_eq_length
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

/-- The top root exposes Stokes-residue input count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportInput_importedRectangleCount_eq_length
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

/-- The top root exposes refinement input count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportInput_importedRectangleCount_eq_length
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

/-- The top root exposes associativity input count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportInput_importedRectangleCount_eq_length
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

/-- The top root exposes left-identity input count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportInput_importedRectangleCount_eq_length
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

/-- The top root exposes right-identity input count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportInput_importedRectangleCount_eq_length
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
