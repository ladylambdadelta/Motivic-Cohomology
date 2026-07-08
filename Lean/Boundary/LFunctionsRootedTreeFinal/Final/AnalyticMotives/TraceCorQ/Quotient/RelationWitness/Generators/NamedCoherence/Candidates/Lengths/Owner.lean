import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.Owner

/-!
# Length invariants for named-coherence support candidates

This file records that each named-coherence support candidate counts exactly
the imported rectangles that it exposes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini support candidate's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.fubiniSupportCandidate_importedRectangleCount_eq_length
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
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.fubiniSupportCandidate source target support)

/-- A schedule-exchange support candidate's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_importedRectangleCount_eq_length
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
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate source target support)

/-- A residue-channel support candidate's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.residueChannelSupportCandidate_importedRectangleCount_eq_length
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
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.residueChannelSupportCandidate source target support)

/-- A Stokes-residue support candidate's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportCandidate_importedRectangleCount_eq_length
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
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate source target support)

/-- A refinement support candidate's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.refinementSupportCandidate_importedRectangleCount_eq_length
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
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.refinementSupportCandidate source target support)

/-- An associativity support candidate's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.associativitySupportCandidate_importedRectangleCount_eq_length
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
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.associativitySupportCandidate source target support)

/-- A left-identity support candidate's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportCandidate_importedRectangleCount_eq_length
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
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate source target support)

/-- A right-identity support candidate's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportCandidate_importedRectangleCount_eq_length
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
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate source target support)

end AnalyticMotives
end LFunctions
end Boundary
