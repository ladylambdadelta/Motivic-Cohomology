import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Payload.Owner

/-!
# Length invariants for named-coherence witness payloads

This file records that each named-coherence support witness counts exactly the
imported rectangles that it exposes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini support witness's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.fubiniSupportWitness_importedRectangleCount_eq_length
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
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.fubiniSupportWitness source target support)

/-- A schedule-exchange support witness's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportWitness_importedRectangleCount_eq_length
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
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness source target support)

/-- A residue-channel support witness's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.residueChannelSupportWitness_importedRectangleCount_eq_length
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
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.residueChannelSupportWitness source target support)

/-- A Stokes-residue support witness's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportWitness_importedRectangleCount_eq_length
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
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.stokesResidueSupportWitness source target support)

/-- A refinement support witness's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.refinementSupportWitness_importedRectangleCount_eq_length
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
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.refinementSupportWitness source target support)

/-- An associativity support witness's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.associativitySupportWitness_importedRectangleCount_eq_length
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
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.associativitySupportWitness source target support)

/-- A left-identity support witness's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportWitness_importedRectangleCount_eq_length
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
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.leftIdentitySupportWitness source target support)

/-- A right-identity support witness's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportWitness_importedRectangleCount_eq_length
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
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.rightIdentitySupportWitness source target support)

end AnalyticMotives
end LFunctions
end Boundary
