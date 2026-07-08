import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Owner

/-!
# Length invariants for named-coherence support inputs

This file records that each named-coherence support input counts exactly the
imported rectangles that it exposes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini support input's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.fubiniSupportInput_importedRectangleCount_eq_length
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
  TraceCorQQuotientInput.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.fubiniSupportInput source target support)

/-- A schedule-exchange support input's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportInput_importedRectangleCount_eq_length
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
  TraceCorQQuotientInput.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput source target support)

/-- A residue-channel support input's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.residueChannelSupportInput_importedRectangleCount_eq_length
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
  TraceCorQQuotientInput.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.residueChannelSupportInput source target support)

/-- A Stokes-residue support input's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportInput_importedRectangleCount_eq_length
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
  TraceCorQQuotientInput.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.stokesResidueSupportInput source target support)

/-- A refinement support input's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.refinementSupportInput_importedRectangleCount_eq_length
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
  TraceCorQQuotientInput.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.refinementSupportInput source target support)

/-- An associativity support input's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.associativitySupportInput_importedRectangleCount_eq_length
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
  TraceCorQQuotientInput.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.associativitySupportInput source target support)

/-- A left-identity support input's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportInput_importedRectangleCount_eq_length
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
  TraceCorQQuotientInput.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.leftIdentitySupportInput source target support)

/-- A right-identity support input's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportInput_importedRectangleCount_eq_length
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
  TraceCorQQuotientInput.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.rightIdentitySupportInput source target support)

end AnalyticMotives
end LFunctions
end Boundary
