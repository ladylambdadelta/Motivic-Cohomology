import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Relations.NamedCoherence.Payload.Owner

/-!
# Length invariants for named-coherence relation generators

This file records that each named-coherence relation generator counts exactly
the imported rectangles that it exposes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini relation generator's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.fubini_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubini
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.fubini
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.fubini source target support)

/-- A schedule-exchange relation generator's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.scheduleExchange_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchange
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.scheduleExchange
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.scheduleExchange source target support)

/-- A residue-channel relation generator's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.residueChannel_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannel
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.residueChannel
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.residueChannel source target support)

/-- A Stokes-residue relation generator's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.stokesResidue_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidue
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.stokesResidue
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.stokesResidue source target support)

/-- A refinement relation generator's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.refinement_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinement
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.refinement
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.refinement source target support)

/-- An associativity relation generator's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.associativity_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativity
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.associativity
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.associativity source target support)

/-- A left-identity relation generator's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.leftIdentity_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentity
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.leftIdentity
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.leftIdentity source target support)

/-- A right-identity relation generator's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.rightIdentity_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentity
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationGenerator.rightIdentity
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationGenerator.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.rightIdentity source target support)

end AnalyticMotives
end LFunctions
end Boundary
