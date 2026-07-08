import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.NamedCoherence.Payload.Owner

/-!
# Length invariants for named-coherence relation ledgers

This file records that each named-coherence relation ledger counts exactly the
imported rectangles that it exposes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini relation ledger's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationLedger.fubini_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.fubini
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.fubini
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationLedger.fubini source target support)

/-- A schedule-exchange relation ledger's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationLedger.scheduleExchange_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.scheduleExchange
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.scheduleExchange
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationLedger.scheduleExchange source target support)

/-- A residue-channel relation ledger's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationLedger.residueChannel_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.residueChannel
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.residueChannel
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationLedger.residueChannel source target support)

/-- A Stokes-residue relation ledger's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationLedger.stokesResidue_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.stokesResidue
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.stokesResidue
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationLedger.stokesResidue source target support)

/-- A refinement relation ledger's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationLedger.refinement_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.refinement
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.refinement
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationLedger.refinement source target support)

/-- An associativity relation ledger's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationLedger.associativity_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.associativity
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.associativity
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationLedger.associativity source target support)

/-- A left-identity relation ledger's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationLedger.leftIdentity_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.leftIdentity
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.leftIdentity
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationLedger.leftIdentity source target support)

/-- A right-identity relation ledger's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationLedger.rightIdentity_importedRectangleCount_eq_length
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.rightIdentity
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.rightIdentity
        source
        target
        support).importedRectangles.length :=
  TraceCorQRelationLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationLedger.rightIdentity source target support)

end AnalyticMotives
end LFunctions
end Boundary
