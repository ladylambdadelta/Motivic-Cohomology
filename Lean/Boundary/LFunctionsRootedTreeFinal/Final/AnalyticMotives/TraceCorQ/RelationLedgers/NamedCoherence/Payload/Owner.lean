import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.NamedCoherence.Payload.CertificateLedgers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.NamedCoherence.Payload.RewriteSteps.Owner

/-!
# Payload facts for named coherence relation ledgers

This file records imported-rectangle and bookkeeping payloads carried by the
singleton relation ledgers generated from named coherence cells.  Certificate
ledgers and rewrite-step payloads are owned by child files.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini relation ledger carries no imported finite rectangles. -/
theorem TraceCorQRelationLedger.fubini_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.fubini
      source
      target
      support).importedRectangleCount =
      (0 + (0 + (0 + 0))) + 0 :=
  rfl

/-- A Fubini relation ledger exposes no imported finite rectangles. -/
theorem TraceCorQRelationLedger.fubini_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.fubini
      source
      target
      support).importedRectangles =
      ([] ++ ([] ++ ([] ++ []))) ++ [] :=
  rfl

/-- A Fubini relation ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCorQRelationLedger.fubini_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.fubini
      source
      target
      support).traceBookkeepingCount =
      (1 + (1 + (1 + 0))) + 0 :=
  rfl

/-- A schedule-exchange relation ledger carries no imported finite rectangles. -/
theorem TraceCorQRelationLedger.scheduleExchange_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.scheduleExchange
      source
      target
      support).importedRectangleCount =
      (0 + (0 + (0 + 0))) + 0 :=
  rfl

/-- A schedule-exchange relation ledger exposes no imported finite rectangles. -/
theorem TraceCorQRelationLedger.scheduleExchange_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.scheduleExchange
      source
      target
      support).importedRectangles =
      ([] ++ ([] ++ ([] ++ []))) ++ [] :=
  rfl

/-- A schedule-exchange relation ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCorQRelationLedger.scheduleExchange_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.scheduleExchange
      source
      target
      support).traceBookkeepingCount =
      (1 + (1 + (1 + 0))) + 0 :=
  rfl

/-- A residue-channel relation ledger carries no imported finite rectangles. -/
theorem TraceCorQRelationLedger.residueChannel_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.residueChannel
      source
      target
      support).importedRectangleCount =
      (0 + (0 + (0 + 0))) + 0 :=
  rfl

/-- A residue-channel relation ledger exposes no imported finite rectangles. -/
theorem TraceCorQRelationLedger.residueChannel_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.residueChannel
      source
      target
      support).importedRectangles =
      ([] ++ ([] ++ ([] ++ []))) ++ [] :=
  rfl

/-- A residue-channel relation ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCorQRelationLedger.residueChannel_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.residueChannel
      source
      target
      support).traceBookkeepingCount =
      (1 + (1 + (1 + 0))) + 0 :=
  rfl

/-- A Stokes-residue relation ledger carries no imported finite rectangles. -/
theorem TraceCorQRelationLedger.stokesResidue_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.stokesResidue
      source
      target
      support).importedRectangleCount =
      (0 + (0 + (0 + 0))) + 0 :=
  rfl

/-- A Stokes-residue relation ledger exposes no imported finite rectangles. -/
theorem TraceCorQRelationLedger.stokesResidue_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.stokesResidue
      source
      target
      support).importedRectangles =
      ([] ++ ([] ++ ([] ++ []))) ++ [] :=
  rfl

/-- A Stokes-residue relation ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCorQRelationLedger.stokesResidue_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.stokesResidue
      source
      target
      support).traceBookkeepingCount =
      (1 + (1 + (1 + 0))) + 0 :=
  rfl

/-- A refinement relation ledger carries no imported finite rectangles. -/
theorem TraceCorQRelationLedger.refinement_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.refinement
      source
      target
      support).importedRectangleCount =
      (0 + (0 + (0 + 0))) + 0 :=
  rfl

/-- A refinement relation ledger exposes no imported finite rectangles. -/
theorem TraceCorQRelationLedger.refinement_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.refinement
      source
      target
      support).importedRectangles =
      ([] ++ ([] ++ ([] ++ []))) ++ [] :=
  rfl

/-- A refinement relation ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCorQRelationLedger.refinement_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.refinement
      source
      target
      support).traceBookkeepingCount =
      (1 + (1 + (1 + 0))) + 0 :=
  rfl

/-- An associativity relation ledger carries no imported finite rectangles. -/
theorem TraceCorQRelationLedger.associativity_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.associativity
      source
      target
      support).importedRectangleCount =
      (0 + (0 + (0 + 0))) + 0 :=
  rfl

/-- An associativity relation ledger exposes no imported finite rectangles. -/
theorem TraceCorQRelationLedger.associativity_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.associativity
      source
      target
      support).importedRectangles =
      ([] ++ ([] ++ ([] ++ []))) ++ [] :=
  rfl

/-- An associativity relation ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCorQRelationLedger.associativity_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.associativity
      source
      target
      support).traceBookkeepingCount =
      (1 + (1 + (1 + 0))) + 0 :=
  rfl

/-- A left-identity relation ledger carries no imported finite rectangles. -/
theorem TraceCorQRelationLedger.leftIdentity_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.leftIdentity
      source
      target
      support).importedRectangleCount =
      (0 + (0 + (0 + 0))) + 0 :=
  rfl

/-- A left-identity relation ledger exposes no imported finite rectangles. -/
theorem TraceCorQRelationLedger.leftIdentity_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.leftIdentity
      source
      target
      support).importedRectangles =
      ([] ++ ([] ++ ([] ++ []))) ++ [] :=
  rfl

/-- A left-identity relation ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCorQRelationLedger.leftIdentity_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.leftIdentity
      source
      target
      support).traceBookkeepingCount =
      (1 + (1 + (1 + 0))) + 0 :=
  rfl

/-- A right-identity relation ledger carries no imported finite rectangles. -/
theorem TraceCorQRelationLedger.rightIdentity_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.rightIdentity
      source
      target
      support).importedRectangleCount =
      (0 + (0 + (0 + 0))) + 0 :=
  rfl

/-- A right-identity relation ledger exposes no imported finite rectangles. -/
theorem TraceCorQRelationLedger.rightIdentity_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.rightIdentity
      source
      target
      support).importedRectangles =
      ([] ++ ([] ++ ([] ++ []))) ++ [] :=
  rfl

/-- A right-identity relation ledger has source-path, target-path, and cell bookkeeping. -/
theorem TraceCorQRelationLedger.rightIdentity_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.rightIdentity
      source
      target
      support).traceBookkeepingCount =
      (1 + (1 + (1 + 0))) + 0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
