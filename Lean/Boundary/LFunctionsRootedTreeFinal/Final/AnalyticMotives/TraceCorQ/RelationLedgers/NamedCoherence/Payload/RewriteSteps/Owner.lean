import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.NamedCoherence.Owner

/-!
# Rewrite-step payloads for named coherence relation ledgers

This file owns the rewrite-step count facts for singleton relation ledgers
generated from named coherence cells.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini relation ledger counts the source and target paths of the coherence. -/
theorem TraceCorQRelationLedger.fubini_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.fubini
      source
      target
      support).rewriteStepCount =
      (source.stepCount + (target.stepCount + (0 + 0))) + 0 :=
  rfl

/-- A schedule-exchange relation ledger counts the source and target paths. -/
theorem TraceCorQRelationLedger.scheduleExchange_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.scheduleExchange
      source
      target
      support).rewriteStepCount =
      (source.stepCount + (target.stepCount + (0 + 0))) + 0 :=
  rfl

/-- A residue-channel relation ledger counts the source and target paths. -/
theorem TraceCorQRelationLedger.residueChannel_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.residueChannel
      source
      target
      support).rewriteStepCount =
      (source.stepCount + (target.stepCount + (0 + 0))) + 0 :=
  rfl

/-- A Stokes-residue relation ledger counts the source and target paths. -/
theorem TraceCorQRelationLedger.stokesResidue_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.stokesResidue
      source
      target
      support).rewriteStepCount =
      (source.stepCount + (target.stepCount + (0 + 0))) + 0 :=
  rfl

/-- A refinement relation ledger counts the source and target paths. -/
theorem TraceCorQRelationLedger.refinement_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.refinement
      source
      target
      support).rewriteStepCount =
      (source.stepCount + (target.stepCount + (0 + 0))) + 0 :=
  rfl

/-- An associativity relation ledger counts the source and target paths. -/
theorem TraceCorQRelationLedger.associativity_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.associativity
      source
      target
      support).rewriteStepCount =
      (source.stepCount + (target.stepCount + (0 + 0))) + 0 :=
  rfl

/-- A left-identity relation ledger counts the source and target paths. -/
theorem TraceCorQRelationLedger.leftIdentity_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.leftIdentity
      source
      target
      support).rewriteStepCount =
      (source.stepCount + (target.stepCount + (0 + 0))) + 0 :=
  rfl

/-- A right-identity relation ledger counts the source and target paths. -/
theorem TraceCorQRelationLedger.rightIdentity_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationLedger.rightIdentity
      source
      target
      support).rewriteStepCount =
      (source.stepCount + (target.stepCount + (0 + 0))) + 0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
