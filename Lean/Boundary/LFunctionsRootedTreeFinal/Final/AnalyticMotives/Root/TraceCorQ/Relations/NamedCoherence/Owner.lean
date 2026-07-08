import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Relations.NamedCoherence.Owner

/-!
# Top-root named coherence relation generators

This file exposes projection facts for named Q-linear trace-correspondence
relation generators under the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the Fubini relation-generator cell. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubini_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubini source target support).cell =
      TraceCoherenceCell.fubini source target :=
  TraceCorQRelationGenerator.fubini_cell
    source
    target
    support

/-- The top root exposes the schedule-exchange relation-generator cell. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchange_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchange source target support).cell =
      TraceCoherenceCell.scheduleExchange source target :=
  TraceCorQRelationGenerator.scheduleExchange_cell
    source
    target
    support

/-- The top root exposes the residue-channel relation-generator cell. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannel_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannel source target support).cell =
      TraceCoherenceCell.residueChannel source target :=
  TraceCorQRelationGenerator.residueChannel_cell
    source
    target
    support

/-- The top root exposes the Stokes-residue relation-generator cell. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidue_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidue source target support).cell =
      TraceCoherenceCell.stokesResidue source target :=
  TraceCorQRelationGenerator.stokesResidue_cell
    source
    target
    support

/-- The top root exposes the refinement relation-generator cell. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinement_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinement source target support).cell =
      TraceCoherenceCell.refinement source target :=
  TraceCorQRelationGenerator.refinement_cell
    source
    target
    support

/-- The top root exposes the associativity relation-generator cell. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativity_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativity source target support).cell =
      TraceCoherenceCell.associativity source target :=
  TraceCorQRelationGenerator.associativity_cell
    source
    target
    support

/-- The top root exposes the left-identity relation-generator cell. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentity_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentity source target support).cell =
      TraceCoherenceCell.leftIdentity source target :=
  TraceCorQRelationGenerator.leftIdentity_cell
    source
    target
    support

/-- The top root exposes the right-identity relation-generator cell. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentity_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentity source target support).cell =
      TraceCoherenceCell.rightIdentity source target :=
  TraceCorQRelationGenerator.rightIdentity_cell
    source
    target
    support

/-- The top root exposes the Fubini relation-generator support. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubini_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubini source target support).support =
      support :=
  TraceCorQRelationGenerator.fubini_support
    source
    target
    support

/-- The top root exposes the schedule-exchange relation-generator support. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchange_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchange source target support).support =
      support :=
  TraceCorQRelationGenerator.scheduleExchange_support
    source
    target
    support

/-- The top root exposes the residue-channel relation-generator support. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannel_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannel source target support).support =
      support :=
  TraceCorQRelationGenerator.residueChannel_support
    source
    target
    support

/-- The top root exposes the Stokes-residue relation-generator support. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidue_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidue source target support).support =
      support :=
  TraceCorQRelationGenerator.stokesResidue_support
    source
    target
    support

/-- The top root exposes the refinement relation-generator support. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinement_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinement source target support).support =
      support :=
  TraceCorQRelationGenerator.refinement_support
    source
    target
    support

/-- The top root exposes the associativity relation-generator support. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativity_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativity source target support).support =
      support :=
  TraceCorQRelationGenerator.associativity_support
    source
    target
    support

/-- The top root exposes the left-identity relation-generator support. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentity_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentity source target support).support =
      support :=
  TraceCorQRelationGenerator.leftIdentity_support
    source
    target
    support

/-- The top root exposes the right-identity relation-generator support. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentity_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentity source target support).support =
      support :=
  TraceCorQRelationGenerator.rightIdentity_support
    source
    target
    support

/-- The top root exposes the Fubini relation-generator certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubini_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubini source target support).certificateLedger =
      TraceCoherenceCell.fubiniCertificateLedger source target :=
  TraceCorQRelationGenerator.fubini_certificateLedger
    source
    target
    support

/-- The top root exposes the schedule-exchange relation-generator certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchange_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchange source target support).certificateLedger =
      TraceCoherenceCell.scheduleExchangeCertificateLedger source target :=
  TraceCorQRelationGenerator.scheduleExchange_certificateLedger
    source
    target
    support

/-- The top root exposes the residue-channel relation-generator certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannel_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannel source target support).certificateLedger =
      TraceCoherenceCell.residueChannelCertificateLedger source target :=
  TraceCorQRelationGenerator.residueChannel_certificateLedger
    source
    target
    support

/-- The top root exposes the Stokes-residue relation-generator certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidue_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidue source target support).certificateLedger =
      TraceCoherenceCell.stokesResidueCertificateLedger source target :=
  TraceCorQRelationGenerator.stokesResidue_certificateLedger
    source
    target
    support

/-- The top root exposes the refinement relation-generator certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinement_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinement source target support).certificateLedger =
      TraceCoherenceCell.refinementCertificateLedger source target :=
  TraceCorQRelationGenerator.refinement_certificateLedger
    source
    target
    support

/-- The top root exposes the associativity relation-generator certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativity_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativity source target support).certificateLedger =
      TraceCoherenceCell.associativityCertificateLedger source target :=
  TraceCorQRelationGenerator.associativity_certificateLedger
    source
    target
    support

/-- The top root exposes the left-identity relation-generator certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentity_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentity source target support).certificateLedger =
      TraceCoherenceCell.leftIdentityCertificateLedger source target :=
  TraceCorQRelationGenerator.leftIdentity_certificateLedger
    source
    target
    support

/-- The top root exposes the right-identity relation-generator certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentity_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentity source target support).certificateLedger =
      TraceCoherenceCell.rightIdentityCertificateLedger source target :=
  TraceCorQRelationGenerator.rightIdentity_certificateLedger
    source
    target
    support

/-- The top root exposes the Fubini relation-generator rewrite-step count. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubini_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubini source target support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCorQRelationGenerator.fubini_rewriteStepCount
    source
    target
    support

/-- The top root exposes the schedule-exchange relation-generator rewrite-step count. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchange_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchange source target support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCorQRelationGenerator.scheduleExchange_rewriteStepCount
    source
    target
    support

/-- The top root exposes the residue-channel relation-generator rewrite-step count. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannel_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannel source target support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCorQRelationGenerator.residueChannel_rewriteStepCount
    source
    target
    support

/-- The top root exposes the Stokes-residue relation-generator rewrite-step count. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidue_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidue source target support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCorQRelationGenerator.stokesResidue_rewriteStepCount
    source
    target
    support

/-- The top root exposes the refinement relation-generator rewrite-step count. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinement_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinement source target support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCorQRelationGenerator.refinement_rewriteStepCount
    source
    target
    support

/-- The top root exposes the associativity relation-generator rewrite-step count. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativity_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativity source target support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCorQRelationGenerator.associativity_rewriteStepCount
    source
    target
    support

/-- The top root exposes the left-identity relation-generator rewrite-step count. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentity_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentity source target support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCorQRelationGenerator.leftIdentity_rewriteStepCount
    source
    target
    support

/-- The top root exposes the right-identity relation-generator rewrite-step count. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentity_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentity source target support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCorQRelationGenerator.rightIdentity_rewriteStepCount
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
