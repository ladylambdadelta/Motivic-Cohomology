import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Relations.NamedCoherence.Constructors.Owner

/-!
# Named coherence relation generators

This file records the projection facts for Q-linear trace-correspondence
relation generators built from named higher coherence cells.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini relation generator has the corresponding Fubini coherence cell. -/
theorem TraceCorQRelationGenerator.fubini_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubini
      source
      target
      support).cell =
      TraceCoherenceCell.fubini source target :=
  rfl

/-- A schedule-exchange relation generator has the corresponding coherence cell. -/
theorem TraceCorQRelationGenerator.scheduleExchange_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchange
      source
      target
      support).cell =
      TraceCoherenceCell.scheduleExchange source target :=
  rfl

/-- A residue-channel relation generator has the corresponding coherence cell. -/
theorem TraceCorQRelationGenerator.residueChannel_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannel
      source
      target
      support).cell =
      TraceCoherenceCell.residueChannel source target :=
  rfl

/-- A Stokes-residue relation generator has the corresponding coherence cell. -/
theorem TraceCorQRelationGenerator.stokesResidue_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidue
      source
      target
      support).cell =
      TraceCoherenceCell.stokesResidue source target :=
  rfl

/-- A refinement relation generator has the corresponding coherence cell. -/
theorem TraceCorQRelationGenerator.refinement_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinement
      source
      target
      support).cell =
      TraceCoherenceCell.refinement source target :=
  rfl

/-- An associativity relation generator has the corresponding coherence cell. -/
theorem TraceCorQRelationGenerator.associativity_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativity
      source
      target
      support).cell =
      TraceCoherenceCell.associativity source target :=
  rfl

/-- A left-identity relation generator has the corresponding coherence cell. -/
theorem TraceCorQRelationGenerator.leftIdentity_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentity
      source
      target
      support).cell =
      TraceCoherenceCell.leftIdentity source target :=
  rfl

/-- A right-identity relation generator has the corresponding coherence cell. -/
theorem TraceCorQRelationGenerator.rightIdentity_cell
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentity
      source
      target
      support).cell =
      TraceCoherenceCell.rightIdentity source target :=
  rfl

/-- A Fubini relation generator has the supplied formal support. -/
theorem TraceCorQRelationGenerator.fubini_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubini
      source
      target
      support).support =
      support :=
  rfl

/-- A schedule-exchange relation generator has the supplied formal support. -/
theorem TraceCorQRelationGenerator.scheduleExchange_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchange
      source
      target
      support).support =
      support :=
  rfl

/-- A residue-channel relation generator has the supplied formal support. -/
theorem TraceCorQRelationGenerator.residueChannel_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannel
      source
      target
      support).support =
      support :=
  rfl

/-- A Stokes-residue relation generator has the supplied formal support. -/
theorem TraceCorQRelationGenerator.stokesResidue_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidue
      source
      target
      support).support =
      support :=
  rfl

/-- A refinement relation generator has the supplied formal support. -/
theorem TraceCorQRelationGenerator.refinement_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinement
      source
      target
      support).support =
      support :=
  rfl

/-- An associativity relation generator has the supplied formal support. -/
theorem TraceCorQRelationGenerator.associativity_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativity
      source
      target
      support).support =
      support :=
  rfl

/-- A left-identity relation generator has the supplied formal support. -/
theorem TraceCorQRelationGenerator.leftIdentity_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentity
      source
      target
      support).support =
      support :=
  rfl

/-- A right-identity relation generator has the supplied formal support. -/
theorem TraceCorQRelationGenerator.rightIdentity_support
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentity
      source
      target
      support).support =
      support :=
  rfl

/-- A Fubini relation generator is certified by the Fubini coherence ledger. -/
theorem TraceCorQRelationGenerator.fubini_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubini
      source
      target
      support).certificateLedger =
      TraceCoherenceCell.fubiniCertificateLedger source target :=
  rfl

/-- A schedule-exchange relation generator is certified by its coherence ledger. -/
theorem TraceCorQRelationGenerator.scheduleExchange_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchange
      source
      target
      support).certificateLedger =
      TraceCoherenceCell.scheduleExchangeCertificateLedger source target :=
  rfl

/-- A residue-channel relation generator is certified by its coherence ledger. -/
theorem TraceCorQRelationGenerator.residueChannel_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannel
      source
      target
      support).certificateLedger =
      TraceCoherenceCell.residueChannelCertificateLedger source target :=
  rfl

/-- A Stokes-residue relation generator is certified by its coherence ledger. -/
theorem TraceCorQRelationGenerator.stokesResidue_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidue
      source
      target
      support).certificateLedger =
      TraceCoherenceCell.stokesResidueCertificateLedger source target :=
  rfl

/-- A refinement relation generator is certified by its coherence ledger. -/
theorem TraceCorQRelationGenerator.refinement_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinement
      source
      target
      support).certificateLedger =
      TraceCoherenceCell.refinementCertificateLedger source target :=
  rfl

/-- An associativity relation generator is certified by its coherence ledger. -/
theorem TraceCorQRelationGenerator.associativity_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativity
      source
      target
      support).certificateLedger =
      TraceCoherenceCell.associativityCertificateLedger source target :=
  rfl

/-- A left-identity relation generator is certified by its coherence ledger. -/
theorem TraceCorQRelationGenerator.leftIdentity_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentity
      source
      target
      support).certificateLedger =
      TraceCoherenceCell.leftIdentityCertificateLedger source target :=
  rfl

/-- A right-identity relation generator is certified by its coherence ledger. -/
theorem TraceCorQRelationGenerator.rightIdentity_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentity
      source
      target
      support).certificateLedger =
      TraceCoherenceCell.rightIdentityCertificateLedger source target :=
  rfl

/-- A Fubini relation generator counts the source and target coherence paths. -/
theorem TraceCorQRelationGenerator.fubini_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubini
      source
      target
      support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

/-- A schedule-exchange relation generator counts the source and target paths. -/
theorem TraceCorQRelationGenerator.scheduleExchange_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchange
      source
      target
      support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

/-- A residue-channel relation generator counts the source and target paths. -/
theorem TraceCorQRelationGenerator.residueChannel_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannel
      source
      target
      support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

/-- A Stokes-residue relation generator counts the source and target paths. -/
theorem TraceCorQRelationGenerator.stokesResidue_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidue
      source
      target
      support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

/-- A refinement relation generator counts the source and target paths. -/
theorem TraceCorQRelationGenerator.refinement_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinement
      source
      target
      support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

/-- An associativity relation generator counts the source and target paths. -/
theorem TraceCorQRelationGenerator.associativity_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativity
      source
      target
      support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

/-- A left-identity relation generator counts the source and target paths. -/
theorem TraceCorQRelationGenerator.leftIdentity_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentity
      source
      target
      support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

/-- A right-identity relation generator counts the source and target paths. -/
theorem TraceCorQRelationGenerator.rightIdentity_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentity
      source
      target
      support).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
