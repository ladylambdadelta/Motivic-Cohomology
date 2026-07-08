import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.FormalSumClass.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Setoid.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.NamedCoherence.Owner

/-!
# Formal-sum classes killed by named coherence ledgers

This file states the named coherence quotient equalities in the direct
`ofFormalSumLedger` form used by quotient operations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A formal sum with its Fubini relation ledger is zero in the quotient. -/
theorem TraceCorQQuotient.ofFormalSumLedger_fubini_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.fubini source target support) =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.sound_fubiniSupportZero
      source
      target
      support)
    (Eq.symm TraceCorQQuotient.zero_eq_ofCandidate_empty)

/-- A formal sum with its schedule-exchange relation ledger is zero in the quotient. -/
theorem TraceCorQQuotient.ofFormalSumLedger_scheduleExchange_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.scheduleExchange source target support) =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.sound_scheduleExchangeSupportZero
      source
      target
      support)
    (Eq.symm TraceCorQQuotient.zero_eq_ofCandidate_empty)

/-- A formal sum with its residue-channel relation ledger is zero in the quotient. -/
theorem TraceCorQQuotient.ofFormalSumLedger_residueChannel_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.residueChannel source target support) =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.sound_residueChannelSupportZero
      source
      target
      support)
    (Eq.symm TraceCorQQuotient.zero_eq_ofCandidate_empty)

/-- A formal sum with its Stokes-residue relation ledger is zero in the quotient. -/
theorem TraceCorQQuotient.ofFormalSumLedger_stokesResidue_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.stokesResidue source target support) =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.sound_stokesResidueSupportZero
      source
      target
      support)
    (Eq.symm TraceCorQQuotient.zero_eq_ofCandidate_empty)

/-- A formal sum with its refinement relation ledger is zero in the quotient. -/
theorem TraceCorQQuotient.ofFormalSumLedger_refinement_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.refinement source target support) =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.sound_refinementSupportZero
      source
      target
      support)
    (Eq.symm TraceCorQQuotient.zero_eq_ofCandidate_empty)

/-- A formal sum with its associativity relation ledger is zero in the quotient. -/
theorem TraceCorQQuotient.ofFormalSumLedger_associativity_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.associativity source target support) =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.sound_associativitySupportZero
      source
      target
      support)
    (Eq.symm TraceCorQQuotient.zero_eq_ofCandidate_empty)

/-- A formal sum with its left-identity relation ledger is zero in the quotient. -/
theorem TraceCorQQuotient.ofFormalSumLedger_leftIdentity_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.leftIdentity source target support) =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.sound_leftIdentitySupportZero
      source
      target
      support)
    (Eq.symm TraceCorQQuotient.zero_eq_ofCandidate_empty)

/-- A formal sum with its right-identity relation ledger is zero in the quotient. -/
theorem TraceCorQQuotient.ofFormalSumLedger_rightIdentity_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.rightIdentity source target support) =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.sound_rightIdentitySupportZero
      source
      target
      support)
    (Eq.symm TraceCorQQuotient.zero_eq_ofCandidate_empty)

end AnalyticMotives
end LFunctions
end Boundary
