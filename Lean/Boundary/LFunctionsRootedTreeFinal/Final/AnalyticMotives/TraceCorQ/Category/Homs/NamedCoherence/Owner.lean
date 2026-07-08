import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Ambient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.FormalSumClass.NamedCoherence.Owner

/-!
# Typed hom classes killed by named coherence ledgers

This file lifts the named coherence-zero relations from the ambient untyped
quotient to fixed-endpoint typed hom classes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A typed formal sum with its Fubini relation ledger is zero as a typed hom. -/
theorem TraceCorQHom.ofFormalSumLedger_fubini_eq_zero
    {homSource homTarget : TraceCorQObject}
    (pathSource pathTarget : TraceRewritePath)
    (support : TraceCorQHomFormalSum homSource homTarget) :
    TraceCorQHom.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.fubini
        pathSource
        pathTarget
        support.raw) =
      TraceCorQHom.zero homSource homTarget :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_ofFormalSumLedger
        support
        (TraceCorQRelationLedger.fubini
          pathSource
          pathTarget
          support.raw))
      (Eq.trans
        (TraceCorQQuotient.ofFormalSumLedger_fubini_eq_zero
          pathSource
          pathTarget
          support.raw)
        (Eq.symm
          (TraceCorQHom.ambient_zero homSource homTarget))))

/-- A typed formal sum with its schedule-exchange ledger is zero as a typed hom. -/
theorem TraceCorQHom.ofFormalSumLedger_scheduleExchange_eq_zero
    {homSource homTarget : TraceCorQObject}
    (pathSource pathTarget : TraceRewritePath)
    (support : TraceCorQHomFormalSum homSource homTarget) :
    TraceCorQHom.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.scheduleExchange
        pathSource
        pathTarget
        support.raw) =
      TraceCorQHom.zero homSource homTarget :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_ofFormalSumLedger
        support
        (TraceCorQRelationLedger.scheduleExchange
          pathSource
          pathTarget
          support.raw))
      (Eq.trans
        (TraceCorQQuotient.ofFormalSumLedger_scheduleExchange_eq_zero
          pathSource
          pathTarget
          support.raw)
        (Eq.symm
          (TraceCorQHom.ambient_zero homSource homTarget))))

/-- A typed formal sum with its residue-channel ledger is zero as a typed hom. -/
theorem TraceCorQHom.ofFormalSumLedger_residueChannel_eq_zero
    {homSource homTarget : TraceCorQObject}
    (pathSource pathTarget : TraceRewritePath)
    (support : TraceCorQHomFormalSum homSource homTarget) :
    TraceCorQHom.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.residueChannel
        pathSource
        pathTarget
        support.raw) =
      TraceCorQHom.zero homSource homTarget :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_ofFormalSumLedger
        support
        (TraceCorQRelationLedger.residueChannel
          pathSource
          pathTarget
          support.raw))
      (Eq.trans
        (TraceCorQQuotient.ofFormalSumLedger_residueChannel_eq_zero
          pathSource
          pathTarget
          support.raw)
        (Eq.symm
          (TraceCorQHom.ambient_zero homSource homTarget))))

/-- A typed formal sum with its Stokes-residue ledger is zero as a typed hom. -/
theorem TraceCorQHom.ofFormalSumLedger_stokesResidue_eq_zero
    {homSource homTarget : TraceCorQObject}
    (pathSource pathTarget : TraceRewritePath)
    (support : TraceCorQHomFormalSum homSource homTarget) :
    TraceCorQHom.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.stokesResidue
        pathSource
        pathTarget
        support.raw) =
      TraceCorQHom.zero homSource homTarget :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_ofFormalSumLedger
        support
        (TraceCorQRelationLedger.stokesResidue
          pathSource
          pathTarget
          support.raw))
      (Eq.trans
        (TraceCorQQuotient.ofFormalSumLedger_stokesResidue_eq_zero
          pathSource
          pathTarget
          support.raw)
        (Eq.symm
          (TraceCorQHom.ambient_zero homSource homTarget))))

/-- A typed formal sum with its refinement ledger is zero as a typed hom. -/
theorem TraceCorQHom.ofFormalSumLedger_refinement_eq_zero
    {homSource homTarget : TraceCorQObject}
    (pathSource pathTarget : TraceRewritePath)
    (support : TraceCorQHomFormalSum homSource homTarget) :
    TraceCorQHom.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.refinement
        pathSource
        pathTarget
        support.raw) =
      TraceCorQHom.zero homSource homTarget :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_ofFormalSumLedger
        support
        (TraceCorQRelationLedger.refinement
          pathSource
          pathTarget
          support.raw))
      (Eq.trans
        (TraceCorQQuotient.ofFormalSumLedger_refinement_eq_zero
          pathSource
          pathTarget
          support.raw)
        (Eq.symm
          (TraceCorQHom.ambient_zero homSource homTarget))))

/-- A typed formal sum with its associativity ledger is zero as a typed hom. -/
theorem TraceCorQHom.ofFormalSumLedger_associativity_eq_zero
    {homSource homTarget : TraceCorQObject}
    (pathSource pathTarget : TraceRewritePath)
    (support : TraceCorQHomFormalSum homSource homTarget) :
    TraceCorQHom.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.associativity
        pathSource
        pathTarget
        support.raw) =
      TraceCorQHom.zero homSource homTarget :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_ofFormalSumLedger
        support
        (TraceCorQRelationLedger.associativity
          pathSource
          pathTarget
          support.raw))
      (Eq.trans
        (TraceCorQQuotient.ofFormalSumLedger_associativity_eq_zero
          pathSource
          pathTarget
          support.raw)
        (Eq.symm
          (TraceCorQHom.ambient_zero homSource homTarget))))

/-- A typed formal sum with its left-identity ledger is zero as a typed hom. -/
theorem TraceCorQHom.ofFormalSumLedger_leftIdentity_eq_zero
    {homSource homTarget : TraceCorQObject}
    (pathSource pathTarget : TraceRewritePath)
    (support : TraceCorQHomFormalSum homSource homTarget) :
    TraceCorQHom.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.leftIdentity
        pathSource
        pathTarget
        support.raw) =
      TraceCorQHom.zero homSource homTarget :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_ofFormalSumLedger
        support
        (TraceCorQRelationLedger.leftIdentity
          pathSource
          pathTarget
          support.raw))
      (Eq.trans
        (TraceCorQQuotient.ofFormalSumLedger_leftIdentity_eq_zero
          pathSource
          pathTarget
          support.raw)
        (Eq.symm
          (TraceCorQHom.ambient_zero homSource homTarget))))

/-- A typed formal sum with its right-identity ledger is zero as a typed hom. -/
theorem TraceCorQHom.ofFormalSumLedger_rightIdentity_eq_zero
    {homSource homTarget : TraceCorQObject}
    (pathSource pathTarget : TraceRewritePath)
    (support : TraceCorQHomFormalSum homSource homTarget) :
    TraceCorQHom.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.rightIdentity
        pathSource
        pathTarget
        support.raw) =
      TraceCorQHom.zero homSource homTarget :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_ofFormalSumLedger
        support
        (TraceCorQRelationLedger.rightIdentity
          pathSource
          pathTarget
          support.raw))
      (Eq.trans
        (TraceCorQQuotient.ofFormalSumLedger_rightIdentity_eq_zero
          pathSource
          pathTarget
          support.raw)
        (Eq.symm
          (TraceCorQHom.ambient_zero homSource homTarget))))

end AnalyticMotives
end LFunctions
end Boundary
