import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.NamedCoherence.Owner

/-!
# Top-root typed named coherence zero theorems

This file exposes the fixed-endpoint hom quotient theorems saying that named
coherence ledgers kill their formal supports as typed zero morphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes typed Fubini coherence supports as zero morphisms. -/
theorem AnalyticMotivesRoot.traceCorQHom_ofFormalSumLedger_fubini_eq_zero
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
  TraceCorQHom.ofFormalSumLedger_fubini_eq_zero
    pathSource
    pathTarget
    support

/-- The top root exposes typed schedule-exchange coherence supports as zero morphisms. -/
theorem AnalyticMotivesRoot.traceCorQHom_ofFormalSumLedger_scheduleExchange_eq_zero
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
  TraceCorQHom.ofFormalSumLedger_scheduleExchange_eq_zero
    pathSource
    pathTarget
    support

/-- The top root exposes typed residue-channel coherence supports as zero morphisms. -/
theorem AnalyticMotivesRoot.traceCorQHom_ofFormalSumLedger_residueChannel_eq_zero
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
  TraceCorQHom.ofFormalSumLedger_residueChannel_eq_zero
    pathSource
    pathTarget
    support

/-- The top root exposes typed Stokes-residue coherence supports as zero morphisms. -/
theorem AnalyticMotivesRoot.traceCorQHom_ofFormalSumLedger_stokesResidue_eq_zero
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
  TraceCorQHom.ofFormalSumLedger_stokesResidue_eq_zero
    pathSource
    pathTarget
    support

/-- The top root exposes typed refinement coherence supports as zero morphisms. -/
theorem AnalyticMotivesRoot.traceCorQHom_ofFormalSumLedger_refinement_eq_zero
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
  TraceCorQHom.ofFormalSumLedger_refinement_eq_zero
    pathSource
    pathTarget
    support

/-- The top root exposes typed associativity coherence supports as zero morphisms. -/
theorem AnalyticMotivesRoot.traceCorQHom_ofFormalSumLedger_associativity_eq_zero
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
  TraceCorQHom.ofFormalSumLedger_associativity_eq_zero
    pathSource
    pathTarget
    support

/-- The top root exposes typed left-identity coherence supports as zero morphisms. -/
theorem AnalyticMotivesRoot.traceCorQHom_ofFormalSumLedger_leftIdentity_eq_zero
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
  TraceCorQHom.ofFormalSumLedger_leftIdentity_eq_zero
    pathSource
    pathTarget
    support

/-- The top root exposes typed right-identity coherence supports as zero morphisms. -/
theorem AnalyticMotivesRoot.traceCorQHom_ofFormalSumLedger_rightIdentity_eq_zero
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
  TraceCorQHom.ofFormalSumLedger_rightIdentity_eq_zero
    pathSource
    pathTarget
    support

/-- The top root exposes law-facing typed associativity coherence supports as zero. -/
theorem AnalyticMotivesRoot.traceCorQHom_associativitySupport_eq_zero
    {source target : TraceCorQObject}
    (pathSource pathTarget : TraceRewritePath)
    (support : TraceCorQHomFormalSum source target) :
    TraceCorQHom.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.associativity
        pathSource
        pathTarget
        support.raw) =
      TraceCorQHom.zero source target :=
  TraceCorQHom.associativitySupport_eq_zero
    pathSource
    pathTarget
    support

/-- The top root exposes law-facing typed left-identity coherence supports as zero. -/
theorem AnalyticMotivesRoot.traceCorQHom_leftIdentitySupport_eq_zero
    {source target : TraceCorQObject}
    (pathSource pathTarget : TraceRewritePath)
    (support : TraceCorQHomFormalSum source target) :
    TraceCorQHom.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.leftIdentity
        pathSource
        pathTarget
        support.raw) =
      TraceCorQHom.zero source target :=
  TraceCorQHom.leftIdentitySupport_eq_zero
    pathSource
    pathTarget
    support

/-- The top root exposes law-facing typed right-identity coherence supports as zero. -/
theorem AnalyticMotivesRoot.traceCorQHom_rightIdentitySupport_eq_zero
    {source target : TraceCorQObject}
    (pathSource pathTarget : TraceRewritePath)
    (support : TraceCorQHomFormalSum source target) :
    TraceCorQHom.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.rightIdentity
        pathSource
        pathTarget
        support.raw) =
      TraceCorQHom.zero source target :=
  TraceCorQHom.rightIdentitySupport_eq_zero
    pathSource
    pathTarget
    support

end AnalyticMotives
end LFunctions
end Boundary
