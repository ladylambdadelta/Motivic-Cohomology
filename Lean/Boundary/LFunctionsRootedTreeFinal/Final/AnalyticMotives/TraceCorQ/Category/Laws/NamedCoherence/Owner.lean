import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.NamedCoherence.Owner

/-!
# Law-facing named coherence zero theorems

This file gives category-law names to the typed hom relations killed by the
associativity and identity coherence ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The typed associativity coherence support is zero in the hom quotient. -/
theorem TraceCorQHom.associativitySupport_eq_zero
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
  TraceCorQHom.ofFormalSumLedger_associativity_eq_zero
    pathSource
    pathTarget
    support

/-- The typed left-identity coherence support is zero in the hom quotient. -/
theorem TraceCorQHom.leftIdentitySupport_eq_zero
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
  TraceCorQHom.ofFormalSumLedger_leftIdentity_eq_zero
    pathSource
    pathTarget
    support

/-- The typed right-identity coherence support is zero in the hom quotient. -/
theorem TraceCorQHom.rightIdentitySupport_eq_zero
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
  TraceCorQHom.ofFormalSumLedger_rightIdentity_eq_zero
    pathSource
    pathTarget
    support

end AnalyticMotives
end LFunctions
end Boundary
