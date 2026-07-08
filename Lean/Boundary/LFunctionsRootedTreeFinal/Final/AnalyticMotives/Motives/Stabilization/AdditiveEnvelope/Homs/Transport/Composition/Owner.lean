import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Transport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.Typed.Owner

/-!
# Composition of transported identity entries

Transported identity entries compose to ordinary identities when the transports
are inverse object equalities.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A transported identity followed by the inverse transported identity is the identity. -/
theorem TraceAnalyticAdditiveHom.transportedId_comp_symm
    {source target : TraceCorQObject}
    (object_eq : source = target) :
    TraceCorQHom.comp
      (TraceAnalyticAdditiveHom.transportedId object_eq)
      (TraceAnalyticAdditiveHom.transportedId (Eq.symm object_eq)) =
      TraceCorQHom.id source :=
  by
    cases object_eq
    exact
      TraceCorQHom.right_id
        (TraceCorQHom.id source)

/-- The inverse transported identity followed by a transported identity is the identity. -/
theorem TraceAnalyticAdditiveHom.transportedId_symm_comp
    {source target : TraceCorQObject}
    (object_eq : source = target) :
    TraceCorQHom.comp
      (TraceAnalyticAdditiveHom.transportedId (Eq.symm object_eq))
      (TraceAnalyticAdditiveHom.transportedId object_eq) =
      TraceCorQHom.id target :=
  by
    cases object_eq
    exact
      TraceCorQHom.right_id
        (TraceCorQHom.id source)

end AnalyticMotives
end LFunctions
end Boundary
