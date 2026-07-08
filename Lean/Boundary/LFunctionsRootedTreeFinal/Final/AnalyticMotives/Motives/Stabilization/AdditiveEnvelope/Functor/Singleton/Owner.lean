import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Instance.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Instance.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Singleton.Owner

/-!
# Singleton functor into the analytic additive envelope

This file owns the functor that embeds the concrete trace-correspondence
category into the analytic additive envelope by sending a certified trace
object to its singleton additive object and a trace correspondence to the
corresponding one-entry matrix.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The singleton additive-envelope functor from trace correspondences. -/
def TraceAnalyticAdditiveObject.singletonFunctor :
    TraceCorQObject ⥤ TraceAnalyticAdditiveCategoryObject where
  obj object :=
    TraceAnalyticAdditiveObject.singleton object
  map hom :=
    TraceAnalyticAdditiveHom.singletonMap hom
  map_id object :=
    Eq.symm
      (TraceAnalyticAdditiveHom.singletonMap_id object)
  map_comp left right :=
    Eq.symm
      (TraceAnalyticAdditiveHom.singletonMap_comp left right)

/-- The singleton functor sends a trace object to its singleton additive
object. -/
theorem TraceAnalyticAdditiveObject.singletonFunctor_obj
    (object : TraceCorQObject) :
    TraceAnalyticAdditiveObject.singletonFunctor.obj object =
      TraceAnalyticAdditiveObject.singleton object :=
  rfl

/-- The singleton functor sends a trace correspondence to its singleton matrix. -/
theorem TraceAnalyticAdditiveObject.singletonFunctor_map
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    TraceAnalyticAdditiveObject.singletonFunctor.map hom =
      TraceAnalyticAdditiveHom.singletonMap hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
