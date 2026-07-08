import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Operations.Owner

/-!
# Identity matrices in the analytic additive envelope

Identity morphisms in the additive envelope are diagonal matrices whose
diagonal entries are identity trace correspondences and whose off-diagonal
entries are zero trace correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The identity matrix-valued analytic trace correspondence. -/
def TraceAnalyticAdditiveHom.id
    (object : TraceAnalyticAdditiveObject) :
    TraceAnalyticAdditiveHom object object :=
  fun sourceIndex targetIndex =>
    match Classical.decEq sourceIndex targetIndex with
    | isTrue indices_eq =>
        Eq.ndrec
          (TraceCorQHom.id (object.component sourceIndex))
          indices_eq
    | isFalse _ =>
        0

/-- An entry of the identity matrix is determined by equality of the two indices. -/
theorem TraceAnalyticAdditiveHom.id_entry
    (object : TraceAnalyticAdditiveObject)
    (sourceIndex targetIndex : Fin object.length) :
    (TraceAnalyticAdditiveHom.id object).entry sourceIndex targetIndex =
      match Classical.decEq sourceIndex targetIndex with
      | isTrue indices_eq =>
          Eq.ndrec
            (TraceCorQHom.id (object.component sourceIndex))
            indices_eq
      | isFalse _ =>
          0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
