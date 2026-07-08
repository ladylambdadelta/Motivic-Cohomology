import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Identity.Owner

/-!
# Entry lemmas for additive-envelope identity matrices

The concrete identity matrix has trace identities on the diagonal and zero
trace correspondences away from the diagonal.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A diagonal entry of the identity matrix is the identity trace correspondence. -/
theorem TraceAnalyticAdditiveHom.id_entry_self
    (object : TraceAnalyticAdditiveObject)
    (index : Fin object.length) :
    (TraceAnalyticAdditiveHom.id object).entry index index =
      TraceCorQHom.id (object.component index) :=
  by
    cases h : Classical.decEq index index with
    | isTrue indices_eq =>
        cases indices_eq
        rfl
    | isFalse indices_ne =>
        exact False.elim (indices_ne rfl)

/-- An off-diagonal entry of the identity matrix is zero. -/
theorem TraceAnalyticAdditiveHom.id_entry_ne
    (object : TraceAnalyticAdditiveObject)
    (sourceIndex targetIndex : Fin object.length)
    (indices_ne : sourceIndex ≠ targetIndex) :
    (TraceAnalyticAdditiveHom.id object).entry sourceIndex targetIndex =
      0 :=
  by
    cases h : Classical.decEq sourceIndex targetIndex with
    | isTrue indices_eq =>
        exact False.elim (indices_ne indices_eq)
    | isFalse _ =>
        rfl

end AnalyticMotives
end LFunctions
end Boundary
