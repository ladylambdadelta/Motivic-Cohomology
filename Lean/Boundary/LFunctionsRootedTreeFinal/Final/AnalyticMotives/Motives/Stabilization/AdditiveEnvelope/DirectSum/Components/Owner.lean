import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Indices.Owner

/-!
# Direct-sum components in the analytic additive envelope

This file exposes the concrete components of a concatenated finite trace family
at the left and right summand index embeddings.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The component of `left ++ right` at a left-summand index. -/
def TraceAnalyticAdditiveObject.leftDirectSumComponent
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin left.length) :
    TraceCorQObject :=
  (TraceAnalyticAdditiveObject.directSum left right).component
    (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index)

/-- The component of `left ++ right` at a right-summand index. -/
def TraceAnalyticAdditiveObject.rightDirectSumComponent
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin right.length) :
    TraceCorQObject :=
  (TraceAnalyticAdditiveObject.directSum left right).component
    (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index)

/-- The source-side comparison target for a left direct-sum component. -/
def TraceAnalyticAdditiveObject.leftDirectSumComponentTarget
    (left : TraceAnalyticAdditiveObject)
    (index : Fin left.length) :
    TraceCorQObject :=
  left.component index

/-- The source-side comparison target for a right direct-sum component. -/
def TraceAnalyticAdditiveObject.rightDirectSumComponentTarget
    (right : TraceAnalyticAdditiveObject)
    (index : Fin right.length) :
    TraceCorQObject :=
  right.component index

/-- The left direct-sum component is the direct-sum component at the left index embedding. -/
theorem TraceAnalyticAdditiveObject.leftDirectSumComponent_eq
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin left.length) :
    TraceAnalyticAdditiveObject.leftDirectSumComponent left right index =
      (TraceAnalyticAdditiveObject.directSum left right).component
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index) :=
  rfl

/-- The right direct-sum component is the direct-sum component at the right index embedding. -/
theorem TraceAnalyticAdditiveObject.rightDirectSumComponent_eq
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin right.length) :
    TraceAnalyticAdditiveObject.rightDirectSumComponent left right index =
      (TraceAnalyticAdditiveObject.directSum left right).component
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index) :=
  rfl

/-- A left embedded direct-sum component is the corresponding left component. -/
theorem TraceAnalyticAdditiveObject.leftDirectSumComponent_eq_target
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin left.length) :
    TraceAnalyticAdditiveObject.leftDirectSumComponent left right index =
      TraceAnalyticAdditiveObject.leftDirectSumComponentTarget left index :=
  List.getElem_append_left
    (l₁ := left)
    (l₂ := right)
    (i := index.val)
    index.isLt

/-- A right embedded direct-sum component is the corresponding right component. -/
theorem TraceAnalyticAdditiveObject.rightDirectSumComponent_eq_target
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin right.length) :
    TraceAnalyticAdditiveObject.rightDirectSumComponent left right index =
      TraceAnalyticAdditiveObject.rightDirectSumComponentTarget right index :=
  Eq.trans
    (List.getElem_append_right
      (l₁ := left)
      (l₂ := right)
      (i := left.length + index.val)
      (Nat.le_add_right left.length index.val))
    (congrArg
      (fun value =>
        right.get ⟨value, index.isLt⟩)
      (Nat.add_sub_cancel_left index.val left.length))

end AnalyticMotives
end LFunctions
end Boundary
