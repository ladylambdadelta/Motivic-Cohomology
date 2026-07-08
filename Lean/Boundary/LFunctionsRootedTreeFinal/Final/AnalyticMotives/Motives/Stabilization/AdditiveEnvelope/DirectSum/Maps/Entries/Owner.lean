import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Maps.Owner

/-!
# Entry formulas for direct-sum projection and inclusion matrices

This file exposes the definitional entry formulas for the sparse direct-sum
projection and inclusion matrices.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Entry formula for the left direct-sum projection. -/
theorem TraceAnalyticAdditiveObject.leftDirectSumProjection_entry
    (left right : TraceAnalyticAdditiveObject)
    (sourceIndex : Fin (TraceAnalyticAdditiveObject.directSum left right).length)
    (targetIndex : Fin left.length) :
    (TraceAnalyticAdditiveObject.leftDirectSumProjection left right).entry
        sourceIndex
        targetIndex =
      match Classical.decEq sourceIndex
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex) with
      | isTrue source_eq =>
          TraceAnalyticAdditiveHom.transportedId
            (Eq.trans
              (congrArg
                (fun index =>
                  (TraceAnalyticAdditiveObject.directSum left right).component index)
                source_eq)
              (TraceAnalyticAdditiveObject.leftDirectSumComponent_eq_target
                left
                right
                targetIndex))
      | isFalse _ =>
          0 :=
  rfl

/-- Entry formula for the right direct-sum projection. -/
theorem TraceAnalyticAdditiveObject.rightDirectSumProjection_entry
    (left right : TraceAnalyticAdditiveObject)
    (sourceIndex : Fin (TraceAnalyticAdditiveObject.directSum left right).length)
    (targetIndex : Fin right.length) :
    (TraceAnalyticAdditiveObject.rightDirectSumProjection left right).entry
        sourceIndex
        targetIndex =
      match Classical.decEq sourceIndex
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex) with
      | isTrue source_eq =>
          TraceAnalyticAdditiveHom.transportedId
            (Eq.trans
              (congrArg
                (fun index =>
                  (TraceAnalyticAdditiveObject.directSum left right).component index)
                source_eq)
              (TraceAnalyticAdditiveObject.rightDirectSumComponent_eq_target
                left
                right
                targetIndex))
      | isFalse _ =>
          0 :=
  rfl

/-- Entry formula for the left direct-sum inclusion. -/
theorem TraceAnalyticAdditiveObject.leftDirectSumInclusion_entry
    (left right : TraceAnalyticAdditiveObject)
    (sourceIndex : Fin left.length)
    (targetIndex : Fin (TraceAnalyticAdditiveObject.directSum left right).length) :
    (TraceAnalyticAdditiveObject.leftDirectSumInclusion left right).entry
        sourceIndex
        targetIndex =
      match Classical.decEq targetIndex
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex) with
      | isTrue target_eq =>
          TraceAnalyticAdditiveHom.transportedId
            (Eq.symm
              (Eq.trans
                (congrArg
                  (fun index =>
                    (TraceAnalyticAdditiveObject.directSum left right).component index)
                  target_eq)
                (TraceAnalyticAdditiveObject.leftDirectSumComponent_eq_target
                  left
                  right
                  sourceIndex)))
      | isFalse _ =>
          0 :=
  rfl

/-- Entry formula for the right direct-sum inclusion. -/
theorem TraceAnalyticAdditiveObject.rightDirectSumInclusion_entry
    (left right : TraceAnalyticAdditiveObject)
    (sourceIndex : Fin right.length)
    (targetIndex : Fin (TraceAnalyticAdditiveObject.directSum left right).length) :
    (TraceAnalyticAdditiveObject.rightDirectSumInclusion left right).entry
        sourceIndex
        targetIndex =
      match Classical.decEq targetIndex
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex) with
      | isTrue target_eq =>
          TraceAnalyticAdditiveHom.transportedId
            (Eq.symm
              (Eq.trans
                (congrArg
                  (fun index =>
                    (TraceAnalyticAdditiveObject.directSum left right).component index)
                  target_eq)
                (TraceAnalyticAdditiveObject.rightDirectSumComponent_eq_target
                  left
                  right
                  sourceIndex)))
      | isFalse _ =>
          0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
