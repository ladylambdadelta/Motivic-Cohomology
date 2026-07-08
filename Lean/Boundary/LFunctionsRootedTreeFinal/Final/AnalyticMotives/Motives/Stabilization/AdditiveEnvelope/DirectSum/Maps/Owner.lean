import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Components.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Transport.Owner

/-!
# Direct-sum projection and inclusion matrices

Binary direct sums in the analytic additive envelope are concatenated finite
trace families.  Their projection and inclusion maps are sparse matrices with
transported identity entries on the matching summand coordinates and zero
entries elsewhere.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Projection from a binary direct sum to its left summand. -/
def TraceAnalyticAdditiveObject.leftDirectSumProjection
    (left right : TraceAnalyticAdditiveObject) :
    TraceAnalyticAdditiveHom
      (TraceAnalyticAdditiveObject.directSum left right)
      left :=
  fun sourceIndex targetIndex =>
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
        0

/-- Projection from a binary direct sum to its right summand. -/
def TraceAnalyticAdditiveObject.rightDirectSumProjection
    (left right : TraceAnalyticAdditiveObject) :
    TraceAnalyticAdditiveHom
      (TraceAnalyticAdditiveObject.directSum left right)
      right :=
  fun sourceIndex targetIndex =>
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
        0

/-- Inclusion of the left summand into a binary direct sum. -/
def TraceAnalyticAdditiveObject.leftDirectSumInclusion
    (left right : TraceAnalyticAdditiveObject) :
    TraceAnalyticAdditiveHom
      left
      (TraceAnalyticAdditiveObject.directSum left right) :=
  fun sourceIndex targetIndex =>
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
        0

/-- Inclusion of the right summand into a binary direct sum. -/
def TraceAnalyticAdditiveObject.rightDirectSumInclusion
    (left right : TraceAnalyticAdditiveObject) :
    TraceAnalyticAdditiveHom
      right
      (TraceAnalyticAdditiveObject.directSum left right) :=
  fun sourceIndex targetIndex =>
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
        0

end AnalyticMotives
end LFunctions
end Boundary
