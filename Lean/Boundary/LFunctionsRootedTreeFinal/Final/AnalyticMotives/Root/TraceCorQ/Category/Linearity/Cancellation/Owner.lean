import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Add.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Sub.Cancellation.Owner

/-!
# Public cancellation solvers for TraceCorQ composition

This file exposes additive and subtractive composition solver laws through the
public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: postcomposition preserves an additive decomposition. -/
theorem AnalyticMotivesRoot.traceCorQHom_add_comp_eq_of_add_eq
    {source middle target : TraceCorQObject}
    (left right delta : TraceCorQHom source middle)
    (post : TraceCorQHom middle target)
    (left_eq_right_add_delta :
      left = TraceCorQHom.add right delta) :
    TraceCorQHom.comp left post =
      TraceCorQHom.add
        (TraceCorQHom.comp right post)
        (TraceCorQHom.comp delta post) :=
  TraceCorQHom.add_comp_eq_of_add_eq
    left
    right
    delta
    post
    left_eq_right_add_delta

/-- Public wrapper: precomposition preserves an additive decomposition. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_add_eq_of_add_eq
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (left right delta : TraceCorQHom middle target)
    (left_eq_right_add_delta :
      left = TraceCorQHom.add right delta) :
    TraceCorQHom.comp pre left =
      TraceCorQHom.add
        (TraceCorQHom.comp pre right)
        (TraceCorQHom.comp pre delta) :=
  TraceCorQHom.comp_add_eq_of_add_eq
    pre
    left
    right
    delta
    left_eq_right_add_delta

/-- Public wrapper: solve a postcomposed additive decomposition as a subtraction. -/
theorem AnalyticMotivesRoot.traceCorQHom_sub_comp_eq_of_comp_add_eq
    {source middle target : TraceCorQObject}
    (left right delta : TraceCorQHom source middle)
    (post : TraceCorQHom middle target)
    (left_comp_eq_right_comp_add_delta_comp :
      TraceCorQHom.comp left post =
        TraceCorQHom.add
          (TraceCorQHom.comp right post)
          (TraceCorQHom.comp delta post)) :
    TraceCorQHom.sub
      (TraceCorQHom.comp left post)
      (TraceCorQHom.comp right post) =
      TraceCorQHom.comp delta post :=
  TraceCorQHom.sub_comp_eq_of_comp_add_eq
    left
    right
    delta
    post
    left_comp_eq_right_comp_add_delta_comp

/-- Public wrapper: solve a precomposed additive decomposition as a subtraction. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_sub_eq_of_comp_add_eq
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (left right delta : TraceCorQHom middle target)
    (pre_comp_left_eq_pre_comp_right_add_pre_comp_delta :
      TraceCorQHom.comp pre left =
        TraceCorQHom.add
          (TraceCorQHom.comp pre right)
          (TraceCorQHom.comp pre delta)) :
    TraceCorQHom.sub
      (TraceCorQHom.comp pre left)
      (TraceCorQHom.comp pre right) =
      TraceCorQHom.comp pre delta :=
  TraceCorQHom.comp_sub_eq_of_comp_add_eq
    pre
    left
    right
    delta
    pre_comp_left_eq_pre_comp_right_add_pre_comp_delta

/-- Public wrapper: compose on the right with a subtraction and solve from an additive decomposition. -/
theorem AnalyticMotivesRoot.traceCorQHom_sub_comp_eq_of_add_eq
    {source middle target : TraceCorQObject}
    (left right delta : TraceCorQHom source middle)
    (post : TraceCorQHom middle target)
    (left_eq_right_add_delta :
      left = TraceCorQHom.add right delta) :
    TraceCorQHom.comp
      (TraceCorQHom.sub left right)
      post =
      TraceCorQHom.comp delta post :=
  TraceCorQHom.sub_comp_eq_of_add_eq
    left
    right
    delta
    post
    left_eq_right_add_delta

/-- Public wrapper: compose on the left with a subtraction and solve from an additive decomposition. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_sub_eq_of_add_eq
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (left right delta : TraceCorQHom middle target)
    (left_eq_right_add_delta :
      left = TraceCorQHom.add right delta) :
    TraceCorQHom.comp
      pre
      (TraceCorQHom.sub left right) =
      TraceCorQHom.comp pre delta :=
  TraceCorQHom.comp_sub_eq_of_add_eq
    pre
    left
    right
    delta
    left_eq_right_add_delta

/-- Public wrapper: rebuild right-composed addition from a solved subtraction. -/
theorem AnalyticMotivesRoot.traceCorQHom_add_comp_eq_of_sub_comp_eq
    {source middle target : TraceCorQObject}
    (left right delta : TraceCorQHom source middle)
    (post : TraceCorQHom middle target)
    (left_sub_right_comp_eq_delta_comp :
      TraceCorQHom.comp
        (TraceCorQHom.sub left right)
        post =
        TraceCorQHom.comp delta post) :
    TraceCorQHom.comp left post =
      TraceCorQHom.add
        (TraceCorQHom.comp right post)
        (TraceCorQHom.comp delta post) :=
  TraceCorQHom.add_comp_eq_of_sub_comp_eq
    left
    right
    delta
    post
    left_sub_right_comp_eq_delta_comp

/-- Public wrapper: rebuild left-composed addition from a solved subtraction. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_add_eq_of_comp_sub_eq
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (left right delta : TraceCorQHom middle target)
    (pre_comp_left_sub_right_eq_pre_comp_delta :
      TraceCorQHom.comp
        pre
        (TraceCorQHom.sub left right) =
        TraceCorQHom.comp pre delta) :
    TraceCorQHom.comp pre left =
      TraceCorQHom.add
        (TraceCorQHom.comp pre right)
        (TraceCorQHom.comp pre delta) :=
  TraceCorQHom.comp_add_eq_of_comp_sub_eq
    pre
    left
    right
    delta
    pre_comp_left_sub_right_eq_pre_comp_delta

/-- Public wrapper: zero postcomposition of a subtraction detects equality after postcomposition. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_eq_of_sub_comp_eq_zero
    {source middle target : TraceCorQObject}
    (left right : TraceCorQHom source middle)
    (post : TraceCorQHom middle target)
    (left_sub_right_comp_eq_zero :
      TraceCorQHom.comp
        (TraceCorQHom.sub left right)
        post =
        TraceCorQHom.zero source target) :
    TraceCorQHom.comp left post =
      TraceCorQHom.comp right post :=
  TraceCorQHom.comp_eq_of_sub_comp_eq_zero
    left
    right
    post
    left_sub_right_comp_eq_zero

/-- Public wrapper: zero precomposition of a subtraction detects equality after precomposition. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_eq_of_comp_sub_eq_zero
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (left right : TraceCorQHom middle target)
    (pre_comp_left_sub_right_eq_zero :
      TraceCorQHom.comp
        pre
        (TraceCorQHom.sub left right) =
        TraceCorQHom.zero source target) :
    TraceCorQHom.comp pre left =
      TraceCorQHom.comp pre right :=
  TraceCorQHom.comp_eq_of_comp_sub_eq_zero
    pre
    left
    right
    pre_comp_left_sub_right_eq_zero

/-- Public wrapper: equality after postcomposition gives zero postcomposition of the subtraction. -/
theorem AnalyticMotivesRoot.traceCorQHom_sub_comp_eq_zero_of_comp_eq
    {source middle target : TraceCorQObject}
    (left right : TraceCorQHom source middle)
    (post : TraceCorQHom middle target)
    (left_comp_post_eq_right_comp_post :
      TraceCorQHom.comp left post =
        TraceCorQHom.comp right post) :
    TraceCorQHom.comp
      (TraceCorQHom.sub left right)
      post =
      TraceCorQHom.zero source target :=
  TraceCorQHom.sub_comp_eq_zero_of_comp_eq
    left
    right
    post
    left_comp_post_eq_right_comp_post

/-- Public wrapper: equality after precomposition gives zero precomposition of the subtraction. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_sub_eq_zero_of_comp_eq
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (left right : TraceCorQHom middle target)
    (pre_comp_left_eq_pre_comp_right :
      TraceCorQHom.comp pre left =
        TraceCorQHom.comp pre right) :
    TraceCorQHom.comp
      pre
      (TraceCorQHom.sub left right) =
      TraceCorQHom.zero source target :=
  TraceCorQHom.comp_sub_eq_zero_of_comp_eq
    pre
    left
    right
    pre_comp_left_eq_pre_comp_right

end AnalyticMotives
end LFunctions
end Boundary
