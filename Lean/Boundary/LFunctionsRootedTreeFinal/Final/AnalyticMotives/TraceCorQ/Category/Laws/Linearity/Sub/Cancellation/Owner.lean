import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Sub.Owner

/-!
# Cancellation solvers for subtractive composition linearity

This file collects typed composition solver laws derived from subtractive
linearity of composition and typed hom subtraction cancellation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compose on the right with a subtraction and solve from an additive decomposition. -/
theorem TraceCorQHom.sub_comp_eq_of_add_eq
    {source middle target : TraceCorQObject}
    (left right delta : TraceCorQHom source middle)
    (post : TraceCorQHom middle target)
    (left_eq_right_add_delta :
      left = TraceCorQHom.add right delta) :
    TraceCorQHom.comp
      (TraceCorQHom.sub left right)
      post =
      TraceCorQHom.comp delta post :=
  Eq.trans
    (TraceCorQHom.sub_comp left right post)
    (TraceCorQHom.sub_eq_of_add_eq
      (TraceCorQHom.comp left post)
      (TraceCorQHom.comp right post)
      (TraceCorQHom.comp delta post)
      (Eq.trans
        (congrArg
          (fun leftHom =>
            TraceCorQHom.comp leftHom post)
          left_eq_right_add_delta)
        (Eq.trans
          (TraceCorQHom.add_comp right delta post)
          (TraceCorQHom.add_comm
            (TraceCorQHom.comp right post)
            (TraceCorQHom.comp delta post)))))

/-- Compose on the left with a subtraction and solve from an additive decomposition. -/
theorem TraceCorQHom.comp_sub_eq_of_add_eq
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (left right delta : TraceCorQHom middle target)
    (left_eq_right_add_delta :
      left = TraceCorQHom.add right delta) :
    TraceCorQHom.comp
      pre
      (TraceCorQHom.sub left right) =
      TraceCorQHom.comp pre delta :=
  Eq.trans
    (TraceCorQHom.comp_sub pre left right)
    (TraceCorQHom.sub_eq_of_add_eq
      (TraceCorQHom.comp pre left)
      (TraceCorQHom.comp pre right)
      (TraceCorQHom.comp pre delta)
      (Eq.trans
        (congrArg
          (TraceCorQHom.comp pre)
          left_eq_right_add_delta)
        (Eq.trans
          (TraceCorQHom.comp_add pre right delta)
          (TraceCorQHom.add_comm
            (TraceCorQHom.comp pre right)
            (TraceCorQHom.comp pre delta)))))

/-- Rebuild right-composed addition from a solved subtraction. -/
theorem TraceCorQHom.add_comp_eq_of_sub_comp_eq
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
  Eq.symm
    (TraceCorQHom.add_eq_of_right_eq_sub
      (TraceCorQHom.comp right post)
      (TraceCorQHom.comp delta post)
      (TraceCorQHom.comp left post)
      (Eq.trans
        (Eq.symm left_sub_right_comp_eq_delta_comp)
        (TraceCorQHom.sub_comp left right post)))

/-- Rebuild left-composed addition from a solved subtraction. -/
theorem TraceCorQHom.comp_add_eq_of_comp_sub_eq
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
  Eq.symm
    (TraceCorQHom.add_eq_of_right_eq_sub
      (TraceCorQHom.comp pre right)
      (TraceCorQHom.comp pre delta)
      (TraceCorQHom.comp pre left)
      (Eq.trans
        (Eq.symm pre_comp_left_sub_right_eq_pre_comp_delta)
        (TraceCorQHom.comp_sub pre left right)))

/-- Zero postcomposition of a subtraction detects equality after postcomposition. -/
theorem TraceCorQHom.comp_eq_of_sub_comp_eq_zero
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
  TraceCorQHom.eq_of_sub_eq_zero
    (TraceCorQHom.comp left post)
    (TraceCorQHom.comp right post)
    (Eq.trans
      (Eq.symm (TraceCorQHom.sub_comp left right post))
      left_sub_right_comp_eq_zero)

/-- Zero precomposition of a subtraction detects equality after precomposition. -/
theorem TraceCorQHom.comp_eq_of_comp_sub_eq_zero
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
  TraceCorQHom.eq_of_sub_eq_zero
    (TraceCorQHom.comp pre left)
    (TraceCorQHom.comp pre right)
    (Eq.trans
      (Eq.symm (TraceCorQHom.comp_sub pre left right))
      pre_comp_left_sub_right_eq_zero)

/-- Equality after postcomposition gives zero postcomposition of the subtraction. -/
theorem TraceCorQHom.sub_comp_eq_zero_of_comp_eq
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
  Eq.trans
    (TraceCorQHom.sub_comp left right post)
    (TraceCorQHom.sub_eq_zero_of_eq
      (TraceCorQHom.comp left post)
      (TraceCorQHom.comp right post)
      left_comp_post_eq_right_comp_post)

/-- Equality after precomposition gives zero precomposition of the subtraction. -/
theorem TraceCorQHom.comp_sub_eq_zero_of_comp_eq
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
  Eq.trans
    (TraceCorQHom.comp_sub pre left right)
    (TraceCorQHom.sub_eq_zero_of_eq
      (TraceCorQHom.comp pre left)
      (TraceCorQHom.comp pre right)
      pre_comp_left_eq_pre_comp_right)

end AnalyticMotives
end LFunctions
end Boundary
