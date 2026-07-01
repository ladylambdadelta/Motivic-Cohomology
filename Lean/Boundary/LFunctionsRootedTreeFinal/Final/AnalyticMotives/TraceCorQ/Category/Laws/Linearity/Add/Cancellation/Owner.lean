import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Add.Owner

/-!
# Cancellation solvers for additive composition linearity

This file collects typed composition solver laws derived from additive
linearity of composition and typed hom subtraction cancellation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Postcomposition preserves an additive decomposition. -/
theorem TraceCorQHom.add_comp_eq_of_add_eq
    {source middle target : TraceCorQObject}
    (left right delta : TraceCorQHom source middle)
    (post : TraceCorQHom middle target)
    (left_eq_right_add_delta :
      left = TraceCorQHom.add right delta) :
    TraceCorQHom.comp left post =
      TraceCorQHom.add
        (TraceCorQHom.comp right post)
        (TraceCorQHom.comp delta post) :=
  Eq.trans
    (congrArg
      (fun leftHom =>
        TraceCorQHom.comp leftHom post)
      left_eq_right_add_delta)
    (TraceCorQHom.add_comp right delta post)

/-- Precomposition preserves an additive decomposition. -/
theorem TraceCorQHom.comp_add_eq_of_add_eq
    {source middle target : TraceCorQObject}
    (pre : TraceCorQHom source middle)
    (left right delta : TraceCorQHom middle target)
    (left_eq_right_add_delta :
      left = TraceCorQHom.add right delta) :
    TraceCorQHom.comp pre left =
      TraceCorQHom.add
        (TraceCorQHom.comp pre right)
        (TraceCorQHom.comp pre delta) :=
  Eq.trans
    (congrArg
      (TraceCorQHom.comp pre)
      left_eq_right_add_delta)
    (TraceCorQHom.comp_add pre right delta)

/-- Solve a postcomposed additive decomposition as a subtraction. -/
theorem TraceCorQHom.sub_comp_eq_of_comp_add_eq
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
  TraceCorQHom.sub_eq_of_add_eq
    (TraceCorQHom.comp left post)
    (TraceCorQHom.comp right post)
    (TraceCorQHom.comp delta post)
    left_comp_eq_right_comp_add_delta_comp

/-- Solve a precomposed additive decomposition as a subtraction. -/
theorem TraceCorQHom.comp_sub_eq_of_comp_add_eq
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
  TraceCorQHom.sub_eq_of_add_eq
    (TraceCorQHom.comp pre left)
    (TraceCorQHom.comp pre right)
    (TraceCorQHom.comp pre delta)
    pre_comp_left_eq_pre_comp_right_add_pre_comp_delta

end AnalyticMotives
end LFunctions
end Boundary
