import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Instances.Laws.Algebra.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Sub.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Zero.Owner

/-!
# Standard-notation composition linearity laws

This file restates the proved typed composition linearity laws using the
standard operation notation on typed homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Standard typed composition annihilates a zero left input. -/
theorem TraceCorQHom.std_zero_comp
    {source middle target : TraceCorQObject}
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (0 : TraceCorQHom source middle)
      tail =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.zero_comp source tail

/-- Standard typed composition annihilates a zero right input. -/
theorem TraceCorQHom.std_comp_zero
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle) :
    TraceCorQHom.comp
      left
      (0 : TraceCorQHom middle target) =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.comp_zero left target

/-- Standard typed composition is left-distributive over standard addition. -/
theorem TraceCorQHom.std_add_comp
    {source middle target : TraceCorQObject}
    (left right : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp (left + right) tail =
      TraceCorQHom.comp left tail +
        TraceCorQHom.comp right tail :=
  TraceCorQHom.add_comp left right tail

/-- Standard typed composition is right-distributive over standard addition. -/
theorem TraceCorQHom.std_comp_add
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right tail : TraceCorQHom middle target) :
    TraceCorQHom.comp left (right + tail) =
      TraceCorQHom.comp left right +
        TraceCorQHom.comp left tail :=
  TraceCorQHom.comp_add left right tail

/-- Scaling the left standard typed input scales typed composition. -/
theorem TraceCorQHom.std_smul_comp
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp (coefficient • left) right =
      coefficient • TraceCorQHom.comp left right :=
  TraceCorQHom.smul_comp coefficient left right

/-- Scaling the right standard typed input scales typed composition. -/
theorem TraceCorQHom.std_comp_smul
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp left (coefficient • right) =
      coefficient • TraceCorQHom.comp left right :=
  TraceCorQHom.comp_smul coefficient left right

/-- Standard typed composition is left-distributive over subtraction. -/
theorem TraceCorQHom.std_sub_comp
    {source middle target : TraceCorQObject}
    (left right : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp (left - right) tail =
      TraceCorQHom.comp left tail -
        TraceCorQHom.comp right tail :=
  TraceCorQHom.sub_comp left right tail

/-- Standard typed composition is right-distributive over subtraction. -/
theorem TraceCorQHom.std_comp_sub
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right tail : TraceCorQHom middle target) :
    TraceCorQHom.comp left (right - tail) =
      TraceCorQHom.comp left right -
        TraceCorQHom.comp left tail :=
  TraceCorQHom.comp_sub left right tail

/-- Negating the left standard typed input negates typed composition. -/
theorem TraceCorQHom.std_neg_comp
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp (-left) right =
      -TraceCorQHom.comp left right :=
  TraceCorQHom.neg_comp left right

/-- Negating the right standard typed input negates typed composition. -/
theorem TraceCorQHom.std_comp_neg
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp left (-right) =
      -TraceCorQHom.comp left right :=
  TraceCorQHom.comp_neg left right

end AnalyticMotives
end LFunctions
end Boundary
