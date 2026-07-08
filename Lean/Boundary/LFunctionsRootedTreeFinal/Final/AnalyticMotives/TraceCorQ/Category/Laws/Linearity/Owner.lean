import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Add.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Smul.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Sub.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Sub.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Zero.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Instances.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.FiniteSums.Owner

/-!
# Linearity laws for typed trace-correspondence composition

This file re-exports the typed composition laws showing compatibility with
addition, finite sums, scalar multiplication, subtraction, sign normalization,
and zero morphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Linearity aggregate: composing the zero typed hom on the left gives zero. -/
theorem TraceCorQCategoryLinearity.zero_comp
    {source middle target : TraceCorQObject}
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.zero source middle)
      tail =
      TraceCorQHom.zero source target :=
  TraceCorQHom.zero_comp
    tail

/-- Linearity aggregate: composing the zero typed hom on the right gives zero. -/
theorem TraceCorQCategoryLinearity.comp_zero
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle) :
    TraceCorQHom.comp
      head
      (TraceCorQHom.zero middle target) =
      TraceCorQHom.zero source target :=
  TraceCorQHom.comp_zero
    head

/-- Linearity aggregate: composition is left-distributive over addition. -/
theorem TraceCorQCategoryLinearity.add_comp
    {source middle target : TraceCorQObject}
    (left right : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.add left right)
      tail =
      TraceCorQHom.add
        (TraceCorQHom.comp left tail)
        (TraceCorQHom.comp right tail) :=
  TraceCorQHom.add_comp
    left
    right
    tail

/-- Linearity aggregate: composition is right-distributive over addition. -/
theorem TraceCorQCategoryLinearity.comp_add
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (left right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      head
      (TraceCorQHom.add left right) =
      TraceCorQHom.add
        (TraceCorQHom.comp head left)
        (TraceCorQHom.comp head right) :=
  TraceCorQHom.comp_add
    head
    left
    right

/-- Linearity aggregate: scaling the left input scales composition. -/
theorem TraceCorQCategoryLinearity.smul_comp
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.smul coefficient left)
      right =
      TraceCorQHom.smul
        coefficient
        (TraceCorQHom.comp left right) :=
  TraceCorQHom.smul_comp
    coefficient
    left
    right

/-- Linearity aggregate: scaling the right input scales composition. -/
theorem TraceCorQCategoryLinearity.comp_smul
    {source middle target : TraceCorQObject}
    (coefficient : Rat)
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      left
      (TraceCorQHom.smul coefficient right) =
      TraceCorQHom.smul
        coefficient
        (TraceCorQHom.comp left right) :=
  TraceCorQHom.comp_smul
    coefficient
    left
    right

/-- Linearity aggregate: negating the left input negates composition. -/
theorem TraceCorQCategoryLinearity.neg_comp
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.neg left)
      right =
      TraceCorQHom.neg
        (TraceCorQHom.comp left right) :=
  TraceCorQHom.neg_comp
    left
    right

/-- Linearity aggregate: negating the right input negates composition. -/
theorem TraceCorQCategoryLinearity.comp_neg
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      left
      (TraceCorQHom.neg right) =
      TraceCorQHom.neg
        (TraceCorQHom.comp left right) :=
  TraceCorQHom.comp_neg
    left
    right

/-- Linearity aggregate: composition is left-distributive over subtraction. -/
theorem TraceCorQCategoryLinearity.sub_comp
    {source middle target : TraceCorQObject}
    (left right : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.sub left right)
      tail =
      TraceCorQHom.sub
        (TraceCorQHom.comp left tail)
        (TraceCorQHom.comp right tail) :=
  TraceCorQHom.sub_comp
    left
    right
    tail

/-- Linearity aggregate: composition is right-distributive over subtraction. -/
theorem TraceCorQCategoryLinearity.comp_sub
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (left right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      head
      (TraceCorQHom.sub left right) =
      TraceCorQHom.sub
        (TraceCorQHom.comp head left)
        (TraceCorQHom.comp head right) :=
  TraceCorQHom.comp_sub
    head
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
