import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Owner

/-!
# Public linearity laws for TraceCorQ composition

This file exposes the Q-linear compatibility laws for typed
trace-correspondence composition through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: composing the zero typed hom on the left gives zero. -/
theorem AnalyticMotivesRoot.traceCorQHom_zero_comp
    {source middle target : TraceCorQObject}
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.zero source middle)
      tail =
      TraceCorQHom.zero source target :=
  TraceCorQCategoryLinearity.zero_comp
    tail

/-- Public wrapper: composing the zero typed hom on the right gives zero. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_zero
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle) :
    TraceCorQHom.comp
      head
      (TraceCorQHom.zero middle target) =
      TraceCorQHom.zero source target :=
  TraceCorQCategoryLinearity.comp_zero
    head

/-- Public wrapper: composition is left-distributive over addition. -/
theorem AnalyticMotivesRoot.traceCorQHom_linearity_add_comp
    {source middle target : TraceCorQObject}
    (left right : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.add left right)
      tail =
      TraceCorQHom.add
        (TraceCorQHom.comp left tail)
        (TraceCorQHom.comp right tail) :=
  TraceCorQCategoryLinearity.add_comp
    left
    right
    tail

/-- Public wrapper: composition is right-distributive over addition. -/
theorem AnalyticMotivesRoot.traceCorQHom_linearity_comp_add
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (left right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      head
      (TraceCorQHom.add left right) =
      TraceCorQHom.add
        (TraceCorQHom.comp head left)
        (TraceCorQHom.comp head right) :=
  TraceCorQCategoryLinearity.comp_add
    head
    left
    right

/-- Public wrapper: scaling the left input scales composition. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_comp
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
  TraceCorQCategoryLinearity.smul_comp
    coefficient
    left
    right

/-- Public wrapper: scaling the right input scales composition. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_smul
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
  TraceCorQCategoryLinearity.comp_smul
    coefficient
    left
    right

/-- Public wrapper: negating the left input negates composition. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_comp
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.neg left)
      right =
      TraceCorQHom.neg
        (TraceCorQHom.comp left right) :=
  TraceCorQCategoryLinearity.neg_comp
    left
    right

/-- Public wrapper: negating the right input negates composition. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_neg
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      left
      (TraceCorQHom.neg right) =
      TraceCorQHom.neg
        (TraceCorQHom.comp left right) :=
  TraceCorQCategoryLinearity.comp_neg
    left
    right

/-- Public wrapper: composition is left-distributive over subtraction. -/
theorem AnalyticMotivesRoot.traceCorQHom_sub_comp
    {source middle target : TraceCorQObject}
    (left right : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.sub left right)
      tail =
      TraceCorQHom.sub
        (TraceCorQHom.comp left tail)
        (TraceCorQHom.comp right tail) :=
  TraceCorQCategoryLinearity.sub_comp
    left
    right
    tail

/-- Public wrapper: composition is right-distributive over subtraction. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_sub
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (left right : TraceCorQHom middle target) :
    TraceCorQHom.comp
      head
      (TraceCorQHom.sub left right) =
      TraceCorQHom.sub
        (TraceCorQHom.comp head left)
        (TraceCorQHom.comp head right) :=
  TraceCorQCategoryLinearity.comp_sub
    head
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
