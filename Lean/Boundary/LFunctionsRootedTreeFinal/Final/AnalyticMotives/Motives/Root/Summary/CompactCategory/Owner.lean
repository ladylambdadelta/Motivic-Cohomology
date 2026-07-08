import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Owner

/-!
# Motive-root compact-category summaries

This file exposes root summary theorems for compact-generator category and
Q-linear trace-hom behavior.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root summary: compact-generator composition is trace-hom composition. -/
theorem TraceAnalyticMotive.rootSummary_compactGenerator_comp_traceHom
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    (left ≫ right).traceHom =
      left.traceHom ≫ right.traceHom :=
  TraceAnalyticMotive.compactGenerator_root_category_comp_traceHom
    left
    right

/-- Motive-root summary: compact-generator addition is trace-hom addition. -/
theorem TraceAnalyticMotive.rootSummary_compactGenerator_add_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target) :
    (left + right).traceHom =
      left.traceHom + right.traceHom :=
  TraceAnalyticMotive.compactGenerator_root_category_add_traceHom
    left
    right

/-- Motive-root summary: compact-generator trace subtraction from itself is zero. -/
theorem TraceAnalyticMotive.rootSummary_compactGenerator_traceSub_self
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceCorQHom.sub morphism morphism =
      TraceCorQHom.zero source.traceObject target.traceObject :=
  TraceAnalyticMotive.compactGenerator_root_category_traceSub_self_traceHom
    morphism

/-- Motive-root summary: compact-generator trace subtraction detects equality. -/
theorem TraceAnalyticMotive.rootSummary_compactGenerator_eq_of_traceSub_eq_zero
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target)
    (left_sub_right_eq_zero :
      TraceCorQHom.sub left right =
        TraceCorQHom.zero source.traceObject target.traceObject) :
    left = right :=
  TraceAnalyticMotive.compactGenerator_root_category_eq_of_traceSub_eq_zero
    left
    right
    left_sub_right_eq_zero

/-- Motive-root summary: scalar multiplication distributes over compact-generator trace subtraction. -/
theorem TraceAnalyticMotive.rootSummary_compactGenerator_traceSmul_sub
    {source target : TraceAnalyticGeometricGenerator}
    (coefficient : Rat)
    (left right : source ⟶ target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.sub left right) =
      TraceCorQHom.sub
        (TraceCorQHom.smul coefficient left)
        (TraceCorQHom.smul coefficient right) :=
  TraceAnalyticMotive.compactGenerator_root_category_traceSmul_sub
    coefficient
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
