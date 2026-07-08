import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.CompactCategory.Owner

/-!
# Top-root compact-category summaries

This file exposes compact-generator category and Q-linear trace-hom behavior
under the public analytic-motives root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public motive summary: compact-generator composition is trace-hom composition. -/
theorem AnalyticMotivesRoot.rootSummary_compactGenerator_comp_traceHom
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    (left ≫ right).traceHom =
      left.traceHom ≫ right.traceHom :=
  TraceAnalyticMotive.rootSummary_compactGenerator_comp_traceHom
    left
    right

/-- Public motive summary: compact-generator addition is trace-hom addition. -/
theorem AnalyticMotivesRoot.rootSummary_compactGenerator_add_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target) :
    (left + right).traceHom =
      left.traceHom + right.traceHom :=
  TraceAnalyticMotive.rootSummary_compactGenerator_add_traceHom
    left
    right

/-- Public motive summary: compact-generator trace subtraction from itself is zero. -/
theorem AnalyticMotivesRoot.rootSummary_compactGenerator_traceSub_self
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceCorQHom.sub morphism morphism =
      TraceCorQHom.zero source.traceObject target.traceObject :=
  TraceAnalyticMotive.rootSummary_compactGenerator_traceSub_self
    morphism

/-- Public motive summary: compact-generator trace subtraction detects equality. -/
theorem AnalyticMotivesRoot.rootSummary_compactGenerator_eq_of_traceSub_eq_zero
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target)
    (left_sub_right_eq_zero :
      TraceCorQHom.sub left right =
        TraceCorQHom.zero source.traceObject target.traceObject) :
    left = right :=
  TraceAnalyticMotive.rootSummary_compactGenerator_eq_of_traceSub_eq_zero
    left
    right
    left_sub_right_eq_zero

/-- Public motive summary: scalar multiplication distributes over compact-generator trace subtraction. -/
theorem AnalyticMotivesRoot.rootSummary_compactGenerator_traceSmul_sub
    {source target : TraceAnalyticGeometricGenerator}
    (coefficient : Rat)
    (left right : source ⟶ target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.sub left right) =
      TraceCorQHom.sub
        (TraceCorQHom.smul coefficient left)
        (TraceCorQHom.smul coefficient right) :=
  TraceAnalyticMotive.rootSummary_compactGenerator_traceSmul_sub
    coefficient
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
