import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Linear.Owner

/-!
# Motive-root compact-generator linear wrappers

This file mirrors the additive and rational-linear trace-hom formulas for
compact geometric analytic generator morphisms under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root addition of compact-generator morphisms is addition of trace homs. -/
theorem TraceAnalyticMotive.compactGenerator_add_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target) :
    (left + right).traceHom =
      left.traceHom + right.traceHom :=
  TraceAnalyticGeometricGenerator.add_traceHom
    left
    right

/-- Motive-root rational scalar multiplication is inherited from trace homs. -/
theorem TraceAnalyticMotive.compactGenerator_smul_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    (coefficient • morphism).traceHom =
      coefficient • morphism.traceHom :=
  TraceAnalyticGeometricGenerator.smul_traceHom
    coefficient
    morphism

/-- Motive-root zero compact-generator morphism is the zero trace hom. -/
theorem TraceAnalyticMotive.compactGenerator_zero_traceHom
    {source target : TraceAnalyticGeometricGenerator} :
    (0 : source ⟶ target).traceHom =
      (0 : source.traceObject ⟶ target.traceObject) :=
  TraceAnalyticGeometricGenerator.zero_traceHom

/-- Motive-root explicit trace negation is inherited from typed trace homs. -/
theorem TraceAnalyticMotive.compactGenerator_traceNeg_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    (TraceCorQHom.neg morphism).traceHom =
      TraceCorQHom.neg morphism.traceHom :=
  TraceAnalyticGeometricGenerator.traceNeg_traceHom
    morphism

/-- Motive-root explicit trace subtraction is inherited from typed trace homs. -/
theorem TraceAnalyticMotive.compactGenerator_traceSub_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target) :
    (TraceCorQHom.sub left right).traceHom =
      TraceCorQHom.sub left.traceHom right.traceHom :=
  TraceAnalyticGeometricGenerator.traceSub_traceHom
    left
    right

/-- Motive-root explicit trace subtraction of a compact-generator morphism from itself is zero. -/
theorem TraceAnalyticMotive.compactGenerator_traceSub_self_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceCorQHom.sub morphism morphism =
      TraceCorQHom.zero source.traceObject target.traceObject :=
  TraceAnalyticGeometricGenerator.traceSub_self_traceHom
    morphism

/-- Motive-root explicit trace subtraction detects equality of compact-generator morphisms. -/
theorem TraceAnalyticMotive.compactGenerator_eq_of_traceSub_eq_zero
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target)
    (left_sub_right_eq_zero :
      TraceCorQHom.sub left right =
        TraceCorQHom.zero source.traceObject target.traceObject) :
    left = right :=
  TraceAnalyticGeometricGenerator.eq_of_traceSub_eq_zero
    left
    right
    left_sub_right_eq_zero

/-- Motive-root scalar multiplication distributes over explicit trace subtraction. -/
theorem TraceAnalyticMotive.compactGenerator_traceSmul_sub
    {source target : TraceAnalyticGeometricGenerator}
    (coefficient : Rat)
    (left right : source ⟶ target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.sub left right) =
      TraceCorQHom.sub
        (TraceCorQHom.smul coefficient left)
        (TraceCorQHom.smul coefficient right) :=
  TraceAnalyticGeometricGenerator.traceSmul_sub
    coefficient
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
