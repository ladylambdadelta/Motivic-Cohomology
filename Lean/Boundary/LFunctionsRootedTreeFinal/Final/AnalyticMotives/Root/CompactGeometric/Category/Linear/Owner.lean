import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Category.Linear.Owner

/-!
# Top-root compact-generator linear wrappers

This file mirrors motive-root additive and rational-linear trace-hom formulas
under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root addition of compact-generator morphisms is addition of trace homs. -/
theorem AnalyticMotivesRoot.compactGenerator_add_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (left right : source ⟶ target) :
    (left + right).traceHom =
      left.traceHom + right.traceHom :=
  TraceAnalyticMotive.compactGenerator_add_traceHom
    left
    right

/-- Top-root rational scalar multiplication is inherited from trace homs. -/
theorem AnalyticMotivesRoot.compactGenerator_smul_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    (coefficient • morphism).traceHom =
      coefficient • morphism.traceHom :=
  TraceAnalyticMotive.compactGenerator_smul_traceHom
    coefficient
    morphism

/-- Top-root zero compact-generator morphism is the zero trace hom. -/
theorem AnalyticMotivesRoot.compactGenerator_zero_traceHom
    {source target : TraceAnalyticGeometricGenerator} :
    (0 : source ⟶ target).traceHom =
      (0 : source.traceObject ⟶ target.traceObject) :=
  TraceAnalyticMotive.compactGenerator_zero_traceHom

end AnalyticMotives
end LFunctions
end Boundary
