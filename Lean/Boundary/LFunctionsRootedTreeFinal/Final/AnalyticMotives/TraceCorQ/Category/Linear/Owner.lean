import Mathlib.CategoryTheory.Linear.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Instance.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Instances.Algebraic.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Instances.Owner

/-!
# Preadditive and Q-linear structure on the trace-correspondence category

This file packages the fixed-endpoint hom algebra and bilinearity laws as
Mathlib's standard category-level `Preadditive` and `Linear Rat` instances.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The typed trace-correspondence category is preadditive. -/
instance traceCorQPreadditive :
    CategoryTheory.Preadditive TraceCorQObject where
  homGroup := fun source target =>
    traceCorQHomAddCommGroup
  add_comp := fun source middle target left right tail =>
    TraceCorQHom.std_add_comp left right tail
  comp_add := fun source middle target left right tail =>
    TraceCorQHom.std_comp_add left right tail

/-- The typed trace-correspondence category is rational-linear. -/
instance traceCorQLinearRat :
    CategoryTheory.Linear Rat TraceCorQObject where
  homModule := fun source target =>
    traceCorQHomRatModule
  smul_comp := fun source middle target coefficient left right =>
    TraceCorQHom.std_smul_comp coefficient left right
  comp_smul := fun source middle target left coefficient right =>
    TraceCorQHom.std_comp_smul coefficient left right

end AnalyticMotives
end LFunctions
end Boundary
