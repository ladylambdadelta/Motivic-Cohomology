import Mathlib.CategoryTheory.Linear.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Instance.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Linear.Standard.Owner

/-!
# Preadditive and Q-linear additive-envelope category structure

The concrete matrix category on finite trace families inherits additive
commutative groups and rational modules on homs entrywise, and composition is
bilinear by the finite-sum trace calculus.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic additive-envelope category is preadditive. -/
instance traceAnalyticAdditivePreadditive :
    CategoryTheory.Preadditive TraceAnalyticAdditiveCategoryObject where
  homGroup := fun source target =>
    TraceAnalyticAdditiveCategory.addCommGroupStructure source target
  add_comp := fun source middle target left right tail =>
    TraceAnalyticAdditiveCategory.std_add_comp left right tail
  comp_add := fun source middle target head left right =>
    TraceAnalyticAdditiveCategory.std_comp_add head left right

/-- The analytic additive-envelope category is rational-linear. -/
instance traceAnalyticAdditiveLinearRat :
    CategoryTheory.Linear Rat TraceAnalyticAdditiveCategoryObject where
  homModule := fun source target =>
    TraceAnalyticAdditiveCategory.ratModuleStructure source target
  smul_comp := fun source middle target coefficient left right =>
    TraceAnalyticAdditiveCategory.std_smul_comp coefficient left right
  comp_smul := fun source middle target left coefficient right =>
    TraceAnalyticAdditiveCategory.std_comp_smul coefficient left right

end AnalyticMotives
end LFunctions
end Boundary
