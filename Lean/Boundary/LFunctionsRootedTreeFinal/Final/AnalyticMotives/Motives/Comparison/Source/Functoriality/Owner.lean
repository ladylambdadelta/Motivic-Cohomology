import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Functoriality.Owner

/-!
# Functoriality of represented comparison-source morphisms

The analytic comparison source is the stable analytic Verdier quotient under
comparison-source names.  This file exposes the represented-morphism identity,
composition, and zero-composite formulas at that comparison layer.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The represented comparison-source morphism of an identity additive-homotopy
morphism is the identity comparison-source morphism. -/
theorem TraceAnalyticDMgmComparisonSource.mapOf_id
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticDMgmComparisonSource.mapOf
        (𝟙 object : object ⟶ object) =
      𝟙 (TraceAnalyticDMgmComparisonSource.objectOf object) :=
  TraceAnalyticStableMotiveCategory.mapOf_id object

/-- The represented comparison-source morphism of a composite
additive-homotopy morphism is the composite of the represented
comparison-source morphisms. -/
theorem TraceAnalyticDMgmComparisonSource.mapOf_comp
    {first second third : TraceAnalyticAdditiveHomotopyCategory}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticDMgmComparisonSource.mapOf (left ≫ right) =
      TraceAnalyticDMgmComparisonSource.mapOf left ≫
        TraceAnalyticDMgmComparisonSource.mapOf right :=
  TraceAnalyticStableMotiveCategory.mapOf_comp left right

/-- If a composite additive-homotopy morphism is zero, then the composite of
the represented comparison-source morphisms is zero. -/
theorem TraceAnalyticDMgmComparisonSource.mapOf_comp_eq_zero_of_comp_eq_zero
    {first second third : TraceAnalyticAdditiveHomotopyCategory}
    (left : first ⟶ second)
    (right : second ⟶ third)
    (vanishing : left ≫ right = 0) :
    TraceAnalyticDMgmComparisonSource.mapOf left ≫
        TraceAnalyticDMgmComparisonSource.mapOf right =
      0 :=
  TraceAnalyticStableMotiveCategory.mapOf_comp_eq_zero_of_comp_eq_zero
    left
    right
    vanishing

end AnalyticMotives
end LFunctions
end Boundary
