import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Preadditive.Owner

/-!
# Preadditivity of the analytic comparison source

The analytic comparison source is the stable analytic Verdier quotient.  This
file exposes the inherited preadditive structure and quotient-functor
additivity under comparison-source names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The analytic comparison source is preadditive. -/
def TraceAnalyticDMgmComparisonSource.preadditiveStructure :
    Preadditive TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticStableMotiveCategory.preadditiveStructure

/-- The comparison-source quotient functor is additive. -/
def TraceAnalyticDMgmComparisonSource.quotientFunctorAdditive :
    TraceAnalyticDMgmComparisonSource.quotientFunctor.Additive :=
  TraceAnalyticStableMotiveCategory.quotientFunctorAdditive

/-- The comparison-source preadditive structure is the stable analytic
preadditive structure. -/
theorem TraceAnalyticDMgmComparisonSource.preadditiveStructure_eq_stable :
    TraceAnalyticDMgmComparisonSource.preadditiveStructure =
      TraceAnalyticStableMotiveCategory.preadditiveStructure :=
  rfl

/-- The comparison-source quotient-functor additivity is the stable analytic
quotient-functor additivity. -/
theorem TraceAnalyticDMgmComparisonSource.quotientFunctorAdditive_eq_stable :
    TraceAnalyticDMgmComparisonSource.quotientFunctorAdditive =
      TraceAnalyticStableMotiveCategory.quotientFunctorAdditive :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
