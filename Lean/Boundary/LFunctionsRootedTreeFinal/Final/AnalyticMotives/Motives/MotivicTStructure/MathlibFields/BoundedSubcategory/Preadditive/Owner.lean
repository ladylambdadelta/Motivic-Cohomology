import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Preadditive.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.Owner

/-!
# Preadditivity of the bounded stable source

The bounded stable source is a full subcategory of the preadditive analytic
comparison source.  This file exposes the inherited preadditive structure and
the additivity of the bounded inclusion under bounded-source names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The bounded stable source inherits preadditivity from the analytic
comparison source. -/
def preadditiveStructure :
    Preadditive TraceAnalyticDMgmComparisonSource.BoundedStable :=
  inferInstance

/-- The bounded stable source inclusion is additive. -/
def inclusionAdditive :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.Additive :=
  inferInstance

/-- The additive structure on bounded morphisms is the ambient additive
structure on the corresponding comparison-source morphisms. -/
theorem hom_add_eq_ambient
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (first second : source ⟶ target) :
    (first + second : source ⟶ target) =
      (first + second : source.object ⟶ target.object) :=
  rfl

/-- The bounded inclusion sends addition of bounded morphisms to ambient
addition. -/
theorem inclusion_map_add
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (first second : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
        (first + second) =
      TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map first +
        TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
          second :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map_add

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
