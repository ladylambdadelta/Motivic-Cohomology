import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Preadditive.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Owner

/-!
# Preadditivity of the degreewise bounded stable source

The degreewise bounded stable source is a full subcategory of the preadditive
analytic comparison source.  This file exposes the inherited preadditive
structure and the additivity of its inclusion.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The degreewise bounded stable source inherits preadditivity from the
analytic comparison source. -/
def preadditiveStructure :
    Preadditive
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
  infer_instance

/-- The degreewise bounded stable source inclusion is additive. -/
def inclusionAdditive :
    TraceAnalyticDMgmComparisonSource
      .DegreewiseBoundedStable.inclusion.Additive :=
  infer_instance

/-- The additive structure on degreewise bounded morphisms is the ambient
additive structure on the corresponding comparison-source morphisms. -/
theorem hom_add_eq_ambient
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (first second : source ⟶ target) :
    (first + second : source ⟶ target) =
      (first + second : source.object ⟶ target.object) :=
  rfl

/-- The degreewise bounded inclusion sends addition of morphisms to ambient
addition. -/
theorem inclusion_map_add
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (first second : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .inclusion.map (first + second) =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .inclusion.map first +
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .inclusion.map second :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .inclusion.map_add

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
