import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.Owner

/-!
# Stable infinity structure on the analytic comparison source

The analytic `DMgm` comparison source is definitionally the Verdier-localized
stable analytic motive category.  This file exposes the already-constructed
stable-infinity package under the comparison-source name.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The stable-infinity category package carried by the analytic comparison
source. -/
def stableInfinityCategory :
    TraceAnalyticStableInfinityCategory :=
  traceAnalyticStableInfinityCategory

/-- The comparison-source stable-infinity package is the owner-level analytic
stable-infinity package. -/
theorem stableInfinityCategory_eq_owner :
    TraceAnalyticDMgmComparisonSource.stableInfinityCategory =
      traceAnalyticStableInfinityCategory :=
  rfl

/-- The presented category of the stable-infinity package is the analytic
comparison source. -/
theorem stableInfinityCategory_presentedCategory_eq_source :
    StableInfinityOwner.PresentedCategory =
      TraceAnalyticDMgmComparisonSource :=
  rfl

/-- The comparison-source stable quasicategory is the nerve of the analytic
comparison source. -/
theorem stableInfinityCategory_quasicategory_eq_nerve_source :
    TraceAnalyticStableMotiveQuasicategory =
      CategoryTheory.nerve TraceAnalyticDMgmComparisonSource :=
  rfl

/-- The comparison-source stable-infinity package uses the comparison-source
localization structure. -/
theorem stableInfinityCategory_localization_eq_source :
    TraceAnalyticDMgmComparisonSource.stableInfinityCategory.localization =
      TraceAnalyticDMgmComparisonSource.isLocalization :=
  rfl

/-- The comparison-source stable-infinity package uses the comparison-source
integer shift structure. -/
theorem stableInfinityCategory_shift_eq_source :
    TraceAnalyticDMgmComparisonSource.stableInfinityCategory.shift =
      TraceAnalyticDMgmComparisonSource.hasShiftStructure :=
  rfl

/-- The comparison-source stable-infinity package uses the comparison-source
pretriangulated structure. -/
theorem stableInfinityCategory_pretriangulated_eq_source :
    TraceAnalyticDMgmComparisonSource.stableInfinityCategory.pretriangulated =
      TraceAnalyticDMgmComparisonSource.pretriangulatedStructure :=
  rfl

/-- The comparison-source stable-infinity package uses the comparison-source
triangulated structure. -/
theorem stableInfinityCategory_triangulated_eq_source :
    TraceAnalyticDMgmComparisonSource.stableInfinityCategory.triangulated =
      TraceAnalyticDMgmComparisonSource.triangulatedStructure :=
  rfl

/-- The comparison-source stable-infinity package uses the comparison-source
distinguished triangles. -/
theorem stableInfinityCategory_distinguishedTriangles_eq_source :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.distinguishedTriangles =
      TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  rfl

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
