import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.IntervalLocalization.ContourCorQConstruction.Owner

/-!
# Constructed effective analytic motives

This owner names the effective layer produced by constructed descent and
interval localization, before formal Tate stabilization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The constructed effective analytic motive layer. -/
structure ConstructedEffectiveAnalyticMotive where
  intervalLocal : ConstructedIntervalLocalAnalyticPresheaf

namespace ConstructedEffectiveAnalyticMotive

/-- The constructed interval-local presheaf underlying the effective motive. -/
def underlying (M : ConstructedEffectiveAnalyticMotive) :
    ConstructedIntervalLocalAnalyticPresheaf :=
  M.intervalLocal

/-- The constructed descent-local presheaf underlying the effective motive. -/
def descentLocal (M : ConstructedEffectiveAnalyticMotive) :
    ConstructedDescentLocalAnalyticPresheaf :=
  M.intervalLocal.descentLocal

/-- The constructed interval-locality data. -/
def intervalLocality (M : ConstructedEffectiveAnalyticMotive) :
    ConstructedIntervalLocalObject M.descentLocal :=
  M.intervalLocal.intervalLocality

end ConstructedEffectiveAnalyticMotive

end AnalyticMotives
end LFunctions
end Boundary
