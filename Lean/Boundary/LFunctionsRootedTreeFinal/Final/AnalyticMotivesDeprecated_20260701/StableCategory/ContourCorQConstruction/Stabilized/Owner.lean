import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.ContourCorQConstruction.Effective.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.TateStabilization.ContourCorQConstruction.Owner

/-!
# Constructed stabilized analytic motives

This owner names the formal Tate-stabilized layer of constructed analytic
motives.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The constructed stabilized analytic motive layer. -/
structure ConstructedStabilizedAnalyticMotive where
  effective : ConstructedEffectiveAnalyticMotive
  stabilizedPresheaf : ConstructedTateStabilizedAnalyticPresheaf
  effective_level_zero_eq :
    stabilizedPresheaf.levelAt 0 = effective.intervalLocal

namespace ConstructedStabilizedAnalyticMotive

/-- The effective layer of a constructed stabilized motive. -/
def effectiveLayer (M : ConstructedStabilizedAnalyticMotive) :
    ConstructedEffectiveAnalyticMotive :=
  M.effective

/-- The constructed Tate-stabilized presheaf. -/
def stabilized (M : ConstructedStabilizedAnalyticMotive) :
    ConstructedTateStabilizedAnalyticPresheaf :=
  M.stabilizedPresheaf

/-- The interval-local presheaf at one Tate weight. -/
def levelAt (M : ConstructedStabilizedAnalyticMotive)
    (n : Int) :
    ConstructedIntervalLocalAnalyticPresheaf :=
  M.stabilizedPresheaf.levelAt n

/-- The zero Tate level agrees with the effective layer. -/
theorem level_zero_eq_effective
    (M : ConstructedStabilizedAnalyticMotive) :
    M.levelAt 0 = M.effective.intervalLocal :=
  M.effective_level_zero_eq

end ConstructedStabilizedAnalyticMotive

end AnalyticMotives
end LFunctions
end Boundary
