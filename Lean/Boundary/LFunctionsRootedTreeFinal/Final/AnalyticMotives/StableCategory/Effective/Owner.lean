import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.IntervalLocalization.Owner

/-!
# Effective analytic motive category

This file owns the effective analytic motive category after transfer
presheaves, descent localization, and interval localization, before Tate
stabilization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
The effective analytic motive layer: descent-local and interval-local
presheaves with contour transfers, before Tate inversion.
-/
structure EffectiveAnalyticMotive where
  intervalLocalPresheaf : IntervalLocalAnalyticPresheaf

namespace EffectiveAnalyticMotive

/-- The interval-local presheaf underlying an effective analytic motive. -/
def underlying (M : EffectiveAnalyticMotive) :
    IntervalLocalAnalyticPresheaf :=
  M.intervalLocalPresheaf

/-- The descent-local presheaf underlying an effective analytic motive. -/
def descentLocal (M : EffectiveAnalyticMotive) :
    DescentLocalAnalyticPresheaf :=
  M.intervalLocalPresheaf.descentLocal

/-- The interval-locality data underlying an effective analytic motive. -/
def intervalLocality (M : EffectiveAnalyticMotive) :
    IntervalLocalObject M.intervalLocalPresheaf.descentLocal :=
  M.intervalLocalPresheaf.intervalLocality

/-- The interval equivalence carried by an effective analytic motive. -/
def intervalEquivalence (M : EffectiveAnalyticMotive) :
    PresheafIntervalHomotopyEquivalence M.descentLocal :=
  M.intervalLocality.equivalence

/-- The endpoint pullbacks carried by an effective analytic motive agree. -/
theorem endpoint_pullbacks_agree (M : EffectiveAnalyticMotive) :
    M.intervalEquivalence.leftPullback =
      M.intervalEquivalence.rightPullback :=
  M.intervalLocality.endpoint_pullbacks_agree

end EffectiveAnalyticMotive

end AnalyticMotives
end LFunctions
end Boundary
