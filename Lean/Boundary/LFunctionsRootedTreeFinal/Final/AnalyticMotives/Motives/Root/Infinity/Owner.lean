import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.Owner

/-!
# Motive-root infinity facade

This file exposes the quasicategory presentation of the stable analytic motive
category at the motive-root layer.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root facade: the stable analytic motive quasicategory is the nerve
of the stable analytic motive category. -/
theorem TraceAnalyticMotive.rootStableMotiveQuasicategory_eq_nerve :
    TraceAnalyticStableMotiveQuasicategory =
      CategoryTheory.nerve TraceAnalyticStableMotiveCategory :=
  TraceAnalyticStableMotiveQuasicategory_eq_nerve

/-- Motive-root facade: the stable analytic motive nerve is a quasicategory. -/
def TraceAnalyticMotive.rootStableMotiveQuasicategory_quasicategory :
    Quasicategory TraceAnalyticStableMotiveQuasicategory :=
  TraceAnalyticStableMotiveQuasicategory.quasicategory

end AnalyticMotives
end LFunctions
end Boundary
