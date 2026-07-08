import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Owner

/-!
# The quasicategory of stable analytic motives

This file gives the already-constructed stable analytic motive category its
first infinity-categorical presentation: the simplicial nerve of the Verdier
localized analytic motive category.  Mathlib proves that the nerve of an
ordinary category is a quasicategory.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The simplicial nerve of the stable analytic motive category. -/
abbrev TraceAnalyticStableMotiveQuasicategory :=
  CategoryTheory.nerve TraceAnalyticStableMotiveCategory

/-- The stable analytic motive nerve is a quasicategory. -/
def TraceAnalyticStableMotiveQuasicategory.quasicategory :
    Quasicategory TraceAnalyticStableMotiveQuasicategory :=
  inferInstance

/-- The stable analytic motive quasicategory is the nerve of the Verdier
localized stable analytic motive category. -/
theorem TraceAnalyticStableMotiveQuasicategory_eq_nerve :
    TraceAnalyticStableMotiveQuasicategory =
      CategoryTheory.nerve TraceAnalyticStableMotiveCategory :=
  rfl

/-- The zero-simplices of the stable analytic motive nerve are composable-arrow
objects of length zero in the stable analytic motive category. -/
theorem TraceAnalyticStableMotiveQuasicategory_obj_zero :
    TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 0)) =
      ComposableArrows TraceAnalyticStableMotiveCategory 0 :=
  rfl

/-- The one-simplices of the stable analytic motive nerve are composable-arrow
objects of length one in the stable analytic motive category. -/
theorem TraceAnalyticStableMotiveQuasicategory_obj_one :
    TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 1)) =
      ComposableArrows TraceAnalyticStableMotiveCategory 1 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
