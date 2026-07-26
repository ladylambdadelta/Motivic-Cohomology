import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner

/-!
# Countable avoiding height schedules

This owner part contains only the generic countable-avoidance schedule
construction.  Concrete contour families import this file without importing
autocorrelation-specific canonical inputs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter

namespace ZetaAdmissibleFunction

/-- A selected height in `(u,u+1)` outside a countable bad-height set. -/
noncomputable def countableAvoidingHeight
    (s : Set ℝ) (hs : s.Countable) (u : ℝ) : ℝ :=
  Classical.choose (exists_height_between_not_mem_countable s hs u)

/-- The selected countable-avoiding height lies above its parameter. -/
theorem countableAvoidingHeight_parameter_lt
    (s : Set ℝ) (hs : s.Countable) (u : ℝ) :
    u < countableAvoidingHeight s hs u :=
  (Classical.choose_spec
    (exists_height_between_not_mem_countable s hs u)).1

/-- The selected countable-avoiding height lies below the next unit endpoint. -/
theorem countableAvoidingHeight_lt_parameter_add_one
    (s : Set ℝ) (hs : s.Countable) (u : ℝ) :
    countableAvoidingHeight s hs u < u + 1 :=
  (Classical.choose_spec
    (exists_height_between_not_mem_countable s hs u)).2.1

/-- The selected height avoids the prescribed countable set. -/
theorem countableAvoidingHeight_not_mem
    (s : Set ℝ) (hs : s.Countable) (u : ℝ) :
    countableAvoidingHeight s hs u ∉ s :=
  (Classical.choose_spec
    (exists_height_between_not_mem_countable s hs u)).2.2

/-- The intervalwise countable-avoiding selector tends to positive infinity. -/
theorem countableAvoidingHeight_tendsto_atTop
    (s : Set ℝ) (hs : s.Countable) :
    Tendsto (countableAvoidingHeight s hs) atTop atTop :=
  Filter.tendsto_atTop.2
    (fun lower : ℝ =>
      Filter.eventually_atTop.2
        ⟨lower, fun parameter hparameter =>
          le_trans hparameter
            (le_of_lt (countableAvoidingHeight_parameter_lt s hs parameter))⟩)

/-- Every countable real set has a cofinal avoiding schedule. -/
noncomputable def countableAvoidingCofinalHeightSchedule
    (s : Set ℝ) (hs : s.Countable) :
    CountableAvoidingCofinalHeightSchedule s :=
  { bad_countable := hs
    height := countableAvoidingHeight s hs
    cofinal := countableAvoidingHeight_tendsto_atTop s hs
    avoids := countableAvoidingHeight_not_mem s hs }

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
