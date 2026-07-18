import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner

/-!
# Canonical analytic inputs for the Weil positivity owner

This file constructs the countable-avoidance schedule consumed by the completed
explicit-formula contour.  The selector is chosen inside `(u,u+1)` at every
parameter `u`, so cofinality is an explicit consequence of its lower bound.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A selected height in `(u,u+1)` outside a countable bad-height set. -/
noncomputable def countableAvoidingHeight
    (s : Set ℝ) (hs : s.Countable) (u : ℝ) : ℝ :=
  Classical.choose (exists_height_between_not_mem_countable s hs u)

/-- The selected countable-avoiding height lies above its parameter. -/
theorem countableAvoidingHeight_parameter_lt
    (s : Set ℝ) (hs : s.Countable) (u : ℝ) :
    u < countableAvoidingHeight s hs u := by
  exact (Classical.choose_spec
    (exists_height_between_not_mem_countable s hs u)).1

/-- The selected countable-avoiding height lies below the next unit endpoint. -/
theorem countableAvoidingHeight_lt_parameter_add_one
    (s : Set ℝ) (hs : s.Countable) (u : ℝ) :
    countableAvoidingHeight s hs u < u + 1 := by
  exact (Classical.choose_spec
    (exists_height_between_not_mem_countable s hs u)).2.1

/-- The selected height avoids the prescribed countable set. -/
theorem countableAvoidingHeight_not_mem
    (s : Set ℝ) (hs : s.Countable) (u : ℝ) :
    countableAvoidingHeight s hs u ∉ s := by
  exact (Classical.choose_spec
    (exists_height_between_not_mem_countable s hs u)).2.2

/-- The intervalwise countable-avoiding selector tends to positive infinity. -/
theorem countableAvoidingHeight_tendsto_atTop
    (s : Set ℝ) (hs : s.Countable) :
    Tendsto (countableAvoidingHeight s hs) atTop atTop := by
  exact Filter.tendsto_atTop.2
    (fun lower : ℝ =>
      ⟨lower, fun parameter hparameter =>
        le_trans hparameter
          (le_of_lt (countableAvoidingHeight_parameter_lt s hs parameter))⟩)

/-- Every countable real set has a canonical cofinal avoiding schedule. -/
noncomputable def countableAvoidingCofinalHeightSchedule
    (s : Set ℝ) (hs : s.Countable) :
    CountableAvoidingCofinalHeightSchedule s :=
  { bad_countable := hs
    height := countableAvoidingHeight s hs
    cofinal := countableAvoidingHeight_tendsto_atTop s hs
    avoids := countableAvoidingHeight_not_mem s hs }

/-- The autocorrelation contour family has a canonical horizontal avoiding schedule. -/
noncomputable def zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule
    (f : ZetaAdmissibleFunction) :
    ExplicitFormulaHorizontalAvoidingHeightSchedule
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  countableAvoidingCofinalHeightSchedule
    (explicitFormulaContourHorizontalBadHeightSet
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (explicitFormulaContourHorizontalBadHeightSet_countable
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
