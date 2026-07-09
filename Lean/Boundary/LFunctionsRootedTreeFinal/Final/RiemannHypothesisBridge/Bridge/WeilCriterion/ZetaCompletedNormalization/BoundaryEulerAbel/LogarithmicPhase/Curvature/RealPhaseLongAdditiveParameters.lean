import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongWeylArithmetic

/-!
# Long additive resonance parameters

This file owns the canonical thickness and window-cardinality scales used by
the all-integer monotone-curvature decomposition on the long branch.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Canonical resonance thickness for the long all-integer monotone-curvature
decomposition. -/
abbrev Real.logarithmicPhaseRealPhase_longEta
    (T : ℝ)
    (b h : ℕ) : ℝ :=
  min Real.pi
    (Real.sqrt
      (T * (h : ℝ) /
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ))))))

/-- Canonical curvature-spread scale for long resonant windows. -/
abbrev Real.logarithmicPhaseRealPhase_longRho
    (T : ℝ)
    (b h : ℕ) : ℝ :=
  T * (h : ℝ) /
    ((((b + 1 : ℕ) : ℝ) *
      (((b + 1 : ℕ) : ℝ) *
        (((b + 1 : ℕ) : ℝ))))

/-- Canonical resonant-window cardinality budget. -/
abbrev Real.logarithmicPhaseRealPhase_longWindowBudget
    (T : ℝ)
    (b h : ℕ) : ℝ :=
  (2 * Real.logarithmicPhaseRealPhase_longEta T b h) /
      Real.logarithmicPhaseRealPhase_longRho T b h +
    1

/-- The canonical long resonance thickness is positive on every Weyl shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b : ℕ} :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        0 < Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h := by
  intro h hh
  have hsqrt_pos :
      0 <
        Real.sqrt
          (‖t‖ * (h : ℝ) /
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))))) := by
    have hT_pos : 0 < ‖t‖ :=
      lt_of_lt_of_le zero_lt_one ht
    have hh_pos : 0 < (h : ℝ) :=
      Nat.cast_pos.mpr
        (Complex.realPhase_secondDerivative_vdc_shiftRange_pos hh)
    have hnum_pos : 0 < ‖t‖ * (h : ℝ) :=
      mul_pos hT_pos hh_pos
    have hB_pos : 0 < ((b + 1 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.succ_pos b)
    have hden_pos :
        0 <
          ((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ))) :=
      mul_pos hB_pos (mul_pos hB_pos hB_pos)
    exact Real.sqrt_pos.mpr (div_pos hnum_pos hden_pos)
  exact lt_min Real.pi_pos hsqrt_pos

end

end LFunctions
end Boundary
