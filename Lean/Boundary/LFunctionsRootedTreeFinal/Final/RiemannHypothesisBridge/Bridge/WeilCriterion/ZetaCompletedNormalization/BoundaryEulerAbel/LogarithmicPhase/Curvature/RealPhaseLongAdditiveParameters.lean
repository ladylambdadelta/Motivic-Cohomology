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
            (((b + 1 : ℕ) : ℝ)))))))

/-- Canonical curvature-spread scale for long resonant windows. -/
abbrev Real.logarithmicPhaseRealPhase_longRho
    (T : ℝ)
    (b h : ℕ) : ℝ :=
    T * (h : ℝ) /
    ((((b + 1 : ℕ) : ℝ) *
      (((b + 1 : ℕ) : ℝ) *
        (((b + 1 : ℕ) : ℝ)))))

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

/-- The canonical long curvature-spread scale is positive on every Weyl
shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_longRho_pos
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b : ℕ} :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        0 < Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h := by
  intro h hh
  have hT_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hh_pos : 0 < (h : ℝ) :=
    Nat.cast_pos.mpr
      (Complex.realPhase_secondDerivative_vdc_shiftRange_pos hh)
  have hnum_pos : 0 < ‖t‖ * (h : ℝ) :=
    mul_pos hT_pos hh_pos
  have hB_pos : 0 < ((b + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hBsq_pos :
      0 <
        ((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) :=
    mul_pos hB_pos (mul_pos hB_pos hB_pos)
  exact div_pos hnum_pos hBsq_pos

/-- The capped canonical thickness has square bounded by the curvature-spread
scale. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_longEta_sq_le_longRho
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b : ℕ} :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h *
            Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h ≤
          Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h := by
  intro h hh
  let eta : ℝ := Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h
  let rho : ℝ := Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h
  have heta_nonneg : 0 ≤ eta :=
    le_of_lt
      (Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
        t ht (b := b) h hh)
  have hrho_nonneg : 0 ≤ rho :=
    le_of_lt
      (Complex.logarithmicPhaseRealPhase_shiftRange_longRho_pos
        t ht (b := b) h hh)
  have heta_le_sqrt : eta ≤ Real.sqrt rho := by
    exact min_le_right Real.pi (Real.sqrt rho)
  have hsquare_le :
      eta * eta ≤ Real.sqrt rho * Real.sqrt rho :=
    mul_le_mul heta_le_sqrt heta_le_sqrt heta_nonneg
      (Real.sqrt_nonneg rho)
  have hsqrt_square : Real.sqrt rho * Real.sqrt rho = rho := by
    exact
      Eq.trans
        (pow_two (Real.sqrt rho)).symm
        (Real.sq_sqrt hrho_nonneg)
  exact
    Eq.subst
      (motive := fun right : ℝ => eta * eta ≤ right)
      hsqrt_square
      hsquare_le

/-- The canonical resonant-window budget is nonnegative on the Weyl shift
range. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_longWindowBudget_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b : ℕ} :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        0 ≤ Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h := by
  intro h hh
  have heta_nonneg :
      0 ≤ Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h :=
    le_of_lt
      (Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
        t ht (b := b) h hh)
  have hrho_nonneg :
      0 ≤ Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h :=
    le_of_lt
      (Complex.logarithmicPhaseRealPhase_shiftRange_longRho_pos
        t ht (b := b) h hh)
  have htwo_eta_nonneg :
      0 ≤ 2 * Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h :=
    mul_nonneg zero_le_two heta_nonneg
  have hquot_nonneg :
      0 ≤
        (2 * Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) /
          Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h :=
    div_nonneg htwo_eta_nonneg hrho_nonneg
  exact add_nonneg hquot_nonneg zero_le_one

/-- The square-root normalization `η² ≤ ρ` converts the resonant-window
budget into the canonical second-derivative scale for one Weyl shift. -/
theorem Complex.logarithmicPhaseRealPhase_longWindowBudget_le_sqrtScale
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b : ℕ} :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h ≤
          2 * (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ + 1 := by
  intro h hh
  let eta : ℝ := Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h
  let rho : ℝ := Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h
  have heta_pos : 0 < eta :=
    Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
      t ht (b := b) h hh
  have hrho_pos : 0 < rho :=
    Complex.logarithmicPhaseRealPhase_shiftRange_longRho_pos
      t ht (b := b) h hh
  have heta_sq_le_rho : eta * eta ≤ rho :=
    Complex.logarithmicPhaseRealPhase_shiftRange_longEta_sq_le_longRho
      t ht (b := b) h hh
  have heta_inv_nonneg : 0 ≤ eta⁻¹ :=
    inv_nonneg.mpr (le_of_lt heta_pos)
  have heta_le_rho_mul_inv : eta ≤ rho * eta⁻¹ := by
    have hmul : eta * eta * eta⁻¹ ≤ rho * eta⁻¹ :=
      mul_le_mul_of_nonneg_right heta_sq_le_rho heta_inv_nonneg
    have hleft : eta * eta * eta⁻¹ = eta := by
      exact
        Eq.trans
          (mul_assoc eta eta eta⁻¹)
          (Eq.trans
            (congrArg (fun value : ℝ => eta * value)
              (mul_inv_cancel₀ (ne_of_gt heta_pos)))
            (mul_one eta))
    exact
      calc
        eta = eta * eta * eta⁻¹ := hleft.symm
        _ ≤ rho * eta⁻¹ := hmul
  have htwo_eta : 2 * eta ≤ (2 * eta⁻¹) * rho := by
    have hscaled : 2 * eta ≤ 2 * (rho * eta⁻¹) :=
      mul_le_mul_of_nonneg_left heta_le_rho_mul_inv zero_le_two
    have hright : 2 * (rho * eta⁻¹) = (2 * eta⁻¹) * rho := by
      exact
        Eq.trans
          (mul_assoc 2 rho eta⁻¹).symm
          (Eq.trans
            (congrArg (fun value : ℝ => value * eta⁻¹) (mul_comm 2 rho))
            (Eq.trans
              (mul_assoc rho 2 eta⁻¹)
              (mul_comm rho (2 * eta⁻¹))))
    exact
      Eq.subst
        (motive := fun right : ℝ => 2 * eta ≤ right)
        hright
        hscaled
  have hquot : (2 * eta) / rho ≤ 2 * eta⁻¹ :=
    (div_le_iff₀ hrho_pos).mpr htwo_eta
  exact add_le_add_right hquot 1

end

end LFunctions
end Boundary
