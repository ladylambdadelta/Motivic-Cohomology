import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.FixedVerticalEnvelope.CompactStrip

/-!
# Reciprocal fixed vertical Gamma half-strip bounds

This subowner contains the reciprocal fixed-vertical estimates needed for the
completed-zeta Gamma boundary normalization.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem Complex.Gamma_verticalStrip_reciprocal_bound_of_lower_bound
    {A B H c : ℝ}
    (hc_pos : 0 < c)
    (hlower :
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖) :
    ∀ x y : ℝ,
      A ≤ x →
      x ≤ B →
      H ≤ ‖y‖ →
        ‖(Complex.Gamma (Complex.fixedRealPartVerticalPoint x y))⁻¹‖ ≤
          c⁻¹ * Complex.fixedRealPartVerticalReciprocalStirlingEnvelope x y := by
  exact
    fun x y hx_left hx_right hy =>
      let R : ℝ := (Real.pi / 2) * ‖y‖
      let T : ℝ := 1 + ‖y‖
      let G : ℂ := Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)
      have hT_pos : 0 < T :=
        lt_of_lt_of_le zero_lt_one
          (le_add_of_nonneg_right (norm_nonneg y))
      have hexp_pos : 0 < Real.exp (-R) :=
        Real.exp_pos (-R)
      have hrpow_pos : 0 < T ^ (x - 1 / 2) :=
        Real.rpow_pos_of_pos hT_pos (x - 1 / 2)
      have henvelope_pos :
          0 < c * Real.exp (-R) * T ^ (x - 1 / 2) :=
        mul_pos (mul_pos hc_pos hexp_pos) hrpow_pos
      have hG_lower :
          c * Real.exp (-R) * T ^ (x - 1 / 2) ≤ ‖G‖ := by
        have hR_def : R = (Real.pi / 2) * ‖y‖ := rfl
        have hT_def : T = 1 + ‖y‖ := rfl
        calc
          c * Real.exp (-R) * T ^ (x - 1 / 2) =
              c * Real.exp (-((Real.pi / 2) * ‖y‖)) *
                T ^ (x - 1 / 2) := by
            exact
              congrArg
                (fun u : ℝ => c * Real.exp (-u) * T ^ (x - 1 / 2))
                hR_def
          _ = c * Real.exp (-(Real.pi / 2) * ‖y‖) *
                T ^ (x - 1 / 2) := by
            exact
              congrArg
                (fun u : ℝ => c * Real.exp u * T ^ (x - 1 / 2))
                (neg_mul (Real.pi / 2) ‖y‖).symm
          _ = c * Real.exp (-(Real.pi / 2) * ‖y‖) *
                (1 + ‖y‖) ^ (x - 1 / 2) := by
            exact
              congrArg
                (fun u : ℝ =>
                  c * Real.exp (-(Real.pi / 2) * ‖y‖) *
                    u ^ (x - 1 / 2))
                hT_def
          _ = c * Complex.fixedRealPartVerticalStirlingEnvelope x y := by
            exact
              mul_assoc c (Real.exp (-(Real.pi / 2) * ‖y‖))
                ((1 + ‖y‖) ^ (x - 1 / 2))
          _ ≤ ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ :=
            hlower x y hx_left hx_right hy
          _ = ‖G‖ := rfl
      have hG_inv_norm :
          ‖G⁻¹‖ = ‖G‖⁻¹ :=
        norm_inv G
      have hreciprocal_le :
          ‖G‖⁻¹ ≤ (c * Real.exp (-R) * T ^ (x - 1 / 2))⁻¹ :=
        inv_le_inv_of_le henvelope_pos hG_lower
      have htarget_eq :
          (c * Real.exp (-R) * T ^ (x - 1 / 2))⁻¹ =
            c⁻¹ * Complex.fixedRealPartVerticalReciprocalStirlingEnvelope x y := by
        have hexp_neg_eq : Real.exp (-R) = (Real.exp R)⁻¹ :=
          Real.exp_neg R
        have hexp_neg_inv_eq : (Real.exp (-R))⁻¹ = Real.exp R := by
          calc
            (Real.exp (-R))⁻¹ = ((Real.exp R)⁻¹)⁻¹ :=
              congrArg Inv.inv hexp_neg_eq
            _ = Real.exp R := inv_inv (Real.exp R)
        have hpow_neg_eq :
            T ^ (1 / 2 - x) = (T ^ (x - 1 / 2))⁻¹ := by
          have hneg : 1 / 2 - x = -(x - 1 / 2) := by
            exact (neg_sub x (1 / 2)).symm
          exact Eq.trans
            (congrArg (fun u : ℝ => T ^ u) hneg)
            (Real.rpow_neg (le_of_lt hT_pos) (x - 1 / 2))
        calc
          (c * Real.exp (-R) * T ^ (x - 1 / 2))⁻¹ =
              (T ^ (x - 1 / 2))⁻¹ * (c * Real.exp (-R))⁻¹ := by
                exact mul_inv_rev (c * Real.exp (-R)) (T ^ (x - 1 / 2))
          _ = (T ^ (x - 1 / 2))⁻¹ *
              ((Real.exp (-R))⁻¹ * c⁻¹) := by
                exact congrArg
                  (fun u : ℝ => (T ^ (x - 1 / 2))⁻¹ * u)
                  (mul_inv_rev c (Real.exp (-R)))
          _ = c⁻¹ * (Real.exp (-R))⁻¹ * (T ^ (x - 1 / 2))⁻¹ := by
                calc
                  (T ^ (x - 1 / 2))⁻¹ *
                      ((Real.exp (-R))⁻¹ * c⁻¹) =
                    ((T ^ (x - 1 / 2))⁻¹ * (Real.exp (-R))⁻¹) * c⁻¹ :=
                      (mul_assoc (T ^ (x - 1 / 2))⁻¹ (Real.exp (-R))⁻¹ c⁻¹).symm
                  _ = c⁻¹ *
                      ((T ^ (x - 1 / 2))⁻¹ * (Real.exp (-R))⁻¹) :=
                    mul_comm ((T ^ (x - 1 / 2))⁻¹ * (Real.exp (-R))⁻¹) c⁻¹
                  _ = c⁻¹ *
                      ((Real.exp (-R))⁻¹ * (T ^ (x - 1 / 2))⁻¹) := by
                    exact congrArg
                      (fun u : ℝ => c⁻¹ * u)
                      (mul_comm (T ^ (x - 1 / 2))⁻¹ (Real.exp (-R))⁻¹)
                  _ = c⁻¹ * (Real.exp (-R))⁻¹ *
                      (T ^ (x - 1 / 2))⁻¹ :=
                    (mul_assoc c⁻¹ (Real.exp (-R))⁻¹
                      (T ^ (x - 1 / 2))⁻¹).symm
          _ = (c⁻¹ * Real.exp R) * (T ^ (x - 1 / 2))⁻¹ := by
                exact congrArg
                  (fun u : ℝ => (c⁻¹ * u) * (T ^ (x - 1 / 2))⁻¹)
                  hexp_neg_inv_eq
          _ = (c⁻¹ * Real.exp R) * T ^ (1 / 2 - x) := by
                exact congrArg
                  (fun u : ℝ => (c⁻¹ * Real.exp R) * u)
                  hpow_neg_eq.symm
          _ = c⁻¹ * (Real.exp ((Real.pi / 2) * ‖y‖) *
                (1 + ‖y‖) ^ (1 / 2 - x)) := by
                have hR_def : R = (Real.pi / 2) * ‖y‖ := rfl
                have hT_def : T = 1 + ‖y‖ := rfl
                calc
                  (c⁻¹ * Real.exp R) * T ^ (1 / 2 - x) =
                    c⁻¹ * (Real.exp R * T ^ (1 / 2 - x)) :=
                      mul_assoc c⁻¹ (Real.exp R) (T ^ (1 / 2 - x))
                  _ = c⁻¹ * (Real.exp ((Real.pi / 2) * ‖y‖) *
                      T ^ (1 / 2 - x)) := by
                    exact congrArg
                      (fun u : ℝ => c⁻¹ * (Real.exp u * T ^ (1 / 2 - x)))
                      hR_def
                  _ = c⁻¹ * (Real.exp ((Real.pi / 2) * ‖y‖) *
                      (1 + ‖y‖) ^ (1 / 2 - x)) := by
                    exact congrArg
                      (fun u : ℝ =>
                        c⁻¹ * (Real.exp ((Real.pi / 2) * ‖y‖) *
                          u ^ (1 / 2 - x)))
                      hT_def
          _ = c⁻¹ * Complex.fixedRealPartVerticalReciprocalStirlingEnvelope x y := rfl
      calc
        ‖G⁻¹‖ = ‖G‖⁻¹ := hG_inv_norm
        _ ≤ (c * Real.exp (-R) * T ^ (x - 1 / 2))⁻¹ :=
          hreciprocal_le
        _ = c⁻¹ * Complex.fixedRealPartVerticalReciprocalStirlingEnvelope x y :=
          htarget_eq

/-- Large-height vertical-strip reciprocal Gamma bound from the lower half of
the uniform strip Stirling theorem. -/
theorem Complex.Gamma_inv_verticalStrip_largeHeight_stirling_bound_classical
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ,
      0 < H ∧
      0 < C ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖(Complex.Gamma (Complex.fixedRealPartVerticalPoint x y))⁻¹‖ ≤
            C * Complex.fixedRealPartVerticalReciprocalStirlingEnvelope x y := by
  match Complex.sectorialStirling_verticalStrip_largeHeight_classical hbranch A B with
  | ⟨H, C, c, hH_pos, _hC_pos, hc_pos, hbounds⟩ =>
      exact
        ⟨H, c⁻¹, hH_pos, inv_pos.mpr hc_pos,
          Complex.Gamma_verticalStrip_reciprocal_bound_of_lower_bound
            hc_pos
            (fun x y hx_left hx_right hy =>
              (hbounds x y hx_left hx_right hy).2)⟩

/-- Coordinate-free large-height vertical-strip reciprocal Gamma bound. -/
theorem Complex.Gamma_inv_verticalStrip_largeHeight_stirling_bound_classical_point
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ,
      0 < H ∧
      0 < C ∧
      ∀ w : ℂ,
        A ≤ w.re →
        w.re ≤ B →
        H ≤ ‖w.im‖ →
          ‖(Complex.Gamma w)⁻¹‖ ≤
            C * Complex.fixedRealPartVerticalReciprocalStirlingEnvelope w.re w.im := by
  match Complex.Gamma_inv_verticalStrip_largeHeight_stirling_bound_classical
      hbranch A B with
  | ⟨H, C, hH_pos, hC_pos, hbound⟩ =>
      exact
        ⟨H, C, hH_pos, hC_pos,
          fun w hw_left hw_right hw_im =>
            have hpoint : Complex.fixedRealPartVerticalPoint w.re w.im = w :=
              Complex.fixedRealPartVerticalPoint_re_im w
            have hnorm :
                ‖(Complex.Gamma w)⁻¹‖ =
                  ‖(Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint w.re w.im))⁻¹‖ := by
              exact
                (congrArg
                  (fun u : ℂ => ‖(Complex.Gamma u)⁻¹‖)
                  hpoint).symm
            calc
              ‖(Complex.Gamma w)⁻¹‖ =
                  ‖(Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint w.re w.im))⁻¹‖ :=
                hnorm
              _ ≤ C *
                  Complex.fixedRealPartVerticalReciprocalStirlingEnvelope
                    w.re w.im :=
                hbound w.re w.im hw_left hw_right hw_im⟩

/-- Large-height vertical-strip Gamma upper bound from the upper half of the
uniform strip Stirling theorem. -/
theorem Complex.Gamma_verticalStrip_largeHeight_stirling_bound_classical
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ,
      0 < H ∧
      0 < C ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y := by
  match Complex.sectorialStirling_verticalStrip_largeHeight_classical hbranch A B with
  | ⟨H, C, _c, hH_pos, hC_pos, _hc_pos, hbounds⟩ =>
      exact
        ⟨H, C, hH_pos, hC_pos,
          fun x y hx_left hx_right hy =>
            (hbounds x y hx_left hx_right hy).1⟩

/-- Coordinate-free large-height vertical-strip Gamma upper bound. -/
theorem Complex.Gamma_verticalStrip_largeHeight_stirling_bound_classical_point
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ,
      0 < H ∧
      0 < C ∧
      ∀ w : ℂ,
        A ≤ w.re →
        w.re ≤ B →
        H ≤ ‖w.im‖ →
          ‖Complex.Gamma w‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope w.re w.im := by
  match Complex.Gamma_verticalStrip_largeHeight_stirling_bound_classical
      hbranch A B with
  | ⟨H, C, hH_pos, hC_pos, hbound⟩ =>
      exact
        ⟨H, C, hH_pos, hC_pos,
          fun w hw_left hw_right hw_im =>
            have hpoint : Complex.fixedRealPartVerticalPoint w.re w.im = w :=
              Complex.fixedRealPartVerticalPoint_re_im w
            have hnorm :
                ‖Complex.Gamma w‖ =
                  ‖Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint w.re w.im)‖ := by
              exact
                (congrArg
                  (fun u : ℂ => ‖Complex.Gamma u‖)
                  hpoint).symm
            calc
              ‖Complex.Gamma w‖ =
                  ‖Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint w.re w.im)‖ :=
                hnorm
              _ ≤ C *
                  Complex.fixedRealPartVerticalStirlingEnvelope
                    w.re w.im :=
                hbound w.re w.im hw_left hw_right hw_im⟩

/-- The direct fixed-line Stirling envelope is bounded by `1` on the closed
half-strip used by the `Gammaℝ` half-argument. -/
theorem Complex.fixedRealPartVerticalStirlingEnvelope_zero_half_le_one
    {x y : ℝ}
    (hx_half : x ≤ (1 / 2 : ℝ)) :
    Complex.fixedRealPartVerticalStirlingEnvelope x y ≤ 1 := by
  let T : ℝ := 1 + ‖y‖
  have hT_pos : 0 < T :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg y))
  have hT_ge_one : (1 : ℝ) ≤ T :=
    le_add_of_nonneg_right (norm_nonneg y)
  have hexponent_nonpos : x - 1 / 2 ≤ 0 :=
    sub_nonpos.mpr hx_half
  have hpow_le_one : T ^ (x - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hT_ge_one hexponent_nonpos
  have hpow_nonneg : 0 ≤ T ^ (x - 1 / 2) :=
    Real.rpow_nonneg (le_of_lt hT_pos) (x - 1 / 2)
  have hpi_div_nonneg : 0 ≤ Real.pi / 2 :=
    div_nonneg (le_of_lt Real.pi_pos) zero_le_two
  have hneg_pi_div_nonpos : -(Real.pi / 2) ≤ 0 :=
    neg_nonpos.mpr hpi_div_nonneg
  have hheight_nonneg : 0 ≤ ‖y‖ :=
    norm_nonneg y
  have hexp_arg_nonpos : -(Real.pi / 2) * ‖y‖ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hneg_pi_div_nonpos hheight_nonneg
  have hexp_le_one :
      Real.exp (-(Real.pi / 2) * ‖y‖) ≤ 1 := by
    calc
      Real.exp (-(Real.pi / 2) * ‖y‖) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr hexp_arg_nonpos
      _ = 1 := Real.exp_zero
  have hexp_nonneg : 0 ≤ Real.exp (-(Real.pi / 2) * ‖y‖) :=
    le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖y‖))
  calc
    Complex.fixedRealPartVerticalStirlingEnvelope x y =
        Real.exp (-(Real.pi / 2) * ‖y‖) * T ^ (x - 1 / 2) := rfl
    _ ≤ 1 * 1 :=
      mul_le_mul hexp_le_one hpow_le_one hpow_nonneg zero_le_one
    _ = 1 := one_mul 1

/-- Uniform finite-order Gamma bound on the closed half-strip
`0 ≤ Re w ≤ 1/2`, away from the real axis. -/
theorem Complex.Gamma_zero_half_strip_verticalTail_finiteOrder_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        w.re ≤ (1 / 2 : ℝ) →
        (1 / 2 : ℝ) ≤ ‖w.im‖ →
          ‖Complex.Gamma w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  match Complex.Gamma_verticalStrip_largeHeight_stirling_bound_classical_point
      hbranch 0 (1 / 2) with
  | ⟨H, Clarge, hH_pos, hClarge_pos, hlarge⟩ =>
  match Complex.Gamma_closedRealStrip_compactHeight_bound
      0 (1 / 2) (1 / 2) H one_half_pos with
  | ⟨Ccompact, hCcompact_pos, hcompact⟩ =>
      let A : ℝ := Clarge + Ccompact
      let B : ℝ := 1
      have hA_pos : 0 < A :=
        add_pos hClarge_pos hCcompact_pos
      have hB_pos : 0 < B := zero_lt_one
      have hClarge_le_A : Clarge ≤ A :=
        le_add_of_nonneg_right (le_of_lt hCcompact_pos)
      have hCcompact_le_A : Ccompact ≤ A :=
        le_add_of_nonneg_left (le_of_lt hClarge_pos)
      exact
        ⟨A, B, 1, hA_pos, hB_pos,
          fun w hw_re_nonneg hw_re_half hw_im_tail =>
            if hw_large : H ≤ ‖w.im‖ then
              have hlarge_w :
                  ‖Complex.Gamma w‖ ≤
                    Clarge * Complex.fixedRealPartVerticalStirlingEnvelope
                        w.re w.im :=
                hlarge w hw_re_nonneg hw_re_half hw_large
              have henv :
                  Complex.fixedRealPartVerticalStirlingEnvelope w.re w.im ≤ 1 :=
                Complex.fixedRealPartVerticalStirlingEnvelope_zero_half_le_one
                  hw_re_half
              have hscaled_env :
                  Clarge * Complex.fixedRealPartVerticalStirlingEnvelope
                      w.re w.im ≤ Clarge * 1 :=
                mul_le_mul_of_nonneg_left henv (le_of_lt hClarge_pos)
              have hconst_le_A : Clarge * 1 ≤ A := by
                calc
                  Clarge * 1 = Clarge := mul_one Clarge
                  _ ≤ A := hClarge_le_A
              have hbase_nonneg : 0 ≤ 1 + ‖w‖ :=
                le_trans zero_le_one
                  (le_add_of_nonneg_right (norm_nonneg w))
              have hpow_nonneg : 0 ≤ (1 + ‖w‖) ^ (1 : ℕ) :=
                pow_nonneg hbase_nonneg 1
              have hexponent_nonneg : 0 ≤ B * (1 + ‖w‖) ^ (1 : ℕ) :=
                mul_nonneg (le_of_lt hB_pos) hpow_nonneg
              have hone_le_exp :
                  (1 : ℝ) ≤ Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                Real.one_le_exp hexponent_nonneg
              have hA_nonneg : 0 ≤ A :=
                le_of_lt hA_pos
              have hA_le_Aexp :
                  A ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) := by
                calc
                  A = A * 1 := (mul_one A).symm
                  _ ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                    mul_le_mul_of_nonneg_left hone_le_exp hA_nonneg
              calc
                ‖Complex.Gamma w‖ ≤
                    Clarge * Complex.fixedRealPartVerticalStirlingEnvelope
                      w.re w.im := hlarge_w
                _ ≤ Clarge * 1 := hscaled_env
                _ ≤ A := hconst_le_A
                _ ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                  hA_le_Aexp
            else
              have hw_compact_upper : ‖w.im‖ ≤ H :=
                le_of_not_ge hw_large
              have hcompact_w :
                  ‖Complex.Gamma w‖ ≤ Ccompact :=
                hcompact w hw_re_nonneg hw_re_half hw_im_tail hw_compact_upper
              have hbase_nonneg : 0 ≤ 1 + ‖w‖ :=
                le_trans zero_le_one
                  (le_add_of_nonneg_right (norm_nonneg w))
              have hpow_nonneg : 0 ≤ (1 + ‖w‖) ^ (1 : ℕ) :=
                pow_nonneg hbase_nonneg 1
              have hexponent_nonneg : 0 ≤ B * (1 + ‖w‖) ^ (1 : ℕ) :=
                mul_nonneg (le_of_lt hB_pos) hpow_nonneg
              have hone_le_exp :
                  (1 : ℝ) ≤ Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                Real.one_le_exp hexponent_nonneg
              have hA_nonneg : 0 ≤ A :=
                le_of_lt hA_pos
              have hA_le_Aexp :
                  A ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) := by
                calc
                  A = A * 1 := (mul_one A).symm
                  _ ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                    mul_le_mul_of_nonneg_left hone_le_exp hA_nonneg
              calc
                ‖Complex.Gamma w‖ ≤ Ccompact := hcompact_w
                _ ≤ A := hCcompact_le_A
                _ ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                  hA_le_Aexp⟩

/-- The reciprocal fixed-line Stirling envelope is finite-order on the
half-strip used by the `Gammaℝ` half-argument. -/
theorem Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_zero_half_le_exp
    {x y : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hx_half : x ≤ (1 / 2 : ℝ)) :
    Complex.fixedRealPartVerticalReciprocalStirlingEnvelope x y ≤
      Real.exp (((Real.pi / 2) + 1) *
        (1 + ‖Complex.fixedRealPartVerticalPoint x y‖)) := by
  let T : ℝ := 1 + ‖y‖
  let e : ℝ := 1 / 2 - x
  let P : ℂ := Complex.fixedRealPartVerticalPoint x y
  have hT_pos : 0 < T :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg y))
  have hT_ge_one : (1 : ℝ) ≤ T :=
    le_add_of_nonneg_right (norm_nonneg y)
  have he_nonneg : 0 ≤ e := by
    exact sub_nonneg.mpr hx_half
  have he_le_one : e ≤ 1 := by
    have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 :=
      div_le_self zero_le_one one_le_two
    calc
      e = 1 / 2 - x := rfl
      _ ≤ 1 / 2 := sub_le_self (1 / 2 : ℝ) hx_nonneg
      _ ≤ 1 := hhalf_le_one
  have hrpow_le_T :
      T ^ e ≤ T := by
    calc
      T ^ e ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT_ge_one he_le_one
      _ = T := Real.rpow_one T
  have hT_eq : T = ‖y‖ + 1 := by
    exact add_comm 1 ‖y‖
  have hT_le_exp_y : T ≤ Real.exp ‖y‖ := by
    calc
      T = ‖y‖ + 1 := hT_eq
      _ ≤ Real.exp ‖y‖ := Real.add_one_le_exp ‖y‖
  have hpow_le_exp_y :
      T ^ e ≤ Real.exp ‖y‖ :=
    le_trans hrpow_le_T hT_le_exp_y
  have hexp_nonneg : 0 ≤ Real.exp ((Real.pi / 2) * ‖y‖) :=
    le_of_lt (Real.exp_pos ((Real.pi / 2) * ‖y‖))
  have henvelope_le :
      Real.exp ((Real.pi / 2) * ‖y‖) * T ^ e ≤
        Real.exp ((Real.pi / 2) * ‖y‖) * Real.exp ‖y‖ :=
    mul_le_mul_of_nonneg_left hpow_le_exp_y hexp_nonneg
  have hexp_product :
      Real.exp ((Real.pi / 2) * ‖y‖) * Real.exp ‖y‖ =
        Real.exp (((Real.pi / 2) + 1) * ‖y‖) := by
    calc
      Real.exp ((Real.pi / 2) * ‖y‖) * Real.exp ‖y‖ =
          Real.exp (((Real.pi / 2) * ‖y‖) + ‖y‖) :=
        (Real.exp_add ((Real.pi / 2) * ‖y‖) ‖y‖).symm
      _ = Real.exp (((Real.pi / 2) + 1) * ‖y‖) := by
        have hsum :
            (Real.pi / 2) * ‖y‖ + ‖y‖ =
              ((Real.pi / 2) + 1) * ‖y‖ := by
          calc
            (Real.pi / 2) * ‖y‖ + ‖y‖ =
                (Real.pi / 2) * ‖y‖ + 1 * ‖y‖ := by
              exact congrArg (fun u : ℝ => (Real.pi / 2) * ‖y‖ + u)
                (one_mul ‖y‖).symm
            _ = ((Real.pi / 2) + 1) * ‖y‖ :=
              (add_mul (Real.pi / 2) 1 ‖y‖).symm
        exact congrArg Real.exp hsum
  have hy_norm_le_P : ‖y‖ ≤ ‖P‖ := by
    have him_le : ‖P.im‖ ≤ ‖P‖ :=
      Complex.abs_im_le_abs P
    have him_eq : P.im = y :=
      Complex.fixedRealPartVerticalPoint_im x y
    have hnorm_eq : ‖P.im‖ = ‖y‖ :=
      congrArg norm him_eq
    calc
      ‖y‖ = ‖P.im‖ := hnorm_eq.symm
      _ ≤ ‖P‖ := him_le
  have hy_le_one_add_P : ‖y‖ ≤ 1 + ‖P‖ :=
    le_trans hy_norm_le_P (le_add_of_nonneg_left zero_le_one)
  have hcoef_nonneg : 0 ≤ (Real.pi / 2) + 1 := by
    have hpi_div_nonneg : 0 ≤ Real.pi / 2 :=
      div_nonneg (le_of_lt Real.pi_pos) zero_le_two
    exact add_nonneg hpi_div_nonneg zero_le_one
  have hexponent_le :
      ((Real.pi / 2) + 1) * ‖y‖ ≤
        ((Real.pi / 2) + 1) * (1 + ‖P‖) :=
    mul_le_mul_of_nonneg_left hy_le_one_add_P hcoef_nonneg
  have hexp_le :
      Real.exp (((Real.pi / 2) + 1) * ‖y‖) ≤
        Real.exp (((Real.pi / 2) + 1) * (1 + ‖P‖)) :=
    Real.exp_le_exp.mpr hexponent_le
  calc
    Complex.fixedRealPartVerticalReciprocalStirlingEnvelope x y =
        Real.exp ((Real.pi / 2) * ‖y‖) * T ^ e := rfl
    _ ≤ Real.exp ((Real.pi / 2) * ‖y‖) * Real.exp ‖y‖ :=
      henvelope_le
    _ = Real.exp (((Real.pi / 2) + 1) * ‖y‖) :=
      hexp_product
    _ ≤ Real.exp (((Real.pi / 2) + 1) * (1 + ‖P‖)) :=
      hexp_le

/-- Uniform finite-order reciprocal Gamma bound on the closed half-strip
`0 ≤ Re w ≤ 1/2`, away from the real axis. -/
theorem Complex.Gamma_inv_zero_half_strip_verticalTail_finiteOrder_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        w.re ≤ (1 / 2 : ℝ) →
        (1 / 2 : ℝ) ≤ ‖w.im‖ →
          ‖(Complex.Gamma w)⁻¹‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  match Complex.Gamma_inv_verticalStrip_largeHeight_stirling_bound_classical_point
      hbranch 0 (1 / 2) with
  | ⟨H, Clarge, hH_pos, hClarge_pos, hlarge⟩ =>
  match Complex.Gamma_inv_closedRealStrip_compactHeight_bound
      0 (1 / 2) (1 / 2) H one_half_pos with
  | ⟨Ccompact, hCcompact_pos, hcompact⟩ =>
      let A : ℝ := Clarge + Ccompact
      let B : ℝ := (Real.pi / 2) + 1
      have hA_pos : 0 < A :=
        add_pos hClarge_pos hCcompact_pos
      have hB_pos : 0 < B := by
        have hpi_div_nonneg : 0 ≤ Real.pi / 2 :=
          div_nonneg (le_of_lt Real.pi_pos) zero_le_two
        exact lt_of_lt_of_le zero_lt_one
          (le_add_of_nonneg_left hpi_div_nonneg)
      have hClarge_le_A : Clarge ≤ A :=
        le_add_of_nonneg_right (le_of_lt hCcompact_pos)
      have hCcompact_le_A : Ccompact ≤ A :=
        le_add_of_nonneg_left (le_of_lt hClarge_pos)
      exact
        ⟨A, B, 1, hA_pos, hB_pos,
          fun w hw_re_nonneg hw_re_half hw_im_tail =>
            if hw_large : H ≤ ‖w.im‖ then
              have hlarge_w :
                  ‖(Complex.Gamma w)⁻¹‖ ≤
                    Clarge *
                      Complex.fixedRealPartVerticalReciprocalStirlingEnvelope
                        w.re w.im :=
                hlarge w hw_re_nonneg hw_re_half hw_large
              have henv :
                  Complex.fixedRealPartVerticalReciprocalStirlingEnvelope
                      w.re w.im ≤
                    Real.exp (B * (1 + ‖w‖)) := by
                have hpoint_eq :
                    Complex.fixedRealPartVerticalPoint w.re w.im = w := by
                  exact Complex.ext
                    (Complex.fixedRealPartVerticalPoint_re w.re w.im)
                    (Complex.fixedRealPartVerticalPoint_im w.re w.im)
                have hraw :
                    Complex.fixedRealPartVerticalReciprocalStirlingEnvelope
                        w.re w.im ≤
                      Real.exp (((Real.pi / 2) + 1) *
                        (1 + ‖Complex.fixedRealPartVerticalPoint w.re w.im‖)) :=
                  Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_zero_half_le_exp
                    hw_re_nonneg hw_re_half
                have hB_def : B = (Real.pi / 2) + 1 := rfl
                have hexp_eq :
                    Real.exp (((Real.pi / 2) + 1) *
                        (1 + ‖Complex.fixedRealPartVerticalPoint w.re w.im‖)) =
                      Real.exp (B * (1 + ‖w‖)) := by
                  have hnorm_eq :
                      ‖Complex.fixedRealPartVerticalPoint w.re w.im‖ = ‖w‖ :=
                    congrArg norm hpoint_eq
                  calc
                    Real.exp (((Real.pi / 2) + 1) *
                        (1 + ‖Complex.fixedRealPartVerticalPoint w.re w.im‖)) =
                        Real.exp (((Real.pi / 2) + 1) * (1 + ‖w‖)) := by
                      exact congrArg
                        (fun u : ℝ => Real.exp (((Real.pi / 2) + 1) * (1 + u)))
                        hnorm_eq
                    _ = Real.exp (B * (1 + ‖w‖)) := by
                      exact congrArg
                        (fun u : ℝ => Real.exp (u * (1 + ‖w‖)))
                        hB_def.symm
                exact le_trans hraw (le_of_eq hexp_eq)
              have henv_nonneg :
                  0 ≤
                    Complex.fixedRealPartVerticalReciprocalStirlingEnvelope
                      w.re w.im :=
                le_of_lt
                  (Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_pos
                    w.re w.im)
              have hexp_nonneg : 0 ≤ Real.exp (B * (1 + ‖w‖)) :=
                le_of_lt (Real.exp_pos (B * (1 + ‖w‖)))
              have hscaled_env :
                  Clarge *
                      Complex.fixedRealPartVerticalReciprocalStirlingEnvelope
                        w.re w.im ≤
                    Clarge * Real.exp (B * (1 + ‖w‖)) :=
                mul_le_mul_of_nonneg_left henv (le_of_lt hClarge_pos)
              have hscaled_const :
                  Clarge * Real.exp (B * (1 + ‖w‖)) ≤
                    A * Real.exp (B * (1 + ‖w‖)) :=
                mul_le_mul_of_nonneg_right hClarge_le_A hexp_nonneg
              have hpow_one :
                  (1 + ‖w‖) ^ (1 : ℕ) = 1 + ‖w‖ :=
                pow_one (1 + ‖w‖)
              calc
                ‖(Complex.Gamma w)⁻¹‖ ≤
                    Clarge *
                      Complex.fixedRealPartVerticalReciprocalStirlingEnvelope
                        w.re w.im := hlarge_w
                _ ≤ Clarge * Real.exp (B * (1 + ‖w‖)) :=
                  hscaled_env
                _ ≤ A * Real.exp (B * (1 + ‖w‖)) :=
                  hscaled_const
                _ = A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) := by
                  exact congrArg (fun u : ℝ => A * Real.exp (B * u))
                    hpow_one.symm
            else
              have hw_compact_upper : ‖w.im‖ ≤ H :=
                le_of_not_ge hw_large
              have hcompact_w :
                  ‖(Complex.Gamma w)⁻¹‖ ≤ Ccompact :=
                hcompact w hw_re_nonneg hw_re_half hw_im_tail hw_compact_upper
              have hbase_nonneg : 0 ≤ 1 + ‖w‖ :=
                le_trans zero_le_one
                  (le_add_of_nonneg_right (norm_nonneg w))
              have hpow_nonneg : 0 ≤ (1 + ‖w‖) ^ (1 : ℕ) :=
                pow_nonneg hbase_nonneg 1
              have hexponent_nonneg : 0 ≤ B * (1 + ‖w‖) ^ (1 : ℕ) :=
                mul_nonneg (le_of_lt hB_pos) hpow_nonneg
              have hone_le_exp :
                  (1 : ℝ) ≤ Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                Real.one_le_exp hexponent_nonneg
              have hCcompact_nonneg : 0 ≤ Ccompact :=
                le_of_lt hCcompact_pos
              have hconst_le_A :
                  Ccompact ≤ A :=
                hCcompact_le_A
              have hA_nonneg : 0 ≤ A :=
                le_of_lt hA_pos
              have hA_le_Aexp :
                  A ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) := by
                calc
                  A = A * 1 := (mul_one A).symm
                  _ ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                    mul_le_mul_of_nonneg_left hone_le_exp hA_nonneg
              calc
                ‖(Complex.Gamma w)⁻¹‖ ≤ Ccompact := hcompact_w
                _ ≤ A := hconst_le_A
                _ ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                  hA_le_Aexp⟩

end
end LFunctions
end Boundary
