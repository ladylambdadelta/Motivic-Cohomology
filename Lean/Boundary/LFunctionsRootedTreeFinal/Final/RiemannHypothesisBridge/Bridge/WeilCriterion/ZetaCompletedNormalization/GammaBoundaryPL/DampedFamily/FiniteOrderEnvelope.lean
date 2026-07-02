import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.HolomorphyAndBarriers

/-!
# Finite-order envelope estimates for damped-family absorption

This file owns the real asymptotic comparison used by the Gamma-boundary
damping absorbers.  It is deliberately independent of the Euler boundary
transport chain: the theorem below is a real growth estimate, not a zeta
transport statement.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open Asymptotics

theorem gammaBoundaryPL_real_isBigO_exp_eventually_le_pos_mul
    {f : ℝ → ℝ}
    (c : ℝ)
    (h : f =O[Filter.atTop] fun T : ℝ => Real.exp (c * T)) :
    ∃ D : ℝ,
      0 < D ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        f T ≤ D * Real.exp (c * T) := by
  match h.isBigOWith with
  | ⟨C, hC⟩ =>
      have hnonneg :
          ∀ᶠ T : ℝ in Filter.atTop,
            0 ≤ Real.exp (c * T) :=
        Filter.Eventually.of_forall
          (fun T => le_of_lt (Real.exp_pos (c * T)))
      exact
        ⟨|C| + 1, add_pos_of_nonneg_of_pos (abs_nonneg C) zero_lt_one,
          (hC.bound.and hnonneg).mono
            (fun T hT =>
              by
                let G : ℝ := Real.exp (c * T)
                let D : ℝ := |C| + 1
                have hf_le_norm : f T ≤ ‖f T‖ :=
                  Real.le_norm_self (f T)
                have hC_le_abs : C ≤ |C| :=
                  le_abs_self C
                have hC_le_D : C ≤ D :=
                  le_trans hC_le_abs (le_add_of_nonneg_right zero_le_one)
                have hG_norm_nonneg : 0 ≤ ‖G‖ :=
                  norm_nonneg G
                have hmul_le : C * ‖G‖ ≤ D * ‖G‖ :=
                  mul_le_mul_of_nonneg_right hC_le_D hG_norm_nonneg
                have hG_norm : ‖G‖ = G :=
                  Real.norm_of_nonneg hT.2
                have hmul_eq : D * ‖G‖ = D * G :=
                  congrArg (fun x : ℝ => D * x) hG_norm
                calc
                  f T ≤ ‖f T‖ :=
                    hf_le_norm
                  _ ≤ C * ‖G‖ :=
                    hT.1
                  _ ≤ D * ‖G‖ :=
                    hmul_le
                  _ = D * G :=
                    hmul_eq)⟩

theorem gammaBoundaryPL_finiteOrder_shiftedPower_isBigO_scaledPower
    (c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => (1 + T) ^ m) =O[Filter.atTop]
      fun T : ℝ => (c * T) ^ m := by
  let K : ℝ := (2 / c) ^ m
  exact
    IsBigO.of_bound K
      (Filter.eventually_atTop.2
        ⟨1, fun T hT =>
            have hT_nonneg : 0 ≤ T :=
              le_trans zero_le_one hT
            have hcT_nonneg : 0 ≤ c * T :=
              mul_nonneg (le_of_lt hc) hT_nonneg
            have hleft_nonneg : 0 ≤ (1 + T) ^ m :=
              pow_nonneg (add_nonneg zero_le_one hT_nonneg) m
            have hnorm_left :
                ‖(1 + T) ^ m‖ = (1 + T) ^ m :=
              Real.norm_of_nonneg hleft_nonneg
            have hnorm_right_base :
                ‖(c * T) ^ m‖ = (c * T) ^ m :=
              Real.norm_of_nonneg (pow_nonneg hcT_nonneg m)
            have hshift_le_twoT : 1 + T ≤ 2 * T := by
              calc
                1 + T ≤ T + T :=
                  add_le_add_right hT T
                _ = 2 * T :=
                  (two_mul T).symm
            have htwoT_eq :
                2 * T = (2 / c) * (c * T) := by
              calc
                2 * T = ((2 / c) * c) * T := by
                  exact
                    (congrArg
                      (fun x : ℝ => x * T)
                      (div_mul_cancel₀ 2 (ne_of_gt hc))).symm
                _ = (2 / c) * (c * T) :=
                  mul_assoc (2 / c) c T
            have hbase_le :
                1 + T ≤ (2 / c) * (c * T) :=
              Eq.subst
                (motive := fun x : ℝ => 1 + T ≤ x)
                htwoT_eq
                hshift_le_twoT
            have hpow_le :
                (1 + T) ^ m ≤ ((2 / c) * (c * T)) ^ m :=
              pow_le_pow_left₀ (add_nonneg zero_le_one hT_nonneg) hbase_le m
            have hmul_pow :
                ((2 / c) * (c * T)) ^ m = K * (c * T) ^ m :=
              mul_pow (2 / c) (c * T) m
            have hraw :
                (1 + T) ^ m ≤ K * (c * T) ^ m :=
              Eq.subst
                (motive := fun x : ℝ => (1 + T) ^ m ≤ x)
                hmul_pow
                hpow_le
            have htarget :
                ‖(1 + T) ^ m‖ ≤ K * ‖(c * T) ^ m‖ :=
              Eq.subst
                (motive := fun x : ℝ => ‖(1 + T) ^ m‖ ≤ K * x)
                hnorm_right_base.symm
                (Eq.subst
                  (motive := fun x : ℝ => x ≤ K * (c * T) ^ m)
                  hnorm_left.symm
                  hraw)
            htarget
        ⟩)

theorem gammaBoundaryPL_finiteOrder_scaledPower_isBigO_exp_scaled
    (c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => (c * T) ^ m) =O[Filter.atTop]
      fun T : ℝ => Real.exp (c * T) := by
  exact
    (Real.isLittleO_pow_exp_atTop (n := m)).isBigO.comp_tendsto
      (Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id)

theorem gammaBoundaryPL_finiteOrder_shiftedPower_isBigO_exp
    (c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => (1 + T) ^ m) =O[Filter.atTop]
      fun T : ℝ => Real.exp (c * T) := by
  exact
    (gammaBoundaryPL_finiteOrder_shiftedPower_isBigO_scaledPower c m hc).trans
      (gammaBoundaryPL_finiteOrder_scaledPower_isBigO_exp_scaled c m hc)

theorem gammaBoundaryPL_finiteOrder_verticalExponent_isBigO_exp
    (A B c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => Real.log A + B * (1 + T) ^ m) =O[Filter.atTop]
      fun T : ℝ => Real.exp (c * T) := by
  have hconst :
      (fun _T : ℝ => Real.log A) =O[Filter.atTop]
        fun T : ℝ => Real.exp (c * T) := by
    have hone :
        (fun _T : ℝ => (1 : ℝ)) =O[Filter.atTop]
          fun T : ℝ => Real.exp (c * T) := by
      exact
        IsBigO.of_bound 1
          (Filter.eventually_atTop.2
            ⟨0, fun T hT =>
              have hcT_nonneg : 0 ≤ c * T :=
                mul_nonneg (le_of_lt hc) hT
              have hone_le_exp : (1 : ℝ) ≤ Real.exp (c * T) := by
                calc
                  (1 : ℝ) = Real.exp 0 :=
                    (Real.exp_zero).symm
                  _ ≤ Real.exp (c * T) :=
                    Real.exp_le_exp.mpr hcT_nonneg
              have hnorm_one : ‖(1 : ℝ)‖ = (1 : ℝ) :=
                norm_one
              have hexp_nonneg : 0 ≤ Real.exp (c * T) :=
                le_of_lt (Real.exp_pos (c * T))
              have hnorm_exp : ‖Real.exp (c * T)‖ = Real.exp (c * T) :=
                Real.norm_of_nonneg hexp_nonneg
              have htarget :
                  ‖(1 : ℝ)‖ ≤ (1 : ℝ) * ‖Real.exp (c * T)‖ :=
                Eq.subst
                  (motive := fun x : ℝ => ‖(1 : ℝ)‖ ≤ (1 : ℝ) * x)
                  hnorm_exp.symm
                  (Eq.subst
                    (motive := fun x : ℝ => x ≤ (1 : ℝ) * Real.exp (c * T))
                    hnorm_one.symm
                    (Eq.subst
                      (motive := fun x : ℝ => (1 : ℝ) ≤ x)
                      (one_mul (Real.exp (c * T))).symm
                      hone_le_exp))
              htarget⟩)
    have hmul_const :
        (fun _T : ℝ => Real.log A * (1 : ℝ)) =O[Filter.atTop]
          fun T : ℝ => Real.exp (c * T) :=
      (isBigO_const_mul_self (Real.log A)
        (fun _T : ℝ => (1 : ℝ)) Filter.atTop).trans hone
    exact
      hmul_const.congr_left
        (fun _T =>
          calc
            Real.log A * (1 : ℝ) = Real.log A :=
              mul_one (Real.log A))
  have hpoly :
      (fun T : ℝ => B * (1 + T) ^ m) =O[Filter.atTop]
        fun T : ℝ => Real.exp (c * T) := by
    exact
      (gammaBoundaryPL_finiteOrder_shiftedPower_isBigO_exp c m hc).const_mul_left B
  exact IsBigO.add hconst hpoly

/-- A finite-order vertical exponent is eventually dominated by a positive
multiple of the double-exponential absorber exponent. -/
theorem gammaBoundaryPL_finiteOrder_verticalExponent_eventually_le_doubleExponentialExponent
    (A B c : ℝ)
    (m : ℕ)
    (_hA : 0 < A)
    (_hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      0 < D ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        Real.log A + B * (1 + T) ^ m ≤ D * Real.exp (c * T) := by
  exact gammaBoundaryPL_real_isBigO_exp_eventually_le_pos_mul c
    (gammaBoundaryPL_finiteOrder_verticalExponent_isBigO_exp A B c m hc)

end

end LFunctions
end Boundary
