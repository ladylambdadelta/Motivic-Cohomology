import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FixedCutoffHolomorphic

/-!
# Local majorants for fixed-cutoff Euler-Maclaurin kernels

This file owns the elementary real-tail estimates used to dominate the
fixed-cutoff Bernoulli kernel locally on the punctured strip.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open MeasureTheory
local notation "π" => Real.pi

/-- A positive natural cutoff tail starts at least at one. -/
theorem eulerMaclaurin_one_le_of_mem_Ioi_nat_cast
    (N : ℕ)
    (hN : 0 < N)
    {x : ℝ}
    (hx : x ∈ Set.Ioi (((N : ℕ) : ℝ))) :
    1 ≤ x := by
  have hN_one_nat : 1 ≤ N :=
    Nat.succ_le_of_lt hN
  have hN_one_real : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by
    have hcast : (((1 : ℕ) : ℝ)) ≤ ((N : ℕ) : ℝ) :=
      (Nat.cast_le (α := ℝ)).mpr hN_one_nat
    exact Eq.subst
      (motive := fun t : ℝ => t ≤ ((N : ℕ) : ℝ))
      (Nat.cast_one)
      hcast
  exact le_trans hN_one_real (le_of_lt hx)

/-- Positive-real complex powers in the local Euler-Maclaurin tail have the
expected real-power norm. -/
theorem eulerMaclaurin_norm_real_cpow_neg_add_one_eq_rpow
    {x : ℝ}
    (hx : 0 < x)
    (z : ℂ) :
    ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ = x ^ (-(z.re + 1)) := by
  have hnorm :
      ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ =
        Complex.abs (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
    exact Complex.norm_eq_abs (((x : ℝ) : ℂ) ^ (-(z + 1)))
  have habs :
      Complex.abs (((x : ℝ) : ℂ) ^ (-(z + 1))) =
        x ^ (-(z + 1)).re :=
    Complex.abs_cpow_eq_rpow_re_of_pos hx (-(z + 1))
  have hre : (-(z + 1)).re = -(z.re + 1) := by
    calc
      (-(z + 1)).re = -((z + 1).re) := by
        exact Complex.neg_re (z + 1)
      _ = -(z.re + (1 : ℂ).re) := by
        exact congrArg Neg.neg (Complex.add_re z 1)
      _ = -(z.re + 1) := by
        exact congrArg (fun t : ℝ => -(z.re + t)) Complex.one_re
  exact Eq.trans (Eq.trans hnorm habs) (congrArg (fun e : ℝ => x ^ e) hre)

/-- If `δ ≤ re z`, then on a tail with `x ≥ 1` the local complex-power norm
is bounded by `x ^ (-(δ + 1))`. -/
theorem eulerMaclaurin_norm_real_cpow_le_rpow_of_re_lower
    {x δ : ℝ}
    (hx_pos : 0 < x)
    (hx_one : 1 ≤ x)
    (z : ℂ)
    (hδz : δ ≤ z.re) :
    ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ x ^ (-(δ + 1)) := by
  have hnorm :
      ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ =
        x ^ (-(z.re + 1)) :=
    eulerMaclaurin_norm_real_cpow_neg_add_one_eq_rpow hx_pos z
  have hexponent :
      -(z.re + 1) ≤ -(δ + 1) := by
    exact neg_le_neg (add_le_add_right hδz 1)
  have hpow :
      x ^ (-(z.re + 1)) ≤ x ^ (-(δ + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hx_one hexponent
  exact Eq.subst
    (motive := fun t : ℝ => t ≤ x ^ (-(δ + 1)))
    hnorm.symm
    hpow

/-- A small complex ball around a point with positive real part has a uniform
positive lower bound on real parts.

The intended radius and lower bound are both `z₀.re / 2`.  This is the local
geometric input needed for Euler-Maclaurin dominated estimates on the full
punctured strip `0 < re z < 2`, where no global `1 ≤ re z` lower bound is
available. -/
theorem eulerMaclaurin_ball_realPart_lowerBound_of_pos_re
    (z₀ : ℂ)
  (hz₀_pos : 0 < z₀.re) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      ∀ z : ℂ, z ∈ Metric.ball z₀ r → δ ≤ z.re := by
  let r : ℝ := z₀.re / 2
  let δ : ℝ := z₀.re / 2
  have hr_pos : 0 < r := by
    exact half_pos hz₀_pos
  have hδ_pos : 0 < δ := by
    exact half_pos hz₀_pos
  have hlower :
      ∀ z : ℂ, z ∈ Metric.ball z₀ r → δ ≤ z.re := by
    intro z hz
    have hdist : dist z z₀ < r :=
      hz
    have hnorm : ‖z - z₀‖ < r := by
      exact Eq.subst
        (motive := fun t : ℝ => t < r)
        (dist_eq_norm z z₀)
        hdist
    have habs_re :
        |(z - z₀).re| < r := by
      have hle_abs :
          |(z - z₀).re| ≤ Complex.abs (z - z₀) :=
        Complex.abs_re_le_abs (z - z₀)
      have habs_norm :
          Complex.abs (z - z₀) = ‖z - z₀‖ := by
        exact (Complex.norm_eq_abs (z - z₀)).symm
      exact lt_of_le_of_lt hle_abs
        (Eq.subst
          (motive := fun t : ℝ => t < r)
          habs_norm.symm
          hnorm)
    have hre_sub_lt : z₀.re - z.re < r := by
      have hneg :
          -(z.re - z₀.re) ≤ |z.re - z₀.re| :=
        neg_le_abs (z.re - z₀.re)
      have hsub_re :
          (z - z₀).re = z.re - z₀.re := by
        exact Complex.sub_re z z₀
      have hrewrite :
          |(z - z₀).re| = |z.re - z₀.re| := by
        exact congrArg abs hsub_re
      have hneg_lt :
          -(z.re - z₀.re) < r :=
        lt_of_le_of_lt hneg
          (Eq.subst
            (motive := fun t : ℝ => t < r)
            hrewrite
            habs_re)
      calc
        z₀.re - z.re = -(z.re - z₀.re) := by
          exact (neg_sub z.re z₀.re).symm
        _ < r := hneg_lt
    have hre_lower : z₀.re - r < z.re := by
      have hlt_add : z₀.re < r + z.re :=
        sub_lt_iff_lt_add.mp hre_sub_lt
      calc
        z₀.re - r < (r + z.re) - r :=
          sub_lt_sub_right hlt_add r
        _ = z.re := by
          calc
            (r + z.re) - r = z.re + r - r := by
              exact congrArg (fun t : ℝ => t - r) (add_comm r z.re)
            _ = z.re := add_sub_cancel_right z.re r
    have hdelta_eq : δ = z₀.re - r := by
      calc
        δ = z₀.re / 2 := rfl
        _ = z₀.re - z₀.re / 2 := by
          exact (sub_half z₀.re).symm
        _ = z₀.re - r := rfl
    exact le_of_lt (Eq.subst (motive := fun t : ℝ => t < z.re) hdelta_eq.symm hre_lower)
  exact ⟨r, δ, hr_pos, hδ_pos, hlower⟩

/-- The real power tail with exponent `-(δ + 1)` is integrable on any positive
Euler-Maclaurin cutoff tail when `δ > 0`. -/
theorem eulerMaclaurin_integrableOn_Ioi_rpow_neg_delta_add_one
    (N : ℕ)
    (hN : 0 < N)
    (δ : ℝ)
    (hδ : 0 < δ) :
    IntegrableOn
      (fun x : ℝ => x ^ (-(δ + 1)))
      (Set.Ioi (((N : ℕ) : ℝ))) := by
  have hcutoff_pos : 0 < (((N : ℕ) : ℝ)) := by
    exact Nat.cast_pos.mpr hN
  have hexponent_lt :
      -(δ + 1) < -(1 : ℝ) := by
    exact neg_lt_neg (lt_add_of_pos_left 1 hδ)
  exact integrableOn_Ioi_rpow_of_lt hexponent_lt hcutoff_pos

/-- On a parameter ball with `δ ≤ re z`, the fixed-cutoff Bernoulli kernel is
dominated on the tail by the scalar integrable power `x ^ (-(δ + 1))`.

This is the analytic sink for the local punctured-strip majorant: it combines
`|B₁({x})| ≤ 1`, strict lower bounds for the real tail variable, the positive-real
`cpow` norm formula, and monotonicity of `x ^ s` in the exponent for `x ≥ N ≥ 1`.
It deliberately uses only the local lower bound `δ > 0`, not the later
closed-strip hypothesis `1 ≤ re z`. -/
theorem eulerMaclaurinBernoulliKernel_ae_le_rpow_majorant_of_ball_re_lower
    (N : ℕ)
    (hN : 0 < N)
    (z₀ : ℂ)
    (r δ : ℝ)
    (_hδ : 0 < δ)
    (hre_lower : ∀ z : ℂ, z ∈ Metric.ball z₀ r → δ ≤ z.re) :
    ∀ z : ℂ, z ∈ Metric.ball z₀ r →
      ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
        ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ ≤
            x ^ (-(δ + 1)) := by
  intro z hz_ball
  exact ae_restrict_of_forall_mem measurableSet_Ioi
    (fun x hx_tail => by
      have hx_one : 1 ≤ x :=
        eulerMaclaurin_one_le_of_mem_Ioi_nat_cast N hN hx_tail
      have hx_pos : 0 < x :=
        lt_of_lt_of_le zero_lt_one hx_one
      have hδz : δ ≤ z.re :=
        hre_lower z hz_ball
      have hB :
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 :=
        eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_finite x
      have hcpow :
          ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ x ^ (-(δ + 1)) :=
        eulerMaclaurin_norm_real_cpow_le_rpow_of_re_lower
          hx_pos hx_one z hδz
      have hcpow_nonneg :
          0 ≤ ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ :=
        norm_nonneg (((x : ℝ) : ℂ) ^ (-(z + 1)))
      have htarget_nonneg :
          0 ≤ x ^ (-(δ + 1)) :=
        Real.rpow_nonneg (le_of_lt hx_pos) (-(δ + 1))
      have hmul :
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ =
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
              ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ :=
        norm_mul
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
          (((x : ℝ) : ℂ) ^ (-(z + 1)))
      have hproduct :
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
              ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤
            1 * (x ^ (-(δ + 1))) :=
        mul_le_mul hB hcpow hcpow_nonneg zero_le_one
      exact Eq.subst
        (motive := fun t : ℝ => t ≤ x ^ (-(δ + 1)))
        hmul.symm
        (Eq.subst
          (motive := fun t : ℝ =>
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ t)
          (one_mul (x ^ (-(δ + 1))))
          hproduct))

/-- Locally uniform integrable majorant for the fixed-cutoff Bernoulli kernel
on compact parameter neighborhoods inside the punctured strip. -/
theorem eulerMaclaurinBernoulliKernel_local_integrable_majorant_on_puncturedStrip
    (N : ℕ)
    (hN : 0 < N)
    (z₀ : ℂ)
    (hz₀ : z₀ ∈ ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1})) :
    ∃ r : ℝ, 0 < r ∧
      ∃ g : ℝ → ℝ, IntegrableOn g (Set.Ioi (((N : ℕ) : ℝ))) ∧
        ∀ z : ℂ, z ∈ Metric.ball z₀ r →
          ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ ≤ g x := by
  have hz₀_pos : 0 < z₀.re :=
    hz₀.1
  exact
    match eulerMaclaurin_ball_realPart_lowerBound_of_pos_re z₀ hz₀_pos with
    | ⟨r, δ, hr_pos, hδ_pos, hre_lower⟩ =>
        let g : ℝ → ℝ := fun x : ℝ => x ^ (-(δ + 1))
        have hg_integrable :
            IntegrableOn g (Set.Ioi (((N : ℕ) : ℝ))) :=
          eulerMaclaurin_integrableOn_Ioi_rpow_neg_delta_add_one
            N hN δ hδ_pos
        have hmajorant :
            ∀ z : ℂ, z ∈ Metric.ball z₀ r →
              ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
                ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ ≤ g x := by
          intro z hz
          exact
            eulerMaclaurinBernoulliKernel_ae_le_rpow_majorant_of_ball_re_lower
              N hN z₀ r δ hδ_pos hre_lower z hz
        ⟨r, hr_pos, g, hg_integrable, hmajorant⟩

end

end LFunctions
end Boundary
