import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.PoleClearedBoundarySetup.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.Owner

/-!
# Pole-cleared zeta and boundary-line setup

This file is a mechanically split owner layer from the completed normalization
package.  It preserves the original declaration order and keeps downstream
imports routed through `ZetaCompletedNormalization.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The removable pole-cleared zeta factor is continuous everywhere. -/
theorem poleClearedRiemannZeta_continuousAt
    (z : ℂ) :
    ContinuousAt poleClearedRiemannZeta z := by
  exact dite (z = 1)
    (fun hz : z = 1 =>
      Eq.subst
        (motive := fun w : ℂ => ContinuousAt poleClearedRiemannZeta w)
        hz.symm
        ((continuousAt_update_same).2 riemannZeta_residue_one))
    (fun hz : z ≠ 1 => by
      have hraw :
        ContinuousAt (fun w : ℂ => (w - 1) * riemannZeta w) z :=
        (continuousAt_id.sub continuousAt_const).mul
          ((differentiableAt_riemannZeta hz).continuousAt)
      have hevent :
        poleClearedRiemannZeta =ᶠ[𝓝 z]
          (fun w : ℂ => (w - 1) * riemannZeta w) := by
        exact (eventually_ne_nhds hz).mono
          (fun w hw => poleClearedRiemannZeta_eq_of_ne_one hw)
      exact hraw.congr_of_eventuallyEq hevent)

/-- The removable pole-cleared zeta factor is continuous on the right critical compact
rectangle. -/
theorem poleClearedRiemannZeta_continuousOn_rightCriticalStripCompactSet :
    ContinuousOn poleClearedRiemannZeta
      completedRiemannZeta₀_rightCriticalStripCompactSet := by
  intro z _hz
  exact (poleClearedRiemannZeta_continuousAt z).continuousWithinAt

/-- Away from the removable pole face, the pole-cleared zeta factor is differentiable by
the ordinary zeta differentiability theorem. -/
theorem poleClearedRiemannZeta_differentiableAt_of_ne_one
    {z : ℂ}
    (hz : z ≠ 1) :
    DifferentiableAt ℂ poleClearedRiemannZeta z := by
  have hraw :
      DifferentiableAt ℂ (fun w : ℂ => (w - 1) * riemannZeta w) z :=
    (differentiableAt_id.sub differentiableAt_const).mul
      (differentiableAt_riemannZeta hz)
  have hevent :
      poleClearedRiemannZeta =ᶠ[𝓝 z]
        (fun w : ℂ => (w - 1) * riemannZeta w) := by
    exact (eventually_ne_nhds hz).mono
      (fun w hw => poleClearedRiemannZeta_eq_of_ne_one hw)
  exact hraw.congr_of_eventuallyEq hevent

/-- The residue-normalized pole-cleared zeta factor is analytic at the removable pole. -/
theorem poleClearedRiemannZeta_analyticAt_one :
    AnalyticAt ℂ poleClearedRiemannZeta 1 := by
  have hd :
      ∀ᶠ z in 𝓝[≠] (1 : ℂ),
        DifferentiableAt ℂ poleClearedRiemannZeta z := by
    exact self_mem_nhdsWithin.mono
      (fun z hz => poleClearedRiemannZeta_differentiableAt_of_ne_one hz)
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hd
    (poleClearedRiemannZeta_continuousAt 1)

/-- The removable pole-cleared zeta factor is differentiable everywhere. -/
theorem poleClearedRiemannZeta_differentiableAt
    (z : ℂ) :
    DifferentiableAt ℂ poleClearedRiemannZeta z := by
  exact dite (z = 1)
    (fun hz : z = 1 =>
      Eq.subst
        (motive := fun w : ℂ => DifferentiableAt ℂ poleClearedRiemannZeta w)
        hz.symm
        poleClearedRiemannZeta_analyticAt_one.differentiableAt)
    (fun hz : z ≠ 1 => poleClearedRiemannZeta_differentiableAt_of_ne_one hz)

/-- The pole-cleared zeta factor is differentiable on every set. -/
theorem poleClearedRiemannZeta_differentiableOn
    (s : Set ℂ) :
    DifferentiableOn ℂ poleClearedRiemannZeta s := by
  intro z _hz
  exact (poleClearedRiemannZeta_differentiableAt z).differentiableWithinAt

/-- Removable-pole holomorphy of the pole-cleared zeta factor on the open right
critical strip.

This is the zeta-side holomorphy input for the strip Phragmen-Lindelöf theorem: away
from `1` it is `(s - 1)ζ(s)`, and at `1` the removable value is the zeta residue. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl :
    DiffContOnCl ℂ poleClearedRiemannZeta
      (Complex.re ⁻¹' Set.Ioo 0 2) := by
  exact
    ⟨poleClearedRiemannZeta_differentiableOn (Complex.re ⁻¹' Set.Ioo 0 2),
      fun z _hz => (poleClearedRiemannZeta_continuousAt z).continuousWithinAt⟩

/-- Compact boundedness for the removable pole-cleared zeta factor. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet →
        ‖poleClearedRiemannZeta z‖ ≤ C := by
  exact match IsCompact.exists_bound_of_continuousOn
      completedRiemannZeta₀_rightCriticalStripCompactSet_isCompact
      poleClearedRiemannZeta_continuousOn_rightCriticalStripCompactSet with
    | ⟨C0, hC0⟩ =>
      ⟨max C0 0 + 1,
        add_pos_of_nonneg_of_pos (le_max_right C0 0) zero_lt_one,
        fun z hz => by
          have hraw : ‖poleClearedRiemannZeta z‖ ≤ C0 :=
            hC0 z hz
          exact le_trans hraw
            (le_trans (le_max_left C0 0)
              (le_add_of_nonneg_right zero_le_one))⟩

/-- Compact part of the pole-cleared zeta strip estimate. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_compact_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖z.im‖ ≤ 1 →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact match poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
    | ⟨C, hC, hbound⟩ =>
      ⟨C, 1, 0, hC, zero_lt_one, fun z hz0 hz2 hz_im => by
  have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
    ⟨hz0, hz2, hz_im⟩
  have hfactor_ge_one : (1 : ℝ) ≤ Real.exp (1 * (1 + ‖z‖) ^ 0) := by
    have hone : (1 : ℝ) * (1 + ‖z‖) ^ 0 = 1 := by
      exact Eq.trans (one_mul ((1 + ‖z‖) ^ 0)) (pow_zero (1 + ‖z‖))
    exact Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ Real.exp x)
      hone.symm
      (Real.one_le_exp_iff.mpr zero_le_one)
  have hC_nonneg : 0 ≤ C :=
    le_of_lt hC
  have hC_le_scaled :
      C ≤ C * Real.exp (1 * (1 + ‖z‖) ^ 0) :=
    le_mul_of_one_le_right hC_nonneg hfactor_ge_one
  exact dite (z = 1)
    (fun hz1 : z = 1 => by
    have hzero :
        ((1 : ℂ) - 1) * riemannZeta (1 : ℂ) = 0 := by
      exact Eq.trans (congrArg (fun x : ℂ => x * riemannZeta (1 : ℂ)) (sub_self (1 : ℂ)))
        (zero_mul (riemannZeta (1 : ℂ)))
    have hnorm_zero :
        ‖((1 : ℂ) - 1) * riemannZeta (1 : ℂ)‖ = 0 := by
      calc
        ‖((1 : ℂ) - 1) * riemannZeta (1 : ℂ)‖ = ‖(0 : ℂ)‖ := by
          exact congrArg norm hzero
        _ = 0 := by
          exact norm_zero
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ C * Real.exp (1 * (1 + ‖(1 : ℂ)‖) ^ 0))
      hnorm_zero.symm
      (le_trans (le_of_lt hC) hC_le_scaled))
    (fun hz1 : z ≠ 1 => by
    have hpc_eq :
        poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
      poleClearedRiemannZeta_eq_of_ne_one hz1
    have hraw :
        ‖(z - 1) * riemannZeta z‖ ≤ C := by
      exact Eq.subst
        (motive := fun w : ℂ => ‖w‖ ≤ C)
        hpc_eq
        (hbound z hz_mem)
    exact le_trans hraw hC_le_scaled)⟩

/-- Reflection sends the left edge of the zeta strip to the vertical line `re = 1`. -/
theorem one_sub_leftBoundary_re_eq_one
    {z : ℂ}
    (hz_re : z.re = 0) :
    ((1 : ℂ) - z).re = 1 := by
  calc
    ((1 : ℂ) - z).re = (1 : ℂ).re - z.re := by
      exact Complex.sub_re (1 : ℂ) z
    _ = 1 - z.re := by
      exact congrArg (fun x : ℝ => x - z.re) Complex.one_re
    _ = 1 := by
      exact Eq.subst
        (motive := fun x : ℝ => 1 - x = 1)
        hz_re.symm
        (sub_zero 1)

/-- On the left vertical tail, neither `z`, `1-z`, nor `Gammaℝ z` hits the exceptional
faces used in the completed-zeta normalization. -/
theorem Gammaℝ_leftBoundary_nonzero_of_verticalTail
    {z : ℂ}
    (hz_re : z.re = 0)
    (hz_im : 1 ≤ ‖z.im‖) :
    z ≠ 0 ∧ (1 : ℂ) - z ≠ 0 ∧
      Complex.Gammaℝ z ≠ 0 ∧ Complex.Gammaℝ ((1 : ℂ) - z) ≠ 0 := by
  have hz_ne_zero : z ≠ 0 := by
    intro hz
    have him_zero : z.im = 0 := by
      calc
        z.im = (0 : ℂ).im := by
          exact congrArg Complex.im hz
        _ = 0 := by
          exact Complex.zero_im
    have him_norm_zero : ‖z.im‖ = 0 := by
      calc
        ‖z.im‖ = ‖(0 : ℝ)‖ := by
          exact congrArg norm him_zero
        _ = 0 := by
          exact norm_zero
    have hone_le_zero : (1 : ℝ) ≤ 0 :=
      Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) ≤ x)
        him_norm_zero
        hz_im
    exact not_lt_of_ge hone_le_zero zero_lt_one
  have hone_sub_ne_zero : (1 : ℂ) - z ≠ 0 := by
    intro hsub
    have hre_zero : ((1 : ℂ) - z).re = 0 := by
      calc
        ((1 : ℂ) - z).re = (0 : ℂ).re := by
          exact congrArg Complex.re hsub
        _ = 0 := by
          exact Complex.zero_re
    have hre_one : ((1 : ℂ) - z).re = 1 := by
      exact one_sub_leftBoundary_re_eq_one hz_re
    have hone_eq_zero : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) = ((1 : ℂ) - z).re := hre_one.symm
        _ = 0 := hre_zero
    exact one_ne_zero hone_eq_zero
  have hGamma_ne : Complex.Gammaℝ z ≠ 0 := by
    exact Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm
      (le_of_eq hz_re.symm)
      (one_le_norm_of_one_le_norm_im hz_im)
  have hGamma_reflected_ne : Complex.Gammaℝ ((1 : ℂ) - z) ≠ 0 := by
    have hw_re_nonneg : 0 ≤ ((1 : ℂ) - z).re := by
      exact le_trans zero_le_one (le_of_eq (one_sub_leftBoundary_re_eq_one hz_re).symm)
    have hw_norm_ge_one : 1 ≤ ‖(1 : ℂ) - z‖ := by
      have him_abs_le : ‖((1 : ℂ) - z).im‖ ≤ ‖(1 : ℂ) - z‖ :=
        Complex.abs_im_le_abs ((1 : ℂ) - z)
      have him_eq : ((1 : ℂ) - z).im = -z.im := by
        calc
          ((1 : ℂ) - z).im = (1 : ℂ).im - z.im := by
            exact Complex.sub_im (1 : ℂ) z
          _ = 0 - z.im := by
            exact congrArg (fun x : ℝ => x - z.im) Complex.one_im
          _ = -z.im := by
            exact zero_sub z.im
      have him_norm_eq : ‖((1 : ℂ) - z).im‖ = ‖z.im‖ := by
        calc
          ‖((1 : ℂ) - z).im‖ = ‖-z.im‖ := by
            exact congrArg norm him_eq
          _ = ‖z.im‖ := by
            exact norm_neg z.im
      exact le_trans
        (Eq.subst (motive := fun x : ℝ => 1 ≤ x) him_norm_eq.symm hz_im)
        him_abs_le
    exact Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm hw_re_nonneg hw_norm_ge_one
  exact ⟨hz_ne_zero, hone_sub_ne_zero, hGamma_ne, hGamma_reflected_ne⟩

/-- The elementary pole-clearing ratio on the left boundary has finite-order growth.

This is the algebraic factor
`(z - 1) / (((1 : ℂ) - z) - 1)` separated from the Gamma-ratio Stirling input. -/
theorem leftBoundary_completedFunctionalEquation_poleClearing_ratio_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact ⟨2, 1, 1, zero_lt_two, zero_lt_one, fun z hz_re hz_im => by
  have hz_norm_ge_one : (1 : ℝ) ≤ ‖z‖ :=
    one_le_norm_of_one_le_norm_im hz_im
  have hden_eq : (((1 : ℂ) - z) - 1) = -z := by
    calc
      (((1 : ℂ) - z) - 1) = ((1 : ℂ) - 1) - z := by
        exact sub_sub (1 : ℂ) z 1
      _ = 0 - z := by
        exact congrArg (fun x : ℂ => x - z) (sub_self (1 : ℂ))
      _ = -z := by
        exact zero_sub z
  have hnum_norm_le : ‖z - 1‖ ≤ ‖z‖ + 1 :=
    le_trans (norm_sub_le z (1 : ℂ))
      (by
        exact le_of_eq
          (congrArg (fun x : ℝ => ‖z‖ + x) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))))
  have hnum_norm_le_two_norm : ‖z - 1‖ ≤ 2 * ‖z‖ := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + 1 := hnum_norm_le
      _ ≤ ‖z‖ + ‖z‖ := add_le_add_left hz_norm_ge_one ‖z‖
      _ = 2 * ‖z‖ := by
        exact (two_mul ‖z‖).symm
  have hz_norm_pos : 0 < ‖z‖ :=
    lt_of_lt_of_le zero_lt_one hz_norm_ge_one
  have hratio_le_two : ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤ (2 : ℝ) := by
    calc
      ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ =
          ‖z - 1‖ / ‖z‖ := by
        calc
          ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ =
              ‖z - 1‖ / ‖(((1 : ℂ) - z) - 1)‖ := by
            exact norm_div (z - 1) (((1 : ℂ) - z) - 1)
          _ = ‖z - 1‖ / ‖z‖ := by
            exact congrArg (fun x : ℝ => ‖z - 1‖ / x)
              (by
                calc
                  ‖(((1 : ℂ) - z) - 1)‖ = ‖-z‖ := by
                    exact congrArg norm hden_eq
                  _ = ‖z‖ := norm_neg z)
      _ ≤ (2 * ‖z‖) / ‖z‖ := div_le_div_of_nonneg_right hnum_norm_le_two_norm (norm_nonneg z)
      _ = 2 := by
        exact mul_div_cancel_right₀ 2 (ne_of_gt hz_norm_pos)
  have hone_le_exp :
      (1 : ℝ) ≤ Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ)) := by
    have hbase_nonneg : 0 ≤ (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) := by
      exact mul_nonneg zero_le_one
        (pow_nonneg (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))) 1)
    exact le_trans (le_add_of_nonneg_left hbase_nonneg)
      (Real.add_one_le_exp ((1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ)))
  calc
    ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤ 2 := hratio_le_two
    _ ≤ 2 * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ)) := by
      exact le_mul_of_one_le_right zero_le_two hone_le_exp⟩

/-- A positive polynomial vertical-height bound is an exponential finite-order bound in the
same vertical-height variable. -/
theorem vertical_polynomial_growth_bound_to_exponential_growth_bound
    {f : ℂ → ℂ}
    (hpoly :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * (1 + ‖z.im‖) ^ m) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m) := by
  exact match hpoly with
    | ⟨A, m, hA_pos, hbound⟩ =>
      ⟨A, 1, m, hA_pos, zero_lt_one, fun z hz_re hz_im => by
  let H : ℝ := (1 + ‖z.im‖) ^ m
  have hH_nonneg : 0 ≤ H :=
    pow_nonneg
      (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z.im)))
      m
  have hH_le_exp : H ≤ Real.exp ((1 : ℝ) * H) := by
    have hone_mul : (1 : ℝ) * H = H := by
      exact one_mul H
    exact Eq.subst
      (motive := fun x : ℝ => H ≤ Real.exp x)
      hone_mul.symm
      (Real.one_le_exp H)
  have hscaled :
      A * H ≤ A * Real.exp ((1 : ℝ) * H) :=
    mul_le_mul_of_nonneg_left hH_le_exp (le_of_lt hA_pos)
  exact le_trans (hbound z hz_re hz_im) hscaled⟩

/-- A point on the left boundary line is its vertical coordinate times `I`. -/
theorem leftBoundary_eq_im_mul_I
    (z : ℂ)
    (hz_re : z.re = 0) :
    z = (z.im : ℂ) * Complex.I := by
  ext
  · exact hz_re
  · rfl

/-- The unfolded completed real-Gamma ratio on the left boundary line `z = it`. -/
def unfoldedGammaℝLeftBoundaryRatioRealParam (t : ℝ) : ℂ :=
  (π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
      Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
    (π ^ (-((t : ℂ) * Complex.I) / 2) *
      Complex.Gamma (((t : ℂ) * Complex.I) / 2))

/-- The numerator in the unfolded completed real-Gamma ratio on the left boundary. -/
def unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam (t : ℝ) : ℂ :=
  π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
    Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)

/-- The denominator in the unfolded completed real-Gamma ratio on the left boundary. -/
def unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam (t : ℝ) : ℂ :=
  π ^ (-((t : ℂ) * Complex.I) / 2) *
    Complex.Gamma (((t : ℂ) * Complex.I) / 2)

/-- The unfolded left-boundary Gamma-ratio is the quotient of its named numerator
and denominator. -/
theorem unfoldedGammaℝLeftBoundaryRatioRealParam_eq_named_quotient
    (t : ℝ) :
    unfoldedGammaℝLeftBoundaryRatioRealParam t =
      unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t /
        unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t := by
  rfl

/-- The named numerator is the unfolded `Gammaℝ` factor at the reflected left-boundary
point. -/
theorem unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam_eq_Gammaℝ
    (t : ℝ) :
    unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t =
      Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) := by
  exact (Complex.Gammaℝ_def ((1 : ℂ) - (t : ℂ) * Complex.I)).symm

/-- The named denominator is the unfolded `Gammaℝ` factor at the left-boundary point. -/
theorem unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam_eq_Gammaℝ
    (t : ℝ) :
    unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t =
      Complex.Gammaℝ ((t : ℂ) * Complex.I) := by
  exact (Complex.Gammaℝ_def ((t : ℂ) * Complex.I)).symm

/-- The denominator in the unfolded left-boundary Gamma quotient is nonzero on the
vertical-tail range. -/
theorem unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam_ne_zero_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t ≠ 0 := by
  have haxis_re : (((t : ℂ) * Complex.I).re) = 0 := by
    calc
      (((t : ℂ) * Complex.I).re) =
          (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im := by
        exact Complex.mul_re (t : ℂ) Complex.I
      _ = t * 0 - 0 * 1 := by
        exact congrArg₂
          (fun x y : ℝ => x * Complex.I.re - y * Complex.I.im)
          Complex.ofReal_re
          Complex.ofReal_im
      _ = 0 := by
        exact Eq.trans (congrArg (fun x : ℝ => x - 0 * 1) (mul_zero t))
          (Eq.trans (congrArg (fun x : ℝ => 0 - x) (zero_mul 1)) (sub_self 0))
  have haxis_im_norm : ‖((t : ℂ) * Complex.I).im‖ = ‖t‖ := by
    have him : ((t : ℂ) * Complex.I).im = t := by
      calc
      ((t : ℂ) * Complex.I).im =
            (t : ℂ).re * Complex.I.im + (t : ℂ).im * Complex.I.re := by
          exact Complex.mul_im (t : ℂ) Complex.I
      _ = t * 1 + 0 * 0 := by
          exact congrArg₂
            (fun x y : ℝ => x * Complex.I.im + y * Complex.I.re)
            Complex.ofReal_re
            Complex.ofReal_im
      _ = t := by
        exact Eq.trans
          (congrArg₂ HAdd.hAdd (mul_one t) (zero_mul 0))
          (add_zero t)
    exact congrArg norm him
  have haxis_im : 1 ≤ ‖((t : ℂ) * Complex.I).im‖ :=
    Eq.subst
      (motive := fun x : ℝ => 1 ≤ x)
      haxis_im_norm.symm
      ht
  have hGamma_ne :
      Complex.Gammaℝ ((t : ℂ) * Complex.I) ≠ 0 :=
    (Gammaℝ_leftBoundary_nonzero_of_verticalTail haxis_re haxis_im).2.2.1
  intro hzero
  exact hGamma_ne
    (Eq.trans
      (unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam_eq_Gammaℝ t).symm
      hzero)

/-- The denominator in the unfolded left-boundary Gamma quotient has positive norm on
the vertical-tail range. -/
theorem norm_unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam_pos_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    0 < ‖unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t‖ :=
  norm_pos_iff.mpr
    (unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam_ne_zero_of_one_le_norm ht)

/-- Norm of the unfolded left-boundary Gamma quotient after naming numerator and
denominator. -/
theorem norm_unfoldedGammaℝLeftBoundaryRatioRealParam_eq_named_quotient
    (t : ℝ) :
    ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ =
      ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t /
        unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t‖ := by
  exact congrArg norm (unfoldedGammaℝLeftBoundaryRatioRealParam_eq_named_quotient t)

/-- Norm of the named unfolded left-boundary Gamma quotient is the quotient of the named
numerator and denominator norms. -/
theorem norm_unfoldedGammaℝLeftBoundaryRatio_named_quotient_eq_norm_div
    (t : ℝ) :
    ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t /
        unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t‖ =
      ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ /
        ‖unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t‖ := by
  exact norm_div
    (unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t)
    (unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)

/-- The π-normalized two-Gamma quotient is exactly the named unfolded quotient. -/
theorem inline_twoGammaQuotient_eq_unfoldedGammaℝLeftBoundaryRatioRealParam
    (t : ℝ) :
    (π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
          Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
        (π ^ (-((t : ℂ) * Complex.I) / 2) *
          Complex.Gamma (((t : ℂ) * Complex.I) / 2)) =
      unfoldedGammaℝLeftBoundaryRatioRealParam t := by
  rfl

/-- Norm transport from the inline π-normalized two-Gamma quotient to the named unfolded
quotient. -/
theorem norm_inline_twoGammaQuotient_eq_norm_unfoldedGammaℝLeftBoundaryRatioRealParam
    (t : ℝ) :
    ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
          Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
        (π ^ (-((t : ℂ) * Complex.I) / 2) *
          Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ =
      ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ := by
  exact congrArg norm (inline_twoGammaQuotient_eq_unfoldedGammaℝLeftBoundaryRatioRealParam t)

/-- The real-parameter unfolded Gamma-ratio is exactly the inline two-Gamma formula. -/
theorem unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline
    (t : ℝ) :
    unfoldedGammaℝLeftBoundaryRatioRealParam t =
      (π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
          Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
        (π ^ (-((t : ℂ) * Complex.I) / 2) *
          Complex.Gamma (((t : ℂ) * Complex.I) / 2)) := by
  rfl

/-- The completed real-Gamma ratio on the left boundary unfolds to the classical
two-Gamma ratio. -/
theorem Gammaℝ_leftBoundary_ratio_realParam_eq_unfolded
    (t : ℝ) :
    Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
        Complex.Gammaℝ ((t : ℂ) * Complex.I) =
      unfoldedGammaℝLeftBoundaryRatioRealParam t := by
  exact unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline t

/-- Norm form of the completed real-Gamma ratio unfolding on the left boundary. -/
theorem norm_Gammaℝ_leftBoundary_ratio_realParam_eq_norm_unfolded
    (t : ℝ) :
    ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
        Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ =
      ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ := by
  exact congrArg norm (Gammaℝ_leftBoundary_ratio_realParam_eq_unfolded t)

/-- The two-sided fixed-real-part vertical Stirling norm estimates for `Complex.Gamma`.

This is the exact classical special-function input after all downstream algebra has
been peeled off: for fixed real part `a`, `Γ(a + i b)` has vertical decay
`exp (-π |b| / 2)` and its reciprocal has the opposite exponential envelope,
with the dual polynomial powers; cf. DLMF §5.11. -/
theorem verticalComplexGammaStirling_fixedRealPart_twoSided_core_bound_standard
    (a : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
          C * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2) ∧
        ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
          C * Real.exp ((Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (1 / 2 - a) := by
  exact
    Complex.Gamma_closedRightHalfPlane_sectorial_and_vertical_stirling_bounds_classical.2 a

/-- The direct fixed-real-part vertical Stirling norm estimate for `Complex.Gamma`.

This is the canonical special-function owner input after the `π`-normalization has
been peeled off: for fixed real part `a`, the norm of `Γ(a + i b)` has the standard
`exp (-π |b| / 2)` vertical decay with polynomial factor
`(1 + |b|)^(a - 1/2)`; cf. DLMF §5.11. -/
theorem verticalComplexGammaStirling_fixedRealPart_norm_core_bound_standard
    (a : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
          C * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2) := by
  exact match verticalComplexGammaStirling_fixedRealPart_twoSided_core_bound_standard a with
    | ⟨C, hC_pos, hC⟩ => ⟨C, hC_pos, fun b hb => (hC b hb).1⟩

/-- The reciprocal fixed-real-part vertical Stirling estimate for `Complex.Gamma`.

This is the dual canonical special-function owner input: on each fixed vertical
line the reciprocal has the opposite exponential envelope and the reciprocal
polynomial exponent; cf. DLMF §5.11. -/
theorem verticalComplexGammaStirling_fixedRealPart_reciprocal_core_bound_standard
    (a : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
          C * Real.exp ((Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (1 / 2 - a) := by
  exact match verticalComplexGammaStirling_fixedRealPart_twoSided_core_bound_standard a with
    | ⟨C, hC_pos, hC⟩ => ⟨C, hC_pos, fun b hb => (hC b hb).2⟩

/-- The fixed-real-part direct Stirling envelope factor is nonnegative. -/
theorem fixedRealPart_gamma_norm_envelope_nonneg
    (a b : ℝ) :
    0 ≤ Real.exp (-(Real.pi / 2) * ‖b‖) *
      (1 + ‖b‖) ^ (a - 1 / 2) := by
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  exact mul_nonneg
    (le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖b‖)))
    (le_of_lt (Real.rpow_pos_of_pos hbase_pos (a - 1 / 2)))

/-- The fixed-real-part reciprocal Stirling envelope factor is nonnegative. -/
theorem fixedRealPart_gamma_reciprocal_envelope_nonneg
    (a b : ℝ) :
    0 ≤ Real.exp ((Real.pi / 2) * ‖b‖) *
      (1 + ‖b‖) ^ (1 / 2 - a) := by
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  exact mul_nonneg
    (le_of_lt (Real.exp_pos ((Real.pi / 2) * ‖b‖)))
    (le_of_lt (Real.rpow_pos_of_pos hbase_pos (1 / 2 - a)))

/-- A direct fixed-real-part vertical Gamma estimate remains valid after enlarging
its constant. -/
theorem verticalComplexGammaStirling_fixedRealPart_norm_core_bound_mono_constant
    {a C D : ℝ}
    (hCD : C ≤ D)
    (hC :
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
          C * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2)) :
    ∀ b : ℝ,
      1 / 2 ≤ ‖b‖ →
      ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
        D * Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2) := by
  intro b hb
  let E : ℝ :=
    Real.exp (-(Real.pi / 2) * ‖b‖) *
      (1 + ‖b‖) ^ (a - 1 / 2)
  have hE_nonneg : 0 ≤ E :=
    fixedRealPart_gamma_norm_envelope_nonneg a b
  have hscaled : C * E ≤ D * E :=
    mul_le_mul_of_nonneg_right hCD hE_nonneg
  have hsource_assoc :
      C * Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2) =
        C * E :=
    mul_assoc C (Real.exp (-(Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (a - 1 / 2))
  have htarget_assoc :
      D * Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2) =
        D * E :=
    mul_assoc D (Real.exp (-(Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (a - 1 / 2))
  exact Eq.subst
    (motive := fun x : ℝ =>
      ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ x)
    htarget_assoc.symm
    (le_trans
      (Eq.subst
        (motive := fun x : ℝ =>
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ x)
        hsource_assoc
        (hC b hb))
      hscaled)

/-- A reciprocal fixed-real-part vertical Gamma estimate remains valid after enlarging
its constant. -/
theorem verticalComplexGammaStirling_fixedRealPart_reciprocal_core_bound_mono_constant
    {a C D : ℝ}
    (hCD : C ≤ D)
    (hC :
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
          C * Real.exp ((Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (1 / 2 - a)) :
    ∀ b : ℝ,
      1 / 2 ≤ ‖b‖ →
      ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
        D * Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a) := by
  intro b hb
  let E : ℝ :=
    Real.exp ((Real.pi / 2) * ‖b‖) *
      (1 + ‖b‖) ^ (1 / 2 - a)
  have hE_nonneg : 0 ≤ E :=
    fixedRealPart_gamma_reciprocal_envelope_nonneg a b
  have hscaled : C * E ≤ D * E :=
    mul_le_mul_of_nonneg_right hCD hE_nonneg
  have hsource_assoc :
      C * Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a) =
        C * E :=
    mul_assoc C (Real.exp ((Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (1 / 2 - a))
  have htarget_assoc :
      D * Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a) =
        D * E :=
    mul_assoc D (Real.exp ((Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (1 / 2 - a))
  exact Eq.subst
    (motive := fun x : ℝ =>
      ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤ x)
    htarget_assoc.symm
    (le_trans
      (Eq.subst
        (motive := fun x : ℝ =>
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤ x)
        hsource_assoc
        (hC b hb))
      hscaled)

/-- The two fixed-real-part vertical Gamma estimates can be put under one positive
constant by enlarging to the sum of the two constants. -/
theorem verticalComplexGammaStirling_fixedRealPart_core_bounds_of_norm_and_reciprocal
    {a : ℝ}
    (hnorm :
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
            C * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2))
    (hreciprocal :
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
            C * Real.exp ((Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (1 / 2 - a)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
          C * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2) ∧
        ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
          C * Real.exp ((Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (1 / 2 - a) := by
  exact match hnorm, hreciprocal with
    | ⟨Cn, hCn_pos, hCn⟩, ⟨Cr, hCr_pos, hCr⟩ => by
  let C : ℝ := Cn + Cr
  have hC_pos : 0 < C :=
    add_pos hCn_pos hCr_pos
  have hCn_le_C : Cn ≤ C :=
    le_add_of_nonneg_right (le_of_lt hCr_pos)
  have hCr_le_C : Cr ≤ C :=
    le_add_of_nonneg_left (le_of_lt hCn_pos)
  have hnorm_C :
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
          C * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2) :=
    verticalComplexGammaStirling_fixedRealPart_norm_core_bound_mono_constant
      hCn_le_C hCn
  have hreciprocal_C :
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
          C * Real.exp ((Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (1 / 2 - a) :=
    verticalComplexGammaStirling_fixedRealPart_reciprocal_core_bound_mono_constant
      hCr_le_C hCr
  exact ⟨C, hC_pos, fun b hb => ⟨hnorm_C b hb, hreciprocal_C b hb⟩⟩

/-- Vertical complex Stirling on fixed real lines, in the two norm forms needed for
left-boundary Gamma transport.

This owner theorem is now only the common-constant transport from the direct and
reciprocal fixed-real-part vertical Stirling estimates. -/
theorem verticalComplexGammaStirling_fixedRealPart_core_bounds
    (a : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
          C * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2) ∧
        ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
          C * Real.exp ((Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (1 / 2 - a) := by
  exact verticalComplexGammaStirling_fixedRealPart_core_bounds_of_norm_and_reciprocal
    (verticalComplexGammaStirling_fixedRealPart_norm_core_bound_standard a)
    (verticalComplexGammaStirling_fixedRealPart_reciprocal_core_bound_standard a)

/-- The numerator Gamma argument on the left boundary is the fixed-real-part
vertical point `1/2 + i(-t/2)`. -/
theorem leftBoundary_numerator_complexGamma_argument_eq_fixedRealPart
    (t : ℝ) :
    (((1 : ℂ) - (t : ℂ) * Complex.I) / 2) =
      ((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · calc
      ((((1 : ℂ) - (t : ℂ) * Complex.I) / 2)).re =
          (((1 : ℂ) - (t : ℂ) * Complex.I).re) / 2 := by
        exact Complex.div_re_ofReal ((1 : ℂ) - (t : ℂ) * Complex.I) 2
      _ = 1 / 2 := by
        exact congrArg (fun x : ℝ => x / 2)
          (by
            calc
              (((1 : ℂ) - (t : ℂ) * Complex.I).re) =
                  (1 : ℂ).re - ((t : ℂ) * Complex.I).re := by
                exact Complex.sub_re (1 : ℂ) ((t : ℂ) * Complex.I)
              _ = 1 - ((t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im) := by
                exact congrArg
                  (fun x : ℝ => x - ((t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im))
                  Complex.one_re
              _ = 1 - (t * 0 - 0 * 1) := rfl
              _ = 1 := by
                calc
                  1 - (t * 0 - 0 * 1) = 1 - (0 - 0 * 1) := by
                    exact congrArg (fun x : ℝ => 1 - (x - 0 * 1)) (mul_zero t)
                  _ = 1 - (0 - 0) := by
                    exact congrArg (fun x : ℝ => 1 - (0 - x)) (zero_mul 1)
                  _ = 1 - 0 := by
                    exact congrArg (fun x : ℝ => 1 - x) (sub_zero 0)
                  _ = 1 := sub_zero 1)
      _ = (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I).re := by
        rfl
  · calc
      ((((1 : ℂ) - (t : ℂ) * Complex.I) / 2)).im =
          (((1 : ℂ) - (t : ℂ) * Complex.I).im) / 2 := by
        exact Complex.div_im_ofReal ((1 : ℂ) - (t : ℂ) * Complex.I) 2
      _ = -t / 2 := by
        exact congrArg (fun x : ℝ => x / 2)
          (by
            calc
              (((1 : ℂ) - (t : ℂ) * Complex.I).im) =
                  (1 : ℂ).im - ((t : ℂ) * Complex.I).im := by
                exact Complex.sub_im (1 : ℂ) ((t : ℂ) * Complex.I)
              _ = 0 - ((t : ℂ).re * Complex.I.im + (t : ℂ).im * Complex.I.re) := by
                exact congrArg
                  (fun x : ℝ => x - ((t : ℂ).re * Complex.I.im + (t : ℂ).im * Complex.I.re))
                  Complex.one_im
              _ = 0 - (t * 1 + 0 * 0) := rfl
              _ = 0 - (t + 0 * 0) := by
                exact congrArg (fun x : ℝ => 0 - (x + 0 * 0)) (mul_one t)
              _ = 0 - (t + 0) := by
                exact congrArg (fun x : ℝ => 0 - (t + x)) (zero_mul 0)
              _ = 0 - t := by
                exact congrArg (fun x : ℝ => 0 - x) (add_zero t)
              _ = -t := by
                exact zero_sub t)
      _ = (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I).im := by
        rfl

/-- The denominator Gamma argument on the left boundary is the fixed-real-part
vertical point `0 + i(t/2)`. -/
theorem leftBoundary_denominator_complexGamma_argument_eq_fixedRealPart
    (t : ℝ) :
    (((t : ℂ) * Complex.I) / 2) =
      ((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · calc
      (((t : ℂ) * Complex.I) / 2).re =
          (((t : ℂ) * Complex.I).re) / 2 := by
        exact Complex.div_re_ofReal ((t : ℂ) * Complex.I) 2
      _ = (t * 0 - 0 * 1) / 2 := by
        exact congrArg (fun x : ℝ => x / 2)
          (by
            calc
              (((t : ℂ) * Complex.I).re) =
                  (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im := by
                exact Complex.mul_re (t : ℂ) Complex.I
              _ = t * 0 - 0 * 1 := rfl)
      _ = 0 := by
        calc
          (t * 0 - 0 * 1) / 2 = (0 - 0 * 1) / 2 := by
            exact congrArg (fun x : ℝ => (x - 0 * 1) / 2) (mul_zero t)
          _ = (0 - 0) / 2 := by
            exact congrArg (fun x : ℝ => (0 - x) / 2) (zero_mul 1)
          _ = 0 / 2 := by
            exact congrArg (fun x : ℝ => x / 2) (sub_zero 0)
          _ = 0 := zero_div 2
      _ = (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I).re := by
        rfl
  · calc
      (((t : ℂ) * Complex.I) / 2).im =
          (((t : ℂ) * Complex.I).im) / 2 := by
        exact Complex.div_im_ofReal ((t : ℂ) * Complex.I) 2
      _ = (t * 1 + 0 * 0) / 2 := by
        exact congrArg (fun x : ℝ => x / 2)
          (by
            calc
              (((t : ℂ) * Complex.I).im) =
                  (t : ℂ).re * Complex.I.im + (t : ℂ).im * Complex.I.re := by
                exact Complex.mul_im (t : ℂ) Complex.I
              _ = t * 1 + 0 * 0 := rfl)
      _ = t / 2 := by
        calc
          (t * 1 + 0 * 0) / 2 = (t + 0 * 0) / 2 := by
            exact congrArg (fun x : ℝ => (x + 0 * 0) / 2) (mul_one t)
          _ = (t + 0) / 2 := by
            exact congrArg (fun x : ℝ => (t + x) / 2) (zero_mul 0)
          _ = t / 2 := by
            exact congrArg (fun x : ℝ => x / 2) (add_zero t)
      _ = (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I).im := by
        rfl

/-- The half-scaled vertical coordinate has norm at least `1/2` on the
left-boundary vertical-tail range. -/
theorem half_norm_ge_one_half_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    (1 / 2 : ℝ) ≤ ‖t / 2‖ := by
  have htwo_pos : (0 : ℝ) < 2 := zero_lt_two
  have hnorm_div : ‖t / 2‖ = ‖t‖ / 2 := by
    calc
      ‖t / 2‖ = ‖t‖ / ‖(2 : ℝ)‖ := by
        exact norm_div t 2
      _ = ‖t‖ / 2 := by
        exact congrArg (fun x : ℝ => ‖t‖ / x)
          (Real.norm_of_nonneg (le_of_lt htwo_pos))
  exact Eq.subst
    (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x)
    hnorm_div.symm
    ((div_le_div_right htwo_pos).mpr ht)

/-- Negating the half-scaled vertical coordinate preserves the half-tail bound. -/
theorem neg_half_norm_ge_one_half_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    (1 / 2 : ℝ) ≤ ‖-t / 2‖ := by
  have hneg_div : -t / 2 = -(t / 2) := by
    exact neg_div t 2
  have hnorm : ‖-t / 2‖ = ‖t / 2‖ := by
    calc
      ‖-t / 2‖ = ‖-(t / 2)‖ := by
        exact congrArg norm hneg_div
      _ = ‖t / 2‖ :=
        norm_neg (t / 2)
  exact Eq.subst
    (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x)
    hnorm.symm
    (half_norm_ge_one_half_of_one_le_norm ht)

/-- The numerator vertical line for the left-boundary quotient, before the `π`
normalization is attached.

This is the canonical classical special-function input: vertical Stirling for
`Γ(1/2 - i t/2)` with the exponential envelope needed on the left boundary;
cf. DLMF §5.11. -/
theorem verticalComplexGammaStirling_leftBoundary_numerator_core_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ ≤
          A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
  exact match verticalComplexGammaStirling_fixedRealPart_core_bounds (1 / 2) with
    | ⟨A, hA_pos, hA⟩ =>
      ⟨A, hA_pos, fun t ht => by
  have htail : (1 / 2 : ℝ) ≤ ‖-t / 2‖ :=
    neg_half_norm_ge_one_half_of_one_le_norm ht
  have hbound :
      ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
        A * Real.exp (-(Real.pi / 2) * ‖-t / 2‖) *
          (1 + ‖-t / 2‖) ^ ((1 / 2 : ℝ) - 1 / 2) :=
    (hA (-t / 2) htail).1
  have harg :
      Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2) =
        Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I) := by
    exact congrArg Complex.Gamma
      (leftBoundary_numerator_complexGamma_argument_eq_fixedRealPart t)
  have hpow :
      (1 + ‖-t / 2‖) ^ ((1 / 2 : ℝ) - 1 / 2) = 1 := by
    have hexponent :
        ((1 / 2 : ℝ) - 1 / 2) = 0 :=
      sub_self (1 / 2 : ℝ)
    exact Eq.subst
      (motive := fun x : ℝ => (1 + ‖-t / 2‖) ^ x = 1)
      hexponent.symm
      (Real.rpow_zero (1 + ‖-t / 2‖))
  have hexp :
      Real.exp (-(Real.pi / 2) * ‖-t / 2‖) =
        Real.exp (-(Real.pi / 4) * ‖t‖) := by
    have hnorm : ‖-t / 2‖ = ‖t‖ / 2 := by
      have hneg_div : -t / 2 = -(t / 2) := by
        exact neg_div t 2
      have htwo_nonneg : (0 : ℝ) ≤ 2 :=
        le_of_lt zero_lt_two
      calc
        ‖-t / 2‖ = ‖-(t / 2)‖ := by
          exact congrArg norm hneg_div
        _ = ‖t / 2‖ :=
          norm_neg (t / 2)
        _ = ‖t‖ / ‖(2 : ℝ)‖ := by
          exact norm_div t 2
        _ = ‖t‖ / 2 := by
          exact congrArg (fun x : ℝ => ‖t‖ / x)
            (Real.norm_of_nonneg htwo_nonneg)
    have hexponent :
        -(Real.pi / 2) * (‖t‖ / 2) = -(Real.pi / 4) * ‖t‖ := by
      have hdiv :
          (Real.pi / 2) / 2 = Real.pi / ((2 : ℝ) * 2) := by
        exact div_div Real.pi (2 : ℝ) 2
      have hnegdiv :
          -(Real.pi / 2) / 2 = -(Real.pi / ((2 : ℝ) * 2)) :=
        congrArg Neg.neg hdiv
      have hfour :
          ((2 : ℝ) * 2) = 4 :=
        rfl
      calc
        -(Real.pi / 2) * (‖t‖ / 2) =
            (-(Real.pi / 2) / 2) * ‖t‖ := by
          exact (mul_div_assoc (-(Real.pi / 2)) ‖t‖ 2).symm
        _ = (-(Real.pi / (2 * 2))) * ‖t‖ := by
          exact congrArg (fun x : ℝ => x * ‖t‖)
            hnegdiv
        _ = -(Real.pi / 4) * ‖t‖ := by
          exact congrArg (fun x : ℝ => -(Real.pi / x) * ‖t‖)
            hfour
    exact congrArg Real.exp
      (Eq.trans
        (congrArg (fun x : ℝ => -(Real.pi / 2) * x) hnorm)
        hexponent)
  exact Eq.subst
    (motive := fun x : ℂ => ‖x‖ ≤ A * Real.exp (-(Real.pi / 4) * ‖t‖))
    harg.symm
    (Eq.subst
      (motive := fun x : ℝ => ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) +
        ((-t / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ A * x)
      hexp
      (Eq.subst
        (motive := fun x : ℝ => ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) +
          ((-t / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
            A * Real.exp (-(Real.pi / 2) * ‖-t / 2‖) * x)
        hpow
        hbound))⟩

/-- The denominator vertical line for the left-boundary quotient, before the `π`
normalization is attached.

This is the canonical classical special-function input: the reciprocal vertical
Stirling estimate for `Γ(i t/2)`; cf. DLMF §5.11. -/
theorem verticalComplexGammaStirling_leftBoundary_denominator_inv_core_bound :
    ∃ B : ℝ,
      0 < B ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(Complex.Gamma (((t : ℂ) * Complex.I) / 2))⁻¹‖ ≤
          B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
  exact match verticalComplexGammaStirling_fixedRealPart_core_bounds 0 with
    | ⟨B, hB_pos, hB⟩ =>
      ⟨B, hB_pos, fun t ht => by
  have htail : (1 / 2 : ℝ) ≤ ‖t / 2‖ :=
    half_norm_ge_one_half_of_one_le_norm ht
  have hbound :
      ‖(Complex.Gamma (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I))⁻¹‖ ≤
        B * Real.exp ((Real.pi / 2) * ‖t / 2‖) *
          (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) :=
    (hB (t / 2) htail).2
  have harg :
      Complex.Gamma (((t : ℂ) * Complex.I) / 2) =
        Complex.Gamma (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I) := by
    exact congrArg Complex.Gamma
      (leftBoundary_denominator_complexGamma_argument_eq_fixedRealPart t)
  have hnorm_half : ‖t / 2‖ = ‖t‖ / 2 := by
    have htwo_nonneg : (0 : ℝ) ≤ 2 :=
      le_of_lt zero_lt_two
    calc
      ‖t / 2‖ = ‖t‖ / ‖(2 : ℝ)‖ := by
        exact norm_div t 2
      _ = ‖t‖ / 2 := by
        exact congrArg (fun x : ℝ => ‖t‖ / x)
          (Real.norm_of_nonneg htwo_nonneg)
  have hexp :
      Real.exp ((Real.pi / 2) * ‖t / 2‖) =
        Real.exp ((Real.pi / 4) * ‖t‖) := by
    have hexponent :
        (Real.pi / 2) * (‖t‖ / 2) = (Real.pi / 4) * ‖t‖ := by
      have hdiv :
          (Real.pi / 2) / 2 = Real.pi / ((2 : ℝ) * 2) := by
        exact div_div Real.pi (2 : ℝ) 2
      have hfour :
          ((2 : ℝ) * 2) = 4 :=
        rfl
      calc
        (Real.pi / 2) * (‖t‖ / 2) =
            ((Real.pi / 2) / 2) * ‖t‖ := by
          exact (mul_div_assoc (Real.pi / 2) ‖t‖ 2).symm
        _ = (Real.pi / ((2 : ℝ) * 2)) * ‖t‖ := by
          exact congrArg (fun x : ℝ => x * ‖t‖) hdiv
        _ = (Real.pi / 4) * ‖t‖ := by
          exact congrArg (fun x : ℝ => (Real.pi / x) * ‖t‖) hfour
    exact congrArg Real.exp
      (Eq.trans
        (congrArg (fun x : ℝ => (Real.pi / 2) * x) hnorm_half)
        hexponent)
  have hsqrt :
      (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) ≤ Real.sqrt (1 + ‖t‖) := by
    have hbase_nonneg : 0 ≤ 1 + ‖t / 2‖ :=
      add_nonneg zero_le_one (norm_nonneg (t / 2))
    have hhalf_le : ‖t‖ / 2 ≤ ‖t‖ :=
      div_le_self (norm_nonneg t) one_le_two
    have hbase_le : 1 + ‖t / 2‖ ≤ 1 + ‖t‖ := by
      exact add_le_add_left
        (Eq.subst
          (motive := fun x : ℝ => x ≤ ‖t‖)
          hnorm_half.symm
          hhalf_le)
        1
    have hexponent :
        ((1 / 2 : ℝ) - 0) = 1 / 2 :=
      sub_zero (1 / 2 : ℝ)
    have hrpow :
        (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) =
          Real.sqrt (1 + ‖t / 2‖) :=
      by
        have hsqrt :
            Real.sqrt (1 + ‖t / 2‖) = (1 + ‖t / 2‖) ^ (1 / 2 : ℝ) := by
          exact (Real.sqrt_eq_rpow (1 + ‖t / 2‖)).symm
        exact Eq.subst
          (motive := fun x : ℝ =>
            (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) =
              (1 + ‖t / 2‖) ^ x)
          hexponent.symm
          hsqrt.symm
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ Real.sqrt (1 + ‖t‖))
      hrpow.symm
      (Real.sqrt_le_sqrt hbase_le)
  have hscaled :
      B * Real.exp ((Real.pi / 2) * ‖t / 2‖) *
          (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) ≤
        B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
    have hleft_nonneg :
        0 ≤ B * Real.exp ((Real.pi / 2) * ‖t / 2‖) :=
      mul_nonneg (le_of_lt hB_pos) (le_of_lt (Real.exp_pos _))
    exact Eq.subst
      (motive := fun x : ℝ =>
        B * x * (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) ≤
          B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖))
      hexp
      (mul_le_mul_of_nonneg_left hsqrt hleft_nonneg)
  exact Eq.subst
    (motive := fun x : ℂ =>
      ‖x⁻¹‖ ≤ B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖))
    harg.symm
    (le_trans hbound hscaled)⟩

/-- The real part of the numerator `π`-normalizing exponent is `-1/2`. -/
theorem leftBoundary_numerator_piExponent_re
    (t : ℝ) :
    (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2).re = -(1 / 2 : ℝ) := by
  calc
    (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2).re =
        (-((1 : ℂ) - (t : ℂ) * Complex.I)).re / 2 := by
      exact Complex.div_re_ofReal (-((1 : ℂ) - (t : ℂ) * Complex.I)) 2
    _ = -(((1 : ℂ) - (t : ℂ) * Complex.I).re) / 2 := by
      exact congrArg (fun x : ℝ => x / 2)
        (Complex.neg_re ((1 : ℂ) - (t : ℂ) * Complex.I))
    _ = -(1 / 2 : ℝ) := by
      have hre_one : (((1 : ℂ) - (t : ℂ) * Complex.I).re) = 1 := by
        calc
          (((1 : ℂ) - (t : ℂ) * Complex.I).re) =
              (1 : ℂ).re - ((t : ℂ) * Complex.I).re := by
            exact Complex.sub_re (1 : ℂ) ((t : ℂ) * Complex.I)
          _ = 1 - ((t : ℂ) * Complex.I).re := by
            exact congrArg (fun x : ℝ => x - ((t : ℂ) * Complex.I).re) Complex.one_re
          _ = 1 - ((t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im) := by
            exact congrArg (fun x : ℝ => 1 - x)
              (Complex.mul_re (t : ℂ) Complex.I)
          _ = 1 - (t * 0 - 0 * 1) := by
            rfl
          _ = 1 := by
            calc
              1 - (t * 0 - 0 * 1) = 1 - (0 - 0 * 1) := by
                exact congrArg (fun x : ℝ => 1 - (x - 0 * 1)) (mul_zero t)
              _ = 1 - (0 - 0) := by
                exact congrArg (fun x : ℝ => 1 - (0 - x)) (zero_mul 1)
              _ = 1 - 0 := by
                exact congrArg (fun x : ℝ => 1 - x) (sub_zero 0)
              _ = 1 :=
                sub_zero 1
      calc
        -(((1 : ℂ) - (t : ℂ) * Complex.I).re) / 2 =
            -1 / 2 := by
          exact congrArg (fun x : ℝ => -x / 2) hre_one
        _ = -(1 / 2 : ℝ) := by
          exact neg_div 1 2

/-- The numerator `π`-normalizing factor is bounded by `1`; its constant
contribution is absorbed into the Stirling constant. -/
theorem norm_leftBoundary_numerator_piFactor_le_one
    (t : ℝ) :
    ‖π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)‖ ≤ 1 := by
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have hpi_one_le : (1 : ℝ) ≤ π :=
    le_of_lt Real.one_lt_pi
  have hnorm_eq :
      ‖π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)‖ =
        π ^ (-(1 / 2 : ℝ)) := by
    calc
      ‖π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)‖ =
          Complex.abs (π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)) := by
        exact Complex.norm_eq_abs
          (π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ))
      _ = π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ).re := by
        exact Complex.abs_cpow_eq_rpow_re_of_pos hpi_pos
          (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)
      _ = π ^ (-(1 / 2 : ℝ)) := by
        exact congrArg (fun x : ℝ => π ^ x)
          (leftBoundary_numerator_piExponent_re t)
  have hexponent_nonpos : (-(1 / 2 : ℝ)) ≤ 0 := by
    exact neg_nonpos.mpr
      (div_nonneg zero_le_one zero_le_two)
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1)
    hnorm_eq.symm
    (Real.rpow_le_one_of_one_le_of_nonpos hpi_one_le hexponent_nonpos)

/-- The real part of the denominator `π`-normalizing exponent is `0`. -/
theorem leftBoundary_denominator_piExponent_re
    (t : ℝ) :
    (-((t : ℂ) * Complex.I) / 2).re = 0 := by
  calc
    (-((t : ℂ) * Complex.I) / 2).re =
        (-((t : ℂ) * Complex.I)).re / 2 := by
      exact Complex.div_re_ofReal (-((t : ℂ) * Complex.I)) 2
    _ = -(((t : ℂ) * Complex.I).re) / 2 := by
      exact congrArg (fun x : ℝ => x / 2)
        (Complex.neg_re ((t : ℂ) * Complex.I))
    _ = -(t * 0 - 0 * 1) / 2 := by
      exact congrArg (fun x : ℝ => -x / 2)
        (calc
          (((t : ℂ) * Complex.I).re) =
              (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im := by
            exact Complex.mul_re (t : ℂ) Complex.I
          _ = t * 0 - 0 * 1 := by
            rfl)
    _ = 0 := by
      calc
        -(t * 0 - 0 * 1) / 2 = -(0 - 0 * 1) / 2 := by
          exact congrArg (fun x : ℝ => -(x - 0 * 1) / 2) (mul_zero t)
        _ = -(0 - 0) / 2 := by
          exact congrArg (fun x : ℝ => -(0 - x) / 2) (zero_mul 1)
        _ = -0 / 2 := by
          exact congrArg (fun x : ℝ => -x / 2) (sub_zero 0)
        _ = 0 / 2 := by
          exact congrArg (fun x : ℝ => x / 2) (neg_zero.symm)
        _ = 0 :=
          zero_div 2

/-- The denominator `π`-normalizing factor has norm one on the left-boundary
vertical line. -/
theorem norm_leftBoundary_denominator_piFactor_eq_one
    (t : ℝ) :
    ‖π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)‖ = 1 := by
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  calc
    ‖π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)‖ =
        Complex.abs (π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)) := by
      exact Complex.norm_eq_abs
        (π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ))
    _ = π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ).re := by
      exact Complex.abs_cpow_eq_rpow_re_of_pos hpi_pos
        (-((t : ℂ) * Complex.I) / 2 : ℂ)
    _ = π ^ (0 : ℝ) := by
      exact congrArg (fun x : ℝ => π ^ x)
        (leftBoundary_denominator_piExponent_re t)
    _ = 1 := by
      exact Real.rpow_zero π

/-- The denominator `π`-normalizing factor is nonzero on the left-boundary
vertical line. -/
theorem leftBoundary_denominator_piFactor_ne_zero
    (t : ℝ) :
    π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ) ≠ 0 := by
  intro hzero
  have hnorm_zero :
      ‖π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)‖ = 0 := by
    exact congrArg norm hzero
  have hone_zero : (1 : ℝ) = 0 := by
    calc
      (1 : ℝ) = ‖π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)‖ := by
        exact (norm_leftBoundary_denominator_piFactor_eq_one t).symm
      _ = 0 := hnorm_zero
  exact one_ne_zero hone_zero

/-- Attach the numerator `π`-normalization to the canonical vertical `Complex.Gamma`
Stirling estimate. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_numerator_bound_of_core
    (hcore :
      ∃ A : ℝ,
        0 < A ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ ≤
            A * Real.exp (-(Real.pi / 4) * ‖t‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ ≤
          A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
  exact match hcore with
    | ⟨A, hA_pos, hA⟩ =>
      ⟨A, hA_pos, fun t ht => by
  have hpi_le_one :
      ‖π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)‖ ≤ 1 :=
    norm_leftBoundary_numerator_piFactor_le_one t
  have hgamma_bound :
      ‖Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ ≤
        A * Real.exp (-(Real.pi / 4) * ‖t‖) :=
    hA t ht
  have htarget_nonneg :
      0 ≤ A * Real.exp (-(Real.pi / 4) * ‖t‖) :=
    mul_nonneg (le_of_lt hA_pos) (le_of_lt (Real.exp_pos _))
  calc
    ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ =
        ‖π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)‖ *
          ‖Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ := by
      exact norm_mul
        (π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ))
        (Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2))
    _ ≤ 1 * (A * Real.exp (-(Real.pi / 4) * ‖t‖)) := by
      exact mul_le_mul hpi_le_one hgamma_bound (norm_nonneg _) zero_le_one
    _ = A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
      exact one_mul (A * Real.exp (-(Real.pi / 4) * ‖t‖))⟩

/-- Attach the denominator `π`-normalization to the canonical reciprocal vertical
`Complex.Gamma` Stirling estimate. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_denominator_inv_bound_of_core
    (hcore :
      ∃ B : ℝ,
        0 < B ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖(Complex.Gamma (((t : ℂ) * Complex.I) / 2))⁻¹‖ ≤
            B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖)) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
          B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
  exact match hcore with
    | ⟨B, hB_pos, hB⟩ =>
      ⟨B, hB_pos, fun t ht => by
  let P : ℂ := π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)
  let G : ℂ := Complex.Gamma (((t : ℂ) * Complex.I) / 2)
  have hP_ne : P ≠ 0 :=
    leftBoundary_denominator_piFactor_ne_zero t
  have hP_norm_one : ‖P‖ = (1 : ℝ) :=
    norm_leftBoundary_denominator_piFactor_eq_one t
  have hraw :
      ‖G⁻¹‖ ≤ B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) :=
    hB t ht
  have hnorm_eq :
      ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ =
        ‖G⁻¹‖ := by
    calc
      ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ =
          ‖(P * G)⁻¹‖ := by
        rfl
      _ = ‖P⁻¹ * G⁻¹‖ := by
        exact congrArg norm (mul_inv_rev P G)
      _ = ‖P⁻¹‖ * ‖G⁻¹‖ := by
        exact norm_mul P⁻¹ G⁻¹
      _ = ‖P‖⁻¹ * ‖G⁻¹‖ := by
        exact congrArg (fun x : ℝ => x * ‖G⁻¹‖) (norm_inv P)
      _ = 1⁻¹ * ‖G⁻¹‖ := by
        exact congrArg (fun x : ℝ => x⁻¹ * ‖G⁻¹‖) hP_norm_one
      _ = 1 * ‖G⁻¹‖ := by
        exact congrArg (fun x : ℝ => x * ‖G⁻¹‖) (inv_one : (1 : ℝ)⁻¹ = 1)
      _ = ‖G⁻¹‖ := by
        exact one_mul ‖G⁻¹‖
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖))
    hnorm_eq.symm
    hraw⟩

/-- Vertical Stirling upper bound for the named numerator in the unfolded left-boundary
Gamma quotient.

This is one of the exact classical special-function inputs: Stirling on the vertical
line `((1 - it) / 2)`, including the `π` normalization; cf. DLMF §5.11. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_numerator_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ ≤
          A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
  exact
    twoSidedVerticalComplexGammaStirling_leftBoundary_numerator_bound_of_core
      verticalComplexGammaStirling_leftBoundary_numerator_core_bound

/-- Vertical Stirling reciprocal bound for the named denominator in the unfolded
left-boundary Gamma quotient.

This is the matching exact classical special-function input: Stirling on the vertical
line `(it / 2)`, inverted and normalized so the quotient algebra has the expected
square-root growth; cf. DLMF §5.11. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_denominator_inv_bound :
    ∃ B : ℝ,
      0 < B ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
          B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
  exact
    twoSidedVerticalComplexGammaStirling_leftBoundary_denominator_inv_bound_of_core
      verticalComplexGammaStirling_leftBoundary_denominator_inv_core_bound

/-- Algebraic quotient estimate obtained from the numerator bound and denominator
reciprocal bound.  The exponential factors cancel, leaving the square-root envelope. -/
theorem unfoldedGammaℝLeftBoundaryRatioRealParam_sqrt_growth_bound_of_numerator_and_denominator
    (hnum :
      ∃ A : ℝ,
        0 < A ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ ≤
            A * Real.exp (-(Real.pi / 4) * ‖t‖))
    (hden :
      ∃ B : ℝ,
        0 < B ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
            B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact match hnum, hden with
    | ⟨Anum, hAnum_pos, hAnum⟩, ⟨Bden, hBden_pos, hBden⟩ =>
      ⟨Anum * Bden, mul_pos hAnum_pos hBden_pos, fun t ht => by
  let Eminus : ℝ := Real.exp (-(Real.pi / 4) * ‖t‖)
  let Eplus : ℝ := Real.exp ((Real.pi / 4) * ‖t‖)
  let S : ℝ := Real.sqrt (1 + ‖t‖)
  have hnum_bound :
      ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ ≤ Anum * Eminus :=
    hAnum t ht
  have hden_bound :
      ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
        Bden * Eplus * S :=
    hBden t ht
  have hden_inv_nonneg :
      0 ≤ ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ :=
    norm_nonneg _
  have hquot_eq :
      ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ =
        ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ *
          ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ := by
    calc
      ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ =
          ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t /
            unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t‖ :=
        norm_unfoldedGammaℝLeftBoundaryRatioRealParam_eq_named_quotient t
      _ = ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t *
            (unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ := by
        rfl
      _ = ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ *
          ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ := by
        exact norm_mul
          (unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t)
          (unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹
  have hmul_bound :
      ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ *
          ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
        (Anum * Eminus) * (Bden * Eplus * S) :=
    mul_le_mul hnum_bound hden_bound hden_inv_nonneg
      (mul_nonneg (le_of_lt hAnum_pos) (Real.exp_pos _).le)
  have hexp_cancel :
      Eminus * Eplus = 1 := by
    have hsum_exp :
        (-(Real.pi / 4) * ‖t‖) + ((Real.pi / 4) * ‖t‖) = 0 := by
      have hneg :
          -(Real.pi / 4) * ‖t‖ =
            -((Real.pi / 4) * ‖t‖) :=
        neg_mul (Real.pi / 4) ‖t‖
      calc
        (-(Real.pi / 4) * ‖t‖) + ((Real.pi / 4) * ‖t‖) =
            -((Real.pi / 4) * ‖t‖) + ((Real.pi / 4) * ‖t‖) := by
          exact congrArg
            (fun x : ℝ => x + ((Real.pi / 4) * ‖t‖))
            hneg
        _ = 0 :=
          add_left_neg ((Real.pi / 4) * ‖t‖)
    calc
      Eminus * Eplus =
          Real.exp ((-(Real.pi / 4) * ‖t‖) + ((Real.pi / 4) * ‖t‖)) := by
        exact (Real.exp_add (-(Real.pi / 4) * ‖t‖) ((Real.pi / 4) * ‖t‖)).symm
      _ = Real.exp 0 := by
        exact congrArg Real.exp hsum_exp
      _ = 1 := Real.exp_zero
  have htarget_eq :
      (Anum * Eminus) * (Bden * Eplus * S) = (Anum * Bden) * S := by
    have hcomm :
        (Anum * Eminus) * (Bden * Eplus * S) =
          (Anum * Bden) * (Eminus * Eplus) * S := by
      calc
        (Anum * Eminus) * (Bden * Eplus * S) =
            Anum * (Eminus * (Bden * Eplus * S)) := by
          exact mul_assoc Anum Eminus (Bden * Eplus * S)
        _ = Anum * (Bden * (Eminus * Eplus * S)) := by
          exact congrArg (fun x : ℝ => Anum * x)
            (calc
              Eminus * (Bden * Eplus * S) =
                  Eminus * (Bden * (Eplus * S)) := by
                exact congrArg (fun x : ℝ => Eminus * x)
                  (mul_assoc Bden Eplus S)
              _ = Bden * (Eminus * (Eplus * S)) := by
                exact mul_left_comm Eminus Bden (Eplus * S)
              _ = Bden * ((Eminus * Eplus) * S) := by
                exact congrArg (fun x : ℝ => Bden * x)
                  (mul_assoc Eminus Eplus S).symm)
        _ = (Anum * Bden) * (Eminus * Eplus * S) := by
          exact (mul_assoc Anum Bden (Eminus * Eplus * S)).symm
        _ = (Anum * Bden) * ((Eminus * Eplus) * S) := by
          exact congrArg (fun x : ℝ => (Anum * Bden) * x)
            (mul_assoc Eminus Eplus S).symm
        _ = (Anum * Bden) * (Eminus * Eplus) * S := by
          exact mul_assoc (Anum * Bden) (Eminus * Eplus) S
    calc
      (Anum * Eminus) * (Bden * Eplus * S) =
          (Anum * Bden) * (Eminus * Eplus) * S :=
        hcomm
      _ = (Anum * Bden) * 1 * S := by
        exact congrArg (fun x : ℝ => (Anum * Bden) * x * S) hexp_cancel
      _ = (Anum * Bden) * S := by
        exact congrArg (fun x : ℝ => x * S)
          (mul_one (Anum * Bden))
  exact Eq.subst
    (motive := fun x : ℝ => ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤ x)
    htarget_eq
    (Eq.subst
      (motive := fun x : ℝ => x ≤ (Anum * Eminus) * (Bden * Eplus * S))
      hquot_eq.symm
      hmul_bound)⟩

/-- Inline form of the quotient algebra for the left-boundary two-Gamma expression. -/
theorem inline_twoGammaQuotient_sqrt_growth_bound_of_unfolded
    (hunfolded :
      ∃ A : ℝ,
        0 < A ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤
            A * Real.sqrt (1 + ‖t‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact match hunfolded with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun t ht =>
        Eq.subst
          (motive := fun x : ℝ => x ≤ A * Real.sqrt (1 + ‖t‖))
          (norm_inline_twoGammaQuotient_eq_norm_unfoldedGammaℝLeftBoundaryRatioRealParam t)
          (hbound t ht)⟩

/-- Vertical Stirling quotient corollary for the completed real-Gamma boundary
ratio.

This is the canonical quotient consequence of the two-sided vertical Stirling
formula, specialized to `(1 - it) / 2` and `it / 2`; cf. DLMF §5.11. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_twoGammaQuotient_sqrt_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact inline_twoGammaQuotient_sqrt_growth_bound_of_unfolded
    (unfoldedGammaℝLeftBoundaryRatioRealParam_sqrt_growth_bound_of_numerator_and_denominator
      twoSidedVerticalComplexGammaStirling_leftBoundary_numerator_bound
      twoSidedVerticalComplexGammaStirling_leftBoundary_denominator_inv_bound)

/-- The historical owner-root spelling for the left-boundary two-Gamma quotient estimate.

The proof is only name transport from the canonical two-sided vertical `Complex.Gamma`
Stirling quotient primitive. -/
theorem verticalStirling_complexGamma_leftBoundary_twoGammaQuotient_sqrt_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact
    twoSidedVerticalComplexGammaStirling_leftBoundary_twoGammaQuotient_sqrt_growth_bound

/-- Classical two-sided vertical Stirling control for the inline two-Gamma quotient on
the left boundary.

This is the smallest special-function input for the left-edge Gamma-ratio: after
substituting `z = it`, apply the two-sided vertical Stirling formula to the numerator
and denominator Gamma factors; cf. DLMF §5.11. -/
theorem classicalStirling_complexGamma_leftBoundary_twoGammaQuotient_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact
    verticalStirling_complexGamma_leftBoundary_twoGammaQuotient_sqrt_growth_bound

/-- Classical two-sided vertical Stirling control for the unfolded completed real-Gamma
ratio on the left boundary.

This is now only transport from the inline two-Gamma quotient to the local unfolded
ratio name. -/
theorem classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact match
    classicalStirling_complexGamma_leftBoundary_twoGammaQuotient_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling
    with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun t ht =>
        Eq.subst
          (motive := fun x : ℝ => x ≤ A * Real.sqrt (1 + ‖t‖))
          (congrArg norm (unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline t)).symm
          (hbound t ht)⟩

/-- Classical vertical Stirling control for the two-Gamma quotient on the left boundary.

This theorem is only the formula-level transport from the unfolded owner primitive to
the inline two-Gamma quotient. -/
theorem classicalStirling_complexGamma_leftBoundary_twoGammaQuotient_vertical_sqrt_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact match
    classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling
    with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun t ht =>
        Eq.subst
          (motive := fun x : ℝ => x ≤ A * Real.sqrt (1 + ‖t‖))
          (congrArg norm (unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline t))
          (hbound t ht)⟩

/-- Classical vertical Stirling control for the unfolded completed real Gamma ratio,
stated on the real parameter of the left boundary line.

This theorem is only the definitional transport from the two-Gamma quotient to the
local unfolded `Gammaℝ` ratio name. -/
theorem classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact
    classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling

/-- The named unfolded Gamma-ratio estimate is the older inline formula spelling. -/
theorem classicalStirling_unfoldedGammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact match classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun t ht =>
        Eq.subst
          (motive := fun x : ℝ => x ≤ A * Real.sqrt (1 + ‖t‖))
          (congrArg norm (unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline t))
          (hbound t ht)⟩

/-- The unfolded vertical Stirling estimate is exactly the corresponding `Gammaℝ`
estimate after applying `Gammaℝ_def`. -/
theorem classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
            Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact match classicalStirling_unfoldedGammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun t ht => by
  calc
    ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
        Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ =
        ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ :=
      norm_Gammaℝ_leftBoundary_ratio_realParam_eq_norm_unfolded t
    _ =
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ := by
      exact congrArg norm (unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline t)
    _ ≤ A * Real.sqrt (1 + ‖t‖) :=
      hbound t ht⟩

/-- On the vertical-tail height range, the square-root height envelope is bounded by the
linear height envelope. -/
theorem sqrt_one_add_norm_le_one_add_norm
    (t : ℝ) :
    Real.sqrt (1 + ‖t‖) ≤ 1 + ‖t‖ := by
  let H : ℝ := 1 + ‖t‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg t)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hH_le_mul_self : H ≤ H * H := by
    have hone_mul_le : (1 : ℝ) * H ≤ H * H :=
      mul_le_mul_of_nonneg_right hH_ge_one hH_nonneg
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ H * H)
      (one_mul H)
      hone_mul_le
  have hH_le_sq : H ≤ H ^ (2 : ℕ) :=
    Eq.subst
      (motive := fun x : ℝ => H ≤ x)
      (pow_two H).symm
      hH_le_mul_self
  exact (Real.sqrt_le_left hH_nonneg).mpr hH_le_sq

/-- Classical vertical Stirling control for the completed real Gamma ratio, stated on
the real parameter of the left boundary line.

This is the linear envelope consumed downstream; its only analytic input is the sharper
unfolded square-root Stirling estimate. -/
theorem classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_linear_growth_bound_realParam :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
            Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ ≤
          A * (1 + ‖t‖) := by
  exact match classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun t ht => by
  have hsqrt_to_linear :
      A * Real.sqrt (1 + ‖t‖) ≤ A * (1 + ‖t‖) :=
    mul_le_mul_of_nonneg_left
      (sqrt_one_add_norm_le_one_add_norm t)
      (le_of_lt hA_pos)
  exact le_trans (hbound t ht) hsqrt_to_linear⟩

/-- The real-parameter square-root Stirling estimate transported to the full left
boundary line. -/
theorem classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.sqrt (1 + ‖z.im‖) := by
  exact match classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun z hz_re hz_im => by
  have hz_axis : z = (z.im : ℂ) * Complex.I :=
    leftBoundary_eq_im_mul_I z hz_re
  have haxis_bound :
      ‖Complex.Gammaℝ ((1 : ℂ) - (z.im : ℂ) * Complex.I) /
          Complex.Gammaℝ ((z.im : ℂ) * Complex.I)‖ ≤
        A * Real.sqrt (1 + ‖z.im‖) :=
    hbound z.im hz_im
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖Complex.Gammaℝ ((1 : ℂ) - w) / Complex.Gammaℝ w‖ ≤
        A * Real.sqrt (1 + ‖z.im‖))
    hz_axis.symm
    haxis_bound⟩

/-- Classical two-sided vertical Stirling control for the completed real Gamma ratio on
the left boundary line, in the sharp polynomial degree needed by the critical-line
functional-equation transport. -/
theorem classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_linear_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * (1 + ‖z.im‖) := by
  exact match classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun z hz_re hz_im => by
  have hsqrt_to_linear :
      A * Real.sqrt (1 + ‖z.im‖) ≤ A * (1 + ‖z.im‖) :=
    mul_le_mul_of_nonneg_left
      (sqrt_one_add_norm_le_one_add_norm z.im)
      (le_of_lt hA_pos)
  exact le_trans (hbound z hz_re hz_im) hsqrt_to_linear⟩

/-- A vertical linear bound is the degree-one polynomial envelope used downstream. -/
theorem Gammaℝ_leftBoundary_ratio_vertical_polynomial_growth_bound_of_linear
    (hlinear :
      ∃ A : ℝ,
        0 < A ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
            A * (1 + ‖z.im‖)) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * (1 + ‖z.im‖) ^ m := by
  exact match hlinear with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, 1, hA_pos, fun z hz_re hz_im => by
  have hpow_one : (1 + ‖z.im‖) ^ (1 : ℕ) = 1 + ‖z.im‖ := by
    exact pow_one (1 + ‖z.im‖)
  exact Eq.subst
    (motive := fun x : ℝ =>
      ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤ A * x)
    hpow_one.symm
    (hbound z hz_re hz_im)⟩

/-- Standard polynomial Stirling control for the completed real Gamma ratio on the left
vertical tail.

This is the classical two-sided vertical Gamma-ratio estimate after substituting the
left boundary line `z = it`: the ratio is controlled by a fixed polynomial in `|t|`. -/
theorem Gammaℝ_leftBoundary_ratio_vertical_polynomial_stirling_growth_bound_standard :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * (1 + ‖z.im‖) ^ m := by
  exact Gammaℝ_leftBoundary_ratio_vertical_polynomial_growth_bound_of_linear
    classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_linear_growth_bound

/-- Standard finite-order Stirling control for the completed real Gamma ratio on the left
vertical tail, converted from the polynomial vertical-height Stirling statement.

This is the exact analytic statement left after the elementary pole-clearing ratio has
been separated from the completed-functional-equation multiplier. -/
theorem Gammaℝ_leftBoundary_ratio_vertical_stirling_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z.im‖) ^ m) := by
  exact vertical_polynomial_growth_bound_to_exponential_growth_bound
    Gammaℝ_leftBoundary_ratio_vertical_polynomial_stirling_growth_bound_standard

/-- A vertical-height Gamma-ratio Stirling estimate implies the complex-height envelope
used by the completed-functional-equation multiplier. -/
theorem Gammaℝ_leftBoundary_ratio_growth_bound_of_vertical_stirling
    (hStirling :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact match hStirling with
    | ⟨A, B, m, hA, hB, hbound⟩ =>
      ⟨A, B, m, hA, hB, fun z hz_re hz_im =>
        le_trans (hbound z hz_re hz_im)
          (finiteOrder_vertical_envelope_le_complex_envelope
            (le_of_lt hA)
            (le_of_lt hB))⟩

/-- Standard finite-order Stirling control for the completed real Gamma ratio on the left
vertical tail, in the complex-height envelope used downstream. -/
theorem Gammaℝ_leftBoundary_ratio_stirling_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact Gammaℝ_leftBoundary_ratio_growth_bound_of_vertical_stirling
    Gammaℝ_leftBoundary_ratio_vertical_stirling_growth_bound_standard

/-- A two-sided Stirling ratio estimate on the left boundary is exactly the current
finite-order Gamma-ratio envelope. -/
theorem Gammaℝ_leftBoundary_ratio_growth_bound_of_standard_twoSided_stirling_ratio
    (hstandard :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact hstandard

/-- The Gamma-ratio Stirling input on the left vertical tail.

This owner primitive is now only the standard vertical-tail Gamma-ratio estimate. -/
theorem Gammaℝ_leftBoundary_ratio_stirling_growth_bound_ownerPrimitive :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact Gammaℝ_leftBoundary_ratio_stirling_growth_bound_standard

/-- Product of two left-edge finite-order envelopes is again a left-edge finite-order
envelope.  This core version is placed before the completed-functional-equation multiplier
so the multiplier can be a product wrapper. -/
theorem leftBoundary_finiteOrder_product_growth_bound_core
    {f g : ℂ → ℂ}
    (hf :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hg :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖g z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖f z‖ * ‖g z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact match hf, hg with
    | ⟨Af, Bf, mf, hAf, hBf, hf_bound⟩,
      ⟨Ag, Bg, mg, hAg, hBg, hg_bound⟩ =>
      ⟨Af * Ag, 2 * (Bf + Bg + 1), mf + mg,
        mul_pos hAf hAg,
        mul_pos zero_lt_two (add_pos (add_pos hBf hBg) zero_lt_one),
        fun z hz_re hz_im => by
  let H : ℝ := 1 + ‖z‖
  have hBf_nonneg : 0 ≤ Bf := le_of_lt hBf
  have hBg_nonneg : 0 ≤ Bg := le_of_lt hBg
  have hf_enlarge :
      Af * Real.exp (Bf * H ^ mf) ≤
        Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      (le_of_lt hAf)
      (le_refl Af)
      (by
        calc
          Bf ≤ Bf + Bg := le_add_of_nonneg_right hBg_nonneg
          _ ≤ Bf + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBf_nonneg
      (Nat.le_add_right mf mg)
  have hmg_le : mg ≤ mf + mg := by
    exact Eq.subst
      (motive := fun d : ℕ => mg ≤ d)
      (Nat.add_comm mg mf)
      (Nat.le_add_right mg mf)
  have hg_enlarge :
      Ag * Real.exp (Bg * H ^ mg) ≤
        Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      (le_of_lt hAg)
      (le_refl Ag)
      (by
        calc
          Bg ≤ Bf + Bg := le_add_of_nonneg_left hBf_nonneg
          _ ≤ Bf + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBg_nonneg
      hmg_le
  have hf_target :
      ‖f z‖ ≤ Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    le_trans (hf_bound z hz_re hz_im) hf_enlarge
  have hg_target :
      ‖g z‖ ≤ Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    le_trans (hg_bound z hz_re hz_im) hg_enlarge
  have hmul :
      ‖f z‖ * ‖g z‖ ≤
        (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) :=
    mul_le_mul hf_target hg_target (norm_nonneg (g z))
      (mul_nonneg (le_of_lt hAf)
        (le_of_lt (Real.exp_pos ((Bf + Bg + 1) * H ^ (mf + mg)))))
  have hcollapse :
      (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) =
        Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) := by
    calc
      (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) =
        (Af * Ag) *
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) *
            Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) := by
        exact mul_mul_mul_comm Af
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)))
          Ag
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)))
      _ = (Af * Ag) *
          Real.exp (((Bf + Bg + 1) * H ^ (mf + mg)) +
            ((Bf + Bg + 1) * H ^ (mf + mg))) := by
        exact congrArg (fun x : ℝ => (Af * Ag) * x)
          (Real.exp_add ((Bf + Bg + 1) * H ^ (mf + mg))
            ((Bf + Bg + 1) * H ^ (mf + mg))).symm
      _ = Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) := by
        have htwo :
            ((Bf + Bg + 1) * H ^ (mf + mg)) +
                ((Bf + Bg + 1) * H ^ (mf + mg)) =
              (2 * (Bf + Bg + 1)) * H ^ (mf + mg) := by
          calc
            ((Bf + Bg + 1) * H ^ (mf + mg)) +
                ((Bf + Bg + 1) * H ^ (mf + mg)) =
              2 * ((Bf + Bg + 1) * H ^ (mf + mg)) := by
                exact (two_mul ((Bf + Bg + 1) * H ^ (mf + mg))).symm
            _ = (2 * (Bf + Bg + 1)) * H ^ (mf + mg) := by
                exact mul_assoc 2 (Bf + Bg + 1) (H ^ (mf + mg))
        exact congrArg (fun x : ℝ => Af * Ag * Real.exp x) htwo
  exact le_trans hmul (hcollapse ▸ le_rfl)⟩

/-- The exact Gamma-ratio Stirling input for the left-edge completed-functional-equation
transport.

The proof is now only the product of the elementary pole-clearing ratio and the
peeled Gamma-ratio Stirling theorem. -/
theorem Gammaℝ_leftBoundary_completedFunctionalEquation_multiplier_stirling_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact match leftBoundary_finiteOrder_product_growth_bound_core
      leftBoundary_completedFunctionalEquation_poleClearing_ratio_growth_bound
      Gammaℝ_leftBoundary_ratio_stirling_growth_bound_ownerPrimitive with
    | ⟨A, B, m, hA, hB, hproduct⟩ =>
      ⟨A, B, m, hA, hB, fun z hz_re hz_im => by
  have hnorm :
      ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ =
        ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ *
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ :=
    norm_mul
      ((z - 1) / (((1 : ℂ) - z) - 1))
      (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    hnorm.symm
    (hproduct z hz_re hz_im)⟩

/-- Product of two left-edge finite-order envelopes is again a left-edge finite-order
envelope. -/
theorem leftBoundary_finiteOrder_product_growth_bound
    {f g : ℂ → ℂ}
    (hf :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hg :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖g z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖f z‖ * ‖g z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact match hf, hg with
    | ⟨Af, Bf, mf, hAf, hBf, hf_bound⟩,
      ⟨Ag, Bg, mg, hAg, hBg, hg_bound⟩ =>
      ⟨Af * Ag, 2 * (Bf + Bg + 1), mf + mg,
        mul_pos hAf hAg,
        mul_pos zero_lt_two (add_pos (add_pos hBf hBg) zero_lt_one),
        fun z hz_re hz_im => by
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg z)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hBf_nonneg : 0 ≤ Bf := le_of_lt hBf
  have hBg_nonneg : 0 ≤ Bg := le_of_lt hBg
  have hf_enlarge :
      Af * Real.exp (Bf * H ^ mf) ≤
        Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      (le_of_lt hAf)
      (le_refl Af)
      (by
        calc
          Bf ≤ Bf + Bg := le_add_of_nonneg_right hBg_nonneg
          _ ≤ Bf + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBf_nonneg
      (Nat.le_add_right mf mg)
  have hmg_le : mg ≤ mf + mg := by
    exact Eq.subst
      (motive := fun d : ℕ => mg ≤ d)
      (Nat.add_comm mg mf)
      (Nat.le_add_right mg mf)
  have hg_enlarge :
      Ag * Real.exp (Bg * H ^ mg) ≤
        Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      (le_of_lt hAg)
      (le_refl Ag)
      (by
        calc
          Bg ≤ Bf + Bg := le_add_of_nonneg_left hBf_nonneg
          _ ≤ Bf + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBg_nonneg
      hmg_le
  have hf_target :
      ‖f z‖ ≤ Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    le_trans (hf_bound z hz_re hz_im) hf_enlarge
  have hg_target :
      ‖g z‖ ≤ Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    le_trans (hg_bound z hz_re hz_im) hg_enlarge
  have hmul :
      ‖f z‖ * ‖g z‖ ≤
        (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) :=
    mul_le_mul hf_target hg_target (norm_nonneg (g z))
      (mul_nonneg (le_of_lt hAf)
        (le_of_lt (Real.exp_pos ((Bf + Bg + 1) * H ^ (mf + mg)))))
  have hcollapse :
      (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) =
        Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) := by
    calc
      (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) =
        (Af * Ag) *
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) *
            Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) := by
        exact mul_mul_mul_comm Af
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)))
          Ag
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)))
      _ = (Af * Ag) *
          Real.exp (((Bf + Bg + 1) * H ^ (mf + mg)) +
            ((Bf + Bg + 1) * H ^ (mf + mg))) := by
        exact congrArg (fun x : ℝ => (Af * Ag) * x)
          (Real.exp_add ((Bf + Bg + 1) * H ^ (mf + mg))
            ((Bf + Bg + 1) * H ^ (mf + mg))).symm
      _ = Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) := by
        have htwo :
            ((Bf + Bg + 1) * H ^ (mf + mg)) +
                ((Bf + Bg + 1) * H ^ (mf + mg)) =
              (2 * (Bf + Bg + 1)) * H ^ (mf + mg) := by
          calc
            ((Bf + Bg + 1) * H ^ (mf + mg)) +
                ((Bf + Bg + 1) * H ^ (mf + mg)) =
              2 * ((Bf + Bg + 1) * H ^ (mf + mg)) := by
                exact (two_mul ((Bf + Bg + 1) * H ^ (mf + mg))).symm
            _ = (2 * (Bf + Bg + 1)) * H ^ (mf + mg) := by
                exact mul_assoc 2 (Bf + Bg + 1) (H ^ (mf + mg))
        exact congrArg (fun x : ℝ => Af * Ag * Real.exp x) htwo
  have htarget_guard :
      Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) ≤
        Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) :=
    le_rfl
  exact le_trans hmul (hcollapse ▸ htarget_guard)⟩

/-- A positive polynomial vertical-height bound on the boundary line `re = 1` is an
exponential finite-order bound in the same vertical-height variable. -/
theorem boundaryLine_one_polynomial_growth_bound_to_exponential_growth_bound
    {f : ℂ → ℂ}
    (hpoly :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖f w‖ ≤ A * (1 + ‖w.im‖) ^ m) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖f w‖ ≤ A * Real.exp (B * (1 + ‖w.im‖) ^ m) := by
  exact match hpoly with
    | ⟨A, m, hA_pos, hbound⟩ =>
      ⟨A, 1, m, hA_pos, zero_lt_one, fun w hw_re hw_im => by
  let H : ℝ := (1 + ‖w.im‖) ^ m
  have hH_nonneg : 0 ≤ H :=
    pow_nonneg
      (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im)))
      m
  have hH_le_exp : H ≤ Real.exp ((1 : ℝ) * H) := by
    have hone_mul : (1 : ℝ) * H = H := by
      exact one_mul H
    exact Eq.subst
      (motive := fun x : ℝ => H ≤ Real.exp x)
      hone_mul.symm
      (Real.one_le_exp H)
  have hscaled :
      A * H ≤ A * Real.exp ((1 : ℝ) * H) :=
    mul_le_mul_of_nonneg_left hH_le_exp (le_of_lt hA_pos)
  exact le_trans (hbound w hw_re hw_im) hscaled⟩

/-- On the boundary line `re = 1`, the pole-clearing factor has zero real part. -/
theorem boundaryLine_one_sub_one_re_eq_zero
    {w : ℂ}
    (hw_re : w.re = 1) :
    (w - 1).re = 0 := by
  have hone_re : (1 : ℂ).re = 1 :=
    rfl
  calc
    (w - 1).re = w.re - (1 : ℂ).re := by
      exact Complex.sub_re w 1
    _ = 1 - (1 : ℂ).re := by
      exact congrArg (fun x : ℝ => x - (1 : ℂ).re) hw_re
    _ = 1 - 1 := by
      exact congrArg (fun x : ℝ => 1 - x) hone_re
    _ = 0 := by
      exact sub_self 1

/-- On the boundary line `re = 1`, the pole-clearing factor keeps the original
imaginary coordinate. -/
theorem boundaryLine_one_sub_one_im_eq
    (w : ℂ) :
    (w - 1).im = w.im := by
  have hone_im : (1 : ℂ).im = 0 :=
    rfl
  calc
    (w - 1).im = w.im - (1 : ℂ).im := by
      exact Complex.sub_im w 1
    _ = w.im - 0 := by
      exact congrArg (fun x : ℝ => w.im - x) hone_im
    _ = w.im := by
      exact sub_zero w.im

/-- On the boundary line `re = 1`, the pole-clearing factor has exactly the vertical
height as norm. -/
theorem boundaryLine_one_sub_one_norm_eq_vertical_height
    {w : ℂ}
    (hw_re : w.re = 1) :
    ‖w - 1‖ = ‖w.im‖ := by
  have hre_zero : (w - 1).re = 0 :=
    boundaryLine_one_sub_one_re_eq_zero hw_re
  have him_eq : (w - 1).im = w.im :=
    boundaryLine_one_sub_one_im_eq w
  have habs_eq_im :
      Complex.abs (w - 1) = |(w - 1).im| :=
    (Complex.abs_im_eq_abs.mpr hre_zero).symm
  have him_abs_eq_norm : |(w - 1).im| = ‖w.im‖ := by
    calc
      |(w - 1).im| = |w.im| := by
        exact congrArg abs him_eq
      _ = ‖w.im‖ := (Real.norm_eq_abs w.im).symm
  calc
    ‖w - 1‖ = Complex.abs (w - 1) := by
      exact Complex.norm_eq_abs (w - 1)
    _ = |(w - 1).im| := habs_eq_im
    _ = ‖w.im‖ := him_abs_eq_norm

/-- On the boundary line `re = 1`, the pole-clearing factor has norm controlled by the
vertical height. -/
theorem boundaryLine_one_sub_one_norm_le_vertical_height
    {w : ℂ}
    (hw_re : w.re = 1) :
    ‖w - 1‖ ≤ 1 + ‖w.im‖ := by
  have hnorm_eq :
      ‖w - 1‖ = ‖w.im‖ :=
    boundaryLine_one_sub_one_norm_eq_vertical_height hw_re
  exact le_trans (le_of_eq hnorm_eq)
    (le_add_of_nonneg_left zero_le_one)

/-- The complex point with real coordinate `1` and imaginary coordinate `t`. -/
def boundaryLineOnePointRealParam (t : ℝ) : ℂ :=
  ⟨1, t⟩

/-- Real coordinate of the canonical point `1 + it` on the boundary line. -/
theorem boundaryLineOnePointRealParam_re
    (t : ℝ) :
    (boundaryLineOnePointRealParam t).re = 1 := by
  rfl

/-- Imaginary coordinate of the canonical point `1 + it` on the boundary line. -/
theorem boundaryLineOnePointRealParam_im
    (t : ℝ) :
    (boundaryLineOnePointRealParam t).im = t := by
  rfl

/-- The vertical height of the canonical point `1 + it` is the absolute value of `t`. -/
theorem boundaryLineOnePointRealParam_vertical_height
    (t : ℝ) :
    ‖(boundaryLineOnePointRealParam t).im‖ = ‖t‖ := by
  rfl

/-- A point on the boundary line `re = 1` is the canonical real-parameter boundary
point attached to its vertical coordinate. -/
theorem boundaryLine_one_eq_realParam_point
    {w : ℂ}
    (hw_re : w.re = 1) :
    w = boundaryLineOnePointRealParam w.im := by
  exact Complex.ext hw_re rfl

/-- The real-parameter zeta value attached to the boundary line `re = 1`. -/
def boundaryLineOneZetaRealParam (t : ℝ) : ℂ :=
  riemannZeta (boundaryLineOnePointRealParam t)

/-- Boundary-line zeta is the real-parameter zeta value at the same vertical
coordinate. -/
theorem riemannZeta_boundaryLine_one_eq_realParam
    {w : ℂ}
    (hw_re : w.re = 1) :
    riemannZeta w = boundaryLineOneZetaRealParam w.im := by
  exact congrArg riemannZeta (boundaryLine_one_eq_realParam_point hw_re)

/-- Norm form of the boundary-line real-parameter zeta transport. -/
theorem norm_riemannZeta_boundaryLine_one_eq_norm_realParam
    {w : ℂ}
    (hw_re : w.re = 1) :
    ‖riemannZeta w‖ = ‖boundaryLineOneZetaRealParam w.im‖ := by
  exact congrArg norm (riemannZeta_boundaryLine_one_eq_realParam hw_re)

/-- Harmonic sums are controlled by the logarithm at the natural cutoff `⌊y⌋₊`.

This is the finite-sum side of the Abel/Euler-Maclaurin estimate: after truncating
at a real height `y`, the positive harmonic majorant is at most `1 + log y`. -/
theorem harmonic_truncation_floor_le_one_add_log
    {y : ℝ}
    (hy : 1 ≤ y) :
    harmonic ⌊y⌋₊ ≤ 1 + Real.log y := by
  exact harmonic_floor_le_one_add_log y hy

/-- The cutoff `2 + |t|` is always in the range where the harmonic-log comparison applies. -/
theorem one_le_two_add_norm
    (t : ℝ) :
    (1 : ℝ) ≤ 2 + ‖t‖ := by
  have hnorm : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have htwo_le : (1 : ℝ) ≤ 2 := by
    calc
      (1 : ℝ) ≤ 1 + 1 :=
        le_add_of_nonneg_right zero_le_one
      _ = 2 := rfl
  exact le_trans htwo_le (le_add_of_nonneg_right hnorm)

/-- Harmonic control at the boundary-line truncation height `2 + |t|`. -/
theorem harmonic_boundaryLine_truncation_le_one_add_log
    (t : ℝ) :
    harmonic ⌊2 + ‖t‖⌋₊ ≤ 1 + Real.log (2 + ‖t‖) := by
  exact harmonic_truncation_floor_le_one_add_log (one_le_two_add_norm t)

/-- Each Dirichlet monomial on the boundary line `re = 1` has norm `1 / n`. -/
theorem boundaryLineOnePointRealParam_dirichletTerm_norm_eq_inv
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    ‖(1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ = 1 / (n : ℝ) := by
  have hnorm_pow :
      ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖ = (n : ℝ) ^ (1 : ℝ) := by
    calc
      ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖ =
          (n : ℝ) ^ (boundaryLineOnePointRealParam t).re := by
            exact Complex.norm_natCast_cpow_of_pos hn (boundaryLineOnePointRealParam t)
      _ = (n : ℝ) ^ (1 : ℝ) := by
            exact congrArg (fun x : ℝ => (n : ℝ) ^ x)
              (boundaryLineOnePointRealParam_re t)
  have hpow_one : (n : ℝ) ^ (1 : ℝ) = (n : ℝ) := by
    exact Real.rpow_one (n : ℝ)
  calc
    ‖(1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ =
        ‖(1 : ℂ)‖ / ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖ := by
          exact norm_div (1 : ℂ) ((n : ℂ) ^ boundaryLineOnePointRealParam t)
    _ = 1 / ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖ := by
          exact congrArg
            (fun x : ℝ => x / ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖)
            (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
    _ = 1 / ((n : ℝ) ^ (1 : ℝ)) := by
          exact congrArg (fun x : ℝ => 1 / x) hnorm_pow
    _ = 1 / (n : ℝ) := by
          exact congrArg (fun x : ℝ => 1 / x) hpow_one

/-- The finite Dirichlet truncation on `re = 1` is bounded by the corresponding
positive harmonic majorant. -/
theorem boundaryLineOnePointRealParam_finite_dirichlet_truncation_norm_le_harmonic
    (t : ℝ)
    (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      harmonic N := by
  have hsum_norm :
      ‖∑ n ∈ Finset.Icc 1 N,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        ∑ n ∈ Finset.Icc 1 N,
          ‖(1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ := by
    exact norm_sum_le _ _
  have hterm_sum :
      (∑ n ∈ Finset.Icc 1 N,
          ‖(1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖) =
        ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) := by
    exact Finset.sum_congr rfl
      (fun n hn_mem => by
        have hn_one_le : 1 ≤ n :=
          (Finset.mem_Icc.mp hn_mem).1
        have hn_pos : 0 < n :=
          Nat.lt_of_succ_le hn_one_le
        exact boundaryLineOnePointRealParam_dirichletTerm_norm_eq_inv t hn_pos)
  have hharmonic :
      (∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ))) = harmonic N := by
    calc
      (∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ))) =
          ∑ n ∈ Finset.Icc 1 N, ((n : ℚ)⁻¹ : ℝ) := by
            exact Finset.sum_congr rfl
              (fun n hn_mem => by
                have hn_one_le : 1 ≤ n :=
                  (Finset.mem_Icc.mp hn_mem).1
                have hn_pos : 0 < n :=
                  Nat.lt_of_succ_le hn_one_le
                have hn_rat_ne : (n : ℚ) ≠ 0 := by
                  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn_pos)
                calc
                  (1 / (n : ℝ)) = ((n : ℝ)⁻¹) := by
                    exact one_div (n : ℝ)
                  _ = (((n : ℚ)⁻¹ : ℚ) : ℝ) := by
                    exact (Rat.cast_inv (R := ℝ) (n : ℚ)).symm)
      _ = harmonic N := by
            have hrat :
                (∑ n ∈ Finset.Icc 1 N, ((n : ℚ)⁻¹ : ℚ)) = harmonic N :=
              (harmonic_eq_sum_Icc (n := N)).symm
            exact congrArg (fun q : ℚ => (q : ℝ)) hrat
  exact le_trans hsum_norm (le_of_eq (hterm_sum.trans hharmonic))

/-- The finite Dirichlet truncation at the Abel/Euler-Maclaurin boundary cutoff is
bounded by `1 + log (2 + |t|)`. -/
theorem boundaryLineOnePointRealParam_finite_dirichlet_truncation_norm_le_one_add_log
    (t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      1 + Real.log (2 + ‖t‖) := by
  exact le_trans
    (boundaryLineOnePointRealParam_finite_dirichlet_truncation_norm_le_harmonic
      t ⌊2 + ‖t‖⌋₊)
    (harmonic_boundaryLine_truncation_le_one_add_log t)

/-- On the logarithmic boundary range used below, `1 ≤ log (2 + |t|)`. -/
theorem one_le_log_two_add_norm_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    (1 : ℝ) ≤ Real.log (2 + ‖t‖) := by
  have hthree_le : (3 : ℝ) ≤ 2 + ‖t‖ := by
    calc
      (3 : ℝ) = 2 + 1 := rfl
      _ ≤ 2 + ‖t‖ :=
        add_le_add_left ht 2
  have hexp_one_le_three : Real.exp (1 : ℝ) ≤ 3 := by
    have hexp_le_d9 : Real.exp (1 : ℝ) ≤ 2.7182818286 :=
      le_of_lt Real.exp_one_lt_d9
    have hd9_eq :
        (2.7182818286 : ℝ) =
          (27182818286 : ℝ) / 10000000000 := rfl
    have hden_pos : (0 : ℝ) < 10000000000 := by
      exact Nat.cast_pos.mpr (show (0 : ℕ) < 10000000000 by decide)
    have hnum_le :
        (27182818286 : ℝ) ≤ 3 * (10000000000 : ℝ) := by
      have hnat : (27182818286 : ℕ) ≤ 3 * 10000000000 := by
        decide
      have hcast : (27182818286 : ℝ) ≤ ((3 * 10000000000 : ℕ) : ℝ) :=
        Nat.cast_le.mpr hnat
      have hprod : ((3 * 10000000000 : ℕ) : ℝ) = 3 * (10000000000 : ℝ) := by
        exact Nat.cast_mul 3 10000000000
      exact Eq.subst
        (motive := fun x : ℝ => (27182818286 : ℝ) ≤ x)
        hprod
        hcast
    have hd9_le_three : (2.7182818286 : ℝ) ≤ 3 := by
      have hfrac :
          (27182818286 : ℝ) / 10000000000 ≤ 3 :=
        (div_le_iff₀ hden_pos).mpr hnum_le
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ 3)
        hd9_eq.symm
        hfrac
    exact le_trans hexp_le_d9 hd9_le_three
  have hexp_one_le : Real.exp (1 : ℝ) ≤ 2 + ‖t‖ :=
    le_trans hexp_one_le_three hthree_le
  exact Real.le_log_of_exp_le
    (lt_of_lt_of_le Real.exp_pos hexp_one_le)
    hexp_one_le

/-- The Abel/Euler-Maclaurin cutoff `⌊2 + |t|⌋₊` is nonzero. -/
theorem boundaryLineOnePointRealParam_cutoff_pos
    (t : ℝ) :
    0 < ⌊2 + ‖t‖⌋₊ := by
  have hone_le : (1 : ℝ) ≤ 2 + ‖t‖ :=
    one_le_two_add_norm t
  exact (Nat.one_le_floor_iff zero_lt_one).mpr hone_le

/-- The Abel/Euler-Maclaurin cutoff dominates `2`. -/
theorem boundaryLineOnePointRealParam_two_le_cutoff
    (t : ℝ) :
    2 ≤ ⌊2 + ‖t‖⌋₊ := by
  have htwo_le : (2 : ℝ) ≤ 2 + ‖t‖ :=
    le_add_of_nonneg_right (norm_nonneg t)
  exact (Nat.le_floor_iff zero_lt_two).mpr htwo_le

/-- Transport the finite Dirichlet truncation from `Icc 1 N` to the successor-indexed
form used by analytic Dirichlet-series tails. -/
theorem boundaryLineOnePointRealParam_dirichlet_truncation_eq_sum_range_add_one
    (t : ℝ)
    (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
      ∑ n ∈ Finset.range N,
        (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t) := by
  induction N with
  | zero =>
      have hleft :
          (∑ n ∈ Finset.Icc 1 0,
              (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) = 0 := by
        exact Finset.sum_eq_zero
          (fun n hn => by
            have hn_bounds : 1 ≤ n ∧ n ≤ 0 :=
              Finset.mem_Icc.mp hn
            have hone_le_zero : (1 : ℕ) ≤ 0 :=
              le_trans hn_bounds.1 hn_bounds.2
            exact False.elim
              ((Nat.not_succ_le_zero 0) hone_le_zero))
      have hright :
          (∑ n ∈ Finset.range 0,
              (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t)) = 0 := by
        exact Eq.subst
          (motive := fun s : Finset ℕ =>
            (∑ n ∈ s,
              (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t)) = 0)
          (Finset.range_zero.symm)
          rfl
      exact Eq.trans hleft hright.symm
  | succ N ih =>
      have hleft :
          (∑ n ∈ Finset.Icc 1 (N + 1),
              (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
            (∑ n ∈ Finset.Icc 1 N,
              (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) +
              (1 : ℂ) / (((N + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t) := by
        exact Finset.sum_Icc_succ_top (Nat.succ_pos N)
          (fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t))
      have hright :
          (∑ n ∈ Finset.range (N + 1),
              (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t)) =
            (∑ n ∈ Finset.range N,
              (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t)) +
              (1 : ℂ) / (((N + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t) := by
        exact Finset.sum_range_succ
          (fun n : ℕ =>
            (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t))
          N
      exact Eq.trans hleft (Eq.trans (congrArg
        (fun z : ℂ =>
          z + (1 : ℂ) / (((N + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t))
        ih) hright.symm)

/-- The oscillatory coefficient in the boundary-line Dirichlet term is exactly `n^{-it}`
after the real part `1` is peeled off. -/
theorem boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) / (n : ℂ) := by
  have hn_complex_ne : (n : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hpoint :
      boundaryLineOnePointRealParam t = 1 + (t : ℂ) * Complex.I := by
    exact Complex.ext rfl rfl
  have hpow_add :
      (n : ℂ) ^ boundaryLineOnePointRealParam t =
        (n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
    exact Eq.subst
      (motive := fun z : ℂ =>
        (n : ℂ) ^ z =
          (n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ ((t : ℂ) * Complex.I))
      hpoint.symm
      (Complex.cpow_add (1 : ℂ) ((t : ℂ) * Complex.I) hn_complex_ne)
  have hinv_osc :
      ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ =
        (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
    have hneg :
        -((t : ℂ) * Complex.I) = -(t : ℂ) * Complex.I := by
      exact neg_mul (t : ℂ) Complex.I
    exact Eq.subst
      (motive := fun z : ℂ =>
        ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ = (n : ℂ) ^ z)
      hneg
      (Complex.cpow_neg (n : ℂ) ((t : ℂ) * Complex.I)).symm
  calc
    (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
        ((n : ℂ) ^ boundaryLineOnePointRealParam t)⁻¹ := by
          exact one_div ((n : ℂ) ^ boundaryLineOnePointRealParam t)
    _ = ((n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ := by
          exact congrArg Inv.inv hpow_add
    _ = ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ * ((n : ℂ) ^ (1 : ℂ))⁻¹ := by
          exact mul_inv_rev ((n : ℂ) ^ (1 : ℂ)) ((n : ℂ) ^ ((t : ℂ) * Complex.I))
    _ = (n : ℂ) ^ (-(t : ℂ) * Complex.I) * ((n : ℂ) ^ (1 : ℂ))⁻¹ := by
          exact congrArg
            (fun z : ℂ => z * ((n : ℂ) ^ (1 : ℂ))⁻¹)
            hinv_osc
    _ = (n : ℂ) ^ (-(t : ℂ) * Complex.I) / (n : ℂ) := by
          exact congrArg
            (fun z : ℂ => (n : ℂ) ^ (-(t : ℂ) * Complex.I) * z⁻¹)
            (Complex.cpow_one (n : ℂ))

/-- The boundary-line Dirichlet monomial with the oscillation written on the right,
matching the Abel-summation convention `f k * c k`. -/
theorem boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
      ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  have hright :
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) / (n : ℂ) =
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
    calc
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) / (n : ℂ) =
          ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) * (n : ℂ)⁻¹ := by
            exact div_eq_mul_inv ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) (n : ℂ)
      _ = ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
            exact mul_comm ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) ((n : ℂ)⁻¹ : ℂ)
  exact Eq.trans
    (boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation t hn)
    hright

/-- Finite boundary-line Dirichlet truncations are exactly the Abel-summation
weighted oscillatory sums. -/
theorem boundaryLineOnePointRealParam_finite_truncation_eq_inv_mul_oscillation_sum
    (t : ℝ)
    (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
      ∑ n ∈ Finset.Icc 1 N,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  exact Finset.sum_congr rfl
    (fun n hn_mem => by
      have hn_one_le : 1 ≤ n :=
        (Finset.mem_Icc.mp hn_mem).1
      have hn_pos : 0 < n :=
        Nat.lt_of_succ_le hn_one_le
      exact boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left t hn_pos)

/-- A finite boundary-line tail after the Abel/Euler-Maclaurin cutoff is exactly the
corresponding Abel weighted oscillatory tail. -/
theorem boundaryLineOnePointRealParam_finite_tail_after_cutoff_eq_inv_mul_oscillation_sum
    (t : ℝ)
    (M : ℕ) :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  exact Finset.sum_congr rfl
    (fun n hn_mem => by
      have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
        (Finset.mem_Ioc.mp hn_mem).1
      have hn_pos : 0 < n :=
        lt_trans (boundaryLineOnePointRealParam_cutoff_pos t) hcutoff_lt_n
      exact boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left t hn_pos)

/-- The natural Abel/Euler-Maclaurin cutoff is fixed by taking the natural floor
after coercion to the real line. -/
theorem boundaryLineOnePointRealParam_cutoff_floor_natCast
    (t : ℝ) :
    ⌊((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)⌋₊ = ⌊2 + ‖t‖⌋₊ := by
  exact Nat.floor_natCast ⌊2 + ‖t‖⌋₊

/-- The Abel/Euler-Maclaurin cutoff is the left endpoint immediately below
`2 + |t|`. -/
theorem boundaryLineOnePointRealParam_cutoff_cast_le_height
    (t : ℝ) :
    (⌊2 + ‖t‖⌋₊ : ℝ) ≤ 2 + ‖t‖ := by
  have hnonneg : (0 : ℝ) ≤ 2 + ‖t‖ :=
    le_trans zero_le_one (one_le_two_add_norm t)
  exact Nat.floor_le hnonneg

/-- The real height `2 + |t|` lies strictly before the successor of the cutoff. -/
theorem boundaryLineOnePointRealParam_height_lt_cutoff_add_one
    (t : ℝ) :
    2 + ‖t‖ < (⌊2 + ‖t‖⌋₊ : ℝ) + 1 := by
  exact Nat.lt_floor_add_one (2 + ‖t‖)

/-- The cutoff endpoint contributes at most one through the reciprocal weight. -/
theorem boundaryLineOnePointRealParam_cutoff_inv_le_one
    (t : ℝ) :
    (1 : ℝ) / (⌊2 + ‖t‖⌋₊ : ℝ) ≤ 1 := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff_nat : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_le_cutoff_real : (1 : ℝ) ≤ (⌊2 + ‖t‖⌋₊ : ℝ) := by
    exact Nat.cast_le.mpr hone_le_cutoff_nat
  calc
    (1 : ℝ) / (⌊2 + ‖t‖⌋₊ : ℝ) =
        ((⌊2 + ‖t‖⌋₊ : ℝ)⁻¹ : ℝ) := by
          exact one_div (⌊2 + ‖t‖⌋₊ : ℝ)
    _ ≤ 1 := by
          exact inv_le_one_of_one_le₀ hone_le_cutoff_real

/-- Reciprocal weights are monotone decreasing along the positive natural tail. -/
theorem positive_nat_reciprocal_antitone
    {m n : ℕ}
    (hm : 0 < m)
    (hmn : m ≤ n) :
    (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (m : ℝ) := by
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by
    exact Nat.cast_pos.mpr hm
  have hmn_real : (m : ℝ) ≤ (n : ℝ) := by
    exact Nat.cast_le.mpr hmn
  exact one_div_le_one_div_of_le hm_real_pos hmn_real

/-- Past the Abel/Euler-Maclaurin cutoff, all reciprocal weights are bounded by
the reciprocal of the cutoff endpoint. -/
theorem boundaryLineOnePointRealParam_post_cutoff_reciprocal_le_cutoff
    (t : ℝ)
    {n : ℕ}
    (hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n) :
    (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (⌊2 + ‖t‖⌋₊ : ℝ) := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hcutoff_le_n : ⌊2 + ‖t‖⌋₊ ≤ n :=
    Nat.le_of_lt hcutoff_lt_n
  exact positive_nat_reciprocal_antitone hcutoff_pos hcutoff_le_n

/-- Logarithmic-phase partial sums for the boundary-line oscillator `n^{-it}`.

The phase is `-t log n`; these sums must not be treated as constant-ratio
geometric sums. -/

end
end LFunctions
end Boundary
