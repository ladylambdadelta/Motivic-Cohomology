import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.PoleClearedBoundarySetup.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.Owner

/-!
# Pole-cleared continuity, analyticity, and compact bounds

This file owns the fundamental analytical properties of the pole-cleared zeta
factor: continuity everywhere, analyticity at the removable pole, compact-region
boundedness, and the conversion from polynomial to exponential growth bounds on
fixed vertical lines.
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
  exact fun z _hz => (poleClearedRiemannZeta_continuousAt z).continuousWithinAt

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
  exact fun z _hz => (poleClearedRiemannZeta_differentiableAt z).differentiableWithinAt

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
    exact
      fun hz =>
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
        not_lt_of_ge hone_le_zero zero_lt_one
  have hone_sub_ne_zero : (1 : ℂ) - z ≠ 0 := by
    exact
      fun hsub =>
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
        one_ne_zero hone_eq_zero
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
  exact
    fun hzero =>
      hGamma_ne
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
  exact
    fun b hb =>
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
      Eq.subst
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
  exact
    fun b hb =>
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
      Eq.subst
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

end

end LFunctions
end Boundary
