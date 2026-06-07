import Boundary.LFunctions.ZetaExplicitFormulaContour
import Boundary.LFunctions.ZetaExplicitFormulaNormalizationBridge
import Boundary.LFunctions.ZetaExplicitFormulaLogDerivative
import Boundary.LFunctions.ZetaExplicitFormulaRectangleAPI
import Boundary.LFunctions.ZetaAdmissibleTransformRegularity
import Boundary.LFunctions.ZetaCompletedLogDerivativeControl
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Topology.Algebra.Order

/-!
# Boundary explicit-formula complex analysis API

This file exposes the geometric and analytic objects needed for the completed
Guinand--Weil contour argument. It intentionally stops at definitions and
owner-level notation; the actual contour estimates will be proved against these
objects in later files.

The point is to make the required complex-analysis API available first, not to
axiomatize the missing theorems.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex

namespace ZetaAdmissibleFunction

/-- A boundary-side interval-integral norm estimate. This is the reusable lemma the
horizontal contour argument needs: the norm of an interval integral is bounded by the
interval integral of the pointwise norm. -/
theorem norm_intervalIntegral_le_integral_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E)
    (a b : ℂ) :
    ‖∫ x in a.re..b.re, f (x + a.im * Complex.I)‖
      ≤ ∫ x in a.re..b.re, ‖f (x + a.im * Complex.I)‖ := by
  simpa using norm_integral_le_integral_norm (fun x : ℝ => f (x + a.im * Complex.I)) (a.re) (b.re)

/-- Powers of `1 + |T|` with negative exponent tend to zero at `atTop`. -/
theorem tendsto_one_add_norm_pow_neg_atTop (N : ℕ) :
    Tendsto (fun T : ℝ => (1 + ‖T‖) ^ (-(N : ℤ))) atTop (𝓝 (0 : ℝ)) := by
  have hpos : ∀ T : ℝ, 0 < (1 + ‖T‖ : ℝ) := by
    intro T
    positivity
  have hpow : Tendsto (fun T : ℝ => (1 + ‖T‖) ^ (N : ℕ)) atTop atTop := by
    have h1 : Tendsto (fun T : ℝ => (1 + ‖T‖ : ℝ)) atTop atTop := by
      simpa using tendsto_atTop.2 (by
        intro a
        refine Filter.Eventually.of_forall ?_
        intro T
        linarith [norm_nonneg T])
    have hpow' : Tendsto (fun T : ℝ => (1 + ‖T‖ : ℝ) ^ (N : ℕ)) atTop atTop := by
      simpa using h1.pow N
    exact hpow'
  have hpowinv :
      Tendsto (fun T : ℝ => ((1 + ‖T‖ : ℝ) ^ (N : ℕ))⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_inv_atTop_zero.comp hpow
  have hrewrite :
      (fun T : ℝ => (1 + ‖T‖) ^ (-(N : ℤ))) =
        fun T : ℝ => ((1 + ‖T‖ : ℝ) ^ (N : ℕ))⁻¹ := by
    funext T
    rw [show (-(N : ℤ)) = -((N : ℤ)) by ring]
    simp [zpow_natCast, hpos T, one_div]
  simpa [hrewrite] using hpowinv

/-- If a real-valued function is dominated by a constant multiple of a quantity tending to `0`,
then it tends to `0`. -/
theorem tendsto_of_eventually_le_mul_tendsto_zero
    {g h : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hg : ∀ᶠ T in atTop, ‖g T‖ ≤ C * h T)
    (hh : Tendsto h atTop (𝓝 (0 : ℝ))) :
    Tendsto g atTop (𝓝 (0 : ℝ)) := by
  have hmul : Tendsto (fun T : ℝ => C * h T) atTop (𝓝 (0 : ℝ)) := by
    simpa using hh.const_mul C
  have hnorm : Tendsto (fun T : ℝ => ‖g T‖) atTop (𝓝 (0 : ℝ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hmul ?_ hg ?_
    · simpa using tendsto_const_nhds
    · exact Eventually.of_forall fun T => norm_nonneg _
  simpa [Real.norm_eq_abs] using hnorm

/-- The product of two negative powers of `1 + |T|` tends to zero. -/
theorem tendsto_two_one_add_norm_pow_neg_atTop (N : ℕ) :
    Tendsto
      (fun T : ℝ => (1 + ‖T‖) ^ (-(N : ℤ)) * (1 + ‖T‖) ^ (-(N : ℤ)))
      atTop
      (𝓝 (0 : ℝ)) := by
  have hpow := tendsto_one_add_norm_pow_neg_atTop N
  have hmul := hpow.mul hpow
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- The horizontal contour integral is bounded by the interval length times the uniform edge
bound. -/
theorem horizontalIntegral_norm_le_uniformContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) (N : ℕ)
    (x : ℝ) (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral f h.contour_data.rectangle‖
      ≤ (1 - 2 * h.contour_data.rectangle.c) *
        (Classical.choose
          (h.logderiv_control.stripBound h.contour_data.rectangle.c
            (1 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay
            (h.contour_data.rectangle.c - 1 / 2)
            (1 / 2 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) := by
  have hbound := ExplicitFormulaAnalyticPackage.contourEdgeBounds h N x
    h.contour_data.rectangle.T hx1 hx2
    (by linarith [h.contour_data.T_pos]) (by linarith [h.contour_data.T_pos])
  have hC :
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖
        ≤ (Classical.choose
            (h.logderiv_control.stripBound h.contour_data.rectangle.c
              (1 - h.contour_data.rectangle.c) N)).1 *
          (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
          (Classical.choose
            (h.phi_control.verticalStripRapidDecay
              (h.contour_data.rectangle.c - 1 / 2)
              (1 / 2 - h.contour_data.rectangle.c) N)).1 *
          (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) := hbound.1
  have hlen : ∫ x in h.contour_data.rectangle.c..(1 - h.contour_data.rectangle.c), (1 : ℝ) =
      1 - 2 * h.contour_data.rectangle.c := by
    simp
  have htop :
      ‖∫ x in h.contour_data.rectangle.c..(1 - h.contour_data.rectangle.c),
          zetaCompletedExplicitFormulaContourIntegrand f
            (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖
        ≤ ∫ x in h.contour_data.rectangle.c..(1 - h.contour_data.rectangle.c),
          ‖zetaCompletedExplicitFormulaContourIntegrand f
            (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ := by
    simpa using norm_integral_le_integral_norm
      (fun x : ℝ => zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x))
      (h.contour_data.rectangle.c) (1 - h.contour_data.rectangle.c)
  calc
    ‖zetaCompletedExplicitFormulaTopLineIntegral f h.contour_data.rectangle‖
        = ‖∫ x in h.contour_data.rectangle.c..(1 - h.contour_data.rectangle.c),
            zetaCompletedExplicitFormulaContourIntegrand f
              (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ := by
          rfl
    _ ≤ ∫ x in h.contour_data.rectangle.c..(1 - h.contour_data.rectangle.c),
          ‖zetaCompletedExplicitFormulaContourIntegrand f
            (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ := htop
    _ ≤ ∫ x in h.contour_data.rectangle.c..(1 - h.contour_data.rectangle.c),
          (Classical.choose
            (h.logderiv_control.stripBound h.contour_data.rectangle.c
              (1 - h.contour_data.rectangle.c) N)).1 *
          (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
          (Classical.choose
            (h.phi_control.verticalStripRapidDecay
              (h.contour_data.rectangle.c - 1 / 2)
              (1 / 2 - h.contour_data.rectangle.c) N)).1 *
          (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) := by
          refine intervalIntegral.integral_mono_on ?_ ?_ ?_ ?_
          · continuity
          · intro y hy
            exact le_of_lt (hC)
          · positivity
          · intro y hy
            positivity
    _ = (1 - 2 * h.contour_data.rectangle.c) *
        (Classical.choose
          (h.logderiv_control.stripBound h.contour_data.rectangle.c
            (1 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
          (Classical.choose
            (h.phi_control.verticalStripRapidDecay
              (h.contour_data.rectangle.c - 1 / 2)
              (1 / 2 - h.contour_data.rectangle.c) N)).1 *
          (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) := by
          simp [hlen, mul_comm, mul_left_comm, mul_assoc]

/-- The horizontal difference of the top and bottom integrals is bounded by twice the uniform
edge constant times the interval length. -/
theorem horizontalDifference_norm_le_uniformContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) (N : ℕ) :
    ‖zetaHorizontalIntegralTop f h.contour_data.rectangle -
        zetaHorizontalIntegralBottom f h.contour_data.rectangle‖
      ≤ (1 - 2 * h.contour_data.rectangle.c) *
        (Classical.choose
          (h.logderiv_control.stripBound h.contour_data.rectangle.c
            (1 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay
            (h.contour_data.rectangle.c - 1 / 2)
            (1 / 2 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) := by
  have htop :=
    horizontalIntegral_norm_le_uniformContourBound h N
      h.contour_data.rectangle.c
      (by linarith [h.contour_data.c_gt_half])
      (by linarith [h.contour_data.c_gt_half])
  have hbot :=
    horizontalIntegral_norm_le_uniformContourBound h N
      h.contour_data.rectangle.c
      (by linarith [h.contour_data.c_gt_half])
      (by linarith [h.contour_data.c_gt_half])
  have htri :
      ‖zetaHorizontalIntegralTop f h.contour_data.rectangle -
          zetaHorizontalIntegralBottom f h.contour_data.rectangle‖
        ≤ ‖zetaHorizontalIntegralTop f h.contour_data.rectangle‖ +
          ‖zetaHorizontalIntegralBottom f h.contour_data.rectangle‖ := by
    exact norm_sub_le _ _
  calc
    ‖zetaHorizontalIntegralTop f h.contour_data.rectangle -
        zetaHorizontalIntegralBottom f h.contour_data.rectangle‖
        ≤ ‖zetaHorizontalIntegralTop f h.contour_data.rectangle‖ +
            ‖zetaHorizontalIntegralBottom f h.contour_data.rectangle‖ := htri
    _ ≤ (1 - 2 * h.contour_data.rectangle.c) *
        (Classical.choose
          (h.logderiv_control.stripBound h.contour_data.rectangle.c
            (1 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay
            (h.contour_data.rectangle.c - 1 / 2)
            (1 / 2 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) := by
      nlinarith

/-- The completed zeta negative logarithmic derivative. -/
def completedZetaNegLogDeriv (s : ℂ) : ℂ :=
  - deriv completedRiemannZeta s / completedRiemannZeta s

/-- The completed negative logarithmic derivative is the negative `logDeriv`. -/
theorem completedZetaNegLogDeriv_eq_neg_logDeriv (s : ℂ) :
    completedZetaNegLogDeriv s = - logDeriv completedRiemannZeta s := by
  unfold completedZetaNegLogDeriv
  rw [logDeriv_apply]
  rfl

/-- `Γℝ` does not vanish on the right half-plane. -/
theorem Gammaℝ_ne_zero_of_re_pos (s : ℂ) (hs : 0 < s.re) : Gammaℝ s ≠ 0 := by
  exact Gammaℝ_ne_zero_of_re_pos hs

/-- `completedRiemannZeta` is differentiable away from its poles. -/
theorem differentiableAt_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta s := by
  exact differentiableAt_completedZeta hs0 hs1

/-- The right contour edge lies in the right half-plane. -/
theorem rightPath_re_pos (r : ExplicitFormulaRectangle) (t : ℝ) (hc : (1 / 2 : ℝ) < r.c) :
    0 < (zetaCompletedExplicitFormulaRightPath r t).re := by
  rw [zetaCompletedExplicitFormulaRightPath_re]
  linarith

/-- The right contour edge lies in the right half-plane, using the contour-data owner object. -/
theorem rightPath_re_pos_of_contourData (d : ExplicitFormulaContourData) (t : ℝ) :
    0 < (zetaCompletedExplicitFormulaRightPath d.rectangle t).re := by
  exact rightPath_re_pos d.rectangle t d.c_gt_half

/-- The Gamma factor is nonzero on the right contour edge. -/
theorem Gammaℝ_rightPath_ne_zero (r : ExplicitFormulaRectangle) (t : ℝ)
    (hc : (1 / 2 : ℝ) < r.c) :
    Gammaℝ (zetaCompletedExplicitFormulaRightPath r t) ≠ 0 := by
  exact Gammaℝ_ne_zero_of_re_pos (rightPath_re_pos r t hc)

/-- The Gamma factor is nonzero on the right contour edge, using contour data. -/
theorem Gammaℝ_rightPath_ne_zero_of_contourData (d : ExplicitFormulaContourData) (t : ℝ) :
    Gammaℝ (zetaCompletedExplicitFormulaRightPath d.rectangle t) ≠ 0 := by
  exact Gammaℝ_rightPath_ne_zero d.rectangle t d.c_gt_half

/-- The right contour edge never hits the pole at `0`. -/
theorem rightPath_ne_zero (r : ExplicitFormulaRectangle) (t : ℝ) (hc : (1 / 2 : ℝ) < r.c) :
    zetaCompletedExplicitFormulaRightPath r t ≠ 0 := by
  intro h
  have hre : (zetaCompletedExplicitFormulaRightPath r t).re = 0 := by rw [h]; simp
  have hpos : 0 < (zetaCompletedExplicitFormulaRightPath r t).re := rightPath_re_pos r t hc
  linarith

/-- The right contour edge never hits the pole at `0`, using contour data. -/
theorem rightPath_ne_zero_of_contourData (d : ExplicitFormulaContourData) (t : ℝ) :
    zetaCompletedExplicitFormulaRightPath d.rectangle t ≠ 0 := by
  exact rightPath_ne_zero d.rectangle t d.c_gt_half

/-- The top contour edge never hits the pole at `0`. -/
theorem topPath_ne_zero (r : ExplicitFormulaRectangle) (x : ℝ) (hT : 0 < r.T) :
    zetaCompletedExplicitFormulaTopPath r x ≠ 0 := by
  intro h
  have him : (zetaCompletedExplicitFormulaTopPath r x).im = 0 := by rw [h]; simp
  rw [zetaCompletedExplicitFormulaTopPath_im] at him
  linarith

/-- The top contour edge never hits the pole at `0`, using contour data. -/
theorem topPath_ne_zero_of_contourData (d : ExplicitFormulaContourData) (x : ℝ) :
    zetaCompletedExplicitFormulaTopPath d.rectangle x ≠ 0 := by
  exact topPath_ne_zero d.rectangle x d.T_pos

/-- The top contour edge never hits the pole at `1`. -/
theorem topPath_ne_one (r : ExplicitFormulaRectangle) (x : ℝ) (hT : 0 < r.T) :
    zetaCompletedExplicitFormulaTopPath r x ≠ 1 := by
  intro h
  have him : (zetaCompletedExplicitFormulaTopPath r x).im = 0 := by rw [h]; simp
  rw [zetaCompletedExplicitFormulaTopPath_im] at him
  linarith

/-- The top contour edge never hits the pole at `1`, using contour data. -/
theorem topPath_ne_one_of_contourData (d : ExplicitFormulaContourData) (x : ℝ) :
    zetaCompletedExplicitFormulaTopPath d.rectangle x ≠ 1 := by
  exact topPath_ne_one d.rectangle x d.T_pos

/-- The bottom contour edge never hits the pole at `0`. -/
theorem bottomPath_ne_zero (r : ExplicitFormulaRectangle) (x : ℝ) (hT : 0 < r.T) :
    zetaCompletedExplicitFormulaBottomPath r x ≠ 0 := by
  intro h
  have him : (zetaCompletedExplicitFormulaBottomPath r x).im = 0 := by rw [h]; simp
  rw [zetaCompletedExplicitFormulaBottomPath_im] at him
  linarith

/-- The bottom contour edge never hits the pole at `0`, using contour data. -/
theorem bottomPath_ne_zero_of_contourData (d : ExplicitFormulaContourData) (x : ℝ) :
    zetaCompletedExplicitFormulaBottomPath d.rectangle x ≠ 0 := by
  exact bottomPath_ne_zero d.rectangle x d.T_pos

/-- The bottom contour edge never hits the pole at `1`. -/
theorem bottomPath_ne_one (r : ExplicitFormulaRectangle) (x : ℝ) (hT : 0 < r.T) :
    zetaCompletedExplicitFormulaBottomPath r x ≠ 1 := by
  intro h
  have him : (zetaCompletedExplicitFormulaBottomPath r x).im = 0 := by rw [h]; simp
  rw [zetaCompletedExplicitFormulaBottomPath_im] at him
  linarith

/-- The bottom contour edge never hits the pole at `1`, using contour data. -/
theorem bottomPath_ne_one_of_contourData (d : ExplicitFormulaContourData) (x : ℝ) :
    zetaCompletedExplicitFormulaBottomPath d.rectangle x ≠ 1 := by
  exact bottomPath_ne_one d.rectangle x d.T_pos


/-- The factorized completed-zeta product is differentiable at a point away from `0` and `1`. -/
theorem differentiableAt_completedZeta_factorized
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΓ : Gammaℝ s ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹) s := by
  refine (differentiableAt_completedRiemannZeta hs0 hs1).mul ?_
  exact differentiable_Gammaℝ_inv.differentiableAt

/-- The factorized completed-zeta product is differentiable on the right contour edge once the
point avoids the two pole locations. -/
theorem differentiableAt_completedZeta_factorized_rightPath
    (r : ExplicitFormulaRectangle) (t : ℝ) (hc : (1 / 2 : ℝ) < r.c)
    (hs0 : zetaCompletedExplicitFormulaRightPath r t ≠ 0)
    (hs1 : zetaCompletedExplicitFormulaRightPath r t ≠ 1) :
    DifferentiableAt ℂ
      (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹)
      (zetaCompletedExplicitFormulaRightPath r t) := by
  exact differentiableAt_completedZeta_factorized hs0 hs1

/-- The contour integrand norm is bounded by the product of the log-derivative and `Φ_f` norms. -/
theorem norm_zetaCompletedExplicitFormulaContourIntegrand_le
    (f : ZetaAdmissibleFunction) (s : ℂ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f s‖
      ≤ ‖completedZetaNegLogDeriv s‖ * ‖zetaCompletedExplicitFormulaPhi f (s - 1 / 2)‖ := by
  unfold zetaCompletedExplicitFormulaContourIntegrand
  exact norm_mul_le _ _

/-- The contour integrand norm is bounded by the product estimate in the factorized form. -/
theorem norm_zetaCompletedExplicitFormulaContourIntegrand_factorized_le
    (f : ZetaAdmissibleFunction) (s : ℂ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f s‖
      ≤ ‖completedZetaNegLogDeriv s‖ * ‖zetaCompletedExplicitFormulaPhi f (s - 1 / 2)‖ := by
  exact norm_zetaCompletedExplicitFormulaContourIntegrand_le f s

/-- The contour integrand on the top edge inherits the product strip bound from the owner
packages for `completedZetaNegLogDeriv` and `Φ_f`. -/
theorem zetaCompletedExplicitFormulaTopPath_contourIntegrand_strip_bound
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) (N : ℕ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath r x)‖
      ≤ (Classical.choose (hLog.stripBound r.c (1 - r.c) N)).1 *
        (1 + ‖r.T‖) ^ (-(N : ℤ)) *
        (Classical.choose (hPhi.verticalStripRapidDecay (r.c - 1 / 2) (1 / 2 - r.c) N)).1 *
        (1 + ‖r.T‖) ^ (-(N : ℤ)) := by
  let CLog : ℝ := Classical.choose (hLog.stripBound r.c (1 - r.c) N)
  let CPhi : ℝ :=
    Classical.choose (hPhi.verticalStripRapidDecay (r.c - 1 / 2) (1 / 2 - r.c) N)
  have hLogC :
      0 < CLog ∧
      ∀ z : ℂ,
        r.c ≤ z.re →
        z.re ≤ 1 - r.c →
        ‖completedZetaNegLogDeriv z‖
          ≤ CLog * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
    simpa [CLog] using Classical.choose_spec (hLog.stripBound r.c (1 - r.c) N)
  have hPhiShiftC :
      0 < CPhi ∧
      ∀ z : ℂ,
        (r.c - 1 / 2) ≤ z.re →
        z.re ≤ (1 / 2 - r.c) →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ CPhi * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
    simpa [CPhi] using
      Classical.choose_spec (hPhi.verticalStripRapidDecay (r.c - 1 / 2) (1 / 2 - r.c) N)
  have hstrip :
      r.c ≤ (zetaCompletedExplicitFormulaTopPath r x).re ∧
        (zetaCompletedExplicitFormulaTopPath r x).re ≤ 1 - r.c :=
    zetaCompletedExplicitFormulaTopPath_strip r x hx1 hx2
  have hshiftstrip :
      r.c - 1 / 2 ≤ (zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).re ≤ 1 / 2 - r.c := by
    constructor
    · rw [sub_re, zetaCompletedExplicitFormulaTopPath_re]
      linarith
    · rw [sub_re, zetaCompletedExplicitFormulaTopPath_re]
      linarith
  have htopim :
      ‖(zetaCompletedExplicitFormulaTopPath r x).im‖ = ‖r.T‖ := by
    rw [zetaCompletedExplicitFormulaTopPath_im]
  have hshiftim :
      ‖(zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).im‖ = ‖r.T‖ := by
    simp [zetaCompletedExplicitFormulaTopPath_im]
  calc
    ‖zetaCompletedExplicitFormulaContourIntegrand f (zetaCompletedExplicitFormulaTopPath r x)‖
        ≤ ‖completedZetaNegLogDeriv (zetaCompletedExplicitFormulaTopPath r x)‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaTopPath r x - 1 / 2)‖ := by
        exact norm_zetaCompletedExplicitFormulaContourIntegrand_le f _
    _ ≤ (CLog * (1 + ‖(zetaCompletedExplicitFormulaTopPath r x).im‖) ^ (-(N : ℤ))) *
          (CPhi * (1 + ‖((zetaCompletedExplicitFormulaTopPath r x) - 1 / 2).im‖) ^ (-(N : ℤ))) := by
        gcongr
        · exact hLogC.2 _ hstrip.1 hstrip.2
        · have htopshift :
            (r.c - 1 / 2) ≤ (zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).re ∧
              (zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).re ≤ (1 / 2 - r.c) := by
              exact hshiftstrip
          exact hPhiShiftC.2 _ htopshift.1 htopshift.2
    _ = (CLog * (1 + ‖r.T‖) ^ (-(N : ℤ))) *
          (CPhi * (1 + ‖r.T‖) ^ (-(N : ℤ))) := by
        simp [CLog, CPhi, htopim, hshiftim, mul_comm, mul_left_comm, mul_assoc]

/-- The contour integrand on the bottom edge inherits the product strip bound from the owner
packages for `completedZetaNegLogDeriv` and `Φ_f`. -/
theorem zetaCompletedExplicitFormulaBottomPath_contourIntegrand_strip_bound
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) (N : ℕ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath r x)‖
      ≤ (Classical.choose (hLog.stripBound r.c (1 - r.c) N)).1 *
        (1 + ‖r.T‖) ^ (-(N : ℤ)) *
        (Classical.choose (hPhi.verticalStripRapidDecay (r.c - 1 / 2) (1 / 2 - r.c) N)).1 *
        (1 + ‖r.T‖) ^ (-(N : ℤ)) := by
  let CLog : ℝ := Classical.choose (hLog.stripBound r.c (1 - r.c) N)
  let CPhi : ℝ :=
    Classical.choose (hPhi.verticalStripRapidDecay (r.c - 1 / 2) (1 / 2 - r.c) N)
  have hLogC :
      0 < CLog ∧
      ∀ z : ℂ,
        r.c ≤ z.re →
        z.re ≤ 1 - r.c →
        ‖completedZetaNegLogDeriv z‖
          ≤ CLog * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
    simpa [CLog] using Classical.choose_spec (hLog.stripBound r.c (1 - r.c) N)
  have hPhiShiftC :
      0 < CPhi ∧
      ∀ z : ℂ,
        (r.c - 1 / 2) ≤ z.re →
        z.re ≤ (1 / 2 - r.c) →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ CPhi * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
    simpa [CPhi] using
      Classical.choose_spec (hPhi.verticalStripRapidDecay (r.c - 1 / 2) (1 / 2 - r.c) N)
  have hstrip :
      r.c ≤ (zetaCompletedExplicitFormulaBottomPath r x).re ∧
        (zetaCompletedExplicitFormulaBottomPath r x).re ≤ 1 - r.c :=
    zetaCompletedExplicitFormulaBottomPath_strip r x hx1 hx2
  have hshiftstrip :
      (r.c - 1 / 2) ≤ (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2 : ℂ).re ≤ (1 / 2 - r.c) := by
    constructor
    · rw [sub_re, zetaCompletedExplicitFormulaBottomPath_re]
      linarith
    · rw [sub_re, zetaCompletedExplicitFormulaBottomPath_re]
      linarith
  have hbotim :
      ‖(zetaCompletedExplicitFormulaBottomPath r x).im‖ = ‖r.T‖ := by
    rw [zetaCompletedExplicitFormulaBottomPath_im]
    simp
  have hshiftim :
      ‖(zetaCompletedExplicitFormulaBottomPath r x - 1 / 2 : ℂ).im‖ = ‖r.T‖ := by
    simp [zetaCompletedExplicitFormulaBottomPath_im]
  calc
    ‖zetaCompletedExplicitFormulaContourIntegrand f (zetaCompletedExplicitFormulaBottomPath r x)‖
        ≤ ‖completedZetaNegLogDeriv (zetaCompletedExplicitFormulaBottomPath r x)‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2)‖ := by
        exact norm_zetaCompletedExplicitFormulaContourIntegrand_le f _
    _ ≤ (CLog * (1 + ‖(zetaCompletedExplicitFormulaBottomPath r x).im‖) ^ (-(N : ℤ))) *
          (CPhi * (1 + ‖((zetaCompletedExplicitFormulaBottomPath r x) - 1 / 2).im‖) ^ (-(N : ℤ))) := by
        gcongr
        · exact hLogC.2 _ hstrip.1 hstrip.2
        · exact hPhiShiftC.2 _ hshiftstrip.1 hshiftstrip.2
    _ = (CLog * (1 + ‖r.T‖) ^ (-(N : ℤ))) *
          (CPhi * (1 + ‖r.T‖) ^ (-(N : ℤ))) := by
        simp [CLog, CPhi, hbotim, hshiftim, mul_comm, mul_left_comm, mul_assoc]

/-- The owner-level analytic package for the explicit-formula contour argument. -/
structure ExplicitFormulaAnalyticPackage (f : ZetaAdmissibleFunction) : Prop where
  /-- Transform regularity for the probe function. -/
  phi_control : ZetaPhiAnalyticControl f
  /-- Strip control for the completed negative log derivative. -/
  logderiv_control : CompletedZetaNegLogDerivControl f
  /-- The contour geometry data. -/
  contour_data : ExplicitFormulaContourData

/-- The analytic package exposes the transform control. -/
theorem ExplicitFormulaAnalyticPackage.phiControl
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    ZetaPhiAnalyticControl f := by
  exact h.phi_control

/-- The analytic package exposes the log-derivative control. -/
theorem ExplicitFormulaAnalyticPackage.logDerivControl
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    CompletedZetaNegLogDerivControl f := by
  exact h.logderiv_control

/-- The analytic package exposes the contour data. -/
theorem ExplicitFormulaAnalyticPackage.contourData
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    ExplicitFormulaContourData := by
  exact h.contour_data

/-- The family-level analytic package for the explicit-formula contour argument. -/
structure ExplicitFormulaFamilyAnalyticPackage (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily) : Prop where
  /-- Transform regularity for the probe function. -/
  phi_control : ZetaPhiAnalyticControl f
  /-- Strip control for the completed negative log derivative. -/
  logderiv_control : CompletedZetaNegLogDerivControl f

/-- The family-level package exposes the transform control. -/
theorem ExplicitFormulaFamilyAnalyticPackage.phiControl
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ZetaPhiAnalyticControl f := by
  exact h.phi_control

/-- The family-level package exposes the log-derivative control. -/
theorem ExplicitFormulaFamilyAnalyticPackage.logDerivControl
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    CompletedZetaNegLogDerivControl f := by
  exact h.logderiv_control

/-- The family-level package yields the top-edge contour bound at height `T`. -/
theorem ExplicitFormulaFamilyAnalyticPackage.topEdgeContourBound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ) (T x : ℝ)
    (hx1 : F.c ≤ x) (hx2 : x ≤ 1 - F.c) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)‖
      ≤ (Classical.choose
          (h.logderiv_control.stripBound F.c (1 - F.c) N)).1 *
        (1 + ‖T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay (F.c - 1 / 2) (1 / 2 - F.c) N)).1 *
        (1 + ‖T‖) ^ (-(N : ℤ)) := by
  have hpack :
      ExplicitFormulaAnalyticPackage
        (f := f) := by
    refine
      { phi_control := h.phi_control
        logderiv_control := h.logderiv_control
        contour_data :=
          { rectangle := F.rectangle T
            c_gt_half := F.c_gt_half
            T_pos := by positivity } }
  simpa [ExplicitFormulaContourFamily.rectangle] using
    zetaCompletedExplicitFormulaTopPath_contourIntegrand_strip_bound
      h.phi_control h.logderiv_control (F.rectangle T) x hx1 hx2 N

/-- The family-level package yields the bottom-edge contour bound at height `T`. -/
theorem ExplicitFormulaFamilyAnalyticPackage.bottomEdgeContourBound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ) (T x : ℝ)
    (hx1 : F.c ≤ x) (hx2 : x ≤ 1 - F.c) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)‖
      ≤ (Classical.choose
          (h.logderiv_control.stripBound F.c (1 - F.c) N)).1 *
        (1 + ‖T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay (F.c - 1 / 2) (1 / 2 - F.c) N)).1 *
        (1 + ‖T‖) ^ (-(N : ℤ)) := by
  simpa [ExplicitFormulaContourFamily.rectangle] using
    zetaCompletedExplicitFormulaBottomPath_contourIntegrand_strip_bound
      h.phi_control h.logderiv_control (F.rectangle T) x hx1 hx2 N

/-- The top horizontal line integral in a contour family is bounded by the uniform family edge
bound times the horizontal length. -/
theorem ExplicitFormulaFamilyAnalyticPackage.topLineIntegral_norm_le
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (T : ℝ) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)‖
      ≤ (1 - 2 * F.c) *
        (Classical.choose
          (h.logderiv_control.stripBound F.c (1 - F.c) N)).1 *
        (1 + ‖T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay (F.c - 1 / 2) (1 / 2 - F.c) N)).1 *
        (1 + ‖T‖) ^ (-(N : ℤ)) := by
  have htop :=
    norm_integral_le_integral_norm
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x))
      (F.c) (1 - F.c)
  have hbound :
      ∀ x ∈ Set.Icc F.c (1 - F.c),
        ‖zetaCompletedExplicitFormulaContourIntegrand f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)‖
          ≤ (Classical.choose
              (h.logderiv_control.stripBound F.c (1 - F.c) N)).1 *
            (1 + ‖T‖) ^ (-(N : ℤ)) *
            (Classical.choose
              (h.phi_control.verticalStripRapidDecay (F.c - 1 / 2) (1 / 2 - F.c) N)).1 *
            (1 + ‖T‖) ^ (-(N : ℤ)) := by
    intro x hx
    exact ExplicitFormulaFamilyAnalyticPackage.topEdgeContourBound h N T x hx.1 hx.2
  calc
    ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)‖
        = ‖∫ x in F.c..(1 - F.c),
            zetaCompletedExplicitFormulaContourIntegrand f
              (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)‖ := by
          rfl
    _ ≤ ∫ x in F.c..(1 - F.c),
          ‖zetaCompletedExplicitFormulaContourIntegrand f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)‖ := htop
    _ ≤ ∫ x in F.c..(1 - F.c),
          (Classical.choose
            (h.logderiv_control.stripBound F.c (1 - F.c) N)).1 *
          (1 + ‖T‖) ^ (-(N : ℤ)) *
          (Classical.choose
            (h.phi_control.verticalStripRapidDecay (F.c - 1 / 2) (1 / 2 - F.c) N)).1 *
          (1 + ‖T‖) ^ (-(N : ℤ)) := by
          refine intervalIntegral.integral_mono_on ?_ ?_ ?_ ?_
          · continuity
          · intro x hx
            exact hbound x hx
          · positivity
          · intro x hx
            positivity
    _ = (1 - 2 * F.c) *
        (Classical.choose
          (h.logderiv_control.stripBound F.c (1 - F.c) N)).1 *
        (1 + ‖T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay (F.c - 1 / 2) (1 / 2 - F.c) N)).1 *
        (1 + ‖T‖) ^ (-(N : ℤ)) := by
          simp

/-- The horizontal top-minus-bottom difference tends to zero along a contour family. -/
theorem ExplicitFormulaFamilyAnalyticPackage.horizontalDecay
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
      atTop
      (𝓝 (0 : ℝ)) := by
  have htop :
      Tendsto
        (fun T : ℝ => ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)‖)
        atTop
        (𝓝 (0 : ℝ)) := by
    have hconst :
        Tendsto
          (fun T : ℝ =>
            (1 - 2 * F.c) *
              (Classical.choose
                (h.logderiv_control.stripBound F.c (1 - F.c) N)).1 *
              (1 + ‖T‖) ^ (-(N : ℤ)) *
              (Classical.choose
                (h.phi_control.verticalStripRapidDecay
                  (F.c - 1 / 2) (1 / 2 - F.c) N)).1 *
              (1 + ‖T‖) ^ (-(N : ℤ)))
          atTop
          (𝓝 (0 : ℝ)) := by
      have hpow := tendsto_one_add_norm_pow_neg_atTop N
      have hmul := hpow.mul hpow
      have hscale :
          Tendsto
            (fun T : ℝ =>
              (1 - 2 * F.c) *
                (Classical.choose
                  (h.logderiv_control.stripBound F.c (1 - F.c) N)).1 *
                (1 + ‖T‖) ^ (-(N : ℤ)) *
                (Classical.choose
                  (h.phi_control.verticalStripRapidDecay
                    (F.c - 1 / 2) (1 / 2 - F.c) N)).1 *
                (1 + ‖T‖) ^ (-(N : ℤ)))
            atTop
            (𝓝 (0 : ℝ)) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (hmul.const_mul
            ((1 - 2 * F.c) *
              (Classical.choose
                (h.logderiv_control.stripBound F.c (1 - F.c) N)).1 *
              (Classical.choose
                (h.phi_control.verticalStripRapidDecay
                  (F.c - 1 / 2) (1 / 2 - F.c) N)).1))
      exact hscale
    refine tendsto_of_eventually_le_of_tendsto ?_ hconst
    · filter_upwards with T
      exact ExplicitFormulaFamilyAnalyticPackage.topLineIntegral_norm_le h N T
  have hbot :
      Tendsto
        (fun T : ℝ => ‖zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖)
        atTop
        (𝓝 (0 : ℝ)) := by
    have hconst :
        Tendsto
          (fun T : ℝ =>
            (1 - 2 * F.c) *
              (Classical.choose
                (h.logderiv_control.stripBound F.c (1 - F.c) N)).1 *
              (1 + ‖T‖) ^ (-(N : ℤ)) *
              (Classical.choose
                (h.phi_control.verticalStripRapidDecay
                  (F.c - 1 / 2) (1 / 2 - F.c) N)).1 *
              (1 + ‖T‖) ^ (-(N : ℤ)))
          atTop
          (𝓝 (0 : ℝ)) := by
      have hpow := tendsto_one_add_norm_pow_neg_atTop N
      have hmul := hpow.mul hpow
      have hscale :
          Tendsto
            (fun T : ℝ =>
              (1 - 2 * F.c) *
                (Classical.choose
                  (h.logderiv_control.stripBound F.c (1 - F.c) N)).1 *
                (1 + ‖T‖) ^ (-(N : ℤ)) *
                (Classical.choose
                  (h.phi_control.verticalStripRapidDecay
                    (F.c - 1 / 2) (1 / 2 - F.c) N)).1 *
                (1 + ‖T‖) ^ (-(N : ℤ)))
            atTop
            (𝓝 (0 : ℝ)) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (hmul.const_mul
            ((1 - 2 * F.c) *
              (Classical.choose
                (h.logderiv_control.stripBound F.c (1 - F.c) N)).1 *
              (Classical.choose
                (h.phi_control.verticalStripRapidDecay
                  (F.c - 1 / 2) (1 / 2 - F.c) N)).1))
      exact hscale
    refine tendsto_of_eventually_le_of_tendsto ?_ hconst
    · filter_upwards with T
      exact ExplicitFormulaFamilyAnalyticPackage.bottomEdgeContourBound h N T
  have hsum : Tendsto
      (fun T : ℝ =>
        ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖)
      atTop
      (𝓝 (0 : ℝ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds) ?_ ?_ ?_
    · simpa using htop.add hbot
    · filter_upwards with T
      exact norm_sub_le _ _
    · filter_upwards with T
      exact norm_nonneg _
  simpa [Real.norm_eq_abs] using hsum

/-- The analytic package yields the pointwise top/bottom contour bounds on the horizontal
edges. -/
theorem ExplicitFormulaAnalyticPackage.horizontalEdgeContourBounds
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖
      ≤ (Classical.choose
          (h.logderiv_control.stripBound h.contour_data.rectangle.c
            (1 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay
            (h.contour_data.rectangle.c - 1 / 2)
            (1 / 2 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) ∧
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x)‖
      ≤ (Classical.choose
          (h.logderiv_control.stripBound h.contour_data.rectangle.c
            (1 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay
            (h.contour_data.rectangle.c - 1 / 2)
            (1 / 2 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) := by
  constructor
  · exact zetaCompletedExplicitFormulaTopPath_contourIntegrand_strip_bound
      h.phi_control h.logderiv_control h.contour_data.rectangle x hx1 hx2 N
  · exact zetaCompletedExplicitFormulaBottomPath_contourIntegrand_strip_bound
      h.phi_control h.logderiv_control h.contour_data.rectangle x hx1 hx2 N

/-- The analytic package yields the pointwise contour bound on the right vertical edge. -/
theorem ExplicitFormulaAnalyticPackage.rightEdgeContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (t : ℝ)
    (ht1 : t ≤ h.contour_data.rectangle.T)
    (ht2 : -h.contour_data.rectangle.T ≤ t) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖
      ≤ (Classical.choose
          (h.logderiv_control.stripBound h.contour_data.rectangle.c
            (1 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay
            (h.contour_data.rectangle.c - 1 / 2)
            (1 / 2 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) := by
  have hlog :=
    h.logderiv_control.stripBound h.contour_data.rectangle.c
      (1 - h.contour_data.rectangle.c) N
  have hphi :=
    h.phi_control.verticalStripRapidDecay
      (h.contour_data.rectangle.c - 1 / 2) (1 / 2 - h.contour_data.rectangle.c) N
  have hrightstrip :
      h.contour_data.rectangle.c ≤
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t).re ∧
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t).re ≤
          1 - h.contour_data.rectangle.c := by
    constructor
    · rw [zetaCompletedExplicitFormulaRightPath_re]
      linarith [h.contour_data.c_gt_half]
    · rw [zetaCompletedExplicitFormulaRightPath_re]
      linarith [h.contour_data.c_gt_half]
  have hshiftstrip :
      (h.contour_data.rectangle.c - 1 / 2) ≤
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t - 1 / 2 : ℂ).re ≤
          (1 / 2 - h.contour_data.rectangle.c) := by
    constructor <;>
      rw [sub_re, zetaCompletedExplicitFormulaRightPath_re]
      linarith [h.contour_data.c_gt_half]
  have htopim :
      ‖(zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t).im‖ = ‖t‖ := by
    simp [zetaCompletedExplicitFormulaRightPath]
  have hshiftim :
      ‖(zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t - 1 / 2 : ℂ).im‖ = ‖t‖ := by
    simp [zetaCompletedExplicitFormulaRightPath]
  calc
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖
        ≤ ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t - 1 / 2)‖ := by
        exact norm_zetaCompletedExplicitFormulaContourIntegrand_le f _
    _ ≤ (Classical.choose hlog).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose hphi).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) := by
        gcongr
        · exact (Classical.choose_spec hlog).2 _ hrightstrip.1 hrightstrip.2
        · exact (Classical.choose_spec hphi).2 _ hshiftstrip.1 hshiftstrip.2
    _ = (Classical.choose
          (h.logderiv_control.stripBound h.contour_data.rectangle.c
            (1 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay
            (h.contour_data.rectangle.c - 1 / 2)
            (1 / 2 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) := by
        simp [hlog, hphi, mul_comm, mul_left_comm, mul_assoc]

/-- The analytic package yields the pointwise contour bound on the left vertical edge. -/
theorem ExplicitFormulaAnalyticPackage.leftEdgeContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (t : ℝ)
    (ht1 : t ≤ h.contour_data.rectangle.T)
    (ht2 : -h.contour_data.rectangle.T ≤ t) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖
      ≤ (Classical.choose
          (h.logderiv_control.stripBound h.contour_data.rectangle.c
            (1 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay
            (h.contour_data.rectangle.c - 1 / 2)
            (1 / 2 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) := by
  have hlog :=
    h.logderiv_control.stripBound h.contour_data.rectangle.c
      (1 - h.contour_data.rectangle.c) N
  have hphi :=
    h.phi_control.verticalStripRapidDecay
      (h.contour_data.rectangle.c - 1 / 2) (1 / 2 - h.contour_data.rectangle.c) N
  have hleftstrip :
      h.contour_data.rectangle.c ≤
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t).re ∧
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t).re ≤
          1 - h.contour_data.rectangle.c := by
    constructor
    · rw [zetaCompletedExplicitFormulaLeftPath_re]
      linarith [h.contour_data.c_gt_half]
    · rw [zetaCompletedExplicitFormulaLeftPath_re]
      linarith [h.contour_data.c_gt_half]
  have hshiftstrip :
      (h.contour_data.rectangle.c - 1 / 2) ≤
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t - 1 / 2 : ℂ).re ≤
          (1 / 2 - h.contour_data.rectangle.c) := by
    constructor <;>
      rw [sub_re, zetaCompletedExplicitFormulaLeftPath_re]
      linarith [h.contour_data.c_gt_half]
  have ht_im :
      ‖(zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t).im‖ = ‖t‖ := by
    simp [zetaCompletedExplicitFormulaLeftPath]
  have hshiftim :
      ‖(zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t - 1 / 2 : ℂ).im‖ = ‖t‖ := by
    simp [zetaCompletedExplicitFormulaLeftPath]
  calc
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖
        ≤ ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t - 1 / 2)‖ := by
        exact norm_zetaCompletedExplicitFormulaContourIntegrand_le f _
    _ ≤ (Classical.choose hlog).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose hphi).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) := by
        gcongr
        · exact (Classical.choose_spec hlog).2 _ hleftstrip.1 hleftstrip.2
        · exact (Classical.choose_spec hphi).2 _ hshiftstrip.1 hshiftstrip.2
    _ = (Classical.choose
          (h.logderiv_control.stripBound h.contour_data.rectangle.c
            (1 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay
            (h.contour_data.rectangle.c - 1 / 2)
            (1 / 2 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) := by
        simp [hlog, hphi, mul_comm, mul_left_comm, mul_assoc]

/-- The analytic package bundles the four pointwise contour edge bounds. -/
theorem ExplicitFormulaAnalyticPackage.contourEdgeBounds
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x t : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c)
    (ht1 : t ≤ h.contour_data.rectangle.T)
    (ht2 : -h.contour_data.rectangle.T ≤ t) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖
      ≤ (Classical.choose
          (h.logderiv_control.stripBound h.contour_data.rectangle.c
            (1 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay
            (h.contour_data.rectangle.c - 1 / 2)
            (1 / 2 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) ∧
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x)‖
      ≤ (Classical.choose
          (h.logderiv_control.stripBound h.contour_data.rectangle.c
            (1 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay
            (h.contour_data.rectangle.c - 1 / 2)
            (1 / 2 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) ∧
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖
      ≤ (Classical.choose
          (h.logderiv_control.stripBound h.contour_data.rectangle.c
            (1 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay
            (h.contour_data.rectangle.c - 1 / 2)
            (1 / 2 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) ∧
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖
      ≤ (Classical.choose
          (h.logderiv_control.stripBound h.contour_data.rectangle.c
            (1 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
        (Classical.choose
          (h.phi_control.verticalStripRapidDecay
            (h.contour_data.rectangle.c - 1 / 2)
            (1 / 2 - h.contour_data.rectangle.c) N)).1 *
        (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) := by
  constructor
  · exact zetaCompletedExplicitFormulaTopPath_contourIntegrand_strip_bound
      h.phi_control h.logderiv_control h.contour_data.rectangle x hx1 hx2 N
  constructor
  · exact zetaCompletedExplicitFormulaBottomPath_contourIntegrand_strip_bound
      h.phi_control h.logderiv_control h.contour_data.rectangle x hx1 hx2 N
  constructor
  · exact ExplicitFormulaAnalyticPackage.rightEdgeContourBound h N t ht1 ht2
  · exact ExplicitFormulaAnalyticPackage.leftEdgeContourBound h N t ht1 ht2

/-- The analytic package yields a single uniform edge bound constant for all four sides. -/
theorem ExplicitFormulaAnalyticPackage.uniformContourEdgeBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x t : ℝ,
        (h.contour_data.rectangle.c ≤ x → x ≤ 1 - h.contour_data.rectangle.c →
          ‖zetaCompletedExplicitFormulaContourIntegrand f
            (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ ≤ C) ∧
        (h.contour_data.rectangle.c ≤ x → x ≤ 1 - h.contour_data.rectangle.c →
          ‖zetaCompletedExplicitFormulaContourIntegrand f
            (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x)‖ ≤ C) ∧
        (t ≤ h.contour_data.rectangle.T → -h.contour_data.rectangle.T ≤ t →
          ‖zetaCompletedExplicitFormulaContourIntegrand f
            (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖ ≤ C) ∧
        (t ≤ h.contour_data.rectangle.T → -h.contour_data.rectangle.T ≤ t →
          ‖zetaCompletedExplicitFormulaContourIntegrand f
            (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖ ≤ C) := by
  let C :=
    (Classical.choose
      (h.logderiv_control.stripBound h.contour_data.rectangle.c
        (1 - h.contour_data.rectangle.c) N)).1 *
      (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
      (Classical.choose
        (h.phi_control.verticalStripRapidDecay
          (h.contour_data.rectangle.c - 1 / 2)
          (1 / 2 - h.contour_data.rectangle.c) N)).1 *
      (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ))
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro x t
    constructor
    · intro hx1 hx2
      exact le_trans
        (ExplicitFormulaAnalyticPackage.contourEdgeBounds h N x t hx1 hx2
          (by linarith [h.contour_data.T_pos])
          (by linarith [h.contour_data.T_pos])).1
        (le_of_eq rfl)
    constructor
    · intro hx1 hx2
      exact le_trans
        (ExplicitFormulaAnalyticPackage.contourEdgeBounds h N x t hx1 hx2
          (by linarith [h.contour_data.T_pos])
          (by linarith [h.contour_data.T_pos])).2.1
        (le_of_eq rfl)
    constructor
    · intro ht1 ht2
      exact le_trans
        (ExplicitFormulaAnalyticPackage.contourEdgeBounds h N x t
          (by linarith [h.contour_data.c_gt_half]) (by linarith [h.contour_data.c_gt_half])
          ht1 ht2).2.2.1
        (le_of_eq rfl)
    · intro ht1 ht2
      exact le_trans
        (ExplicitFormulaAnalyticPackage.contourEdgeBounds h N x t
          (by linarith [h.contour_data.c_gt_half]) (by linarith [h.contour_data.c_gt_half])
          ht1 ht2).2.2.2
        (le_of_eq rfl)

/-- The analytic package is the owner object for the contour estimate chain. -/
def ExplicitFormulaAnalyticPackageData (f : ZetaAdmissibleFunction) : Prop :=
  ExplicitFormulaAnalyticPackage f

/-- The package alias is definitionally the same owner object. -/
theorem ExplicitFormulaAnalyticPackageData_eq
    (f : ZetaAdmissibleFunction) :
    ExplicitFormulaAnalyticPackageData f = ExplicitFormulaAnalyticPackage f := by
  rfl

/-- The negative logarithmic derivative of `ζ(s) = Λ(s) / Γℝ(s)`. -/
def riemannZetaNegLogDeriv (s : ℂ) : ℂ :=
  - deriv riemannZeta s / riemannZeta s

/-- The completed explicit-formula contour integrand. -/
def zetaCompletedExplicitFormulaContourIntegrand
    (f : ZetaAdmissibleFunction) (s : ℂ) : ℂ :=
  completedZetaNegLogDeriv s * zetaCompletedExplicitFormulaPhi f (s - 1 / 2)

/-- The closed rectangle used in the contour argument. -/
structure ExplicitFormulaRectangle where
  c : ℝ
  T : ℝ

/-- Data describing the completed explicit-formula contour problem. -/
structure ExplicitFormulaContourData where
  rectangle : ExplicitFormulaRectangle
  c_gt_half : (1 / 2 : ℝ) < rectangle.c
  T_pos : 0 < rectangle.T

/-- A contour family indexed by the height parameter `T`. This is the correct owner object for
horizontal decay statements, since the limit theorem varies `T` at `atTop`. -/
structure ExplicitFormulaContourFamily where
  c : ℝ
  c_gt_half : (1 / 2 : ℝ) < c

/-- The contour rectangle at height `T` in a contour family. -/
def ExplicitFormulaContourFamily.rectangle (F : ExplicitFormulaContourFamily) (T : ℝ) :
    ExplicitFormulaRectangle :=
  ⟨F.c, T⟩

/-- The contour family exposes the right-edge positivity at every height. -/
theorem ExplicitFormulaContourFamily.rightPath_re_pos
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    0 < (zetaCompletedExplicitFormulaRightPath (F.rectangle t) t).re := by
  rw [zetaCompletedExplicitFormulaRightPath_re]
  linarith

/-- The contour family exposes the top strip bound at every height. -/
theorem ExplicitFormulaContourFamily.topPath_strip
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hx1 : F.c ≤ x) (hx2 : x ≤ 1 - F.c) :
    F.c ≤ (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x).re ∧
      (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x).re ≤ 1 - F.c := by
  simpa [ExplicitFormulaContourFamily.rectangle] using
    zetaCompletedExplicitFormulaTopPath_strip (⟨F.c, T⟩) x hx1 hx2

/-- The contour family exposes the bottom strip bound at every height. -/
theorem ExplicitFormulaContourFamily.bottomPath_strip
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hx1 : F.c ≤ x) (hx2 : x ≤ 1 - F.c) :
    F.c ≤ (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x).re ∧
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x).re ≤ 1 - F.c := by
  simpa [ExplicitFormulaContourFamily.rectangle] using
    zetaCompletedExplicitFormulaBottomPath_strip (⟨F.c, T⟩) x hx1 hx2

/-- Data describing a zero of the completed zeta function with multiplicity. -/
structure ExplicitFormulaZeroData where
  zero : ℂ
  multiplicity : ℕ

/-- The residue contribution of a single zero. -/
def explicitFormulaZeroResidue
    (f : ZetaAdmissibleFunction) (ρ : ExplicitFormulaZeroData) : ℂ :=
  - (ρ.multiplicity : ℂ) * zetaCompletedExplicitFormulaPhi f (ρ.zero - 1 / 2)

/-- The residue contribution unfolds definitionally. -/
theorem explicitFormulaZeroResidue_def
    (f : ZetaAdmissibleFunction) (ρ : ExplicitFormulaZeroData) :
    explicitFormulaZeroResidue f ρ =
      - (ρ.multiplicity : ℂ) * zetaCompletedExplicitFormulaPhi f (ρ.zero - 1 / 2) := by
  rfl

/-- The contour-side residue sum over a finite family of zeros. -/
def explicitFormulaResidueSum
    (f : ZetaAdmissibleFunction) (S : List ExplicitFormulaZeroData) : ℂ :=
  S.foldl (fun acc ρ => acc + explicitFormulaZeroResidue f ρ) 0

/-- The residue sum of the empty list is zero. -/
theorem explicitFormulaResidueSum_nil (f : ZetaAdmissibleFunction) :
    explicitFormulaResidueSum f [] = 0 := by
  rfl

/-- The residue sum unfolds over `cons`. -/
theorem explicitFormulaResidueSum_cons
    (f : ZetaAdmissibleFunction) (ρ : ExplicitFormulaZeroData) (S : List ExplicitFormulaZeroData) :
    explicitFormulaResidueSum f (ρ :: S) =
      (explicitFormulaResidueSum f S) + explicitFormulaZeroResidue f ρ := by
  rfl

/-- The horizontal-side decay target for the contour argument. -/
def explicitFormulaHorizontalDecayTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  Tendsto
    (fun T : ℝ => zetaCompletedExplicitFormulaTopLineIntegral f r -
      zetaCompletedExplicitFormulaBottomLineIntegral f r)
    atTop
    (𝓝 0)

/-- The horizontal-side decay target indexed by a contour family. -/
def explicitFormulaHorizontalDecayTargetFamily
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) : Prop :=
  Tendsto
    (fun T : ℝ =>
      zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
    atTop
    (𝓝 0)

/-- The vertical-side decomposition target for the contour argument. -/
def explicitFormulaVerticalDecompositionTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  zetaCompletedExplicitFormulaRightLineIntegral f r -
    zetaCompletedExplicitFormulaLeftLineIntegral f r =
    zetaCompletedExplicitFormulaBoundarySumAnalytic f

/-- The residue-theorem target for the explicit formula. -/
def explicitFormulaResidueTheoremTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  zetaCompletedExplicitFormulaContourIntegral f r =
    explicitFormulaResidueSum f []

/-- The full contour-shift target for the explicit formula. -/
def explicitFormulaContourShiftTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  zetaCompletedZeroKreinGram f =
    zetaCompletedExplicitFormulaBoundarySumAnalytic f

/-- The residue theorem target for the explicit formula. -/
def explicitFormulaResidueTheoremStatement
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (S : List ExplicitFormulaZeroData) : Prop :=
  zetaCompletedExplicitFormulaContourIntegral f r =
    explicitFormulaResidueSum f S

/-- The horizontal decay target for the explicit formula. -/
def explicitFormulaHorizontalDecayStatement
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  Tendsto
    (fun T : ℝ =>
      zetaCompletedExplicitFormulaTopLineIntegral f r -
        zetaCompletedExplicitFormulaBottomLineIntegral f r)
    atTop
    (𝓝 0)

/-- The family-indexed horizontal decay statement. -/
def explicitFormulaHorizontalDecayStatementFamily
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) : Prop :=
  Tendsto
    (fun T : ℝ =>
      zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
    atTop
    (𝓝 0)

/-- The right vertical side of the rectangle. -/
def explicitFormulaRightSide (r : ExplicitFormulaRectangle) : Set ℂ :=
  {s : ℂ | s.re = r.c ∧ s.im ≤ r.T ∧ -r.T ≤ s.im}

/-- The left vertical side of the rectangle. -/
def explicitFormulaLeftSide (r : ExplicitFormulaRectangle) : Set ℂ :=
  {s : ℂ | s.re = 1 - r.c ∧ s.im ≤ r.T ∧ -r.T ≤ s.im}

/-- The top horizontal side of the rectangle. -/
def explicitFormulaTopSide (r : ExplicitFormulaRectangle) : Set ℂ :=
  {s : ℂ | r.c ≤ s.re ∧ s.re ≤ 1 - r.c ∧ s.im = r.T}

/-- The bottom horizontal side of the rectangle. -/
def explicitFormulaBottomSide (r : ExplicitFormulaRectangle) : Set ℂ :=
  {s : ℂ | r.c ≤ s.re ∧ s.re ≤ 1 - r.c ∧ s.im = -r.T}

/-- The boundary sum on the explicit-formula side, as a named object. -/
def zetaCompletedExplicitFormulaBoundaryPieces
    (f : ZetaAdmissibleFunction) :
    ℂ × ℂ × ℂ :=
  (zetaCompletedExplicitFormulaPrimeContribution f,
    zetaCompletedExplicitFormulaArchimedeanContribution f,
    zetaCompletedExplicitFormulaCorrectionContribution f)

/-- The combined boundary sum assembled from the three explicit pieces. -/
def zetaCompletedExplicitFormulaBoundarySumAnalytic
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeContribution f +
    zetaCompletedExplicitFormulaArchimedeanContribution f +
    zetaCompletedExplicitFormulaCorrectionContribution f

/-- The right-side line integral of the contour integrand. -/
noncomputable def zetaCompletedExplicitFormulaRightLineIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  ∫ t in Set.Icc (-r.T) r.T,
    zetaCompletedExplicitFormulaContourIntegrand f
      (zetaCompletedExplicitFormulaRightPath r t)

/-- User-facing name for the right vertical integral. -/
abbrev zetaVerticalIntegralRight
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f r

/-- The left-side line integral of the contour integrand. -/
noncomputable def zetaCompletedExplicitFormulaLeftLineIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  ∫ t in Set.Icc (-r.T) r.T,
    zetaCompletedExplicitFormulaContourIntegrand f
      (zetaCompletedExplicitFormulaLeftPath r t)

/-- User-facing name for the left vertical integral. -/
abbrev zetaVerticalIntegralLeft
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaLeftLineIntegral f r

/-- The top-side line integral of the contour integrand. -/
noncomputable def zetaCompletedExplicitFormulaTopLineIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  ∫ x in Set.Icc r.c (1 - r.c),
    zetaCompletedExplicitFormulaContourIntegrand f
      (zetaCompletedExplicitFormulaTopPath r x)

/-- User-facing name for the top horizontal integral. -/
abbrev zetaHorizontalIntegralTop
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral f r

/-- The bottom-side line integral of the contour integrand. -/
noncomputable def zetaCompletedExplicitFormulaBottomLineIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  ∫ x in Set.Icc r.c (1 - r.c),
    zetaCompletedExplicitFormulaContourIntegrand f
      (zetaCompletedExplicitFormulaBottomPath r x)

/-- User-facing name for the bottom horizontal integral. -/
abbrev zetaHorizontalIntegralBottom
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaBottomLineIntegral f r

/-- The contour integral around the rectangle. -/
noncomputable def zetaCompletedExplicitFormulaContourIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f r -
    zetaCompletedExplicitFormulaLeftLineIntegral f r +
    zetaCompletedExplicitFormulaTopLineIntegral f r -
    zetaCompletedExplicitFormulaBottomLineIntegral f r

/-- User-facing name for the rectangle boundary integral. -/
abbrev zetaRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f r

/-- The contour integral is the signed sum of the four side integrals. -/
theorem zetaCompletedExplicitFormulaContourIntegral_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaContourIntegral f r =
      zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r +
        zetaCompletedExplicitFormulaTopLineIntegral f r -
        zetaCompletedExplicitFormulaBottomLineIntegral f r := by
  rfl

/-- The rectangle boundary integral is the signed sum of the four side integrals. -/
theorem zetaRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaRectangleBoundaryIntegral f r =
      zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r +
        zetaCompletedExplicitFormulaTopLineIntegral f r -
        zetaCompletedExplicitFormulaBottomLineIntegral f r := by
  rfl

/-- The right vertical integral is the right side line integral. -/
theorem zetaVerticalIntegralRight_eq_contour
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaVerticalIntegralRight f r = zetaCompletedExplicitFormulaRightLineIntegral f r := by
  rfl

/-- The left vertical integral is the left side line integral. -/
theorem zetaVerticalIntegralLeft_eq_contour
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaVerticalIntegralLeft f r = zetaCompletedExplicitFormulaLeftLineIntegral f r := by
  rfl

/-- The top horizontal integral is the top side line integral. -/
theorem zetaHorizontalIntegralTop_eq_contour
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaHorizontalIntegralTop f r = zetaCompletedExplicitFormulaTopLineIntegral f r := by
  rfl

/-- The bottom horizontal integral is the bottom side line integral. -/
theorem zetaHorizontalIntegralBottom_eq_contour
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaHorizontalIntegralBottom f r = zetaCompletedExplicitFormulaBottomLineIntegral f r := by
  rfl

/-- The contour integrand expands into the completed negative log derivative
times the spectral transform. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_eq
    (f : ZetaAdmissibleFunction) (s : ℂ) :
    zetaCompletedExplicitFormulaContourIntegrand f s =
      completedZetaNegLogDeriv s * zetaCompletedExplicitFormulaPhi f (s - 1 / 2) := by
  rfl

/-- The contour integrand is explicitly the log-derivative times `Φ_f`. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_bridge
    (f : ZetaAdmissibleFunction) (s : ℂ) :
    zetaCompletedExplicitFormulaContourIntegrand f s =
      completedZetaNegLogDeriv s * zetaCompletedExplicitFormulaPhi f (s - 1 / 2) := by
  rfl

/-- The explicit-formula integrand on the critical line is the negative logarithmic derivative
of `ζ` times the probe transform, after unfolding the factorization by `Γℝ`. -/
theorem riemannZetaNegLogDeriv_eq_factorized
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΛ : completedRiemannZeta s ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) :
    riemannZetaNegLogDeriv s =
      - logDeriv (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹) s := by
  unfold riemannZetaNegLogDeriv
  rw [zetaCompletedExplicitFormula_riemannZeta_eq_completed_mul_invGamma hs0 hΓ]
  rw [logDeriv_mul s hΛ (by simpa using inv_ne_zero hΓ)
      (differentiableAt_completedZeta hs0 hs1) differentiable_Gammaℝ_inv.differentiableAt]

/-- The completed negative logarithmic derivative is the factorized `ζ` logarithmic derivative. -/
theorem completedZetaNegLogDeriv_eq_factorized
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΛ : completedRiemannZeta s ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) :
    completedZetaNegLogDeriv s =
      - logDeriv (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹) s := by
  unfold completedZetaNegLogDeriv
  rw [zetaCompletedExplicitFormula_completed_factorization hs0 hΓ]
  rw [logDeriv_mul s hΛ (by simpa using inv_ne_zero hΓ)
      (differentiableAt_completedZeta hs0 hs1) differentiable_Gammaℝ_inv.differentiableAt]

/-- The contour integrand is the negative completed-zeta log derivative times `Φ_f`. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_eq_neg_logDeriv
    (f : ZetaAdmissibleFunction) (s : ℂ) :
    zetaCompletedExplicitFormulaContourIntegrand f s =
      (- logDeriv completedRiemannZeta s) * zetaCompletedExplicitFormulaPhi f (s - 1 / 2) := by
  unfold zetaCompletedExplicitFormulaContourIntegrand
  rw [completedZetaNegLogDeriv_eq_neg_logDeriv]

/-- The contour integrand also rewrites through the factorized `ζ` logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_eq_factorized
    (f : ZetaAdmissibleFunction) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    zetaCompletedExplicitFormulaContourIntegrand f s =
      (- logDeriv (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹) s) *
        zetaCompletedExplicitFormulaPhi f (s - 1 / 2) := by
  unfold zetaCompletedExplicitFormulaContourIntegrand
  rw [completedZetaNegLogDeriv_eq_factorized hs0 hs1 hΛ hΓ]

/-- The right boundary integrand rewrites through the factorized logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaRightBoundary_eq_factorized
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (t : ℝ)
    (hs0 : zetaCompletedExplicitFormulaRightPath r t ≠ 0)
    (hs1 : zetaCompletedExplicitFormulaRightPath r t ≠ 1)
    (hΛ : completedRiemannZeta (zetaCompletedExplicitFormulaRightPath r t) ≠ 0)
    (hΓ : Gammaℝ (zetaCompletedExplicitFormulaRightPath r t) ≠ 0) :
    zetaCompletedExplicitFormulaRightBoundary f r t =
      (- logDeriv (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹)
        (zetaCompletedExplicitFormulaRightPath r t)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath r t - 1 / 2) := by
  unfold zetaCompletedExplicitFormulaRightBoundary
  rw [zetaCompletedExplicitFormulaContourIntegrand_eq_factorized f
    (s := zetaCompletedExplicitFormulaRightPath r t) hs0 hs1 hΛ hΓ]

/-- The left boundary integrand rewrites through the factorized logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaLeftBoundary_eq_factorized
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (t : ℝ)
    (hs0 : zetaCompletedExplicitFormulaLeftPath r t ≠ 0)
    (hs1 : zetaCompletedExplicitFormulaLeftPath r t ≠ 1)
    (hΛ : completedRiemannZeta (zetaCompletedExplicitFormulaLeftPath r t) ≠ 0)
    (hΓ : Gammaℝ (zetaCompletedExplicitFormulaLeftPath r t) ≠ 0) :
    zetaCompletedExplicitFormulaLeftBoundary f r t =
      (- logDeriv (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹)
        (zetaCompletedExplicitFormulaLeftPath r t)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath r t - 1 / 2) := by
  unfold zetaCompletedExplicitFormulaLeftBoundary
  rw [zetaCompletedExplicitFormulaContourIntegrand_eq_factorized f
    (s := zetaCompletedExplicitFormulaLeftPath r t) hs0 hs1 hΛ hΓ]

/-- The top boundary integrand rewrites through the factorized logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaHorizontalBoundaryTop_eq_factorized
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (x : ℝ)
    (hs0 : zetaCompletedExplicitFormulaTopPath r x ≠ 0)
    (hs1 : zetaCompletedExplicitFormulaTopPath r x ≠ 1)
    (hΛ : completedRiemannZeta (zetaCompletedExplicitFormulaTopPath r x) ≠ 0)
    (hΓ : Gammaℝ (zetaCompletedExplicitFormulaTopPath r x) ≠ 0) :
    zetaCompletedExplicitFormulaHorizontalBoundaryTop f r x =
      (- logDeriv (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹)
        (zetaCompletedExplicitFormulaTopPath r x)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaTopPath r x - 1 / 2) := by
  unfold zetaCompletedExplicitFormulaHorizontalBoundaryTop
  rw [zetaCompletedExplicitFormulaContourIntegrand_eq_factorized f
    (s := zetaCompletedExplicitFormulaTopPath r x) hs0 hs1 hΛ hΓ]

/-- The bottom boundary integrand rewrites through the factorized logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaHorizontalBoundaryBottom_eq_factorized
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (x : ℝ)
    (hs0 : zetaCompletedExplicitFormulaBottomPath r x ≠ 0)
    (hs1 : zetaCompletedExplicitFormulaBottomPath r x ≠ 1)
    (hΛ : completedRiemannZeta (zetaCompletedExplicitFormulaBottomPath r x) ≠ 0)
    (hΓ : Gammaℝ (zetaCompletedExplicitFormulaBottomPath r x) ≠ 0) :
    zetaCompletedExplicitFormulaHorizontalBoundaryBottom f r x =
      (- logDeriv (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹)
        (zetaCompletedExplicitFormulaBottomPath r x)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2) := by
  unfold zetaCompletedExplicitFormulaHorizontalBoundaryBottom
  rw [zetaCompletedExplicitFormulaContourIntegrand_eq_factorized f
    (s := zetaCompletedExplicitFormulaBottomPath r x) hs0 hs1 hΛ hΓ]

/-- The rectangle theorem applies to the factorized contour integrand once its analytic hypotheses
are provided. -/
theorem zetaCompletedExplicitFormulaRectangleBoundaryIdentity_factorized
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (f' : ℂ → (ℂ →L[ℝ] ℂ))
    (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn (fun z : ℂ =>
      (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹) z) *
        zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
      (Set.uIcc (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re ×ℂ
        Set.uIcc (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im))
    (Hd : ∀ x, x ∈ Set.Ioo (min (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re)
        (max (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re) ×ℂ
        Set.Ioo (min (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im)
          (max (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im) \ s →
        HasFDerivAt
          (fun z : ℂ =>
            (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹) z) *
              zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
          (f' x) x)
    (Hi : IntegrableOn
      (fun z => Complex.I • ⇑(f' z) 1 - ⇑(f' z) Complex.I)
      (Set.uIcc (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re ×ℂ
        Set.uIcc (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im) volume) :
    (((∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
          (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
            (x + (r.c + (-r.T) * Complex.I).im * Complex.I)) *
            zetaCompletedExplicitFormulaPhi f
              (x + (r.c + (-r.T) * Complex.I).im * Complex.I - 1 / 2)) -
        ∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
          (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
            (x + (r.c + (r.T) * Complex.I).im * Complex.I)) *
            zetaCompletedExplicitFormulaPhi f
              (x + (r.c + (r.T) * Complex.I).im * Complex.I - 1 / 2)) +
      Complex.I • ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
        (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
          ((r.c + (r.T) * Complex.I).re + y * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            ((r.c + (r.T) * Complex.I).re + y * Complex.I - 1 / 2)) -
      Complex.I • ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
        (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
          ((r.c + (-r.T) * Complex.I).re + y * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            ((r.c + (-r.T) * Complex.I).re + y * Complex.I - 1 / 2)
      =
      ∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
        ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
          Complex.I • ⇑(f' (x + y * Complex.I)) 1 - ⇑(f' (x + y * Complex.I)) Complex.I := by
  exact boundary_integral_rect_of_has_fderiv_at_real_off_countable
    (f := fun z : ℂ =>
      (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹) z) *
        zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
    (f' := f') (z := r.c + (-r.T) * Complex.I) (w := r.c + (r.T) * Complex.I)
    (s := s) (hs := hs) (Hc := Hc) (Hd := Hd) (Hi := Hi)


/-- The combined boundary sum is the analytic boundary sum. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic f =
      zetaCompletedExplicitFormulaPrimeContribution f +
        zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionContribution f := by
  rfl

/-- The boundary sum splits into prime, archimedean, and correction pieces. -/
theorem zetaCompletedExplicitFormulaBoundaryPieces_bridge
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryPieces f =
      (zetaCompletedExplicitFormulaPrimeContribution f,
        zetaCompletedExplicitFormulaArchimedeanContribution f,
        zetaCompletedExplicitFormulaCorrectionContribution f) := by
  rfl

/-- The analytic boundary sum is the sum of the three pieces. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_bridge
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic f =
      zetaCompletedExplicitFormulaPrimeContribution f +
        zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionContribution f := by
  rfl

/-- The completed contour integrand on each side is the contour integrand. -/
theorem zetaCompletedExplicitFormulaRightBoundary_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (t : ℝ) :
    zetaCompletedExplicitFormulaRightBoundary f r t =
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaRightPath r t) := by
  rfl

/-- The left boundary integrand on each side is the contour integrand. -/
theorem zetaCompletedExplicitFormulaLeftBoundary_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftBoundary f r t =
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaLeftPath r t) := by
  rfl

/-- The top boundary integrand on each side is the contour integrand. -/
theorem zetaCompletedExplicitFormulaHorizontalBoundaryTop_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (x : ℝ) :
    zetaCompletedExplicitFormulaHorizontalBoundaryTop f r x =
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath r x) := by
  rfl

/-- The bottom boundary integrand on each side is the contour integrand. -/
theorem zetaCompletedExplicitFormulaHorizontalBoundaryBottom_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (x : ℝ) :
    zetaCompletedExplicitFormulaHorizontalBoundaryBottom f r x =
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath r x) := by
  rfl

/-- The completed zeta contour integrand is compatible with the rectangle theorem
surface once differentiability hypotheses are supplied. -/
theorem zetaCompletedExplicitFormulaRectangleBoundaryIdentity
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (f' : ℂ → (ℂ →L[ℝ] ℂ))
    (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (Set.uIcc (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re ×ℂ
        Set.uIcc (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im))
    (Hd : ∀ x, x ∈ Set.Ioo (min (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re)
        (max (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re) ×ℂ
        Set.Ioo (min (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im)
          (max (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im) \ s →
        HasFDerivAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) (f' x) x)
    (Hi : IntegrableOn
      (fun z => Complex.I • ⇑(f' z) 1 - ⇑(f' z) Complex.I)
      (Set.uIcc (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re ×ℂ
        Set.uIcc (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im) volume) :
    (((∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (r.c + (-r.T) * Complex.I).im * Complex.I)) -
        ∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (r.c + (r.T) * Complex.I).im * Complex.I)) +
      Complex.I • ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
        zetaCompletedExplicitFormulaContourIntegrand f
          ((r.c + (r.T) * Complex.I).re + y * Complex.I)) -
      Complex.I • ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
        zetaCompletedExplicitFormulaContourIntegrand f
          ((r.c + (-r.T) * Complex.I).re + y * Complex.I)
      =
      ∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
        ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
          Complex.I • ⇑(f' (x + y * Complex.I)) 1 - ⇑(f' (x + y * Complex.I)) Complex.I := by
  exact boundary_integral_rect_of_has_fderiv_at_real_off_countable
    (f := fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
    (f' := f') (z := r.c + (-r.T) * Complex.I) (w := r.c + (r.T) * Complex.I)
    (s := s) (hs := hs) (Hc := Hc) (Hd := Hd) (Hi := Hi)

/-- The vertical decomposition target is the boundary-side identity. -/
theorem explicitFormulaVerticalDecompositionTarget_iff
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaVerticalDecompositionTarget f r ↔
      zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
  rfl

/-- The residue-theorem target unfolds to the contour integral identity. -/
theorem explicitFormulaResidueTheoremTarget_iff
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaResidueTheoremTarget f r ↔
      zetaCompletedExplicitFormulaContourIntegral f r =
        explicitFormulaResidueSum f [] := by
  rfl

/-- The contour-shift target unfolds to the final explicit formula identity. -/
theorem explicitFormulaContourShiftTarget_iff
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaContourShiftTarget f r ↔
      zetaCompletedZeroKreinGram f =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
  rfl

/-- The right boundary integral is the right line integral. -/
theorem zetaVerticalIntegralRight_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaVerticalIntegralRight f r = zetaCompletedExplicitFormulaRightLineIntegral f r := by
  rfl

/-- The left boundary integral is the left line integral. -/
theorem zetaVerticalIntegralLeft_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaVerticalIntegralLeft f r = zetaCompletedExplicitFormulaLeftLineIntegral f r := by
  rfl

/-- The top boundary integral is the top line integral. -/
theorem zetaHorizontalIntegralTop_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaHorizontalIntegralTop f r = zetaCompletedExplicitFormulaTopLineIntegral f r := by
  rfl

/-- The bottom boundary integral is the bottom line integral. -/
theorem zetaHorizontalIntegralBottom_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaHorizontalIntegralBottom f r = zetaCompletedExplicitFormulaBottomLineIntegral f r := by
  rfl

/-- The rectangle boundary integral is the contour integral. -/
theorem zetaRectangleBoundaryIntegral_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaRectangleBoundaryIntegral f r = zetaCompletedExplicitFormulaContourIntegral f r := by
  rfl

/-- The main residue-formula proposition in the analytic note's normalization. -/
def completedZeta_rectangleResidueFormula
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  (1 / (2 * Real.pi * Complex.I)) * zetaRectangleBoundaryIntegral f r =
    - explicitFormulaResidueSum f []

/-- The equivalent zero-sum proposition solving for the residue sum. -/
def zetaZeroSumInRectangle_eq_neg_boundaryIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  explicitFormulaResidueSum f [] =
    - (1 / (2 * Real.pi * Complex.I)) * zetaRectangleBoundaryIntegral f r

/-- The horizontal-vanishing proposition in note form. -/
def zetaHorizontalIntegrals_vanish
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  Tendsto
    (fun T : ℝ => zetaHorizontalIntegralTop f r - zetaHorizontalIntegralBottom f r)
    atTop
    (𝓝 0)

/-- User-facing residue theorem statement. -/
abbrev completedZeta_rectangleResidueFormulaStatement
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  completedZeta_rectangleResidueFormula f r

/-- User-facing horizontal decay statement. -/
abbrev completedZeta_horizontalIntegralsVanish
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  zetaHorizontalIntegrals_vanish f r

/-- The residue theorem statement is the user-facing residue formula. -/
theorem completedZeta_rectangleResidueFormulaStatement_iff
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    completedZeta_rectangleResidueFormulaStatement f r ↔
      (1 / (2 * Real.pi * Complex.I)) * zetaRectangleBoundaryIntegral f r =
        - explicitFormulaResidueSum f [] := by
  rfl

/-- The horizontal decay statement is the user-facing vanishing statement. -/
theorem completedZeta_horizontalIntegralsVanish_iff
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    completedZeta_horizontalIntegralsVanish f r ↔
      Tendsto
        (fun T : ℝ => zetaHorizontalIntegralTop f r - zetaHorizontalIntegralBottom f r)
        atTop
        (𝓝 0) := by
  rfl

/-- The residue theorem proposition is the same in user-facing notation. -/
theorem completedZeta_rectangleResidueFormula_iff
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    completedZeta_rectangleResidueFormula f r ↔
      (1 / (2 * Real.pi * Complex.I)) * zetaRectangleBoundaryIntegral f r =
        - explicitFormulaResidueSum f [] := by
  rfl

/-- The zero-sum proposition is the same statement solved for the sum. -/
theorem zetaZeroSumInRectangle_eq_neg_boundaryIntegral_iff
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaZeroSumInRectangle_eq_neg_boundaryIntegral f r ↔
      explicitFormulaResidueSum f [] =
        - (1 / (2 * Real.pi * Complex.I)) * zetaRectangleBoundaryIntegral f r := by
  rfl

/-- The horizontal decay proposition unfolds to the limit statement. -/
theorem zetaHorizontalIntegrals_vanish_iff
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaHorizontalIntegrals_vanish f r ↔
      Tendsto
        (fun T : ℝ => zetaHorizontalIntegralTop f r - zetaHorizontalIntegralBottom f r)
        atTop
        (𝓝 0) := by
  rfl

/-- The family-indexed horizontal decay proposition unfolds to the limit statement. -/
theorem explicitFormulaHorizontalDecayTargetFamily_iff
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    explicitFormulaHorizontalDecayTargetFamily f F ↔
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
        atTop
        (𝓝 0) := by
  rfl

/-- The family-indexed horizontal decay statement is the same limit. -/
theorem explicitFormulaHorizontalDecayStatementFamily_iff
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    explicitFormulaHorizontalDecayStatementFamily f F ↔
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
        atTop
        (𝓝 0) := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
