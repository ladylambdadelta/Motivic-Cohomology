import Boundary.LFunctions.ZetaExplicitFormulaRectangleAPI
import Boundary.LFunctions.ZetaExplicitFormulaContourPaths
import Boundary.LFunctions.ZetaExplicitFormulaContourPathLemmas
import Boundary.LFunctions.ZetaExplicitFormulaAnalyticCore
import Boundary.LFunctions.ZetaAdmissibleTransformRegularity
import Boundary.LFunctions.ZetaCompletedLogDerivativeControl
import Boundary.LFunctions.ZetaExplicitFormulaPuncturedPlane
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Boundary explicit-formula contour surface

This file names the contour objects used in the completed Guinand--Weil
argument. The actual residue and decay estimates will be proved against these
definitions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter

namespace ZetaAdmissibleFunction

/-- The completed explicit-formula contour integrand, named for the proof. -/
abbrev zetaCompletedExplicitFormulaContourIntegrand
    (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  fun s => completedZetaNegLogDeriv s * zetaCompletedExplicitFormulaPhi f (s - 1 / 2)

/-- The contour integrand expands into the completed negative log derivative
times the spectral transform. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_eq
    (f : ZetaAdmissibleFunction) (s : ℂ) :
    zetaCompletedExplicitFormulaContourIntegrand f s =
      completedZetaNegLogDeriv s * zetaCompletedExplicitFormulaPhi f (s - 1 / 2) := by
  rfl

/-- The contour integrand along the right vertical side. -/
def zetaCompletedExplicitFormulaRightBoundary
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (t : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegrand f (zetaCompletedExplicitFormulaRightPath r t)

/-- The contour integrand along the left vertical side. -/
def zetaCompletedExplicitFormulaLeftBoundary
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (t : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegrand f (zetaCompletedExplicitFormulaLeftPath r t)

/-- The contour integrand along the top horizontal side. -/
def zetaCompletedExplicitFormulaHorizontalBoundaryTop
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (x : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegrand f (zetaCompletedExplicitFormulaTopPath r x)

/-- The contour integrand along the bottom horizontal side. -/
def zetaCompletedExplicitFormulaHorizontalBoundaryBottom
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (x : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegrand f (zetaCompletedExplicitFormulaBottomPath r x)

/-- The contour integrand is the negative completed-zeta log derivative times `Φ_f`. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_eq_neg_logDeriv
    (f : ZetaAdmissibleFunction) (s : ℂ) :
    zetaCompletedExplicitFormulaContourIntegrand f s =
      (- logDeriv completedRiemannZeta s) * zetaCompletedExplicitFormulaPhi f (s - 1 / 2) := by
  exact completedZetaNegLogDeriv_eq_neg_logDeriv s ▸ rfl

/-- The zeta-side factorized contour integrand uses the finite zeta-side negative log derivative. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_eq_factorized_core
    (f : ZetaAdmissibleFunction) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Complex.Gammaℝ s ≠ 0) :
    zetaCompletedExplicitFormulaContourIntegrand f s =
      (zetaSideNegLogDeriv s +
          deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹) *
        zetaCompletedExplicitFormulaPhi f (s - 1 / 2) := by
  have hcoeff :
      completedZetaNegLogDeriv s =
        zetaSideNegLogDeriv s +
          deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ :=
    sub_eq_iff_eq_add.mp
      (zetaSideNegLogDeriv_eq_completed_sub_invGamma_correction hs0 hs1 hΛ hΓ).symm
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaContourIntegrand_eq f s)
      (congrArg
        (fun z : ℂ => z * zetaCompletedExplicitFormulaPhi f (s - 1 / 2))
        hcoeff)

/-- The contour integrand also rewrites through the finite zeta-side logarithmic derivative plus
the explicit Gamma correction. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_eq_factorized
    (f : ZetaAdmissibleFunction) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Complex.Gammaℝ s ≠ 0) :
    zetaCompletedExplicitFormulaContourIntegrand f s =
      (zetaSideNegLogDeriv s +
          deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹) *
        zetaCompletedExplicitFormulaPhi f (s - 1 / 2) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_eq_factorized_core f hs0 hs1 hΛ hΓ

/-- `completedRiemannZeta` is differentiable away from `0` and `1`. -/
theorem differentiableAt_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta s := by
  exact differentiableAt_completedZeta hs0 hs1

/-- The completed negative logarithmic derivative is antisymmetric under `s ↦ 1 - s`. -/
theorem deriv_completedRiemannZeta_one_sub
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv completedRiemannZeta (1 - s) =
      - deriv completedRiemannZeta s := by
  have hfun :
      deriv (fun z : ℂ => completedRiemannZeta (1 - z)) s =
        deriv completedRiemannZeta s :=
    Filter.EventuallyEq.deriv_eq
      (Eventually.of_forall
        (fun z => zetaCompletedExplicitFormula_completedRiemannZeta_one_sub z))
  have hchain :
      deriv (fun z : ℂ => completedRiemannZeta (1 - z)) s =
        - deriv completedRiemannZeta (1 - s) :=
    deriv_comp_const_sub completedRiemannZeta (1 : ℂ) s
  have hneg : - deriv completedRiemannZeta (1 - s) =
      deriv completedRiemannZeta s :=
    Eq.trans hchain.symm hfun
  exact neg_eq_iff_eq_neg.mp hneg

/-- A complex number is nonzero if its real part is nonzero. -/
theorem complex_ne_zero_of_re_ne_zero
    (z : ℂ) (h : z.re ≠ 0) :
    z ≠ 0 := by
  intro hz
  have hzre : z.re = 0 := by
    exact congrArg Complex.re hz
  exact h hzre

/-- The right path has positive real part. -/
theorem rightPath_re_pos_coord (r : ExplicitFormulaRectangle) (t : ℝ)
    (hc : (1 / 2 : ℝ) < r.c) :
    0 < (zetaCompletedExplicitFormulaRightPath r t).re := by
  exact rightPath_re_pos_core r t hc

/-- A complex number is not one if its real part is not `1` or its imaginary part is nonzero. -/
theorem complex_ne_one_of_re_ne_one_or_im_ne_zero
    (z : ℂ) (hre : z.re ≠ 1) (him : z.im ≠ 0) :
    z ≠ 1 := by
  intro hz
  have hre' : z.re = 1 := by
    exact congrArg Complex.re hz
  exact hre hre'

/-- A complex number is not one if its real part is not `1`. -/
theorem complex_ne_one_of_re_ne_one (z : ℂ) (hre : z.re ≠ 1) :
    z ≠ 1 := by
  intro hz
  have hre' : z.re = 1 := by
    exact congrArg Complex.re hz
  exact hre hre'

/-- The right path has nonzero real part, hence is not zero. -/
theorem rightPath_ne_zero_of_re_pos (r : ExplicitFormulaRectangle) (t : ℝ)
    (hc : (1 / 2 : ℝ) < r.c) :
    zetaCompletedExplicitFormulaRightPath r t ≠ 0 := by
  have hre_pos : 0 < (zetaCompletedExplicitFormulaRightPath r t).re :=
    rightPath_re_pos_core r t hc
  have hre_ne : (zetaCompletedExplicitFormulaRightPath r t).re ≠ 0 :=
    Ne.symm (ne_of_lt hre_pos)
  exact complex_ne_zero_of_re_ne_zero
    (zetaCompletedExplicitFormulaRightPath r t)
    hre_ne

/-- The rectangle right edge is strictly positive when `c > 1/2`. -/
theorem rightEdge_c_pos (r : ExplicitFormulaRectangle) (hc : (1 / 2 : ℝ) < r.c) :
    0 < r.c := by
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  exact lt_trans hhalf hc

/-- The left edge real part is strictly positive when `c < 1`. -/
theorem leftEdge_one_sub_c_pos (r : ExplicitFormulaRectangle) (hc : r.c < 1) :
    0 < 1 - r.c := by
  exact sub_pos.mpr hc

/-- The left edge real part is not `1` when `c > 1/2`. -/
theorem leftEdge_one_sub_c_ne_one (r : ExplicitFormulaRectangle) (hc : (1 / 2 : ℝ) < r.c) :
    1 - r.c ≠ 1 := by
  have hpos : 0 < r.c := rightEdge_c_pos r hc
  intro h
  exact (Ne.symm (ne_of_lt hpos)) (sub_eq_self.mp h)

/-- The left path has nonzero real part, hence is not zero. -/
theorem leftPath_ne_zero_of_re_pos (r : ExplicitFormulaRectangle) (t : ℝ)
    (hc : r.c < 1) :
    zetaCompletedExplicitFormulaLeftPath r t ≠ 0 := by
  have hre_pos : 0 < (zetaCompletedExplicitFormulaLeftPath r t).re :=
    leftPath_re_pos_core r t hc
  have hre_ne : (zetaCompletedExplicitFormulaLeftPath r t).re ≠ 0 :=
    Ne.symm (ne_of_lt hre_pos)
  exact complex_ne_zero_of_re_ne_zero
    (zetaCompletedExplicitFormulaLeftPath r t)
    hre_ne

/-- The left path has real part different from `1`. -/
theorem leftPath_re_ne_one (r : ExplicitFormulaRectangle) (t : ℝ)
    (hc : (1 / 2 : ℝ) < r.c) :
    (zetaCompletedExplicitFormulaLeftPath r t).re ≠ 1 := by
  have hre := zetaCompletedExplicitFormulaLeftPath_re r t
  exact hre ▸ leftEdge_one_sub_c_ne_one r hc

/-- The left path has positive real part. -/
theorem leftPath_re_pos_coord (r : ExplicitFormulaRectangle) (t : ℝ)
    (hc : r.c < 1) :
    0 < (zetaCompletedExplicitFormulaLeftPath r t).re := by
  exact leftPath_re_pos_core r t hc

/-- The top path has nonzero imaginary part when `T > 0`. -/
theorem topPath_im_ne_zero (r : ExplicitFormulaRectangle) (x : ℝ) (hT : 0 < r.T) :
    (zetaCompletedExplicitFormulaTopPath r x).im ≠ 0 := by
  have him : (zetaCompletedExplicitFormulaTopPath r x).im = r.T :=
    zetaCompletedExplicitFormulaTopPath_im r x
  exact him ▸ Ne.symm (ne_of_lt hT)

/-- The bottom path has nonzero imaginary part when `T > 0`. -/
theorem bottomPath_im_ne_zero (r : ExplicitFormulaRectangle) (x : ℝ) (hT : 0 < r.T) :
    (zetaCompletedExplicitFormulaBottomPath r x).im ≠ 0 := by
  have him : (zetaCompletedExplicitFormulaBottomPath r x).im = -r.T :=
    zetaCompletedExplicitFormulaBottomPath_im r x
  exact him ▸ neg_ne_zero.mpr (Ne.symm (ne_of_lt hT))

/-- The completed negative logarithmic derivative is antisymmetric under `s ↦ 1 - s`. -/
theorem completedZetaNegLogDeriv_one_sub_core (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) :
    completedZetaNegLogDeriv (1 - s) = - completedZetaNegLogDeriv s := by
  have hsym : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
    zetaCompletedExplicitFormula_completedRiemannZeta_one_sub s
  have hderiv :
      deriv completedRiemannZeta (1 - s) =
        - deriv completedRiemannZeta s :=
    deriv_completedRiemannZeta_one_sub s hs0 hs1
  have hnonzero : completedRiemannZeta (1 - s) ≠ 0 := by
    intro h
    exact hΛ (Eq.trans hsym.symm h)
  calc
    completedZetaNegLogDeriv (1 - s)
        = - deriv completedRiemannZeta (1 - s) / completedRiemannZeta (1 - s) := by
              rfl
    _ = - (- deriv completedRiemannZeta s) / completedRiemannZeta (1 - s) := by
      exact congrArg (fun z : ℂ => - z / completedRiemannZeta (1 - s)) hderiv
    _ = deriv completedRiemannZeta s / completedRiemannZeta s := by
      exact Eq.trans
        (congrArg (fun z : ℂ => - (- deriv completedRiemannZeta s) / z) hsym)
        (by rw [neg_neg])
    _ = - completedZetaNegLogDeriv s := by
      unfold completedZetaNegLogDeriv
      have hneg_div :
          - deriv completedRiemannZeta s / completedRiemannZeta s =
            - (deriv completedRiemannZeta s / completedRiemannZeta s) :=
        neg_div (completedRiemannZeta s) (deriv completedRiemannZeta s)
      have hneg_neg :
          - (- deriv completedRiemannZeta s / completedRiemannZeta s) =
            - (-(deriv completedRiemannZeta s / completedRiemannZeta s)) :=
        congrArg Neg.neg hneg_div
      exact (Eq.trans hneg_neg (neg_neg _)).symm

/-- The completed negative logarithmic derivative is antisymmetric under `s ↦ 1 - s`. -/
theorem completedZetaNegLogDeriv_one_sub (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) :
    completedZetaNegLogDeriv (1 - s) = - completedZetaNegLogDeriv s := by
  exact completedZetaNegLogDeriv_one_sub_core s hs0 hs1 hΛ

/-- The completed negative logarithmic derivative reflects across the left/right vertical paths. -/
theorem completedZetaNegLogDeriv_leftPath_eq_neg_rightPath_core
    (r : ExplicitFormulaRectangle) (t : ℝ)
    (hs0 : zetaCompletedExplicitFormulaRightPath r (-t) ≠ 0)
    (hs1 : zetaCompletedExplicitFormulaRightPath r (-t) ≠ 1)
    (hΛ : completedRiemannZeta (zetaCompletedExplicitFormulaRightPath r (-t)) ≠ 0) :
    completedZetaNegLogDeriv (zetaCompletedExplicitFormulaLeftPath r t) =
      - completedZetaNegLogDeriv (zetaCompletedExplicitFormulaRightPath r (-t)) := by
  exact Eq.trans
    (congrArg completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaLeftPath_eq_one_sub_rightPath r t))
    (completedZetaNegLogDeriv_one_sub_core (zetaCompletedExplicitFormulaRightPath r (-t))
      hs0 hs1 hΛ)

/-- The completed negative logarithmic derivative reflects across the left/right vertical paths. -/
theorem completedZetaNegLogDeriv_leftPath_eq_neg_rightPath
    (r : ExplicitFormulaRectangle) (t : ℝ)
    (hs0 : zetaCompletedExplicitFormulaRightPath r (-t) ≠ 0)
    (hs1 : zetaCompletedExplicitFormulaRightPath r (-t) ≠ 1)
    (hΛ : completedRiemannZeta (zetaCompletedExplicitFormulaRightPath r (-t)) ≠ 0) :
    completedZetaNegLogDeriv (zetaCompletedExplicitFormulaLeftPath r t) =
      - completedZetaNegLogDeriv (zetaCompletedExplicitFormulaRightPath r (-t)) := by
  exact completedZetaNegLogDeriv_leftPath_eq_neg_rightPath_core r t hs0 hs1 hΛ

/-- The completed negative logarithmic derivative reflects across the top/bottom horizontal paths. -/
theorem completedZetaNegLogDeriv_bottomPath_eq_neg_topPath_core
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hs0 : zetaCompletedExplicitFormulaTopPath r (1 - x) ≠ 0)
    (hs1 : zetaCompletedExplicitFormulaTopPath r (1 - x) ≠ 1)
    (hΛ : completedRiemannZeta (zetaCompletedExplicitFormulaTopPath r (1 - x)) ≠ 0) :
    completedZetaNegLogDeriv (zetaCompletedExplicitFormulaBottomPath r x) =
      - completedZetaNegLogDeriv (zetaCompletedExplicitFormulaTopPath r (1 - x)) := by
  exact Eq.trans
    (congrArg completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaBottomPath_eq_one_sub_topPath r x))
    (completedZetaNegLogDeriv_one_sub_core (zetaCompletedExplicitFormulaTopPath r (1 - x))
      hs0 hs1 hΛ)

/-- The completed negative logarithmic derivative reflects across the top/bottom horizontal paths. -/
theorem completedZetaNegLogDeriv_bottomPath_eq_neg_topPath
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hs0 : zetaCompletedExplicitFormulaTopPath r (1 - x) ≠ 0)
    (hs1 : zetaCompletedExplicitFormulaTopPath r (1 - x) ≠ 1)
    (hΛ : completedRiemannZeta (zetaCompletedExplicitFormulaTopPath r (1 - x)) ≠ 0) :
    completedZetaNegLogDeriv (zetaCompletedExplicitFormulaBottomPath r x) =
      - completedZetaNegLogDeriv (zetaCompletedExplicitFormulaTopPath r (1 - x)) := by
  exact completedZetaNegLogDeriv_bottomPath_eq_neg_topPath_core r x hs0 hs1 hΛ

/-- The factorized completed-zeta product is differentiable at a point away from `0` and `1`. -/
theorem differentiableAt_completedZeta_factorized
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΓ : Gammaℝ s ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹) s := by
  refine (differentiableAt_completedRiemannZeta hs0 hs1).mul ?_
  exact differentiable_Gammaℝ_inv.differentiableAt

/-- The factorized completed-zeta product is differentiable at any point away from `0` and `1`.
This is the owner lemma behind the path-specific differentiability wrappers. -/
theorem differentiableAt_completedZeta_factorized_at
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΓ : Gammaℝ s ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹) s := by
  exact differentiableAt_completedZeta_factorized hs0 hs1 hΓ

/-- The factorized completed-zeta product is differentiable on the right contour edge once the
point avoids the two pole locations. -/
theorem differentiableAt_completedZeta_factorized_rightPath
    (r : ExplicitFormulaRectangle) (t : ℝ) (hc : (1 / 2 : ℝ) < r.c)
    (hs0 : zetaCompletedExplicitFormulaRightPath r t ≠ 0)
    (hs1 : zetaCompletedExplicitFormulaRightPath r t ≠ 1) :
    DifferentiableAt ℂ
      (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹)
      (zetaCompletedExplicitFormulaRightPath r t) := by
  exact differentiableAt_completedZeta_factorized_at hs0 hs1
    (Gammaℝ_rightPath_ne_zero r t hc)

/-- The factorized completed-zeta product is differentiable on the left contour edge. -/
theorem differentiableAt_completedZeta_factorized_leftPath
    (r : ExplicitFormulaRectangle) (t : ℝ) (hc : r.c < 1)
    (hs0 : zetaCompletedExplicitFormulaLeftPath r t ≠ 0)
    (hs1 : zetaCompletedExplicitFormulaLeftPath r t ≠ 1) :
    DifferentiableAt ℂ
      (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹)
      (zetaCompletedExplicitFormulaLeftPath r t) := by
  exact differentiableAt_completedZeta_factorized_at hs0 hs1
    (Gammaℝ_leftPath_ne_zero r t hc)

/-- The factorized completed-zeta product is differentiable on the top contour edge. -/
theorem differentiableAt_completedZeta_factorized_topPath
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c)
    (hs0 : zetaCompletedExplicitFormulaTopPath r x ≠ 0)
    (hs1 : zetaCompletedExplicitFormulaTopPath r x ≠ 1)
    (hΓ : Gammaℝ (zetaCompletedExplicitFormulaTopPath r x) ≠ 0) :
    DifferentiableAt ℂ
      (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹)
      (zetaCompletedExplicitFormulaTopPath r x) := by
  exact differentiableAt_completedZeta_factorized_at hs0 hs1 hΓ

/-- The factorized completed-zeta product is differentiable on the bottom contour edge. -/
theorem differentiableAt_completedZeta_factorized_bottomPath
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c)
    (hs0 : zetaCompletedExplicitFormulaBottomPath r x ≠ 0)
    (hs1 : zetaCompletedExplicitFormulaBottomPath r x ≠ 1)
    (hΓ : Gammaℝ (zetaCompletedExplicitFormulaBottomPath r x) ≠ 0) :
    DifferentiableAt ℂ
      (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹)
      (zetaCompletedExplicitFormulaBottomPath r x) := by
  exact differentiableAt_completedZeta_factorized_at hs0 hs1 hΓ

/-- The spectral transform remains differentiable after shifting by `1/2`. -/
theorem zetaCompletedExplicitFormulaPhi_shift_differentiableAt
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f) (z : ℂ) :
    DifferentiableAt ℂ
      (fun w : ℂ => zetaCompletedExplicitFormulaPhi f (w - (1 / 2 : ℂ))) z := by
  have hsub : DifferentiableAt ℂ (fun w : ℂ => w - (1 / 2 : ℂ)) z := by
    exact differentiableAt_id.sub (differentiableAt_const (1 / 2 : ℂ))
  exact (hPhi.differentiableAt (z - (1 / 2 : ℂ))).comp z hsub

/-- The explicit-formula contour integrand is differentiable at any point once the zeta side and
the shifted transform side are differentiable there. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_differentiableAt_core
    {f : ZetaAdmissibleFunction} {z : ℂ}
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv z)
    (hΦ : DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaPhi f w)
      (z - (1 / 2 : ℂ))) :
    DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  unfold zetaCompletedExplicitFormulaContourIntegrand
  have hsub : DifferentiableAt ℂ (fun w : ℂ => w - (1 / 2 : ℂ)) z := by
    exact differentiableAt_id.sub (differentiableAt_const (1 / 2 : ℂ))
  have hshift :
      DifferentiableAt ℂ
        (fun w : ℂ => zetaCompletedExplicitFormulaPhi f (w - (1 / 2 : ℂ))) z := by
    exact hΦ.comp z hsub
  exact hZ.mul hshift

/-- The explicit-formula contour integrand is differentiable at any point once the zeta side and
the shifted transform side are differentiable there. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_differentiableAt
    {f : ZetaAdmissibleFunction} {z : ℂ}
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv z)
    (hΦ : DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaPhi f w)
      (z - (1 / 2 : ℂ))) :
    DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  exact zetaCompletedExplicitFormulaContourIntegrand_differentiableAt_core (f := f) hZ hΦ

/-- The contour integrand norm is bounded by the product of the log-derivative and `Φ_f` norms. -/
theorem norm_zetaCompletedExplicitFormulaContourIntegrand_le_core
    (f : ZetaAdmissibleFunction) (s : ℂ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f s‖
      ≤ ‖completedZetaNegLogDeriv s‖ * ‖zetaCompletedExplicitFormulaPhi f (s - 1 / 2)‖ := by
  unfold zetaCompletedExplicitFormulaContourIntegrand
  exact norm_mul_le _ _

/-- The contour integrand norm is bounded by the product of the log-derivative and `Φ_f` norms. -/
theorem norm_zetaCompletedExplicitFormulaContourIntegrand_le
    (f : ZetaAdmissibleFunction) (s : ℂ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f s‖
      ≤ ‖completedZetaNegLogDeriv s‖ * ‖zetaCompletedExplicitFormulaPhi f (s - 1 / 2)‖ := by
  exact norm_zetaCompletedExplicitFormulaContourIntegrand_le_core f s

/-- The contour integrand norm is bounded by the product estimate in the factorized form. -/
theorem norm_zetaCompletedExplicitFormulaContourIntegrand_factorized_le
    (f : ZetaAdmissibleFunction) (s : ℂ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f s‖
      ≤ ‖completedZetaNegLogDeriv s‖ * ‖zetaCompletedExplicitFormulaPhi f (s - 1 / 2)‖ := by
  exact norm_zetaCompletedExplicitFormulaContourIntegrand_le f s

/-- The explicit-formula contour integrand is differentiable along the right edge whenever the
factorized zeta side and the transform side are differentiable there. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_differentiableAt_rightPath
    {f : ZetaAdmissibleFunction} (r : ExplicitFormulaRectangle) (t : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaRightPath r t))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaRightPath r t - (1 / 2 : ℂ))) :
    DifferentiableAt ℂ (fun z : ℂ =>
      zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaRightPath r t) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_differentiableAt (f := f) hZ hΦ

/-- The explicit-formula contour integrand is differentiable along the left edge. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_differentiableAt_leftPath
    {f : ZetaAdmissibleFunction} (r : ExplicitFormulaRectangle) (t : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaLeftPath r t))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaLeftPath r t - (1 / 2 : ℂ))) :
    DifferentiableAt ℂ (fun z : ℂ =>
      zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaLeftPath r t) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_differentiableAt (f := f) hZ hΦ

/-- The explicit-formula contour integrand is differentiable along the top edge. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_differentiableAt_topPath
    {f : ZetaAdmissibleFunction} (r : ExplicitFormulaRectangle) (x : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaTopPath r x))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaTopPath r x - (1 / 2 : ℂ))) :
    DifferentiableAt ℂ (fun z : ℂ =>
      zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaTopPath r x) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_differentiableAt (f := f) hZ hΦ

/-- The explicit-formula contour integrand is differentiable along the bottom edge. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_differentiableAt_bottomPath
    {f : ZetaAdmissibleFunction} (r : ExplicitFormulaRectangle) (x : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaBottomPath r x))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaBottomPath r x - (1 / 2 : ℂ))) :
    DifferentiableAt ℂ (fun z : ℂ =>
      zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaBottomPath r x) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_differentiableAt (f := f) hZ hΦ

/-- The explicit-formula contour integrand is continuous along the right edge. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_continuousAt_rightPath
    {f : ZetaAdmissibleFunction} (r : ExplicitFormulaRectangle) (t : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaRightPath r t))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaRightPath r t - (1 / 2 : ℂ))) :
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaRightPath r t) := by
  exact (zetaCompletedExplicitFormulaContourIntegrand_differentiableAt_rightPath
      (f := f) r t hZ hΦ).continuousAt

/-- The explicit-formula contour integrand is continuous along the left edge. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_continuousAt_leftPath'
    {f : ZetaAdmissibleFunction} (r : ExplicitFormulaRectangle) (t : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaLeftPath r t))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaLeftPath r t - (1 / 2 : ℂ))) :
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaLeftPath r t) := by
  exact (zetaCompletedExplicitFormulaContourIntegrand_differentiableAt_leftPath
      (f := f) r t hZ hΦ).continuousAt

/-- The explicit-formula contour integrand is continuous along the left edge. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_continuousAt_leftPath
    {f : ZetaAdmissibleFunction} (r : ExplicitFormulaRectangle) (t : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaLeftPath r t))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaLeftPath r t - (1 / 2 : ℂ))) :
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaLeftPath r t) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_continuousAt_leftPath'
      (f := f) r t hZ hΦ

/-- The explicit-formula contour integrand is continuous along the top edge. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_continuousAt_topPath'
    {f : ZetaAdmissibleFunction} (r : ExplicitFormulaRectangle) (x : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaTopPath r x))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaTopPath r x - (1 / 2 : ℂ))) :
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaTopPath r x) := by
  exact (zetaCompletedExplicitFormulaContourIntegrand_differentiableAt_topPath
      (f := f) r x hZ hΦ).continuousAt

/-- The explicit-formula contour integrand is continuous along the top edge. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_continuousAt_topPath
    {f : ZetaAdmissibleFunction} (r : ExplicitFormulaRectangle) (x : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaTopPath r x))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaTopPath r x - (1 / 2 : ℂ))) :
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaTopPath r x) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_continuousAt_topPath'
      (f := f) r x hZ hΦ

/-- The explicit-formula contour integrand is continuous along the bottom edge. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_continuousAt_bottomPath'
    {f : ZetaAdmissibleFunction} (r : ExplicitFormulaRectangle) (x : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaBottomPath r x))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaBottomPath r x - (1 / 2 : ℂ))) :
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaBottomPath r x) := by
  exact (zetaCompletedExplicitFormulaContourIntegrand_differentiableAt_bottomPath
      (f := f) r x hZ hΦ).continuousAt

/-- The explicit-formula contour integrand is continuous along the bottom edge. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_continuousAt_bottomPath
    {f : ZetaAdmissibleFunction} (r : ExplicitFormulaRectangle) (x : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaBottomPath r x))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaBottomPath r x - (1 / 2 : ℂ))) :
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaBottomPath r x) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_continuousAt_bottomPath'
      (f := f) r x hZ hΦ

/-- The completed zeta negative logarithmic derivative is complex differentiable away from `0`,
`1`, and the nontrivial zeros. -/
theorem differentiableAt_completedRiemannZeta_on_puncturedPlane
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta z := by
  exact differentiableAt_completedRiemannZeta hz0 hz1

/-- The derivative of `completedRiemannZeta` is differentiable at points away from `0` and `1`. -/
theorem differentiableAt_deriv_completedRiemannZeta
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    DifferentiableAt ℂ (deriv completedRiemannZeta) z := by
  have hU : AnalyticOnNhd ℂ completedRiemannZeta {w : ℂ | w ≠ 0 ∧ w ≠ 1} := by
    intro w hw
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [eventually_ne_nhds hw.1, eventually_ne_nhds hw.2] with y hy0 hy1
    exact differentiableAt_completedRiemannZeta_on_puncturedPlane hy0 hy1
  exact (hU.deriv z ⟨hz0, hz1⟩).differentiableAt

/-- The quotient defining the completed negative logarithmic derivative is differentiable away
from the zeros of `completedRiemannZeta`. -/
theorem differentiableAt_completedZetaNegLogDeriv_divided
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : completedRiemannZeta z ≠ 0) :
    DifferentiableAt ℂ
      (fun w : ℂ => deriv completedRiemannZeta w / completedRiemannZeta w) z := by
  have hf : DifferentiableAt ℂ completedRiemannZeta z :=
    differentiableAt_completedRiemannZeta_on_puncturedPlane hz0 hz1
  have hderiv : DifferentiableAt ℂ (deriv completedRiemannZeta) z :=
    differentiableAt_deriv_completedRiemannZeta hz0 hz1
  exact hderiv.div hf hz

theorem differentiableAt_completedZetaNegLogDeriv_core
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : completedRiemannZeta z ≠ 0) :
    DifferentiableAt ℂ completedZetaNegLogDeriv z := by
  have hquot :
      DifferentiableAt ℂ
        (fun w : ℂ => deriv completedRiemannZeta w / completedRiemannZeta w) z :=
    differentiableAt_completedZetaNegLogDeriv_divided hz0 hz1 hz
  have hneg :
      DifferentiableAt ℂ
        (fun w : ℂ => - deriv completedRiemannZeta w / completedRiemannZeta w) z :=
    (differentiableAt_deriv_completedRiemannZeta hz0 hz1).neg.div
      (differentiableAt_completedRiemannZeta_on_puncturedPlane hz0 hz1) hz
  change DifferentiableAt ℂ
    (fun w : ℂ => - deriv completedRiemannZeta w / completedRiemannZeta w) z
  exact hneg

/-- The completed zeta negative logarithmic derivative is complex differentiable away from `0`,
`1`, and the nontrivial zeros. -/
theorem differentiableAt_completedZetaNegLogDeriv
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : completedRiemannZeta z ≠ 0) :
    DifferentiableAt ℂ completedZetaNegLogDeriv z := by
  exact differentiableAt_completedZetaNegLogDeriv_core hz0 hz1 hz

/-- The contour integrand is complex differentiable away from the singular set. -/
theorem differentiableAt_zetaCompletedExplicitFormulaContourIntegrand_core
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : completedRiemannZeta z ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  unfold zetaCompletedExplicitFormulaContourIntegrand
  have hZ : DifferentiableAt ℂ completedZetaNegLogDeriv z :=
    differentiableAt_completedZetaNegLogDeriv hz0 hz1 hz
  have hshift :
      DifferentiableAt ℂ
        (fun w : ℂ => zetaCompletedExplicitFormulaPhi f (w - (1 / 2 : ℂ))) z :=
    zetaCompletedExplicitFormulaPhi_shift_differentiableAt (f := f) hPhi z
  exact hZ.mul hshift

/-- The contour integrand is complex differentiable away from the singular set. -/
theorem differentiableAt_zetaCompletedExplicitFormulaContourIntegrand
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : completedRiemannZeta z ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  exact differentiableAt_zetaCompletedExplicitFormulaContourIntegrand_core (f := f) hPhi hz0 hz1 hz

/-- The singular set for the contour integrand is countable. -/
theorem contourIntegrand_singularSet_countable_core :
    ({z : ℂ | z = 0 ∨ z = 1 ∨ (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0)} : Set ℂ).Countable := by
  have h0 : ({z : ℂ | z = 0} : Set ℂ).Countable := by
    exact Set.countable_singleton (0 : ℂ)
  have h1 : ({z : ℂ | z = 1} : Set ℂ).Countable := by
    exact Set.countable_singleton (1 : ℂ)
  have h01 : ({z : ℂ | z = 0 ∨ z = 1} : Set ℂ).Countable := by
    exact h0.union h1
  have hz : ({z : ℂ | z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0} : Set ℂ).Countable := by
    exact completedRiemannZeta_nontrivialZeroSet_countable
  have hsum :
      ({z : ℂ | z = 0 ∨ z = 1} : Set ℂ).Countable ∧
      ({z : ℂ | z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0} : Set ℂ).Countable := by
    exact ⟨h01, hz⟩
  have hunion : ({z : ℂ | z = 0 ∨ z = 1} ∪ {z : ℂ | z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0} : Set ℂ).Countable :=
    hsum.1.union hsum.2
  have hsubset :
      ({z : ℂ | z = 0 ∨ z = 1 ∨ (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0)} : Set ℂ) =
        ({z : ℂ | z = 0 ∨ z = 1} ∪ {z : ℂ | z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0} : Set ℂ) := by
    ext z
    constructor
    · intro hz
      rcases hz with hz | hz | hz
      · exact Or.inl (Or.inl hz)
      · exact Or.inl (Or.inr hz)
      · exact Or.inr hz
    · intro hz
      rcases hz with hz | hz
      · rcases hz with hz | hz
        · exact Or.inl hz
        · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr hz)
  exact hsubset ▸ hunion

/-- The singular set for the contour integrand is countable. -/
theorem contourIntegrand_singularSet_countable :
    ({z : ℂ | z = 0 ∨ z = 1 ∨ (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0)} : Set ℂ).Countable := by
  exact contourIntegrand_singularSet_countable_core

/-- Away from the singular set, the contour integrand is complex differentiable. -/
theorem contourIntegrand_differentiableAt_off_singularSet
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  exact differentiableAt_zetaCompletedExplicitFormulaContourIntegrand hPhi hz.1 hz.2.1 hz.2.2

/-- The contour integrand is differentiable off its countable singular set. -/
theorem contourIntegrand_differentiableAt_off_countable_core_hz0
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ}
    (hz : z ∉ ({w : ℂ | w = 0 ∨ w = 1 ∨ (w ≠ 0 ∧ w ≠ 1 ∧ completedRiemannZeta w = 0)} : Set ℂ)) :
    z ≠ 0 := by
  intro h
  exact hz (Or.inl h)

/-- The contour integrand is differentiable off its countable singular set. -/
theorem contourIntegrand_differentiableAt_off_countable_core_hz1
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ}
    (hz : z ∉ ({w : ℂ | w = 0 ∨ w = 1 ∨ (w ≠ 0 ∧ w ≠ 1 ∧ completedRiemannZeta w = 0)} : Set ℂ)) :
    z ≠ 1 := by
  intro h
  exact hz (Or.inr <| Or.inl h)

/-- The contour integrand is differentiable off its countable singular set. -/
theorem contourIntegrand_differentiableAt_off_countable_core_hzΛ
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ}
    (hz : z ∉ ({w : ℂ | w = 0 ∨ w = 1 ∨ (w ≠ 0 ∧ w ≠ 1 ∧ completedRiemannZeta w = 0)} : Set ℂ)) :
    completedRiemannZeta z ≠ 0 := by
  have hz0 : z ≠ 0 := contourIntegrand_differentiableAt_off_countable_core_hz0 (f := f) hPhi hz
  have hz1 : z ≠ 1 := contourIntegrand_differentiableAt_off_countable_core_hz1 (f := f) hPhi hz
  intro h
  exact hz (Or.inr <| Or.inr ⟨hz0, hz1, h⟩)

/-- The contour integrand is differentiable off its countable singular set. -/
theorem contourIntegrand_differentiableAt_off_countable
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ}
    (hz : z ∉ ({w : ℂ | w = 0 ∨ w = 1 ∨ (w ≠ 0 ∧ w ≠ 1 ∧ completedRiemannZeta w = 0)} : Set ℂ)) :
    DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  have hz0 : z ≠ 0 := contourIntegrand_differentiableAt_off_countable_core_hz0 (f := f) hPhi hz
  have hz1 : z ≠ 1 := contourIntegrand_differentiableAt_off_countable_core_hz1 (f := f) hPhi hz
  have hzΛ : completedRiemannZeta z ≠ 0 :=
    contourIntegrand_differentiableAt_off_countable_core_hzΛ (f := f) hPhi hz
  exact differentiableAt_zetaCompletedExplicitFormulaContourIntegrand hPhi hz0 hz1 hzΛ

/-- The completed contour integrand is the contour integrand on the right side. -/
theorem zetaCompletedExplicitFormulaRightBoundary_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (t : ℝ) :
    zetaCompletedExplicitFormulaRightBoundary f r t =
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaRightPath r t) := by
  rfl

/-- The completed contour integrand is the contour integrand on the left side. -/
theorem zetaCompletedExplicitFormulaLeftBoundary_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftBoundary f r t =
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaLeftPath r t) := by
  rfl

/-- The completed contour integrand is the contour integrand on the top side. -/
theorem zetaCompletedExplicitFormulaHorizontalBoundaryTop_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (x : ℝ) :
    zetaCompletedExplicitFormulaHorizontalBoundaryTop f r x =
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath r x) := by
  rfl

/-- The completed contour integrand is the contour integrand on the bottom side. -/
theorem zetaCompletedExplicitFormulaHorizontalBoundaryBottom_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (x : ℝ) :
    zetaCompletedExplicitFormulaHorizontalBoundaryBottom f r x =
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath r x) := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
