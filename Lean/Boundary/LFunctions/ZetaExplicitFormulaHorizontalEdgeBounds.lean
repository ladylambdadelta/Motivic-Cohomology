import Boundary.LFunctions.ZetaExplicitFormulaContour
import Boundary.LFunctions.ZetaExplicitFormulaContourBounds
import Boundary.LFunctions.ZetaAdmissibleTransformRegularity
import Boundary.LFunctions.ZetaCompletedLogDerivativeControl
import Mathlib.Order.Filter.Basic

/-!
# Boundary explicit-formula horizontal edge bounds

This file owns the pointwise horizontal-edge estimates for the completed-zeta
explicit-formula contour.  It sits below the complex-analysis wrapper layer:
the wrapper layer should consume these named edge estimates rather than repeat
the strip, shift, and product-bound reasoning.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The top horizontal path has imaginary norm `‖T‖`. -/
theorem zetaCompletedExplicitFormulaTopPath_im_norm
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    ‖(zetaCompletedExplicitFormulaTopPath r x).im‖ = ‖r.T‖ :=
  congrArg norm (zetaCompletedExplicitFormulaTopPath_im r x)

/-- The bottom horizontal path has imaginary norm `‖T‖`. -/
theorem zetaCompletedExplicitFormulaBottomPath_im_norm
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    ‖(zetaCompletedExplicitFormulaBottomPath r x).im‖ = ‖r.T‖ :=
  Eq.trans
    (congrArg norm (zetaCompletedExplicitFormulaBottomPath_im r x))
    (norm_neg r.T)

/-- The complex number `1 / 2` has imaginary part zero. -/
theorem complex_half_im :
    ((1 / 2 : ℂ).im) = 0 :=
  Eq.trans
    (congrArg Complex.im complex_half_eq_ofReal_half)
    (Complex.ofReal_im (1 / 2 : ℝ))

/-- Removing `1 / 2` from the top path preserves its imaginary part. -/
theorem zetaCompletedExplicitFormulaTopPath_shift_im
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).im =
      (zetaCompletedExplicitFormulaTopPath r x).im :=
  Eq.trans
    (Complex.sub_im (zetaCompletedExplicitFormulaTopPath r x) (1 / 2 : ℂ))
    (Eq.trans
      (congrArg
        (fun u : ℝ => (zetaCompletedExplicitFormulaTopPath r x).im - u)
        complex_half_im)
      (sub_zero (zetaCompletedExplicitFormulaTopPath r x).im))

/-- Removing `1 / 2` from the top path preserves its imaginary norm. -/
theorem zetaCompletedExplicitFormulaTopPath_shift_im_norm
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    ‖(zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).im‖ = ‖r.T‖ :=
  Eq.trans
    (congrArg norm (zetaCompletedExplicitFormulaTopPath_shift_im r x))
    (zetaCompletedExplicitFormulaTopPath_im_norm r x)

/-- Removing `1 / 2` from the bottom path preserves its imaginary part. -/
theorem zetaCompletedExplicitFormulaBottomPath_shift_im
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2 : ℂ).im =
      (zetaCompletedExplicitFormulaBottomPath r x).im :=
  Eq.trans
    (Complex.sub_im (zetaCompletedExplicitFormulaBottomPath r x) (1 / 2 : ℂ))
    (Eq.trans
      (congrArg
        (fun u : ℝ => (zetaCompletedExplicitFormulaBottomPath r x).im - u)
        complex_half_im)
      (sub_zero (zetaCompletedExplicitFormulaBottomPath r x).im))

/-- Removing `1 / 2` from the bottom path preserves its imaginary norm. -/
theorem zetaCompletedExplicitFormulaBottomPath_shift_im_norm
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    ‖(zetaCompletedExplicitFormulaBottomPath r x - 1 / 2 : ℂ).im‖ = ‖r.T‖ :=
  Eq.trans
    (congrArg norm (zetaCompletedExplicitFormulaBottomPath_shift_im r x))
    (zetaCompletedExplicitFormulaBottomPath_im_norm r x)

/-- The function `1 + ‖t‖` is positive. -/
theorem one_add_norm_pos (t : ℝ) :
    0 < 1 + ‖t‖ :=
  add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg t)

/-- A positive strip constant times a negative power is nonnegative. -/
theorem stripConstant_mul_zpow_nonneg {C t : ℝ} {N : ℕ} (hC : 0 < C) :
    0 ≤ C * (1 + ‖t‖) ^ (-(N : ℤ)) :=
  le_of_lt (mul_pos hC (zpow_pos (one_add_norm_pos t) (-(N : ℤ))))

/-- A positive strip constant times a natural power is nonnegative. -/
theorem stripConstant_mul_pow_nonneg {C t : ℝ} {N : ℕ} (hC : 0 < C) :
    0 ≤ C * (1 + ‖t‖) ^ N :=
  mul_nonneg (le_of_lt hC) (pow_nonneg (le_of_lt (one_add_norm_pos t)) N)

/-- Two pointwise bounds multiply to a product bound. -/
theorem norm_product_le_of_bounds
    {a b A B : ℝ} (ha : a ≤ A) (hb : b ≤ B) (hA : 0 ≤ A) (hb0 : 0 ≤ b) :
    a * b ≤ A * B :=
  mul_le_mul ha hb hb0 hA

/-- The logarithmic-derivative strip bound after substituting the horizontal height `T`. -/
theorem completedZetaNegLogDeriv_horizontal_height_bound
    {f : ZetaAdmissibleFunction} (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (z : ℂ) (N : ℕ)
    (hpath : r.c ≤ z.re ∧ z.re ≤ 1 - r.c)
    (hpath_im : ‖z.im‖ = ‖r.T‖) :
    ‖completedZetaNegLogDeriv z‖ ≤
      hLog.stripBoundConstant r.c (1 - r.c) N * (1 + ‖r.T‖) ^ N :=
  (hLog.stripBoundConstant_bound r.c (1 - r.c) N z hpath.1 hpath.2).trans_eq
    (congrArg
      (fun u : ℝ =>
        hLog.stripBoundConstant r.c (1 - r.c) N * (1 + u) ^ N)
      hpath_im)

/-- The `Φ_f` strip bound after substituting the shifted horizontal height `T`. -/
theorem zetaCompletedExplicitFormulaPhi_horizontal_height_bound
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (r : ExplicitFormulaRectangle) (z : ℂ) (N : ℕ)
    (hshift :
      (r.c - 1 / 2) ≤ (z - 1 / 2 : ℂ).re ∧
        (z - 1 / 2 : ℂ).re ≤ (1 / 2 - r.c))
    (hshift_im : ‖(z - 1 / 2 : ℂ).im‖ = ‖r.T‖) :
    ‖zetaCompletedExplicitFormulaPhi f (z - 1 / 2)‖ ≤
      hPhi.verticalStripRapidDecayConstant (r.c - 1 / 2) (1 / 2 - r.c) N *
        (1 + ‖r.T‖) ^ (-(N : ℤ)) :=
  (hPhi.verticalStripRapidDecayConstant_bound
    (r.c - 1 / 2) (1 / 2 - r.c) N (z - 1 / 2) hshift.1 hshift.2).trans_eq
    (congrArg
      (fun u : ℝ =>
        hPhi.verticalStripRapidDecayConstant (r.c - 1 / 2) (1 / 2 - r.c) N *
          (1 + u) ^ (-(N : ℤ)))
      hshift_im)

/-- The logarithmic-derivative horizontal target bound is nonnegative. -/
theorem completedZetaNegLogDeriv_horizontal_target_nonneg
    {f : ZetaAdmissibleFunction} (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (N : ℕ) :
    0 ≤ hLog.stripBoundConstant r.c (1 - r.c) N *
      (1 + ‖r.T‖) ^ N :=
  stripConstant_mul_pow_nonneg
    (hLog.stripBoundConstant_pos r.c (1 - r.c) N)

/-- The common horizontal edge product constant. -/
def horizontalEdgeIntegrandBoundConstant
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (N : ℕ) : ℝ :=
  (hLog.stripBoundConstant r.c (1 - r.c) N) *
    (1 + ‖r.T‖) ^ N *
    (hPhi.verticalStripRapidDecayConstant (r.c - 1 / 2) (1 / 2 - r.c) N) *
    (1 + ‖r.T‖) ^ (-(N : ℤ))

/-- The horizontal product estimate before reassociating the right-hand side. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_horizontalProduct_bound
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (z : ℂ) (N : ℕ)
    (hpath : r.c ≤ z.re ∧ z.re ≤ 1 - r.c)
    (hshift : (r.c - 1 / 2) ≤ (z - 1 / 2 : ℂ).re ∧
      (z - 1 / 2 : ℂ).re ≤ (1 / 2 - r.c))
    (hpath_im : ‖z.im‖ = ‖r.T‖)
    (hshift_im : ‖(z - 1 / 2 : ℂ).im‖ = ‖r.T‖) :
    ‖completedZetaNegLogDeriv z‖ *
        ‖zetaCompletedExplicitFormulaPhi f (z - 1 / 2)‖
      ≤ (hLog.stripBoundConstant r.c (1 - r.c) N *
            (1 + ‖r.T‖) ^ N) *
          (hPhi.verticalStripRapidDecayConstant (r.c - 1 / 2) (1 / 2 - r.c) N *
            (1 + ‖r.T‖) ^ (-(N : ℤ))) :=
  norm_product_le_of_bounds
    (completedZetaNegLogDeriv_horizontal_height_bound hLog r z N hpath hpath_im)
    (zetaCompletedExplicitFormulaPhi_horizontal_height_bound hPhi r z N hshift hshift_im)
    (completedZetaNegLogDeriv_horizontal_target_nonneg hLog r N)
    (norm_nonneg (zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))

/-- Reassociate the horizontal product target into the public edge-bound shape. -/
theorem horizontalProductTarget_reassociate
    (A B C D : ℝ) :
    A * B * (C * D) = A * B * C * D :=
  (mul_assoc (A * B) C D).symm

/-- The horizontal product estimate in the public edge-bound parenthesization. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_horizontalProduct_bound'
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (z : ℂ) (N : ℕ)
    (hpath : r.c ≤ z.re ∧ z.re ≤ 1 - r.c)
    (hshift : (r.c - 1 / 2) ≤ (z - 1 / 2 : ℂ).re ∧
      (z - 1 / 2 : ℂ).re ≤ (1 / 2 - r.c))
    (hpath_im : ‖z.im‖ = ‖r.T‖)
    (hshift_im : ‖(z - 1 / 2 : ℂ).im‖ = ‖r.T‖) :
    ‖completedZetaNegLogDeriv z‖ *
        ‖zetaCompletedExplicitFormulaPhi f (z - 1 / 2)‖
      ≤ (hLog.stripBoundConstant r.c (1 - r.c) N) *
          (1 + ‖r.T‖) ^ N *
          (hPhi.verticalStripRapidDecayConstant (r.c - 1 / 2) (1 / 2 - r.c) N) *
          (1 + ‖r.T‖) ^ (-(N : ℤ)) :=
  (zetaCompletedExplicitFormulaContourIntegrand_horizontalProduct_bound
    hPhi hLog r z N hpath hshift hpath_im hshift_im).trans_eq
    (horizontalProductTarget_reassociate
      (hLog.stripBoundConstant r.c (1 - r.c) N)
      ((1 + ‖r.T‖) ^ N)
      (hPhi.verticalStripRapidDecayConstant (r.c - 1 / 2) (1 / 2 - r.c) N)
      ((1 + ‖r.T‖) ^ (-(N : ℤ))))

/-- The shifted top path remains inside the vertical strip needed for `Φ_f`. -/
theorem zetaCompletedExplicitFormulaTopPath_shift_strip
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    (r.c - 1 / 2) ≤ (zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).re ∧
      (zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).re ≤ (1 / 2 - r.c) :=
  zetaCompletedExplicitFormulaTopPath_shift_strip' r x hx1 hx2

/-- The shifted bottom path remains inside the vertical strip needed for `Φ_f`. -/
theorem zetaCompletedExplicitFormulaBottomPath_shift_strip
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    (r.c - 1 / 2) ≤ (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2 : ℂ).re ∧
      (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2 : ℂ).re ≤ (1 / 2 - r.c) :=
  zetaCompletedExplicitFormulaBottomPath_shift_strip' r x hx1 hx2

/-- The top path real part lies in the unordered horizontal interval. -/
theorem zetaCompletedExplicitFormulaTopPath_re_mem_uIcc_bounds
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx : x ∈ Set.uIcc r.c (1 - r.c)) :
    min r.c (1 - r.c) ≤ (zetaCompletedExplicitFormulaTopPath r x).re ∧
      (zetaCompletedExplicitFormulaTopPath r x).re ≤ max r.c (1 - r.c) :=
  ⟨Eq.subst
      (motive := fun y : ℝ => min r.c (1 - r.c) ≤ y)
      (zetaCompletedExplicitFormulaTopPath_re_eq r x).symm
      hx.1,
    Eq.subst
      (motive := fun y : ℝ => y ≤ max r.c (1 - r.c))
      (zetaCompletedExplicitFormulaTopPath_re_eq r x).symm
      hx.2⟩

/-- The bottom path real part lies in the unordered horizontal interval. -/
theorem zetaCompletedExplicitFormulaBottomPath_re_mem_uIcc_bounds
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx : x ∈ Set.uIcc r.c (1 - r.c)) :
    min r.c (1 - r.c) ≤ (zetaCompletedExplicitFormulaBottomPath r x).re ∧
      (zetaCompletedExplicitFormulaBottomPath r x).re ≤ max r.c (1 - r.c) :=
  ⟨Eq.subst
      (motive := fun y : ℝ => min r.c (1 - r.c) ≤ y)
      (zetaCompletedExplicitFormulaBottomPath_re_eq r x).symm
      hx.1,
    Eq.subst
      (motive := fun y : ℝ => y ≤ max r.c (1 - r.c))
      (zetaCompletedExplicitFormulaBottomPath_re_eq r x).symm
      hx.2⟩

/-- The shifted top path real part lies in the shifted unordered horizontal interval. -/
theorem zetaCompletedExplicitFormulaTopPath_shift_re_mem_uIcc_bounds
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx : x ∈ Set.uIcc r.c (1 - r.c)) :
    min r.c (1 - r.c) - 1 / 2 ≤
        (zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).re ∧
      (zetaCompletedExplicitFormulaTopPath r x - 1 / 2 : ℂ).re ≤
        max r.c (1 - r.c) - 1 / 2 :=
  ⟨Eq.subst
      (motive := fun y : ℝ => min r.c (1 - r.c) - 1 / 2 ≤ y)
      (zetaCompletedExplicitFormulaTopPath_shift_re r x).symm
      (sub_le_sub_right hx.1 (1 / 2 : ℝ)),
    Eq.subst
      (motive := fun y : ℝ => y ≤ max r.c (1 - r.c) - 1 / 2)
      (zetaCompletedExplicitFormulaTopPath_shift_re r x).symm
      (sub_le_sub_right hx.2 (1 / 2 : ℝ))⟩

/-- The shifted bottom path real part lies in the shifted unordered horizontal interval. -/
theorem zetaCompletedExplicitFormulaBottomPath_shift_re_mem_uIcc_bounds
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx : x ∈ Set.uIcc r.c (1 - r.c)) :
    min r.c (1 - r.c) - 1 / 2 ≤
        (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2 : ℂ).re ∧
      (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2 : ℂ).re ≤
        max r.c (1 - r.c) - 1 / 2 :=
  ⟨Eq.subst
      (motive := fun y : ℝ => min r.c (1 - r.c) - 1 / 2 ≤ y)
      (zetaCompletedExplicitFormulaBottomPath_shift_re r x).symm
      (sub_le_sub_right hx.1 (1 / 2 : ℝ)),
    Eq.subst
      (motive := fun y : ℝ => y ≤ max r.c (1 - r.c) - 1 / 2)
      (zetaCompletedExplicitFormulaBottomPath_shift_re r x).symm
      (sub_le_sub_right hx.2 (1 / 2 : ℝ))⟩

/-- The common unordered horizontal edge product constant. -/
def horizontalUnorderedEdgeIntegrandBoundConstant
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (N : ℕ) : ℝ :=
  (hLog.stripBoundConstant (min r.c (1 - r.c)) (max r.c (1 - r.c)) N) *
    (1 + ‖r.T‖) ^ N *
    (hPhi.verticalStripRapidDecayConstant
      (min r.c (1 - r.c) - 1 / 2) (max r.c (1 - r.c) - 1 / 2) N) *
    (1 + ‖r.T‖) ^ (-(N : ℤ))

/-- The logarithmic-derivative strip bound with a supplied horizontal height. -/
theorem completedZetaNegLogDeriv_strip_height_bound
    {f : ZetaAdmissibleFunction} (hLog : CompletedZetaNegLogDerivControl f)
    (a b t : ℝ) (z : ℂ) (N : ℕ)
    (hpath : a ≤ z.re ∧ z.re ≤ b)
    (hpath_im : ‖z.im‖ = ‖t‖) :
    ‖completedZetaNegLogDeriv z‖ ≤
      hLog.stripBoundConstant a b N * (1 + ‖t‖) ^ N :=
  (hLog.stripBoundConstant_bound a b N z hpath.1 hpath.2).trans_eq
    (congrArg
      (fun u : ℝ =>
        hLog.stripBoundConstant a b N * (1 + u) ^ N)
      hpath_im)

/-- The transform strip bound with a supplied horizontal height. -/
theorem zetaCompletedExplicitFormulaPhi_strip_height_bound
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (a b t : ℝ) (z : ℂ) (N : ℕ)
    (hshift : a ≤ (z - 1 / 2 : ℂ).re ∧ (z - 1 / 2 : ℂ).re ≤ b)
    (hshift_im : ‖(z - 1 / 2 : ℂ).im‖ = ‖t‖) :
    ‖zetaCompletedExplicitFormulaPhi f (z - 1 / 2)‖ ≤
      hPhi.verticalStripRapidDecayConstant a b N * (1 + ‖t‖) ^ (-(N : ℤ)) :=
  (hPhi.verticalStripRapidDecayConstant_bound
    a b N (z - 1 / 2) hshift.1 hshift.2).trans_eq
    (congrArg
      (fun u : ℝ =>
        hPhi.verticalStripRapidDecayConstant a b N * (1 + u) ^ (-(N : ℤ)))
      hshift_im)

/-- The logarithmic-derivative strip-height target is nonnegative. -/
theorem completedZetaNegLogDeriv_strip_height_target_nonneg
    {f : ZetaAdmissibleFunction} (hLog : CompletedZetaNegLogDerivControl f)
    (a b t : ℝ) (N : ℕ) :
    0 ≤ hLog.stripBoundConstant a b N * (1 + ‖t‖) ^ N :=
  stripConstant_mul_pow_nonneg
    (hLog.stripBoundConstant_pos a b N)

/-- The product estimate for arbitrary log-derivative and transform strips. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_stripProduct_bound
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (a b aΦ bΦ t : ℝ) (z : ℂ) (N : ℕ)
    (hpath : a ≤ z.re ∧ z.re ≤ b)
    (hshift : aΦ ≤ (z - 1 / 2 : ℂ).re ∧ (z - 1 / 2 : ℂ).re ≤ bΦ)
    (hpath_im : ‖z.im‖ = ‖t‖)
    (hshift_im : ‖(z - 1 / 2 : ℂ).im‖ = ‖t‖) :
    ‖completedZetaNegLogDeriv z‖ *
        ‖zetaCompletedExplicitFormulaPhi f (z - 1 / 2)‖
      ≤ hLog.stripBoundConstant a b N *
          (1 + ‖t‖) ^ N *
          hPhi.verticalStripRapidDecayConstant aΦ bΦ N *
          (1 + ‖t‖) ^ (-(N : ℤ)) :=
  (norm_product_le_of_bounds
    (completedZetaNegLogDeriv_strip_height_bound hLog a b t z N hpath hpath_im)
    (zetaCompletedExplicitFormulaPhi_strip_height_bound hPhi aΦ bΦ t z N hshift hshift_im)
    (completedZetaNegLogDeriv_strip_height_target_nonneg hLog a b t N)
    (norm_nonneg (zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))).trans_eq
      (horizontalProductTarget_reassociate
        (hLog.stripBoundConstant a b N)
        ((1 + ‖t‖) ^ N)
        (hPhi.verticalStripRapidDecayConstant aΦ bΦ N)
        ((1 + ‖t‖) ^ (-(N : ℤ))))

/-- The product estimate with separated logarithmic-growth and transform-decay exponents. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_stripProduct_bound_split
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (a b aΦ bΦ t : ℝ) (z : ℂ) (logN phiN : ℕ)
    (hpath : a ≤ z.re ∧ z.re ≤ b)
    (hshift : aΦ ≤ (z - 1 / 2 : ℂ).re ∧ (z - 1 / 2 : ℂ).re ≤ bΦ)
    (hpath_im : ‖z.im‖ = ‖t‖)
    (hshift_im : ‖(z - 1 / 2 : ℂ).im‖ = ‖t‖) :
    ‖completedZetaNegLogDeriv z‖ *
        ‖zetaCompletedExplicitFormulaPhi f (z - 1 / 2)‖
      ≤ hLog.stripBoundConstant a b logN *
          (1 + ‖t‖) ^ logN *
          hPhi.verticalStripRapidDecayConstant aΦ bΦ phiN *
          (1 + ‖t‖) ^ (-(phiN : ℤ)) :=
  (norm_product_le_of_bounds
    (completedZetaNegLogDeriv_strip_height_bound hLog a b t z logN hpath hpath_im)
    (zetaCompletedExplicitFormulaPhi_strip_height_bound hPhi aΦ bΦ t z phiN hshift hshift_im)
    (completedZetaNegLogDeriv_strip_height_target_nonneg hLog a b t logN)
    (norm_nonneg (zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))).trans_eq
      (horizontalProductTarget_reassociate
        (hLog.stripBoundConstant a b logN)
        ((1 + ‖t‖) ^ logN)
        (hPhi.verticalStripRapidDecayConstant aΦ bΦ phiN)
        ((1 + ‖t‖) ^ (-(phiN : ℤ))))

/-- The common unordered horizontal edge product constant with separated exponents. -/
def horizontalUnorderedEdgeIntegrandBoundConstantSplit
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (logN phiN : ℕ) : ℝ :=
  (hLog.stripBoundConstant (min r.c (1 - r.c)) (max r.c (1 - r.c)) logN) *
    (1 + ‖r.T‖) ^ logN *
    (hPhi.verticalStripRapidDecayConstant
      (min r.c (1 - r.c) - 1 / 2) (max r.c (1 - r.c) - 1 / 2) phiN) *
    (1 + ‖r.T‖) ^ (-(phiN : ℤ))

/-- The unordered horizontal pointwise contour-integrand bound. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_unorderedHorizontalPoint_bound
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (z : ℂ) (N : ℕ)
    (hpath : min r.c (1 - r.c) ≤ z.re ∧ z.re ≤ max r.c (1 - r.c))
    (hshift :
      min r.c (1 - r.c) - 1 / 2 ≤ (z - 1 / 2 : ℂ).re ∧
        (z - 1 / 2 : ℂ).re ≤ max r.c (1 - r.c) - 1 / 2)
    (hpath_im : ‖z.im‖ = ‖r.T‖)
    (hshift_im : ‖(z - 1 / 2 : ℂ).im‖ = ‖r.T‖) :
    ‖completedZetaNegLogDeriv z‖ *
        ‖zetaCompletedExplicitFormulaPhi f (z - 1 / 2)‖
      ≤ horizontalUnorderedEdgeIntegrandBoundConstant hPhi hLog r N :=
  zetaCompletedExplicitFormulaContourIntegrand_stripProduct_bound
    hPhi hLog (min r.c (1 - r.c)) (max r.c (1 - r.c))
    (min r.c (1 - r.c) - 1 / 2) (max r.c (1 - r.c) - 1 / 2)
    r.T z N hpath hshift hpath_im hshift_im

/-- The unordered horizontal pointwise contour-integrand bound with separated exponents. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_unorderedHorizontalPoint_bound_split
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (z : ℂ) (logN phiN : ℕ)
    (hpath : min r.c (1 - r.c) ≤ z.re ∧ z.re ≤ max r.c (1 - r.c))
    (hshift :
      min r.c (1 - r.c) - 1 / 2 ≤ (z - 1 / 2 : ℂ).re ∧
        (z - 1 / 2 : ℂ).re ≤ max r.c (1 - r.c) - 1 / 2)
    (hpath_im : ‖z.im‖ = ‖r.T‖)
    (hshift_im : ‖(z - 1 / 2 : ℂ).im‖ = ‖r.T‖) :
    ‖completedZetaNegLogDeriv z‖ *
        ‖zetaCompletedExplicitFormulaPhi f (z - 1 / 2)‖
      ≤ horizontalUnorderedEdgeIntegrandBoundConstantSplit hPhi hLog r logN phiN :=
  zetaCompletedExplicitFormulaContourIntegrand_stripProduct_bound_split
    hPhi hLog (min r.c (1 - r.c)) (max r.c (1 - r.c))
    (min r.c (1 - r.c) - 1 / 2) (max r.c (1 - r.c) - 1 / 2)
    r.T z logN phiN hpath hshift hpath_im hshift_im

/-- A pointwise contour-integrand estimate along the unordered top horizontal edge. -/
theorem zetaCompletedExplicitFormulaTopEdgeContourIntegrand_uIcc_bound
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx : x ∈ Set.uIcc r.c (1 - r.c)) (N : ℕ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath r x)‖
      ≤ horizontalUnorderedEdgeIntegrandBoundConstant hPhi hLog r N :=
  (norm_zetaCompletedExplicitFormulaContourIntegrand_le f _).trans
    (zetaCompletedExplicitFormulaContourIntegrand_unorderedHorizontalPoint_bound
      hPhi hLog r (zetaCompletedExplicitFormulaTopPath r x) N
      (zetaCompletedExplicitFormulaTopPath_re_mem_uIcc_bounds r x hx)
      (zetaCompletedExplicitFormulaTopPath_shift_re_mem_uIcc_bounds r x hx)
      (zetaCompletedExplicitFormulaTopPath_im_norm r x)
      (zetaCompletedExplicitFormulaTopPath_shift_im_norm r x))

/-- A pointwise contour-integrand estimate along the unordered bottom horizontal edge. -/
theorem zetaCompletedExplicitFormulaBottomEdgeContourIntegrand_uIcc_bound
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx : x ∈ Set.uIcc r.c (1 - r.c)) (N : ℕ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath r x)‖
      ≤ horizontalUnorderedEdgeIntegrandBoundConstant hPhi hLog r N :=
  (norm_zetaCompletedExplicitFormulaContourIntegrand_le f _).trans
    (zetaCompletedExplicitFormulaContourIntegrand_unorderedHorizontalPoint_bound
      hPhi hLog r (zetaCompletedExplicitFormulaBottomPath r x) N
      (zetaCompletedExplicitFormulaBottomPath_re_mem_uIcc_bounds r x hx)
      (zetaCompletedExplicitFormulaBottomPath_shift_re_mem_uIcc_bounds r x hx)
      (zetaCompletedExplicitFormulaBottomPath_im_norm r x)
      (zetaCompletedExplicitFormulaBottomPath_shift_im_norm r x))

/-- A pointwise contour-integrand estimate along the unordered top horizontal edge with
separated exponents. -/
theorem zetaCompletedExplicitFormulaTopEdgeContourIntegrand_uIcc_bound_split
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx : x ∈ Set.uIcc r.c (1 - r.c)) (logN phiN : ℕ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath r x)‖
      ≤ horizontalUnorderedEdgeIntegrandBoundConstantSplit hPhi hLog r logN phiN :=
  (norm_zetaCompletedExplicitFormulaContourIntegrand_le f _).trans
    (zetaCompletedExplicitFormulaContourIntegrand_unorderedHorizontalPoint_bound_split
      hPhi hLog r (zetaCompletedExplicitFormulaTopPath r x) logN phiN
      (zetaCompletedExplicitFormulaTopPath_re_mem_uIcc_bounds r x hx)
      (zetaCompletedExplicitFormulaTopPath_shift_re_mem_uIcc_bounds r x hx)
      (zetaCompletedExplicitFormulaTopPath_im_norm r x)
      (zetaCompletedExplicitFormulaTopPath_shift_im_norm r x))

/-- A pointwise contour-integrand estimate along the unordered bottom horizontal edge with
separated exponents. -/
theorem zetaCompletedExplicitFormulaBottomEdgeContourIntegrand_uIcc_bound_split
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx : x ∈ Set.uIcc r.c (1 - r.c)) (logN phiN : ℕ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath r x)‖
      ≤ horizontalUnorderedEdgeIntegrandBoundConstantSplit hPhi hLog r logN phiN :=
  (norm_zetaCompletedExplicitFormulaContourIntegrand_le f _).trans
    (zetaCompletedExplicitFormulaContourIntegrand_unorderedHorizontalPoint_bound_split
      hPhi hLog r (zetaCompletedExplicitFormulaBottomPath r x) logN phiN
      (zetaCompletedExplicitFormulaBottomPath_re_mem_uIcc_bounds r x hx)
      (zetaCompletedExplicitFormulaBottomPath_shift_re_mem_uIcc_bounds r x hx)
      (zetaCompletedExplicitFormulaBottomPath_im_norm r x)
      (zetaCompletedExplicitFormulaBottomPath_shift_im_norm r x))

/-- The unordered top horizontal integral is bounded by the explicit horizontal edge envelope. -/
theorem zetaCompletedExplicitFormulaTopLineIntegral_uIcc_norm_le_envelope
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (N : ℕ) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral f r‖ ≤
      horizontalUnorderedEdgeIntegrandBoundConstant hPhi hLog r N *
        horizontalEdgeLength r.c :=
  norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
    (fun x : ℝ =>
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath r x))
    r.c
    (horizontalUnorderedEdgeIntegrandBoundConstant hPhi hLog r N)
    (fun x hx =>
      zetaCompletedExplicitFormulaTopEdgeContourIntegrand_uIcc_bound
        hPhi hLog r x hx N)

/-- The unordered bottom horizontal integral is bounded by the explicit horizontal edge envelope. -/
theorem zetaCompletedExplicitFormulaBottomLineIntegral_uIcc_norm_le_envelope
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (N : ℕ) :
    ‖zetaCompletedExplicitFormulaBottomLineIntegral f r‖ ≤
      horizontalUnorderedEdgeIntegrandBoundConstant hPhi hLog r N *
        horizontalEdgeLength r.c :=
  norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
    (fun x : ℝ =>
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath r x))
    r.c
    (horizontalUnorderedEdgeIntegrandBoundConstant hPhi hLog r N)
    (fun x hx =>
      zetaCompletedExplicitFormulaBottomEdgeContourIntegrand_uIcc_bound
        hPhi hLog r x hx N)

/-- The unordered top horizontal integral is bounded by the split-exponent horizontal edge
envelope. -/
theorem zetaCompletedExplicitFormulaTopLineIntegral_uIcc_norm_le_envelopeSplit
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (logN phiN : ℕ) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral f r‖ ≤
      horizontalUnorderedEdgeIntegrandBoundConstantSplit hPhi hLog r logN phiN *
        horizontalEdgeLength r.c :=
  norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
    (fun x : ℝ =>
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath r x))
    r.c
    (horizontalUnorderedEdgeIntegrandBoundConstantSplit hPhi hLog r logN phiN)
    (fun x hx =>
      zetaCompletedExplicitFormulaTopEdgeContourIntegrand_uIcc_bound_split
        hPhi hLog r x hx logN phiN)

/-- The unordered bottom horizontal integral is bounded by the split-exponent horizontal edge
envelope. -/
theorem zetaCompletedExplicitFormulaBottomLineIntegral_uIcc_norm_le_envelopeSplit
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (logN phiN : ℕ) :
    ‖zetaCompletedExplicitFormulaBottomLineIntegral f r‖ ≤
      horizontalUnorderedEdgeIntegrandBoundConstantSplit hPhi hLog r logN phiN *
        horizontalEdgeLength r.c :=
  norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
    (fun x : ℝ =>
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath r x))
    r.c
    (horizontalUnorderedEdgeIntegrandBoundConstantSplit hPhi hLog r logN phiN)
    (fun x hx =>
      zetaCompletedExplicitFormulaBottomEdgeContourIntegrand_uIcc_bound_split
        hPhi hLog r x hx logN phiN)

/-- The horizontal difference is bounded by the sum of the two unordered edge envelopes. -/
theorem zetaCompletedExplicitFormulaHorizontalDifference_norm_le_unorderedEnvelope
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (N : ℕ) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral f r -
        zetaCompletedExplicitFormulaBottomLineIntegral f r‖
      ≤
        horizontalUnorderedEdgeIntegrandBoundConstant hPhi hLog r N *
          horizontalEdgeLength r.c +
        horizontalUnorderedEdgeIntegrandBoundConstant hPhi hLog r N *
          horizontalEdgeLength r.c :=
  (norm_sub_le
    (zetaCompletedExplicitFormulaTopLineIntegral f r)
    (zetaCompletedExplicitFormulaBottomLineIntegral f r)).trans
      (add_le_add
        (zetaCompletedExplicitFormulaTopLineIntegral_uIcc_norm_le_envelope hPhi hLog r N)
        (zetaCompletedExplicitFormulaBottomLineIntegral_uIcc_norm_le_envelope hPhi hLog r N))

/-- The horizontal difference is bounded by the sum of the two split-exponent unordered edge
envelopes. -/
theorem zetaCompletedExplicitFormulaHorizontalDifference_norm_le_unorderedEnvelopeSplit
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (logN phiN : ℕ) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral f r -
        zetaCompletedExplicitFormulaBottomLineIntegral f r‖
      ≤
        horizontalUnorderedEdgeIntegrandBoundConstantSplit hPhi hLog r logN phiN *
          horizontalEdgeLength r.c +
        horizontalUnorderedEdgeIntegrandBoundConstantSplit hPhi hLog r logN phiN *
          horizontalEdgeLength r.c :=
  (norm_sub_le
    (zetaCompletedExplicitFormulaTopLineIntegral f r)
    (zetaCompletedExplicitFormulaBottomLineIntegral f r)).trans
      (add_le_add
        (zetaCompletedExplicitFormulaTopLineIntegral_uIcc_norm_le_envelopeSplit
          hPhi hLog r logN phiN)
        (zetaCompletedExplicitFormulaBottomLineIntegral_uIcc_norm_le_envelopeSplit
          hPhi hLog r logN phiN))

/-- The horizontal envelope base `T ↦ 1 + ‖T‖` tends to infinity at `atTop`. -/
theorem horizontalEnvelopeBase_tendsto_atTop :
    Tendsto (fun T : ℝ => (1 + ‖T‖ : ℝ)) atTop atTop :=
  tendsto_atTop.2
    (fun a =>
      (eventually_ge_atTop a).mono
        (fun T hT =>
          le_trans hT
            (le_trans (Real.le_norm_self T) (le_add_of_nonneg_left zero_le_one))))

/-- The split exponent product collapses to the remaining negative decay exponent. -/
theorem one_add_norm_pow_mul_zpow_dominated_eq_decay
    (logN requestedDecay : ℕ) (T : ℝ) :
    (1 + ‖T‖) ^ logN *
        (1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ)) =
      (1 + ‖T‖) ^ (-(requestedDecay.succ : ℤ)) := by
  let x : ℝ := 1 + ‖T‖
  have hx_pos : 0 < x :=
    one_add_norm_pos T
  have hx_ne : x ≠ 0 :=
    ne_of_gt hx_pos
  have hnat :
      x ^ logN = x ^ (logN : ℤ) := by
    exact (zpow_natCast x logN).symm
  have hcast_sum :
      ((logN + requestedDecay.succ : ℕ) : ℤ) =
        (logN : ℤ) + (requestedDecay.succ : ℤ) := by
    exact Int.ofNat_add logN requestedDecay.succ
  have hint :
      (logN : ℤ) + -((logN + requestedDecay.succ : ℕ) : ℤ) =
        -(requestedDecay.succ : ℤ) := by
    let a : ℤ := (logN : ℤ)
    let b : ℤ := (requestedDecay.succ : ℤ)
    have hsum : ((logN + requestedDecay.succ : ℕ) : ℤ) = a + b := by
      exact hcast_sum
    calc
      (logN : ℤ) + -((logN + requestedDecay.succ : ℕ) : ℤ) =
          a + -(a + b) := by
        exact congrArg (fun y : ℤ => (logN : ℤ) + -y) hsum
      _ = a + (-a + -b) := by
        exact congrArg (fun y : ℤ => a + y) (neg_add a b)
      _ = (a + -a) + -b := by
        exact (add_assoc a (-a) (-b)).symm
      _ = 0 + -b := by
        exact congrArg (fun y : ℤ => y + -b) (add_right_neg a)
      _ = -b := by
        exact zero_add (-b)
      _ = -(requestedDecay.succ : ℤ) := by
        rfl
  change x ^ logN * x ^ (-(logN + requestedDecay.succ : ℤ)) =
    x ^ (-(requestedDecay.succ : ℤ))
  calc
    x ^ logN * x ^ (-(logN + requestedDecay.succ : ℤ)) =
        x ^ (logN : ℤ) * x ^ (-(logN + requestedDecay.succ : ℤ)) := by
      exact congrArg
        (fun y : ℝ => y * x ^ (-(logN + requestedDecay.succ : ℤ)))
        hnat
    _ = x ^ ((logN : ℤ) + -(logN + requestedDecay.succ : ℤ)) := by
      exact (zpow_add₀ hx_ne (logN : ℤ) (-(logN + requestedDecay.succ : ℤ))).symm
    _ = x ^ (-(requestedDecay.succ : ℤ)) := by
      exact congrArg (fun y : ℤ => x ^ y) hint

/-- A polynomial factor times a sufficiently stronger negative power tends to zero. -/
theorem one_add_norm_pow_mul_zpow_dominated_tendsto_zero
    (logN requestedDecay : ℕ) :
    Tendsto
      (fun T : ℝ =>
        (1 + ‖T‖) ^ logN *
          (1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ)))
      atTop
      (𝓝 (0 : ℝ)) := by
  have hdecay :
      Tendsto
        (fun T : ℝ => (1 + ‖T‖) ^ (-(requestedDecay.succ : ℤ)))
        atTop
        (𝓝 (0 : ℝ)) :=
    (tendsto_zpow_atTop_zero (Int.negSucc_lt_zero requestedDecay)).comp
      horizontalEnvelopeBase_tendsto_atTop
  have hfun :
      (fun T : ℝ =>
        (1 + ‖T‖) ^ logN *
          (1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ))) =
        fun T : ℝ => (1 + ‖T‖) ^ (-(requestedDecay.succ : ℤ)) := by
    funext T
    exact one_add_norm_pow_mul_zpow_dominated_eq_decay logN requestedDecay T
  exact hfun ▸ hdecay

/-- Reassociate the split horizontal envelope into constant times decay factor. -/
theorem horizontalEnvelopeSplit_reassociate (A B L X Y : ℝ) :
    (A * X * B * Y) * L = (A * B * L) * (X * Y) := by
  calc
    (A * X * B * Y) * L = ((A * X) * B * Y) * L := by
      rfl
    _ = ((A * X) * B) * (Y * L) := by
      exact mul_assoc ((A * X) * B) Y L
    _ = (A * X) * (B * (Y * L)) := by
      exact mul_assoc (A * X) B (Y * L)
    _ = (A * X) * (B * (L * Y)) := by
      exact congrArg (fun q : ℝ => (A * X) * (B * q)) (mul_comm Y L)
    _ = (A * X) * ((B * L) * Y) := by
      exact congrArg (fun q : ℝ => (A * X) * q) (mul_assoc B L Y).symm
    _ = ((A * X) * (B * L)) * Y := by
      exact (mul_assoc (A * X) (B * L) Y).symm
    _ = ((B * L) * (A * X)) * Y := by
      exact congrArg (fun q : ℝ => q * Y) (mul_comm (A * X) (B * L))
    _ = (((B * L) * A) * X) * Y := by
      exact congrArg (fun q : ℝ => q * Y) (mul_assoc (B * L) A X).symm
    _ = ((A * (B * L)) * X) * Y := by
      exact congrArg (fun q : ℝ => (q * X) * Y) (mul_comm (B * L) A)
    _ = (((A * B) * L) * X) * Y := by
      exact congrArg (fun q : ℝ => (q * X) * Y) (mul_assoc A B L).symm
    _ = ((A * B) * L) * (X * Y) := by
      exact mul_assoc ((A * B) * L) X Y

/-- The family-level unordered horizontal edge envelope at height `T`. -/
def horizontalUnorderedFamilyEdgeEnvelope
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (F : ExplicitFormulaContourFamily) (N : ℕ) (T : ℝ) : ℝ :=
  horizontalUnorderedEdgeIntegrandBoundConstant hPhi hLog (F.rectangle T) N *
    horizontalEdgeLength F.c

/-- The family-level unordered horizontal difference envelope at height `T`. -/
def horizontalUnorderedFamilyDifferenceEnvelope
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (F : ExplicitFormulaContourFamily) (N : ℕ) (T : ℝ) : ℝ :=
  horizontalUnorderedFamilyEdgeEnvelope hPhi hLog F N T +
    horizontalUnorderedFamilyEdgeEnvelope hPhi hLog F N T

/-- The family-level unordered horizontal edge envelope with separated logarithmic-growth
and transform-decay exponents. -/
def horizontalUnorderedFamilyEdgeEnvelopeSplit
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (F : ExplicitFormulaContourFamily) (logN phiN : ℕ) (T : ℝ) : ℝ :=
  horizontalUnorderedEdgeIntegrandBoundConstantSplit hPhi hLog (F.rectangle T) logN phiN *
    horizontalEdgeLength F.c

/-- The family-level unordered horizontal difference envelope with separated logarithmic-growth
and transform-decay exponents. -/
def horizontalUnorderedFamilyDifferenceEnvelopeSplit
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (F : ExplicitFormulaContourFamily) (logN phiN : ℕ) (T : ℝ) : ℝ :=
  horizontalUnorderedFamilyEdgeEnvelopeSplit hPhi hLog F logN phiN T +
    horizontalUnorderedFamilyEdgeEnvelopeSplit hPhi hLog F logN phiN T

/-- The horizontal difference is bounded by the family-level unordered envelope. -/
theorem zetaCompletedExplicitFormulaHorizontalDifference_norm_le_familyEnvelope
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (F : ExplicitFormulaContourFamily) (N : ℕ) (T : ℝ) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖
      ≤ horizontalUnorderedFamilyDifferenceEnvelope hPhi hLog F N T := by
  unfold horizontalUnorderedFamilyDifferenceEnvelope
  unfold horizontalUnorderedFamilyEdgeEnvelope
  unfold ExplicitFormulaContourFamily.rectangle
  exact zetaCompletedExplicitFormulaHorizontalDifference_norm_le_unorderedEnvelope
    hPhi hLog (F.rectangle T) N

/-- The horizontal difference is bounded by the split-exponent family-level unordered
envelope. -/
theorem zetaCompletedExplicitFormulaHorizontalDifference_norm_le_familyEnvelopeSplit
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (F : ExplicitFormulaContourFamily) (logN phiN : ℕ) (T : ℝ) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖
      ≤ horizontalUnorderedFamilyDifferenceEnvelopeSplit hPhi hLog F logN phiN T := by
  unfold horizontalUnorderedFamilyDifferenceEnvelopeSplit
  unfold horizontalUnorderedFamilyEdgeEnvelopeSplit
  unfold ExplicitFormulaContourFamily.rectangle
  exact zetaCompletedExplicitFormulaHorizontalDifference_norm_le_unorderedEnvelopeSplit
    hPhi hLog (F.rectangle T) logN phiN

/-- The split-exponent unordered family edge envelope tends to zero once the transform
decay exponent dominates the logarithmic-derivative polynomial-growth exponent. -/
theorem horizontalUnorderedFamilyEdgeEnvelopeSplit_tendsto_zero
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (F : ExplicitFormulaContourFamily) (logN requestedDecay : ℕ) :
    Tendsto
      (fun T : ℝ =>
        horizontalUnorderedFamilyEdgeEnvelopeSplit
          hPhi hLog F logN (logN + requestedDecay.succ) T)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hpow :
      Tendsto
        (fun T : ℝ =>
          (1 + ‖T‖) ^ logN *
            (1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ)))
        atTop
        (𝓝 (0 : ℝ)) :=
    one_add_norm_pow_mul_zpow_dominated_tendsto_zero logN requestedDecay
  let C : ℝ :=
    hLog.stripBoundConstant (min F.c (1 - F.c)) (max F.c (1 - F.c)) logN *
      hPhi.verticalStripRapidDecayConstant
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2)
        (logN + requestedDecay.succ) *
      horizontalEdgeLength F.c
  have hscaled :
      Tendsto
        (fun T : ℝ =>
          C *
            ((1 + ‖T‖) ^ logN *
              (1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ))))
        atTop
        (𝓝 (0 : ℝ)) := by
    exact Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun T : ℝ =>
            C *
              ((1 + ‖T‖) ^ logN *
                (1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ))))
          atTop
          (𝓝 x))
      (mul_zero C)
      (hpow.const_mul C)
  have hrewrite :
      (fun T : ℝ =>
        horizontalUnorderedFamilyEdgeEnvelopeSplit
          hPhi hLog F logN (logN + requestedDecay.succ) T) =
        fun T : ℝ =>
          C *
            ((1 + ‖T‖) ^ logN *
              (1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ))) := by
    funext T
    unfold horizontalUnorderedFamilyEdgeEnvelopeSplit
    unfold horizontalUnorderedEdgeIntegrandBoundConstantSplit
    unfold ExplicitFormulaContourFamily.rectangle
    unfold C
    exact horizontalEnvelopeSplit_reassociate
      (hLog.stripBoundConstant (min F.c (1 - F.c)) (max F.c (1 - F.c)) logN)
      (hPhi.verticalStripRapidDecayConstant
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2)
        (logN + requestedDecay.succ))
      (horizontalEdgeLength F.c)
      ((1 + ‖T‖) ^ logN)
      ((1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ)))
  exact hrewrite ▸ hscaled

/-- The split-exponent unordered family difference envelope tends to zero once the transform
decay exponent dominates the logarithmic-derivative polynomial-growth exponent. -/
theorem horizontalUnorderedFamilyDifferenceEnvelopeSplit_tendsto_zero
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (F : ExplicitFormulaContourFamily) (logN requestedDecay : ℕ) :
    Tendsto
      (fun T : ℝ =>
        horizontalUnorderedFamilyDifferenceEnvelopeSplit
          hPhi hLog F logN (logN + requestedDecay.succ) T)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hedge :
      Tendsto
        (fun T : ℝ =>
          horizontalUnorderedFamilyEdgeEnvelopeSplit
            hPhi hLog F logN (logN + requestedDecay.succ) T)
        atTop
        (𝓝 (0 : ℝ)) :=
    horizontalUnorderedFamilyEdgeEnvelopeSplit_tendsto_zero hPhi hLog F logN requestedDecay
  have hsum :
      Tendsto
        (fun T : ℝ =>
          horizontalUnorderedFamilyEdgeEnvelopeSplit
              hPhi hLog F logN (logN + requestedDecay.succ) T +
            horizontalUnorderedFamilyEdgeEnvelopeSplit
              hPhi hLog F logN (logN + requestedDecay.succ) T)
        atTop
        (𝓝 ((0 : ℝ) + 0)) :=
    hedge.add hedge
  have hzero : (0 : ℝ) + 0 = 0 :=
    zero_add 0
  have htarget :
      Tendsto
        (fun T : ℝ =>
          horizontalUnorderedFamilyEdgeEnvelopeSplit
              hPhi hLog F logN (logN + requestedDecay.succ) T +
            horizontalUnorderedFamilyEdgeEnvelopeSplit
              hPhi hLog F logN (logN + requestedDecay.succ) T)
        atTop
        (𝓝 (0 : ℝ)) :=
    Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun T : ℝ =>
            horizontalUnorderedFamilyEdgeEnvelopeSplit
                hPhi hLog F logN (logN + requestedDecay.succ) T +
              horizontalUnorderedFamilyEdgeEnvelopeSplit
                hPhi hLog F logN (logN + requestedDecay.succ) T)
          atTop
          (𝓝 x))
      hzero
      hsum
  unfold horizontalUnorderedFamilyDifferenceEnvelopeSplit
  exact htarget

/-- The unordered horizontal family difference tends to zero. -/
theorem zetaCompletedExplicitFormulaHorizontalDifference_tendsto_zero
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (F : ExplicitFormulaContourFamily) (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
      atTop
      (𝓝 (0 : ℝ)) :=
  squeeze_zero_norm'
    (Eventually.of_forall
      (fun T =>
        zetaCompletedExplicitFormulaHorizontalDifference_norm_le_familyEnvelopeSplit
          hPhi hLog F N (N + N.succ) T))
    (horizontalUnorderedFamilyDifferenceEnvelopeSplit_tendsto_zero hPhi hLog F N N)

/-- A generic pointwise contour-integrand strip bound along a horizontal contour point. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_horizontalPoint_bound
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (z : ℂ) (N : ℕ)
    (hpath : r.c ≤ z.re ∧ z.re ≤ 1 - r.c)
    (hshift : (r.c - 1 / 2) ≤ (z - 1 / 2 : ℂ).re ∧ (z - 1 / 2 : ℂ).re ≤ (1 / 2 - r.c))
    (hpath_im : ‖z.im‖ = ‖r.T‖)
    (hshift_im : ‖(z - 1 / 2 : ℂ).im‖ = ‖r.T‖) :
    ‖completedZetaNegLogDeriv z‖ *
        ‖zetaCompletedExplicitFormulaPhi f (z - 1 / 2)‖
      ≤ (hLog.stripBoundConstant r.c (1 - r.c) N) *
          (1 + ‖r.T‖) ^ N *
          (hPhi.verticalStripRapidDecayConstant (r.c - 1 / 2) (1 / 2 - r.c) N) *
          (1 + ‖r.T‖) ^ (-(N : ℤ)) :=
  zetaCompletedExplicitFormulaContourIntegrand_horizontalProduct_bound'
    hPhi hLog r z N hpath hshift hpath_im hshift_im

/-- The top contour integrand is controlled from its logarithmic and transform factors. -/
theorem zetaCompletedExplicitFormulaTopPath_integrand_norm_le_product
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (x : ℝ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath r x)‖
      ≤ ‖completedZetaNegLogDeriv (zetaCompletedExplicitFormulaTopPath r x)‖ *
          ‖zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaTopPath r x - 1 / 2)‖ :=
  norm_zetaCompletedExplicitFormulaContourIntegrand_le f _

/-- The bottom contour integrand is controlled from its logarithmic and transform factors. -/
theorem zetaCompletedExplicitFormulaBottomPath_integrand_norm_le_product
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (x : ℝ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath r x)‖
      ≤ ‖completedZetaNegLogDeriv (zetaCompletedExplicitFormulaBottomPath r x)‖ *
          ‖zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2)‖ :=
  norm_zetaCompletedExplicitFormulaContourIntegrand_le f _

/-- The top horizontal path satisfies the generic horizontal pointwise bound. -/
theorem zetaCompletedExplicitFormulaTopPath_horizontalPoint_bound
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) (N : ℕ) :
    ‖completedZetaNegLogDeriv (zetaCompletedExplicitFormulaTopPath r x)‖ *
        ‖zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaTopPath r x - 1 / 2)‖
      ≤ (hLog.stripBoundConstant r.c (1 - r.c) N) *
          (1 + ‖r.T‖) ^ N *
          (hPhi.verticalStripRapidDecayConstant (r.c - 1 / 2) (1 / 2 - r.c) N) *
          (1 + ‖r.T‖) ^ (-(N : ℤ)) :=
  zetaCompletedExplicitFormulaContourIntegrand_horizontalPoint_bound
    hPhi hLog r (zetaCompletedExplicitFormulaTopPath r x) N
    (zetaCompletedExplicitFormulaTopPath_strip r x hx1 hx2)
    (zetaCompletedExplicitFormulaTopPath_shift_strip r x hx1 hx2)
    (zetaCompletedExplicitFormulaTopPath_im_norm r x)
    (zetaCompletedExplicitFormulaTopPath_shift_im_norm r x)

/-- The bottom horizontal path satisfies the generic horizontal pointwise bound. -/
theorem zetaCompletedExplicitFormulaBottomPath_horizontalPoint_bound
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) (N : ℕ) :
    ‖completedZetaNegLogDeriv (zetaCompletedExplicitFormulaBottomPath r x)‖ *
        ‖zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2)‖
      ≤ (hLog.stripBoundConstant r.c (1 - r.c) N) *
          (1 + ‖r.T‖) ^ N *
          (hPhi.verticalStripRapidDecayConstant (r.c - 1 / 2) (1 / 2 - r.c) N) *
          (1 + ‖r.T‖) ^ (-(N : ℤ)) :=
  zetaCompletedExplicitFormulaContourIntegrand_horizontalPoint_bound
    hPhi hLog r (zetaCompletedExplicitFormulaBottomPath r x) N
    (zetaCompletedExplicitFormulaBottomPath_strip r x hx1 hx2)
    (zetaCompletedExplicitFormulaBottomPath_shift_strip r x hx1 hx2)
    (zetaCompletedExplicitFormulaBottomPath_im_norm r x)
    (zetaCompletedExplicitFormulaBottomPath_shift_im_norm r x)

/-- A pointwise contour-integrand estimate along the top horizontal edge. -/
theorem zetaCompletedExplicitFormulaTopEdgeContourIntegrand_bound
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) (N : ℕ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath r x)‖
      ≤ (hLog.stripBoundConstant r.c (1 - r.c) N) *
          (1 + ‖r.T‖) ^ N *
          (hPhi.verticalStripRapidDecayConstant (r.c - 1 / 2) (1 / 2 - r.c) N) *
          (1 + ‖r.T‖) ^ (-(N : ℤ)) :=
  (zetaCompletedExplicitFormulaTopPath_integrand_norm_le_product f r x).trans
    (zetaCompletedExplicitFormulaTopPath_horizontalPoint_bound hPhi hLog r x hx1 hx2 N)

/-- A pointwise contour-integrand estimate along the bottom horizontal edge. -/
theorem zetaCompletedExplicitFormulaBottomEdgeContourIntegrand_bound
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) (N : ℕ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath r x)‖
      ≤ (hLog.stripBoundConstant r.c (1 - r.c) N) *
          (1 + ‖r.T‖) ^ N *
          (hPhi.verticalStripRapidDecayConstant (r.c - 1 / 2) (1 / 2 - r.c) N) *
          (1 + ‖r.T‖) ^ (-(N : ℤ)) :=
  (zetaCompletedExplicitFormulaBottomPath_integrand_norm_le_product f r x).trans
    (zetaCompletedExplicitFormulaBottomPath_horizontalPoint_bound hPhi hLog r x hx1 hx2 N)

/-- The contour integrand on the top edge inherits the product strip bound from the owner
packages for `completedZetaNegLogDeriv` and `Φ_f`. -/
theorem zetaCompletedExplicitFormulaTopPath_contourIntegrand_strip_bound
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) (N : ℕ) :
    ∃ C : ℝ, ‖zetaCompletedExplicitFormulaContourIntegrand f
      (zetaCompletedExplicitFormulaTopPath r x)‖ ≤ C :=
  ⟨horizontalEdgeIntegrandBoundConstant hPhi hLog r N,
    zetaCompletedExplicitFormulaTopEdgeContourIntegrand_bound hPhi hLog r x hx1 hx2 N⟩

/-- The contour integrand on the bottom edge inherits the product strip bound from the owner
packages for `completedZetaNegLogDeriv` and `Φ_f`. -/
theorem zetaCompletedExplicitFormulaBottomPath_contourIntegrand_strip_bound
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) (N : ℕ) :
    ∃ C : ℝ, ‖zetaCompletedExplicitFormulaContourIntegrand f
      (zetaCompletedExplicitFormulaBottomPath r x)‖ ≤ C :=
  ⟨horizontalEdgeIntegrandBoundConstant hPhi hLog r N,
    zetaCompletedExplicitFormulaBottomEdgeContourIntegrand_bound hPhi hLog r x hx1 hx2 N⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
