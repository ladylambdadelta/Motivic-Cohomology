import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.ZetaExplicitFormulaContourPaths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.Base
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalizationBridge.ZetaCompletedLogDerivativeCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaAdmissibleTransformRegularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.ZetaExplicitFormulaPuncturedPlane.Owner
import Mathlib.Analysis.Complex.Basic

/-!
# Boundary explicit-formula contour path lemmas

This file owns the explicit path algebra and the basic nonvanishing/strip
lemmas for the contour parametrizations. The main contour file consumes these
as reusable owner-level facts.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

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

theorem real_le_transport_left {a b c : ℝ} (hab : a = b) (hbc : b ≤ c) :
    a ≤ c :=
  match hab with
  | rfl => hbc

theorem real_le_transport_right {a b c : ℝ} (hbc : b = c) (hab : a ≤ c) :
    a ≤ b :=
  match hbc with
  | rfl => hab

theorem ofReal_mul_I_re_zero (t : ℝ) :
    ((t : ℂ) * Complex.I).re = 0 :=
  Eq.trans
    (Complex.mul_I_re (t : ℂ))
    (Eq.trans
      (congrArg Neg.neg (Complex.ofReal_im t))
      (neg_zero : -(0 : ℝ) = 0))

theorem ofReal_mul_I_im (t : ℝ) :
    ((t : ℂ) * Complex.I).im = t :=
  Eq.trans
    (Complex.mul_I_im (t : ℂ))
    (Complex.ofReal_re t)

theorem ofReal_add_mul_I_re (a t : ℝ) :
    ((a : ℂ) + (t : ℂ) * Complex.I).re = a :=
  Eq.trans
    (Complex.add_re (a : ℂ) ((t : ℂ) * Complex.I))
    (Eq.trans
      (congrArg₂ HAdd.hAdd (Complex.ofReal_re a) (ofReal_mul_I_re_zero t))
      (add_zero a))

theorem ofReal_add_mul_I_im (a t : ℝ) :
    ((a : ℂ) + (t : ℂ) * Complex.I).im = t :=
  Eq.trans
    (Complex.add_im (a : ℂ) ((t : ℂ) * Complex.I))
    (Eq.trans
      (congrArg₂ HAdd.hAdd (Complex.ofReal_im a) (ofReal_mul_I_im t))
      (zero_add t))

theorem ofReal_sub_mul_I_re (a t : ℝ) :
    ((a : ℂ) - (t : ℂ) * Complex.I).re = a :=
  Eq.trans
    (Complex.sub_re (a : ℂ) ((t : ℂ) * Complex.I))
    (Eq.trans
      (congrArg₂ HSub.hSub (Complex.ofReal_re a) (ofReal_mul_I_re_zero t))
      (sub_zero a))

theorem ofReal_sub_mul_I_im (a t : ℝ) :
    ((a : ℂ) - (t : ℂ) * Complex.I).im = -t :=
  Eq.trans
    (Complex.sub_im (a : ℂ) ((t : ℂ) * Complex.I))
    (Eq.trans
      (congrArg₂ HSub.hSub (Complex.ofReal_im a) (ofReal_mul_I_im t))
      (zero_sub t))

theorem real_zero_sub_neg (t : ℝ) :
    0 - -t = t :=
  Eq.trans (zero_sub (-t)) (neg_neg t)

theorem real_one_sub_one_sub (x : ℝ) :
    1 - (1 - x) = x :=
  sub_sub_self 1 x

theorem ofReal_one_sub (x : ℝ) :
    ((1 - x : ℝ) : ℂ) = 1 - (x : ℂ) :=
  Complex.ofReal_sub 1 x

theorem one_sub_ofReal_re (a : ℝ) :
    ((1 : ℂ) - (a : ℂ)).re = 1 - a :=
  Eq.trans
    (Complex.sub_re (1 : ℂ) (a : ℂ))
    (congrArg₂ HSub.hSub Complex.one_re (Complex.ofReal_re a))

theorem one_sub_ofReal_im (a : ℝ) :
    ((1 : ℂ) - (a : ℂ)).im = 0 :=
  Eq.trans
    (Complex.sub_im (1 : ℂ) (a : ℂ))
    (Eq.trans
      (congrArg₂ HSub.hSub Complex.one_im (Complex.ofReal_im a))
      (sub_zero 0))

theorem one_sub_ofReal_add_mul_I_re (a t : ℝ) :
    (((1 : ℂ) - (a : ℂ)) + (t : ℂ) * Complex.I).re = 1 - a :=
  Eq.trans
    (Complex.add_re ((1 : ℂ) - (a : ℂ)) ((t : ℂ) * Complex.I))
    (Eq.trans
      (congrArg₂ HAdd.hAdd
        (one_sub_ofReal_re a)
        (ofReal_mul_I_re_zero t))
      (add_zero (1 - a)))

theorem one_sub_ofReal_add_mul_I_im (a t : ℝ) :
    (((1 : ℂ) - (a : ℂ)) + (t : ℂ) * Complex.I).im = t :=
  Eq.trans
    (Complex.add_im ((1 : ℂ) - (a : ℂ)) ((t : ℂ) * Complex.I))
    (Eq.trans
      (congrArg₂ HAdd.hAdd
        (one_sub_ofReal_im a)
        (ofReal_mul_I_im t))
      (zero_add t))

/-- The right path has constant real part `c`. -/
theorem zetaCompletedExplicitFormulaRightPath_re_formula (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaRightPath r t).re = r.c :=
  ofReal_add_mul_I_re r.c t

/-- The right path has constant real part `c`. -/
theorem zetaCompletedExplicitFormulaRightPath_re (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaRightPath r t).re = r.c :=
  zetaCompletedExplicitFormulaRightPath_re_formula r t

/-- The right path has positive real part when the rectangle lies to the right of `1/2`. -/
theorem rightPath_re_pos_core (r : ExplicitFormulaRectangle) (t : ℝ)
    (hc : (1 / 2 : ℝ) < r.c) :
    0 < (zetaCompletedExplicitFormulaRightPath r t).re := by
  have htwo : 0 < (2 : ℝ) := two_pos
  have hhalf : 0 < (1 / 2 : ℝ) := div_pos zero_lt_one htwo
  have hcpos : 0 < r.c := lt_trans hhalf hc
  exact Eq.symm (zetaCompletedExplicitFormulaRightPath_re r t) ▸ hcpos

/-- The right path has imaginary part `t`. -/
theorem zetaCompletedExplicitFormulaRightPath_im_formula (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaRightPath r t).im = t :=
  ofReal_add_mul_I_im r.c t

/-- The right path has imaginary part `t`. -/
theorem zetaCompletedExplicitFormulaRightPath_im (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaRightPath r t).im = t :=
  zetaCompletedExplicitFormulaRightPath_im_formula r t

/-- The left path has constant real part `1 - c`. -/
theorem zetaCompletedExplicitFormulaLeftPath_re_formula (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath r t).re = 1 - r.c :=
  one_sub_ofReal_add_mul_I_re r.c t

/-- The left path has constant real part `1 - c`. -/
theorem zetaCompletedExplicitFormulaLeftPath_re (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath r t).re = 1 - r.c :=
  zetaCompletedExplicitFormulaLeftPath_re_formula r t

/-- The left path has imaginary part `t`. -/
theorem zetaCompletedExplicitFormulaLeftPath_im_formula (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath r t).im = t :=
  one_sub_ofReal_add_mul_I_im r.c t

/-- The left path has imaginary part `t`. -/
theorem zetaCompletedExplicitFormulaLeftPath_im (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath r t).im = t :=
  zetaCompletedExplicitFormulaLeftPath_im_formula r t

/-- The left path has positive real part when the rectangle lies to the right of `1/2`. -/
theorem leftPath_re_pos_core (r : ExplicitFormulaRectangle) (t : ℝ)
    (hc : r.c < 1) :
    0 < (zetaCompletedExplicitFormulaLeftPath r t).re := by
  have hpos : 0 < 1 - r.c := sub_pos.mpr hc
  exact Eq.symm (zetaCompletedExplicitFormulaLeftPath_re r t) ▸ hpos

theorem one_sub_rightPath_re (r : ExplicitFormulaRectangle) (t : ℝ) :
    (1 - zetaCompletedExplicitFormulaRightPath r t).re = 1 - r.c :=
  Eq.trans
    (Complex.sub_re 1 (zetaCompletedExplicitFormulaRightPath r t))
    (congrArg₂ HSub.hSub Complex.one_re (zetaCompletedExplicitFormulaRightPath_re r t))

theorem one_sub_rightPath_neg_im (r : ExplicitFormulaRectangle) (t : ℝ) :
    (1 - zetaCompletedExplicitFormulaRightPath r (-t)).im = t :=
  Eq.trans
    (Complex.sub_im 1 (zetaCompletedExplicitFormulaRightPath r (-t)))
    (Eq.trans
      (congrArg₂ HSub.hSub Complex.one_im (zetaCompletedExplicitFormulaRightPath_im r (-t)))
      (real_zero_sub_neg t))

theorem zetaCompletedExplicitFormulaLeftPath_eq_one_sub_rightPath_re
    (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath r t).re =
      (1 - zetaCompletedExplicitFormulaRightPath r (-t)).re :=
  Eq.trans
    (zetaCompletedExplicitFormulaLeftPath_re r t)
    (one_sub_rightPath_re r (-t)).symm

theorem zetaCompletedExplicitFormulaLeftPath_eq_one_sub_rightPath_im
    (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath r t).im =
      (1 - zetaCompletedExplicitFormulaRightPath r (-t)).im :=
  Eq.trans
    (zetaCompletedExplicitFormulaLeftPath_im r t)
    (one_sub_rightPath_neg_im r t).symm

/-- The left path is the reflection of the right path across `s ↦ 1 - s`. -/
theorem zetaCompletedExplicitFormulaLeftPath_eq_one_sub_rightPath
    (r : ExplicitFormulaRectangle) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath r t =
      1 - zetaCompletedExplicitFormulaRightPath r (-t) :=
  Complex.ext
    (zetaCompletedExplicitFormulaLeftPath_eq_one_sub_rightPath_re r t)
    (zetaCompletedExplicitFormulaLeftPath_eq_one_sub_rightPath_im r t)

/-- The right path at `t = 0` is the lower-right corner. -/
theorem zetaCompletedExplicitFormulaRightPath_zero_core (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaRightPath r 0 = r.c :=
  Complex.ext
    (ofReal_add_mul_I_re r.c 0)
    (Eq.trans (ofReal_add_mul_I_im r.c 0) (Complex.ofReal_im r.c).symm)

theorem zetaCompletedExplicitFormulaRightPath_zero (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaRightPath r 0 = r.c :=
  zetaCompletedExplicitFormulaRightPath_zero_core r

theorem zetaCompletedExplicitFormulaRightPath_T_core (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaRightPath r r.T = r.c + r.T * Complex.I :=
  rfl

theorem zetaCompletedExplicitFormulaRightPath_T (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaRightPath r r.T = r.c + r.T * Complex.I :=
  zetaCompletedExplicitFormulaRightPath_T_core r

theorem zetaCompletedExplicitFormulaLeftPath_zero_core (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaLeftPath r 0 = 1 - r.c :=
  Eq.trans
    (show zetaCompletedExplicitFormulaLeftPath r 0 =
      (1 : ℂ) - (r.c : ℂ) + (0 : ℂ) * Complex.I from rfl)
    (Complex.ext
      (Eq.trans (one_sub_ofReal_add_mul_I_re r.c 0) (one_sub_ofReal_re r.c).symm)
      (Eq.trans (one_sub_ofReal_add_mul_I_im r.c 0) (one_sub_ofReal_im r.c).symm))

theorem zetaCompletedExplicitFormulaLeftPath_zero (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaLeftPath r 0 = 1 - r.c :=
  zetaCompletedExplicitFormulaLeftPath_zero_core r

theorem zetaCompletedExplicitFormulaLeftPath_T_core (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaLeftPath r r.T = (1 - r.c) + r.T * Complex.I :=
  rfl

theorem zetaCompletedExplicitFormulaLeftPath_T (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaLeftPath r r.T = (1 - r.c) + r.T * Complex.I :=
  zetaCompletedExplicitFormulaLeftPath_T_core r

theorem zetaCompletedExplicitFormulaTopPath_c_core (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaTopPath r r.c = r.c + r.T * Complex.I :=
  rfl

theorem zetaCompletedExplicitFormulaTopPath_c (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaTopPath r r.c = r.c + r.T * Complex.I :=
  zetaCompletedExplicitFormulaTopPath_c_core r

theorem zetaCompletedExplicitFormulaTopPath_one_sub_core (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaTopPath r (1 - r.c) = (1 - r.c) + r.T * Complex.I :=
  Eq.trans
    (show zetaCompletedExplicitFormulaTopPath r (1 - r.c) =
      ((1 - r.c : ℝ) : ℂ) + r.T * Complex.I from rfl)
    (congrArg (fun z : ℂ => z + (r.T : ℂ) * Complex.I) (ofReal_one_sub r.c))

theorem zetaCompletedExplicitFormulaTopPath_one_sub (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaTopPath r (1 - r.c) = (1 - r.c) + r.T * Complex.I :=
  zetaCompletedExplicitFormulaTopPath_one_sub_core r

theorem zetaCompletedExplicitFormulaBottomPath_c_core (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaBottomPath r r.c = r.c - r.T * Complex.I :=
  rfl

theorem zetaCompletedExplicitFormulaBottomPath_c (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaBottomPath r r.c = r.c - r.T * Complex.I :=
  zetaCompletedExplicitFormulaBottomPath_c_core r

theorem zetaCompletedExplicitFormulaBottomPath_one_sub (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaBottomPath r (1 - r.c) = (1 - r.c) - r.T * Complex.I :=
  Eq.trans
    (show zetaCompletedExplicitFormulaBottomPath r (1 - r.c) =
      ((1 - r.c : ℝ) : ℂ) - r.T * Complex.I from rfl)
    (congrArg (fun z : ℂ => z - (r.T : ℂ) * Complex.I) (ofReal_one_sub r.c))

theorem zetaCompletedExplicitFormulaTopPath_re_formula (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaTopPath r x).re = x :=
  ofReal_add_mul_I_re x r.T

theorem zetaCompletedExplicitFormulaTopPath_re_eq (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaTopPath r x).re = x :=
  zetaCompletedExplicitFormulaTopPath_re_formula r x

theorem zetaCompletedExplicitFormulaTopPath_im_formula (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaTopPath r x).im = r.T :=
  ofReal_add_mul_I_im x r.T

theorem zetaCompletedExplicitFormulaTopPath_im (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaTopPath r x).im = r.T :=
  zetaCompletedExplicitFormulaTopPath_im_formula r x

theorem zetaCompletedExplicitFormulaBottomPath_re_formula (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaBottomPath r x).re = x :=
  ofReal_sub_mul_I_re x r.T

theorem zetaCompletedExplicitFormulaBottomPath_re_eq (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaBottomPath r x).re = x :=
  zetaCompletedExplicitFormulaBottomPath_re_formula r x

theorem zetaCompletedExplicitFormulaBottomPath_im_formula (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaBottomPath r x).im = -r.T :=
  ofReal_sub_mul_I_im x r.T

theorem zetaCompletedExplicitFormulaBottomPath_im (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaBottomPath r x).im = -r.T :=
  zetaCompletedExplicitFormulaBottomPath_im_formula r x

theorem one_sub_topPath_one_sub_re (r : ExplicitFormulaRectangle) (x : ℝ) :
    (1 - zetaCompletedExplicitFormulaTopPath r (1 - x)).re = x :=
  Eq.trans
    (Complex.sub_re 1 (zetaCompletedExplicitFormulaTopPath r (1 - x)))
    (Eq.trans
      (congrArg₂ HSub.hSub Complex.one_re
        (zetaCompletedExplicitFormulaTopPath_re_eq r (1 - x)))
      (real_one_sub_one_sub x))

theorem one_sub_topPath_im (r : ExplicitFormulaRectangle) (x : ℝ) :
    (1 - zetaCompletedExplicitFormulaTopPath r x).im = -r.T :=
  Eq.trans
    (Complex.sub_im 1 (zetaCompletedExplicitFormulaTopPath r x))
    (Eq.trans
      (congrArg₂ HSub.hSub Complex.one_im (zetaCompletedExplicitFormulaTopPath_im r x))
      (zero_sub r.T))

theorem zetaCompletedExplicitFormulaBottomPath_eq_one_sub_topPath_re
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaBottomPath r x).re =
      (1 - zetaCompletedExplicitFormulaTopPath r (1 - x)).re :=
  Eq.trans
    (zetaCompletedExplicitFormulaBottomPath_re_eq r x)
    (one_sub_topPath_one_sub_re r x).symm

theorem zetaCompletedExplicitFormulaBottomPath_eq_one_sub_topPath_im
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaBottomPath r x).im =
      (1 - zetaCompletedExplicitFormulaTopPath r (1 - x)).im :=
  Eq.trans
    (zetaCompletedExplicitFormulaBottomPath_im r x)
    (one_sub_topPath_im r (1 - x)).symm

/-- The bottom horizontal path is the reflection of the top path across `s ↦ 1 - s`. -/
theorem zetaCompletedExplicitFormulaBottomPath_eq_one_sub_topPath
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    zetaCompletedExplicitFormulaBottomPath r x =
      1 - zetaCompletedExplicitFormulaTopPath r (1 - x) :=
  Complex.ext
    (zetaCompletedExplicitFormulaBottomPath_eq_one_sub_topPath_re r x)
    (zetaCompletedExplicitFormulaBottomPath_eq_one_sub_topPath_im r x)

/-- `Γℝ` is nonzero on the right contour path when the rectangle lies to the right of `1/2`. -/
theorem Gammaℝ_rightPath_ne_zero (r : ExplicitFormulaRectangle) (t : ℝ)
    (hc : (1 / 2 : ℝ) < r.c) :
    Complex.Gammaℝ (zetaCompletedExplicitFormulaRightPath r t) ≠ 0 := by
  exact Gammaℝ_ne_zero_of_re_pos
    (zetaCompletedExplicitFormulaRightPath r t)
    (rightPath_re_pos_core r t hc)

/-- `Γℝ` is nonzero on the left contour path when the rectangle lies to the right of `1/2`. -/
theorem Gammaℝ_leftPath_ne_zero (r : ExplicitFormulaRectangle) (t : ℝ)
    (hc : r.c < 1) :
    Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftPath r t) ≠ 0 := by
  exact Gammaℝ_ne_zero_of_re_pos
    (zetaCompletedExplicitFormulaLeftPath r t)
    (leftPath_re_pos_core r t hc)

theorem zetaCompletedExplicitFormulaRightPath_mem_re (r : ExplicitFormulaRectangle) (t : ℝ)
    (_ht1 : t ≤ r.T) (_ht2 : -r.T ≤ t) :
    (zetaCompletedExplicitFormulaRightPath r t).re = r.c :=
  zetaCompletedExplicitFormulaRightPath_re r t

theorem zetaCompletedExplicitFormulaRightPath_mem_upper (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (_ht2 : -r.T ≤ t) :
    (zetaCompletedExplicitFormulaRightPath r t).im ≤ r.T :=
  real_le_transport_left (zetaCompletedExplicitFormulaRightPath_im r t) ht1

theorem zetaCompletedExplicitFormulaRightPath_mem_lower (r : ExplicitFormulaRectangle) (t : ℝ)
    (_ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    -r.T ≤ (zetaCompletedExplicitFormulaRightPath r t).im :=
  real_le_transport_right (zetaCompletedExplicitFormulaRightPath_im r t) ht2

theorem zetaCompletedExplicitFormulaRightPath_mem_core (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    zetaCompletedExplicitFormulaRightPath r t ∈ explicitFormulaRightSide r :=
  And.intro
    (zetaCompletedExplicitFormulaRightPath_mem_re r t ht1 ht2)
    (And.intro
      (zetaCompletedExplicitFormulaRightPath_mem_upper r t ht1 ht2)
      (zetaCompletedExplicitFormulaRightPath_mem_lower r t ht1 ht2))

theorem zetaCompletedExplicitFormulaRightPath_mem (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    zetaCompletedExplicitFormulaRightPath r t ∈ explicitFormulaRightSide r :=
  zetaCompletedExplicitFormulaRightPath_mem_core r t ht1 ht2

theorem zetaCompletedExplicitFormulaLeftPath_mem_re (r : ExplicitFormulaRectangle) (t : ℝ)
    (_ht1 : t ≤ r.T) (_ht2 : -r.T ≤ t) :
    (zetaCompletedExplicitFormulaLeftPath r t).re = 1 - r.c :=
  zetaCompletedExplicitFormulaLeftPath_re r t

theorem zetaCompletedExplicitFormulaLeftPath_mem_upper (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (_ht2 : -r.T ≤ t) :
    (zetaCompletedExplicitFormulaLeftPath r t).im ≤ r.T :=
  real_le_transport_left (zetaCompletedExplicitFormulaLeftPath_im r t) ht1

theorem zetaCompletedExplicitFormulaLeftPath_mem_lower (r : ExplicitFormulaRectangle) (t : ℝ)
    (_ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    -r.T ≤ (zetaCompletedExplicitFormulaLeftPath r t).im :=
  real_le_transport_right (zetaCompletedExplicitFormulaLeftPath_im r t) ht2

theorem zetaCompletedExplicitFormulaLeftPath_mem_core (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    zetaCompletedExplicitFormulaLeftPath r t ∈ explicitFormulaLeftSide r :=
  And.intro
    (zetaCompletedExplicitFormulaLeftPath_mem_re r t ht1 ht2)
    (And.intro
      (zetaCompletedExplicitFormulaLeftPath_mem_upper r t ht1 ht2)
      (zetaCompletedExplicitFormulaLeftPath_mem_lower r t ht1 ht2))

theorem zetaCompletedExplicitFormulaLeftPath_mem (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    zetaCompletedExplicitFormulaLeftPath r t ∈ explicitFormulaLeftSide r :=
  zetaCompletedExplicitFormulaLeftPath_mem_core r t ht1 ht2

theorem zetaCompletedExplicitFormulaTopPath_mem_lower (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (_hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaTopPath r x).re :=
  real_le_transport_right (zetaCompletedExplicitFormulaTopPath_re_eq r x) hx1

theorem zetaCompletedExplicitFormulaTopPath_mem_upper (r : ExplicitFormulaRectangle) (x : ℝ)
    (_hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    (zetaCompletedExplicitFormulaTopPath r x).re ≤ 1 - r.c :=
  real_le_transport_left (zetaCompletedExplicitFormulaTopPath_re_eq r x) hx2

theorem zetaCompletedExplicitFormulaTopPath_mem_im (r : ExplicitFormulaRectangle) (x : ℝ)
    (_hx1 : r.c ≤ x) (_hx2 : x ≤ 1 - r.c) :
    (zetaCompletedExplicitFormulaTopPath r x).im = r.T :=
  zetaCompletedExplicitFormulaTopPath_im r x

theorem zetaCompletedExplicitFormulaTopPath_mem_core (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    zetaCompletedExplicitFormulaTopPath r x ∈ explicitFormulaTopSide r :=
  And.intro
    (zetaCompletedExplicitFormulaTopPath_mem_lower r x hx1 hx2)
    (And.intro
      (zetaCompletedExplicitFormulaTopPath_mem_upper r x hx1 hx2)
      (zetaCompletedExplicitFormulaTopPath_mem_im r x hx1 hx2))

theorem zetaCompletedExplicitFormulaTopPath_mem (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    zetaCompletedExplicitFormulaTopPath r x ∈ explicitFormulaTopSide r :=
  zetaCompletedExplicitFormulaTopPath_mem_core r x hx1 hx2

theorem zetaCompletedExplicitFormulaTopPath_strip_lower (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaTopPath r x).re :=
  zetaCompletedExplicitFormulaTopPath_mem_lower r x hx1 hx2

theorem zetaCompletedExplicitFormulaTopPath_strip_upper (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    (zetaCompletedExplicitFormulaTopPath r x).re ≤ 1 - r.c :=
  zetaCompletedExplicitFormulaTopPath_mem_upper r x hx1 hx2

theorem zetaCompletedExplicitFormulaTopPath_strip_core (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaTopPath r x).re ∧
      (zetaCompletedExplicitFormulaTopPath r x).re ≤ 1 - r.c := by
  constructor
  · exact zetaCompletedExplicitFormulaTopPath_strip_lower r x hx1 hx2
  · exact zetaCompletedExplicitFormulaTopPath_strip_upper r x hx1 hx2

theorem zetaCompletedExplicitFormulaTopPath_strip (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaTopPath r x).re ∧
      (zetaCompletedExplicitFormulaTopPath r x).re ≤ 1 - r.c :=
  zetaCompletedExplicitFormulaTopPath_strip_core r x hx1 hx2

theorem zetaCompletedExplicitFormulaBottomPath_mem_lower (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (_hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaBottomPath r x).re :=
  real_le_transport_right (zetaCompletedExplicitFormulaBottomPath_re_eq r x) hx1

theorem zetaCompletedExplicitFormulaBottomPath_mem_upper (r : ExplicitFormulaRectangle) (x : ℝ)
    (_hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    (zetaCompletedExplicitFormulaBottomPath r x).re ≤ 1 - r.c :=
  real_le_transport_left (zetaCompletedExplicitFormulaBottomPath_re_eq r x) hx2

theorem zetaCompletedExplicitFormulaBottomPath_mem_im (r : ExplicitFormulaRectangle) (x : ℝ)
    (_hx1 : r.c ≤ x) (_hx2 : x ≤ 1 - r.c) :
    (zetaCompletedExplicitFormulaBottomPath r x).im = -r.T :=
  zetaCompletedExplicitFormulaBottomPath_im r x

theorem zetaCompletedExplicitFormulaBottomPath_mem_core (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    zetaCompletedExplicitFormulaBottomPath r x ∈ explicitFormulaBottomSide r :=
  And.intro
    (zetaCompletedExplicitFormulaBottomPath_mem_lower r x hx1 hx2)
    (And.intro
      (zetaCompletedExplicitFormulaBottomPath_mem_upper r x hx1 hx2)
      (zetaCompletedExplicitFormulaBottomPath_mem_im r x hx1 hx2))

theorem zetaCompletedExplicitFormulaBottomPath_mem (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    zetaCompletedExplicitFormulaBottomPath r x ∈ explicitFormulaBottomSide r :=
  zetaCompletedExplicitFormulaBottomPath_mem_core r x hx1 hx2

theorem zetaCompletedExplicitFormulaBottomPath_strip_lower (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaBottomPath r x).re :=
  zetaCompletedExplicitFormulaBottomPath_mem_lower r x hx1 hx2

theorem zetaCompletedExplicitFormulaBottomPath_strip_upper (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    (zetaCompletedExplicitFormulaBottomPath r x).re ≤ 1 - r.c :=
  zetaCompletedExplicitFormulaBottomPath_mem_upper r x hx1 hx2

theorem zetaCompletedExplicitFormulaBottomPath_strip_core (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaBottomPath r x).re ∧
      (zetaCompletedExplicitFormulaBottomPath r x).re ≤ 1 - r.c := by
  constructor
  · exact zetaCompletedExplicitFormulaBottomPath_strip_lower r x hx1 hx2
  · exact zetaCompletedExplicitFormulaBottomPath_strip_upper r x hx1 hx2

theorem zetaCompletedExplicitFormulaBottomPath_strip (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaBottomPath r x).re ∧
      (zetaCompletedExplicitFormulaBottomPath r x).re ≤ 1 - r.c :=
  zetaCompletedExplicitFormulaBottomPath_strip_core r x hx1 hx2

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
