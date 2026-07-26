import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CenteredZeros.CriticalStrip.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalizationBridge.Owner

/-!
# Autocorrelation vertical regularity

This owner part isolates the vertical regularity of the autocorrelation
completed-explicit-formula rectangle.  The result is geometric: the right side
lies to the right of `1`, while the left side has real part `-1 / 2`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex

namespace ZetaAdmissibleFunction

namespace CleanAutocorrelationVerticalRegularity

/-- The autocorrelation contour right edge is strictly to the right of `1`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_contourFamily_rightEdge_gt_one
    (f : ZetaAdmissibleFunction) :
    (1 : ℝ) <
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c :=
  lt_add_of_pos_left (1 : ℝ) one_half_pos

/-- The autocorrelation contour left edge equals `-1 / 2`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_contourFamily_leftEdge_eq_neg_half
    (f : ZetaAdmissibleFunction) :
    1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c =
      -(1 / 2 : ℝ) :=
  calc
    1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c =
        1 - ((1 / 2 : ℝ) + 1) :=
      Eq.refl (1 - ((1 / 2 : ℝ) + 1))
    _ = 1 - (1 + (1 / 2 : ℝ)) :=
      congrArg (fun x : ℝ => 1 - x) (add_comm (1 / 2 : ℝ) 1)
    _ = 1 - 1 - (1 / 2 : ℝ) :=
      sub_add_eq_sub_sub 1 1 (1 / 2 : ℝ)
    _ = 0 - (1 / 2 : ℝ) :=
      congrArg (fun x : ℝ => x - (1 / 2 : ℝ)) (sub_self 1)
    _ = -(1 / 2 : ℝ) :=
      zero_sub (1 / 2 : ℝ)

/-- The autocorrelation contour left edge is strictly in the left half-plane. -/
theorem zetaCompletedExplicitFormula_autocorrelation_contourFamily_leftEdge_lt_zero
    (f : ZetaAdmissibleFunction) :
    1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c < (0 : ℝ) :=
  Eq.symm
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily_leftEdge_eq_neg_half f) ▸
      neg_lt_zero.mpr one_half_pos

/-- Points on the autocorrelation right vertical side have real part strictly
greater than `1`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_rightPath_one_lt_re
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    (1 : ℝ) <
      (zetaCompletedExplicitFormulaRightPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re :=
  Eq.symm
    (zetaCompletedExplicitFormulaRightPath_re
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) ▸
    zetaCompletedExplicitFormula_autocorrelation_contourFamily_rightEdge_gt_one f

/-- Points on the autocorrelation left vertical side lie strictly in the left half-plane. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_re_lt_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re <
      (0 : ℝ) :=
  Eq.symm
    (zetaCompletedExplicitFormulaLeftPath_re
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) ▸
    zetaCompletedExplicitFormula_autocorrelation_contourFamily_leftEdge_lt_zero f

/-- The completed zeta factor is nonzero on the autocorrelation right vertical side. -/
theorem zetaCompletedExplicitFormula_autocorrelation_rightPath_completedZeta_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    completedRiemannZeta
      (zetaCompletedExplicitFormulaRightPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) ≠ 0 :=
  completedRiemannZeta_ne_zero_of_one_lt_re
    (zetaCompletedExplicitFormulaRightPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t)
    (zetaCompletedExplicitFormula_autocorrelation_rightPath_one_lt_re f T t)

/-- The completed zeta factor is nonzero on the autocorrelation left vertical side. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_completedZeta_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    completedRiemannZeta
      (zetaCompletedExplicitFormulaLeftPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) ≠ 0 :=
  completedRiemannZeta_ne_zero_of_re_lt_zero
    (zetaCompletedExplicitFormulaLeftPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t)
    (zetaCompletedExplicitFormula_autocorrelation_leftPath_re_lt_zero f T t)

/-- `Gammaℝ` is nonzero on the autocorrelation right vertical side. -/
theorem zetaCompletedExplicitFormula_autocorrelation_rightPath_Gammaℝ_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaRightPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos
    (zetaCompletedExplicitFormulaRightPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t)
    (lt_trans zero_lt_one
      (zetaCompletedExplicitFormula_autocorrelation_rightPath_one_lt_re f T t))

/-- The doubled Gamma argument is nonzero on the autocorrelation right vertical side. -/
theorem zetaCompletedExplicitFormula_autocorrelation_rightPath_half_Gammaℝ_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaRightPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t / 2) ≠ 0 :=
  let z : ℂ :=
    zetaCompletedExplicitFormulaRightPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t
  have hz : 0 < z.re :=
    lt_trans zero_lt_one
      (zetaCompletedExplicitFormula_autocorrelation_rightPath_one_lt_re f T t)
  have hhalf : 0 < (z / 2 : ℂ).re := by
    have hdiv : (z / 2 : ℂ).re = z.re / 2 :=
      RCLike.div_re_ofReal (z := z) (r := (2 : ℝ))
    exact Eq.subst hdiv.symm (div_pos hz two_pos)
  Gammaℝ_ne_zero_of_re_pos (z / 2 : ℂ) hhalf

/-- The left autocorrelation path is not the normalization point `0`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t ≠ 0 :=
  fun hzero =>
    let hre_zero :
        (zetaCompletedExplicitFormulaLeftPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re =
          (0 : ℝ) :=
      congrArg Complex.re hzero
    let hre_lt_zero :
        (zetaCompletedExplicitFormulaLeftPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re <
          (0 : ℝ) :=
      zetaCompletedExplicitFormula_autocorrelation_leftPath_re_lt_zero f T t
    (not_lt_of_ge (le_of_eq hre_zero.symm)) hre_lt_zero

/-- Negative even real points have real coordinate at most `-2`. -/
theorem negativeEven_complex_re_le_neg_two
    (n : ℕ) :
    (((-2 : ℂ) * (((n + 1 : ℕ) : ℂ))).re : ℝ) ≤ (-2 : ℝ) :=
  let hone_le_nat : (1 : ℕ) ≤ n + 1 :=
    Nat.succ_le_succ (Nat.zero_le n)
  let hone_le_real : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) :=
    Eq.subst (motive := fun x : ℝ => x ≤ ((n + 1 : ℕ) : ℝ))
      (Nat.cast_one : ((1 : ℕ) : ℝ) = 1)
      (Nat.cast_le.mpr hone_le_nat)
  let hneg_two_nonpos : (-2 : ℝ) ≤ 0 :=
    neg_nonpos.mpr (le_of_lt zero_lt_two)
  let hmul :
      (-2 : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ (-2 : ℝ) * 1 :=
    mul_le_mul_of_nonpos_left hone_le_real hneg_two_nonpos
  let hright :
      (-2 : ℝ) * 1 = (-2 : ℝ) :=
    mul_one (-2 : ℝ)
  let hre :
      (((-2 : ℂ) * (((n + 1 : ℕ) : ℂ))).re : ℝ) =
        (-2 : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    calc
      (((-2 : ℂ) * (((n + 1 : ℕ) : ℂ))).re : ℝ) =
          ((((-2 : ℝ) : ℂ) * (((n + 1 : ℕ) : ℝ) : ℂ)).re : ℝ) := by
        let hneg : (-2 : ℂ) = ((-2 : ℝ) : ℂ) := by
          calc
            (-2 : ℂ) = -((2 : ℂ)) := by rfl
            _ = -(((2 : ℝ) : ℂ)) := congrArg Neg.neg (Complex.ofReal_ofNat 2).symm
            _ = ((-2 : ℝ) : ℂ) := (Complex.ofReal_neg 2).symm
        exact congrArg Complex.re
          (congrArg₂ (· * ·)
            hneg
            (Complex.ofReal_natCast (n + 1)).symm)
      _ = ((((-2 : ℝ) * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ).re : ℝ) := by
        exact congrArg Complex.re
          (Complex.ofReal_mul (-2 : ℝ) ((n + 1 : ℕ) : ℝ)).symm
      _ = (-2 : ℝ) * ((n + 1 : ℕ) : ℝ) := by
        exact Complex.ofReal_re ((-2 : ℝ) * ((n + 1 : ℕ) : ℝ))
  Eq.symm hre ▸ hmul.trans (le_of_eq hright)

/-- The real number `-2` lies strictly to the left of `-1 / 2`. -/
theorem neg_two_lt_neg_half : (-2 : ℝ) < -(1 / 2 : ℝ) :=
  lt_trans
    (neg_lt_neg (show (1 : ℝ) < 2 from one_lt_two))
    (neg_lt_neg one_half_lt_one)

/-- A point with real part `-1 / 2` is not a negative nonzero even point. -/
theorem not_negativeEven_of_re_eq_neg_half
    {z : ℂ}
    (hzre : z.re = -(1 / 2 : ℝ)) :
    ¬ ∃ n : ℕ, z = (-2 : ℂ) * (((n + 1 : ℕ) : ℂ)) :=
  fun hnegative =>
    match hnegative with
    | ⟨n, hn⟩ =>
        let hre_negative :
            z.re =
              (((-2 : ℂ) * (((n + 1 : ℕ) : ℂ))).re : ℝ) :=
          congrArg Complex.re hn
        let hneg_half_le_neg_two :
            -(1 / 2 : ℝ) ≤ (-2 : ℝ) :=
          Eq.symm hzre ▸ hre_negative ▸ negativeEven_complex_re_le_neg_two n
        (not_lt_of_ge hneg_half_le_neg_two) neg_two_lt_neg_half

/-- `Gammaℝ` is nonzero at every point with real part `-1 / 2`. -/
theorem Gammaℝ_ne_zero_of_re_eq_neg_half
    {z : ℂ}
    (hzre : z.re = -(1 / 2 : ℝ)) :
    Complex.Gammaℝ z ≠ 0 :=
  let hz_ne_zero : z ≠ 0 :=
    fun hz_zero =>
      let hre_zero : z.re = (0 : ℝ) :=
        congrArg Complex.re hz_zero
      let hneg_half_eq_zero : -(1 / 2 : ℝ) = (0 : ℝ) :=
        Eq.symm hzre ▸ hre_zero
      (ne_of_lt (neg_lt_zero.mpr one_half_pos)) hneg_half_eq_zero
  Gammaℝ_ne_zero_of_ne_zero_and_not_negative_even
    hz_ne_zero
    (not_negativeEven_of_re_eq_neg_half hzre)

/-- `Gammaℝ` is nonzero on the autocorrelation left vertical side. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_Gammaℝ_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaLeftPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) ≠ 0 :=
  Gammaℝ_ne_zero_of_re_eq_neg_half
    ((zetaCompletedExplicitFormulaLeftPath_re
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).trans
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily_leftEdge_eq_neg_half f))

/-- `Gammaℝ` is nonzero in the horizontal strip `-1 < Re z < 0`. -/
theorem Gammaℝ_ne_zero_of_neg_one_lt_re_and_re_lt_zero
    {z : ℂ}
    (hzre_low : (-1 : ℝ) < z.re)
    (hzre_high : z.re < (0 : ℝ)) :
    Complex.Gammaℝ z ≠ 0 :=
  let hz_ne_zero : z ≠ 0 :=
    fun hz_zero =>
      let hre_zero : z.re = (0 : ℝ) :=
        congrArg Complex.re hz_zero
      (not_lt_of_ge (le_of_eq hre_zero.symm)) hzre_high
  let hnot_negative :
      ¬ ∃ n : ℕ, z = (-2 : ℂ) * (((n + 1 : ℕ) : ℂ)) :=
    fun hnegative =>
      match hnegative with
      | ⟨n, hn⟩ =>
          let hre_negative :
              z.re =
                (((-2 : ℂ) * (((n + 1 : ℕ) : ℂ))).re : ℝ) :=
            congrArg Complex.re hn
          let hzre_le_neg_two : z.re ≤ (-2 : ℝ) :=
            hre_negative ▸ negativeEven_complex_re_le_neg_two n
          let hneg_two_lt_re : (-2 : ℝ) < z.re :=
            lt_trans
              (neg_lt_neg (show (1 : ℝ) < 2 from one_lt_two))
              hzre_low
          (not_lt_of_ge hzre_le_neg_two) hneg_two_lt_re
  Gammaℝ_ne_zero_of_ne_zero_and_not_negative_even hz_ne_zero hnot_negative

/-- The half-argument of the autocorrelation left path lies in the strip
`-1 < Re z < 0`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_half_re_strip
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    (-1 : ℝ) <
        (zetaCompletedExplicitFormulaLeftPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t / 2).re ∧
      (zetaCompletedExplicitFormulaLeftPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t / 2).re <
        (0 : ℝ) :=
  let z : ℂ :=
    zetaCompletedExplicitFormulaLeftPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t
  let hz_re_neg : z.re < (0 : ℝ) :=
    zetaCompletedExplicitFormula_autocorrelation_leftPath_re_lt_zero f T t
  let hz_re_eq : z.re = -(1 / 2 : ℝ) :=
    (zetaCompletedExplicitFormulaLeftPath_re
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).trans
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily_leftEdge_eq_neg_half f)
  let hneg_two_lt_zre : (-2 : ℝ) < z.re :=
    Eq.symm hz_re_eq ▸ neg_two_lt_neg_half
  let hneg_two_div_two_eq_neg_one :
      (-2 : ℝ) / 2 = (-1 : ℝ) :=
    calc
      (-2 : ℝ) / 2 = -(2 / 2 : ℝ) := neg_div (2 : ℝ) 2
      _ = -(1 : ℝ) := congrArg Neg.neg (div_self (two_ne_zero : (2 : ℝ) ≠ 0))
      _ = (-1 : ℝ) := Eq.refl (-1 : ℝ)
  let hre_div : (z / 2).re = z.re / 2 :=
    RCLike.div_re_ofReal (z := z) (r := (2 : ℝ))
  let hlow_div : (-2 : ℝ) / 2 < z.re / 2 :=
    div_lt_div_of_pos_right hneg_two_lt_zre two_pos
  let hlow : (-1 : ℝ) < (z / 2).re :=
    Eq.symm hre_div ▸ (Eq.symm hneg_two_div_two_eq_neg_one ▸ hlow_div)
  let hhigh_div : z.re / 2 < (0 : ℝ) / 2 :=
    div_lt_div_of_pos_right hz_re_neg two_pos
  let hzero_div : (0 : ℝ) / 2 = (0 : ℝ) :=
    zero_div 2
  let hhigh : (z / 2).re < (0 : ℝ) :=
    hre_div ▸ (hzero_div ▸ hhigh_div)
  And.intro hlow hhigh

/-- `Gammaℝ` is nonzero at the half-argument on the autocorrelation left vertical side. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_half_Gammaℝ_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaLeftPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t / 2) ≠ 0 :=
  let hstrip :=
    zetaCompletedExplicitFormula_autocorrelation_leftPath_half_re_strip f T t
  Gammaℝ_ne_zero_of_neg_one_lt_re_and_re_lt_zero hstrip.1 hstrip.2

/-- The autocorrelation right vertical side never meets `0`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_rightPath_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t ≠ 0 :=
  fun hzero =>
    let hre_zero :
        (zetaCompletedExplicitFormulaRightPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re =
          (0 : ℝ) :=
      congrArg Complex.re hzero
    let hone_lt_zero : (1 : ℝ) < 0 :=
      Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) < x)
        hre_zero
        (zetaCompletedExplicitFormula_autocorrelation_rightPath_one_lt_re f T t)
    (not_lt_of_ge zero_le_one) hone_lt_zero

/-- The autocorrelation right vertical side never meets `1`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_rightPath_ne_one
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t ≠ 1 :=
  fun hone =>
    let hre_one :
        (zetaCompletedExplicitFormulaRightPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re =
          (1 : ℝ) :=
      congrArg Complex.re hone
    let hone_lt_one : (1 : ℝ) < 1 :=
      Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) < x)
        hre_one
        (zetaCompletedExplicitFormula_autocorrelation_rightPath_one_lt_re f T t)
    (lt_irrefl (1 : ℝ)) hone_lt_one

/-- The autocorrelation left vertical side never meets `1`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_ne_one
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t ≠ 1 :=
  fun hone =>
    let hre_one :
        (zetaCompletedExplicitFormulaLeftPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re =
          (1 : ℝ) :=
      congrArg Complex.re hone
    let hone_lt_zero : (1 : ℝ) < 0 :=
      Eq.symm hre_one ▸
        zetaCompletedExplicitFormula_autocorrelation_leftPath_re_lt_zero f T t
    (not_lt_of_ge zero_le_one) hone_lt_zero

/-- The autocorrelation right vertical side avoids every completed-zeta contour singularity. -/
theorem zetaCompletedExplicitFormula_autocorrelation_rightPath_not_singular
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    ¬ explicitFormulaContourSingularPoint
      (zetaCompletedExplicitFormulaRightPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) :=
  fun hsingular =>
    match hsingular with
    | Or.inl hzero =>
        zetaCompletedExplicitFormula_autocorrelation_rightPath_ne_zero f T t hzero
    | Or.inr (Or.inl hone) =>
        zetaCompletedExplicitFormula_autocorrelation_rightPath_ne_one f T t hone
    | Or.inr (Or.inr (Or.inl hgamma)) =>
        zetaCompletedExplicitFormula_autocorrelation_rightPath_Gammaℝ_ne_zero
          f T t hgamma
    | Or.inr (Or.inr (Or.inr (Or.inl hgamma_half))) =>
        zetaCompletedExplicitFormula_autocorrelation_rightPath_half_Gammaℝ_ne_zero
          f T t hgamma_half
    | Or.inr (Or.inr (Or.inr (Or.inr hzeta))) =>
        zetaCompletedExplicitFormula_autocorrelation_rightPath_completedZeta_ne_zero
          f T t hzeta.2.2

/-- The autocorrelation left vertical side avoids every completed-zeta contour singularity. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_not_singular
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    ¬ explicitFormulaContourSingularPoint
      (zetaCompletedExplicitFormulaLeftPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) :=
  fun hsingular =>
    match hsingular with
    | Or.inl hzero =>
        zetaCompletedExplicitFormula_autocorrelation_leftPath_ne_zero f T t hzero
    | Or.inr (Or.inl hone) =>
        zetaCompletedExplicitFormula_autocorrelation_leftPath_ne_one f T t hone
    | Or.inr (Or.inr (Or.inl hgamma)) =>
        zetaCompletedExplicitFormula_autocorrelation_leftPath_Gammaℝ_ne_zero
          f T t hgamma
    | Or.inr (Or.inr (Or.inr (Or.inl hgamma_half))) =>
        zetaCompletedExplicitFormula_autocorrelation_leftPath_half_Gammaℝ_ne_zero
          f T t hgamma_half
    | Or.inr (Or.inr (Or.inr (Or.inr hzeta))) =>
        zetaCompletedExplicitFormula_autocorrelation_leftPath_completedZeta_ne_zero
          f T t hzeta.2.2

/-- The autocorrelation contour family has no vertical-side completed-zeta singularities. -/
theorem zetaCompletedExplicitFormula_autocorrelation_vertical_avoids
    (f : ZetaAdmissibleFunction) (T : ℝ) :
    explicitFormulaContourFamilyVerticalAvoidsSingularBoundary
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) T :=
  fun z hsingular hvertical =>
    match hvertical with
    | Or.inl hright =>
        match hright with
        | ⟨t, hrange, hzpath⟩ =>
            (fun boundaryRange : t ∈ Set.Icc (-T) T =>
              False.elim
                (zetaCompletedExplicitFormula_autocorrelation_rightPath_not_singular f T t
                  (Eq.symm hzpath ▸ hsingular)))
              hrange
    | Or.inr hleft =>
        match hleft with
        | ⟨t, hrange, hzpath⟩ =>
            (fun boundaryRange : t ∈ Set.Icc (-T) T =>
              False.elim
                (zetaCompletedExplicitFormula_autocorrelation_leftPath_not_singular f T t
                  (Eq.symm hzpath ▸ hsingular)))
              hrange

/-- The autocorrelation contour family equipped with vertical regularity. -/
def zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily
    (f : ZetaAdmissibleFunction) :
    ExplicitFormulaVerticallyRegularContourFamily :=
  { toContourFamily := zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    vertical_avoids :=
      zetaCompletedExplicitFormula_autocorrelation_vertical_avoids f }

/-- The regular autocorrelation family projects to the contour family used downstream. -/
theorem zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily_toContourFamily
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily f).toContourFamily =
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f :=
  Eq.refl (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)

end CleanAutocorrelationVerticalRegularity

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
