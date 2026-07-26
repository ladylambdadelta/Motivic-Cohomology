import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CenteredZeros.CriticalStrip.Owner

/-!
# Completed prime contour vertical avoidance

This owner part constructs the completed prime contour family and proves its
vertical sides avoid the completed-zeta contour singular set.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The contour family used to compare the finite prime transport remainder with
the horizontal top-minus-bottom contour remainder. -/
def completedPrimeContourTransportFamily : ExplicitFormulaContourFamily where
  c := (1 / 2 : ℝ) + 1
  c_gt_one := by
    have hhalf_pos : (0 : ℝ) < 1 / 2 :=
      real_half_pos_for_contourGeometry
    have hadd :
        (0 : ℝ) + 1 < (1 / 2 : ℝ) + 1 :=
      add_lt_add_right hhalf_pos 1
    exact Eq.subst
      (motive := fun x : ℝ => x < (1 / 2 : ℝ) + 1)
      (zero_add (1 : ℝ))
      hadd
  c_gt_half := by
    exact lt_add_of_pos_right (1 / 2 : ℝ) zero_lt_one
  c_ne_one := by
    intro h
    have hhalf_zero : (1 / 2 : ℝ) = 0 := by
      have hone : (1 / 2 : ℝ) + 1 = 0 + 1 := by
        exact h.trans (zero_add (1 : ℝ)).symm
      exact add_right_cancel hone
    exact (ne_of_gt real_half_pos_for_contourGeometry) hhalf_zero

/-- The completed prime contour right edge is strictly to the right of `1`. -/
theorem completedPrimeContourTransportFamily_rightEdge_gt_one :
    (1 : ℝ) < completedPrimeContourTransportFamily.c := by
  exact lt_add_of_pos_left (1 : ℝ) real_half_pos_for_contourGeometry

/-- The completed prime contour left edge is strictly in the left half-plane. -/
theorem completedPrimeContourTransportFamily_leftEdge_lt_zero :
    1 - completedPrimeContourTransportFamily.c < (0 : ℝ) := by
  have hleft_eq :
      1 - completedPrimeContourTransportFamily.c =
        -(1 / 2 : ℝ) := by
    calc
      1 - completedPrimeContourTransportFamily.c =
          1 - ((1 / 2 : ℝ) + 1) := Eq.refl
            (1 - completedPrimeContourTransportFamily.c)
      _ = 1 - (1 + (1 / 2 : ℝ)) := by
        exact congrArg (fun x : ℝ => 1 - x) (add_comm (1 / 2 : ℝ) 1)
      _ = 1 - 1 - (1 / 2 : ℝ) := by
        exact sub_add_eq_sub_sub 1 1 (1 / 2 : ℝ)
      _ = 0 - (1 / 2 : ℝ) := by
        exact congrArg (fun x : ℝ => x - (1 / 2 : ℝ)) (sub_self 1)
      _ = -(1 / 2 : ℝ) := by
        exact zero_sub (1 / 2 : ℝ)
  exact Eq.symm hleft_eq ▸ neg_lt_zero.mpr real_half_pos_for_contourGeometry

/-- Points on the completed prime contour right vertical side have real part greater
than `1`. -/
theorem completedPrimeContourTransportRightPath_one_lt_re
    (T t : ℝ) :
    (1 : ℝ) <
      (zetaCompletedExplicitFormulaRightPath
        (completedPrimeContourTransportFamily.rectangle T) t).re := by
  exact
    Eq.symm
      (zetaCompletedExplicitFormulaRightPath_re
        (completedPrimeContourTransportFamily.rectangle T) t) ▸
      completedPrimeContourTransportFamily_rightEdge_gt_one

/-- Points on the completed prime contour left vertical side lie in the left half-plane. -/
theorem completedPrimeContourTransportLeftPath_re_lt_zero
    (T t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath
        (completedPrimeContourTransportFamily.rectangle T) t).re <
      (0 : ℝ) := by
  exact
    Eq.symm
      (zetaCompletedExplicitFormulaLeftPath_re
        (completedPrimeContourTransportFamily.rectangle T) t) ▸
      completedPrimeContourTransportFamily_leftEdge_lt_zero

/-- The completed zeta factor is nonzero on the completed prime contour right side. -/
theorem completedPrimeContourTransportRightPath_completedZeta_ne_zero
    (T t : ℝ) :
    completedRiemannZeta
      (zetaCompletedExplicitFormulaRightPath
        (completedPrimeContourTransportFamily.rectangle T) t) ≠ 0 :=
  completedRiemannZeta_ne_zero_of_one_lt_re
    (zetaCompletedExplicitFormulaRightPath
      (completedPrimeContourTransportFamily.rectangle T) t)
    (completedPrimeContourTransportRightPath_one_lt_re T t)

/-- The completed zeta factor is nonzero on the completed prime contour left side. -/
theorem completedPrimeContourTransportLeftPath_completedZeta_ne_zero
    (T t : ℝ) :
    completedRiemannZeta
      (zetaCompletedExplicitFormulaLeftPath
        (completedPrimeContourTransportFamily.rectangle T) t) ≠ 0 :=
  completedRiemannZeta_ne_zero_of_re_lt_zero
    (zetaCompletedExplicitFormulaLeftPath
      (completedPrimeContourTransportFamily.rectangle T) t)
    (completedPrimeContourTransportLeftPath_re_lt_zero T t)

/-- `Gammaℝ` is nonzero on the completed prime contour right side. -/
theorem completedPrimeContourTransportRightPath_Gammaℝ_ne_zero
    (T t : ℝ) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaRightPath
        (completedPrimeContourTransportFamily.rectangle T) t) ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos
    (zetaCompletedExplicitFormulaRightPath
      (completedPrimeContourTransportFamily.rectangle T) t)
    (lt_trans zero_lt_one
      (completedPrimeContourTransportRightPath_one_lt_re T t))

/-- `Gammaℝ` is nonzero at the half-argument on the completed prime contour right side. -/
theorem completedPrimeContourTransportRightPath_half_Gammaℝ_ne_zero
    (T t : ℝ) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaRightPath
        (completedPrimeContourTransportFamily.rectangle T) t / 2) ≠ 0 := by
  have hre_pos :
      0 <
        (zetaCompletedExplicitFormulaRightPath
          (completedPrimeContourTransportFamily.rectangle T) t).re / 2 :=
    div_pos
      (lt_trans zero_lt_one
        (completedPrimeContourTransportRightPath_one_lt_re T t))
      zero_lt_two
  have hre :
      (zetaCompletedExplicitFormulaRightPath
          (completedPrimeContourTransportFamily.rectangle T) t / 2).re =
        (zetaCompletedExplicitFormulaRightPath
          (completedPrimeContourTransportFamily.rectangle T) t).re / 2 := by
    exact RCLike.div_re_ofReal
      (z :=
        zetaCompletedExplicitFormulaRightPath
          (completedPrimeContourTransportFamily.rectangle T) t)
      (r := (2 : ℝ))
  exact Gammaℝ_ne_zero_of_re_pos
    (zetaCompletedExplicitFormulaRightPath
      (completedPrimeContourTransportFamily.rectangle T) t / 2)
    (Eq.symm hre ▸ hre_pos)

/-- The completed prime contour left side never meets `0`. -/
theorem completedPrimeContourTransportLeftPath_ne_zero
    (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath
      (completedPrimeContourTransportFamily.rectangle T) t ≠ 0 := by
  intro hzero
  have hre_zero :
      (zetaCompletedExplicitFormulaLeftPath
        (completedPrimeContourTransportFamily.rectangle T) t).re =
        (0 : ℝ) := by
    exact congrArg Complex.re hzero
  have hre_lt_zero :
      (zetaCompletedExplicitFormulaLeftPath
          (completedPrimeContourTransportFamily.rectangle T) t).re <
        (0 : ℝ) :=
    completedPrimeContourTransportLeftPath_re_lt_zero T t
  exact (not_lt_of_ge (le_of_eq hre_zero.symm)) hre_lt_zero

/-- The completed prime contour right side never meets `0`. -/
theorem completedPrimeContourTransportRightPath_ne_zero
    (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath
      (completedPrimeContourTransportFamily.rectangle T) t ≠ 0 := by
  intro hzero
  have hre_zero :
      (zetaCompletedExplicitFormulaRightPath
        (completedPrimeContourTransportFamily.rectangle T) t).re =
        (0 : ℝ) :=
    congrArg Complex.re hzero
  have hone_lt_zero : (1 : ℝ) < 0 :=
    Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) < x)
      hre_zero
      (completedPrimeContourTransportRightPath_one_lt_re T t)
  exact (not_lt_of_ge zero_le_one) hone_lt_zero

/-- The completed prime contour right side never meets `1`. -/
theorem completedPrimeContourTransportRightPath_ne_one
    (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath
      (completedPrimeContourTransportFamily.rectangle T) t ≠ 1 := by
  intro hone
  have hre_one :
      (zetaCompletedExplicitFormulaRightPath
        (completedPrimeContourTransportFamily.rectangle T) t).re =
        (1 : ℝ) :=
    congrArg Complex.re hone
  have hone_lt_one : (1 : ℝ) < 1 :=
    Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) < x)
      hre_one
      (completedPrimeContourTransportRightPath_one_lt_re T t)
  exact (lt_irrefl (1 : ℝ)) hone_lt_one

/-- The completed prime contour left side never meets `1`. -/
theorem completedPrimeContourTransportLeftPath_ne_one
    (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath
      (completedPrimeContourTransportFamily.rectangle T) t ≠ 1 := by
  intro hone
  have hre_one :
      (zetaCompletedExplicitFormulaLeftPath
        (completedPrimeContourTransportFamily.rectangle T) t).re =
        (1 : ℝ) :=
    congrArg Complex.re hone
  have hone_lt_zero : (1 : ℝ) < 0 :=
    Eq.symm hre_one ▸
      completedPrimeContourTransportLeftPath_re_lt_zero T t
  exact (not_lt_of_ge zero_le_one) hone_lt_zero

/-- Negative even real points have real coordinate at most `-2`. -/
theorem completedPrimeContourTransport_negativeEven_complex_re_le_neg_two
    (n : ℕ) :
    (((-2 : ℂ) * (((n + 1 : ℕ) : ℂ))).re : ℝ) ≤ (-2 : ℝ) := by
  have hone_le_nat : (1 : ℕ) ≤ n + 1 :=
    Nat.succ_le_succ (Nat.zero_le n)
  have hone_le_real : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ ((n + 1 : ℕ) : ℝ))
      Nat.cast_one
      (Nat.cast_le.mpr hone_le_nat)
  have hneg_two_nonpos : (-2 : ℝ) ≤ 0 :=
    neg_nonpos.mpr (le_of_lt zero_lt_two)
  have hmul :
      (-2 : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ (-2 : ℝ) * 1 :=
    mul_le_mul_of_nonpos_left hone_le_real hneg_two_nonpos
  have hright :
      (-2 : ℝ) * 1 = (-2 : ℝ) :=
    mul_one (-2 : ℝ)
  have hre :
      (((-2 : ℂ) * (((n + 1 : ℕ) : ℂ))).re : ℝ) =
        (-2 : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    have hnegCast : (-2 : ℂ) = ((-2 : ℝ) : ℂ) :=
      Complex.ext
        (Eq.trans
          (Complex.neg_re (2 : ℂ))
          (congrArg Neg.neg (Complex.natCast_re 2)))
        (Eq.trans
          (Complex.neg_im (2 : ℂ))
          (Eq.trans
            (congrArg Neg.neg (Complex.natCast_im 2))
            (neg_zero : -(0 : ℝ) = 0)))
    exact
      Eq.trans
        (congrArg
          (fun z : ℂ => (z * (((n + 1 : ℕ) : ℂ))).re)
          hnegCast)
        (Eq.trans
          (Complex.re_ofReal_mul (-2 : ℝ) (((n + 1 : ℕ) : ℂ)))
          (congrArg
            (fun value : ℝ => (-2 : ℝ) * value)
            (Complex.natCast_re (n + 1))))
  exact Eq.symm hre ▸ hmul.trans (le_of_eq hright)

/-- The real number `-2` lies strictly to the left of `-1/2`. -/
theorem completedPrimeContourTransport_neg_two_lt_neg_half :
    (-2 : ℝ) < -(1 / 2 : ℝ) :=
  lt_trans
    (neg_lt_neg (show (1 : ℝ) < 2 from one_lt_two))
    (neg_lt_neg one_half_lt_one)

/-- A point with real part `-1/2` is not a negative nonzero even point. -/
theorem completedPrimeContourTransport_not_negativeEven_of_re_eq_neg_half
    {z : ℂ}
    (hzre : z.re = -(1 / 2 : ℝ)) :
    ¬ ∃ n : ℕ, z = (-2 : ℂ) * (((n + 1 : ℕ) : ℂ)) := by
  intro hnegative
  match hnegative with
  | ⟨n, hn⟩ =>
      have hre_negative :
          z.re =
            (((-2 : ℂ) * (((n + 1 : ℕ) : ℂ))).re : ℝ) :=
        congrArg Complex.re hn
      have hneg_half_le_neg_two :
          -(1 / 2 : ℝ) ≤ (-2 : ℝ) := by
        exact
          Eq.symm hzre ▸
            hre_negative ▸
              completedPrimeContourTransport_negativeEven_complex_re_le_neg_two n
      exact
        (not_lt_of_ge hneg_half_le_neg_two)
          completedPrimeContourTransport_neg_two_lt_neg_half

/-- `Gammaℝ` is nonzero at every point with real part `-1/2`. -/
theorem completedPrimeContourTransport_Gammaℝ_ne_zero_of_re_eq_neg_half
    {z : ℂ}
    (hzre : z.re = -(1 / 2 : ℝ)) :
    Complex.Gammaℝ z ≠ 0 := by
  have hz_ne_zero : z ≠ 0 := by
    intro hz_zero
    have hre_zero : z.re = (0 : ℝ) :=
      congrArg Complex.re hz_zero
    have hneg_half_eq_zero : -(1 / 2 : ℝ) = (0 : ℝ) :=
      Eq.symm hzre ▸ hre_zero
    exact
      (ne_of_lt (neg_lt_zero.mpr real_half_pos_for_contourGeometry))
        hneg_half_eq_zero
  exact
    Gammaℝ_ne_zero_of_ne_zero_and_not_negative_even
      hz_ne_zero
      (completedPrimeContourTransport_not_negativeEven_of_re_eq_neg_half hzre)

/-- `Gammaℝ` is nonzero on the completed prime contour left side. -/
theorem completedPrimeContourTransportLeftPath_Gammaℝ_ne_zero
    (T t : ℝ) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaLeftPath
        (completedPrimeContourTransportFamily.rectangle T) t) ≠ 0 := by
  have hre :
      (zetaCompletedExplicitFormulaLeftPath
          (completedPrimeContourTransportFamily.rectangle T) t).re =
        -(1 / 2 : ℝ) := by
    have hpath :=
      zetaCompletedExplicitFormulaLeftPath_re
        (completedPrimeContourTransportFamily.rectangle T) t
    have hedge :
        1 - completedPrimeContourTransportFamily.c =
          -(1 / 2 : ℝ) := by
      calc
        1 - completedPrimeContourTransportFamily.c =
            1 - ((1 / 2 : ℝ) + 1) := Eq.refl
              (1 - completedPrimeContourTransportFamily.c)
        _ = 1 - (1 + (1 / 2 : ℝ)) := by
          exact congrArg (fun x : ℝ => 1 - x) (add_comm (1 / 2 : ℝ) 1)
        _ = 1 - 1 - (1 / 2 : ℝ) := by
          exact sub_add_eq_sub_sub 1 1 (1 / 2 : ℝ)
        _ = 0 - (1 / 2 : ℝ) := by
          exact congrArg (fun x : ℝ => x - (1 / 2 : ℝ)) (sub_self 1)
        _ = -(1 / 2 : ℝ) := by
          exact zero_sub (1 / 2 : ℝ)
    exact hpath.trans hedge
  exact completedPrimeContourTransport_Gammaℝ_ne_zero_of_re_eq_neg_half hre

/-- `Gammaℝ` is nonzero in the horizontal strip `-1 < Re z < 0`. -/
theorem completedPrimeContourTransport_Gammaℝ_ne_zero_of_neg_one_lt_re_and_re_lt_zero
    {z : ℂ}
    (hzre_low : (-1 : ℝ) < z.re)
    (hzre_high : z.re < (0 : ℝ)) :
    Complex.Gammaℝ z ≠ 0 := by
  have hz_ne_zero : z ≠ 0 := by
    intro hz_zero
    have hre_zero : z.re = (0 : ℝ) :=
      congrArg Complex.re hz_zero
    exact (not_lt_of_ge (le_of_eq hre_zero.symm)) hzre_high
  have hnot_negative :
      ¬ ∃ n : ℕ, z = (-2 : ℂ) * (((n + 1 : ℕ) : ℂ)) := by
    intro hnegative
    match hnegative with
    | ⟨n, hn⟩ =>
        have hre_negative :
            z.re =
              (((-2 : ℂ) * (((n + 1 : ℕ) : ℂ))).re : ℝ) :=
          congrArg Complex.re hn
        have hzre_le_neg_two : z.re ≤ (-2 : ℝ) :=
          hre_negative ▸
            completedPrimeContourTransport_negativeEven_complex_re_le_neg_two n
        have hneg_two_lt_re : (-2 : ℝ) < z.re :=
          lt_trans
            (neg_lt_neg (show (1 : ℝ) < 2 from one_lt_two))
            hzre_low
        exact (not_lt_of_ge hzre_le_neg_two) hneg_two_lt_re
  exact Gammaℝ_ne_zero_of_ne_zero_and_not_negative_even hz_ne_zero hnot_negative

/-- The half-argument of the completed prime contour left side lies in `-1 < Re z < 0`. -/
theorem completedPrimeContourTransportLeftPath_half_re_strip
    (T t : ℝ) :
    (-1 : ℝ) <
        (zetaCompletedExplicitFormulaLeftPath
          (completedPrimeContourTransportFamily.rectangle T) t / 2).re ∧
      (zetaCompletedExplicitFormulaLeftPath
          (completedPrimeContourTransportFamily.rectangle T) t / 2).re <
        (0 : ℝ) := by
  let z : ℂ :=
    zetaCompletedExplicitFormulaLeftPath
      (completedPrimeContourTransportFamily.rectangle T) t
  have hz_re_neg :
      z.re < (0 : ℝ) :=
    completedPrimeContourTransportLeftPath_re_lt_zero T t
  have hz_re_eq :
      z.re = -(1 / 2 : ℝ) := by
    have hpath :=
      zetaCompletedExplicitFormulaLeftPath_re
        (completedPrimeContourTransportFamily.rectangle T) t
    have hedge :
        1 - completedPrimeContourTransportFamily.c =
          -(1 / 2 : ℝ) := by
      calc
        1 - completedPrimeContourTransportFamily.c =
            1 - ((1 / 2 : ℝ) + 1) := Eq.refl
              (1 - completedPrimeContourTransportFamily.c)
        _ = 1 - (1 + (1 / 2 : ℝ)) := by
          exact congrArg (fun x : ℝ => 1 - x) (add_comm (1 / 2 : ℝ) 1)
        _ = 1 - 1 - (1 / 2 : ℝ) := by
          exact sub_add_eq_sub_sub 1 1 (1 / 2 : ℝ)
        _ = 0 - (1 / 2 : ℝ) := by
          exact congrArg (fun x : ℝ => x - (1 / 2 : ℝ)) (sub_self 1)
        _ = -(1 / 2 : ℝ) := by
          exact zero_sub (1 / 2 : ℝ)
    exact hpath.trans hedge
  have hneg_two_lt_zre : (-2 : ℝ) < z.re :=
    Eq.symm hz_re_eq ▸ completedPrimeContourTransport_neg_two_lt_neg_half
  have hneg_two_div_two_eq_neg_one :
      (-2 : ℝ) / 2 = (-1 : ℝ) := by
    calc
      (-2 : ℝ) / 2 = -(2 / 2 : ℝ) := by
        exact neg_div (2 : ℝ) 2
      _ = -(1 : ℝ) := by
        exact congrArg Neg.neg (div_self (two_ne_zero : (2 : ℝ) ≠ 0))
      _ = (-1 : ℝ) := Eq.refl (-1 : ℝ)
  have hre_div :
      (z / 2).re = z.re / 2 :=
    RCLike.div_re_ofReal (z := z) (r := (2 : ℝ))
  have hlow_div :
      (-2 : ℝ) / 2 < z.re / 2 :=
    div_lt_div_of_pos_right hneg_two_lt_zre zero_lt_two
  have hlow :
      (-1 : ℝ) < (z / 2).re :=
    Eq.symm hre_div ▸
      (Eq.symm hneg_two_div_two_eq_neg_one ▸ hlow_div)
  have hhigh_div :
      z.re / 2 < (0 : ℝ) / 2 :=
    div_lt_div_of_pos_right hz_re_neg zero_lt_two
  have hzero_div :
      (0 : ℝ) / 2 = (0 : ℝ) :=
    zero_div 2
  have hhigh :
      (z / 2).re < (0 : ℝ) :=
    hre_div ▸ (hzero_div ▸ hhigh_div)
  exact And.intro hlow hhigh

/-- `Gammaℝ` is nonzero at the half-argument on the completed prime contour left side. -/
theorem completedPrimeContourTransportLeftPath_half_Gammaℝ_ne_zero
    (T t : ℝ) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaLeftPath
        (completedPrimeContourTransportFamily.rectangle T) t / 2) ≠ 0 := by
  have hstrip :=
    completedPrimeContourTransportLeftPath_half_re_strip T t
  exact
    completedPrimeContourTransport_Gammaℝ_ne_zero_of_neg_one_lt_re_and_re_lt_zero
      hstrip.1 hstrip.2

/-- The right vertical side of the completed prime contour-transport family avoids the
completed-zeta contour singular set. -/
theorem completedPrimeContourTransportRightPath_not_singular_owner
    (T t : ℝ) :
    ¬ explicitFormulaContourSingularPoint
      (zetaCompletedExplicitFormulaRightPath
        (completedPrimeContourTransportFamily.rectangle T) t) := by
  intro hsingular
  match hsingular with
  | Or.inl hzero =>
      exact completedPrimeContourTransportRightPath_ne_zero T t hzero
  | Or.inr (Or.inl hone) =>
      exact completedPrimeContourTransportRightPath_ne_one T t hone
  | Or.inr (Or.inr (Or.inl hgamma)) =>
      exact completedPrimeContourTransportRightPath_Gammaℝ_ne_zero T t hgamma
  | Or.inr (Or.inr (Or.inr (Or.inl hgamma_half))) =>
      exact completedPrimeContourTransportRightPath_half_Gammaℝ_ne_zero T t hgamma_half
  | Or.inr (Or.inr (Or.inr (Or.inr hzeta))) =>
      exact completedPrimeContourTransportRightPath_completedZeta_ne_zero T t hzeta.2.2

/-- The left vertical side of the completed prime contour-transport family avoids the
completed-zeta contour singular set. -/
theorem completedPrimeContourTransportLeftPath_not_singular_owner
    (T t : ℝ) :
    ¬ explicitFormulaContourSingularPoint
      (zetaCompletedExplicitFormulaLeftPath
        (completedPrimeContourTransportFamily.rectangle T) t) := by
  intro hsingular
  match hsingular with
  | Or.inl hzero =>
      exact completedPrimeContourTransportLeftPath_ne_zero T t hzero
  | Or.inr (Or.inl hone) =>
      exact completedPrimeContourTransportLeftPath_ne_one T t hone
  | Or.inr (Or.inr (Or.inl hgamma)) =>
      exact completedPrimeContourTransportLeftPath_Gammaℝ_ne_zero T t hgamma
  | Or.inr (Or.inr (Or.inr (Or.inl hgamma_half))) =>
      exact completedPrimeContourTransportLeftPath_half_Gammaℝ_ne_zero T t hgamma_half
  | Or.inr (Or.inr (Or.inr (Or.inr hzeta))) =>
      exact completedPrimeContourTransportLeftPath_completedZeta_ne_zero T t hzeta.2.2

/-- Vertical sides of the completed prime contour-transport family avoid the completed-zeta
contour singular set. -/
theorem completedPrimeContourTransportVerticalAvoids_owner
    (T : ℝ) :
    explicitFormulaContourFamilyVerticalAvoidsSingularBoundary
      completedPrimeContourTransportFamily T := by
  intro z hsingular hvertical
  match hvertical with
  | Or.inl hright =>
      match hright with
      | ⟨t, hinterval, hzpath⟩ =>
          exact
            completedPrimeContourTransportRightPath_not_singular_owner T t
              (Eq.symm hzpath ▸ hsingular)
  | Or.inr hleft =>
      match hleft with
      | ⟨t, hinterval, hzpath⟩ =>
          exact
            completedPrimeContourTransportLeftPath_not_singular_owner T t
              (Eq.symm hzpath ▸ hsingular)

/-- The completed prime contour-transport family with its vertical-side regularity. -/
def completedPrimeContourTransportVerticallyRegularFamily_owner :
    ExplicitFormulaVerticallyRegularContourFamily where
  toContourFamily := completedPrimeContourTransportFamily
  vertical_avoids := completedPrimeContourTransportVerticalAvoids_owner

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
