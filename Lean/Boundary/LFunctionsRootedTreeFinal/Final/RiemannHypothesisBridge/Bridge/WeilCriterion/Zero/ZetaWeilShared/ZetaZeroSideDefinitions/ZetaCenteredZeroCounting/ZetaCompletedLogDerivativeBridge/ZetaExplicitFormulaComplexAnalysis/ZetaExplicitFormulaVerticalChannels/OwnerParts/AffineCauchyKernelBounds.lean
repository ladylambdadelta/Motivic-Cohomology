import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineVerticalKernels

/-!
# Cauchy bounds on fixed affine vertical lines

This file owns the elementary distance estimates for reciprocal pole kernels on
the fixed affine lines used by the vertical-channel inversion proofs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open LSeries ArithmeticFunction
open scoped ArithmeticFunction

namespace ZetaAdmissibleFunction

/-- The right affine line stays at least `F.c` away from the `s = 0` pole in
norm. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_c_le_norm
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    F.c ≤ ‖zetaCompletedExplicitFormulaRightAffineLine F t‖ := by
  let z : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
  have hre : z.re = F.c :=
    zetaCompletedExplicitFormulaRightAffineLine_re F t
  have hle_abs : z.re ≤ Complex.abs z :=
    Complex.re_le_abs z
  have htarget_abs : F.c ≤ Complex.abs z :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ Complex.abs z)
      hre
      hle_abs
  have habs_norm : Complex.abs z = ‖z‖ :=
    (Complex.norm_eq_abs z).symm
  exact Eq.subst
    (motive := fun x : ℝ => F.c ≤ x)
    habs_norm
    htarget_abs

/-- The isolated `s = 0` correction coefficient is uniformly bounded on the
right affine line by the reciprocal of the line's real coordinate. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_zeroPoleCoefficient_norm_le
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    ‖-1 / zetaCompletedExplicitFormulaRightAffineLine F t‖ ≤ 1 / F.c := by
  let z : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
  have hpos : 0 < F.c :=
    F.c_pos
  have hle_norm : F.c ≤ ‖z‖ :=
    zetaCompletedExplicitFormulaRightAffineLine_c_le_norm F t
  have hrecip : 1 / ‖z‖ ≤ 1 / F.c :=
    one_div_le_one_div_of_le hpos hle_norm
  have hneg_div : -1 / z = -(1 / z) :=
    (neg_div z (1 : ℂ)).symm
  have hnorm_neg : ‖-(1 / z)‖ = ‖1 / z‖ :=
    norm_neg (1 / z)
  have hnorm_div : ‖(1 : ℂ) / z‖ = ‖(1 : ℂ)‖ / ‖z‖ :=
    norm_div (1 : ℂ) z
  have hnorm_one : ‖(1 : ℂ)‖ = (1 : ℝ) :=
    norm_one
  have hcoeff : ‖-1 / z‖ = 1 / ‖z‖ := by
    calc
      ‖-1 / z‖ = ‖-(1 / z)‖ := by
        exact congrArg (fun w : ℂ => ‖w‖) hneg_div
      _ = ‖1 / z‖ := by
        exact hnorm_neg
      _ = ‖(1 : ℂ) / z‖ := by
        rfl
      _ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact hnorm_div
      _ = 1 / ‖z‖ := by
        exact congrArg (fun x : ℝ => x / ‖z‖) hnorm_one
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1 / F.c)
    hcoeff.symm
    hrecip

/-- The left affine line stays at least `-(1 - F.c)` away from the `s = 0`
pole in norm.  Since `1 < F.c`, this is the positive distance `F.c - 1`. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_neg_one_sub_c_le_norm
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    -(1 - F.c) ≤ ‖zetaCompletedExplicitFormulaLeftAffineLine F t‖ := by
  let z : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  have hre : z.re = 1 - F.c :=
    zetaCompletedExplicitFormulaLeftAffineLine_re F t
  have habs_re : |z.re| ≤ Complex.abs z :=
    Complex.abs_re_le_abs z
  have hleft_abs : |1 - F.c| = -(1 - F.c) :=
    abs_of_neg F.one_sub_c_neg
  have htarget_abs : -(1 - F.c) ≤ Complex.abs z :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ Complex.abs z)
      hleft_abs
      (Eq.subst
        (motive := fun x : ℝ => |x| ≤ Complex.abs z)
        hre
        habs_re)
  have habs_norm : Complex.abs z = ‖z‖ :=
    (Complex.norm_eq_abs z).symm
  exact Eq.subst
    (motive := fun x : ℝ => -(1 - F.c) ≤ x)
    habs_norm
    htarget_abs

/-- The isolated `s = 0` correction coefficient is uniformly bounded on the
left affine line by the reciprocal of its distance from the pole. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_zeroPoleCoefficient_norm_le
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    ‖-1 / zetaCompletedExplicitFormulaLeftAffineLine F t‖
      ≤ 1 / (-(1 - F.c)) := by
  let z : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  have hpos : 0 < -(1 - F.c) :=
    neg_pos.mpr F.one_sub_c_neg
  have hle_norm : -(1 - F.c) ≤ ‖z‖ :=
    zetaCompletedExplicitFormulaLeftAffineLine_neg_one_sub_c_le_norm F t
  have hrecip : 1 / ‖z‖ ≤ 1 / (-(1 - F.c)) :=
    one_div_le_one_div_of_le hpos hle_norm
  have hneg_div : -1 / z = -(1 / z) :=
    (neg_div z (1 : ℂ)).symm
  have hnorm_neg : ‖-(1 / z)‖ = ‖1 / z‖ :=
    norm_neg (1 / z)
  have hnorm_div : ‖(1 : ℂ) / z‖ = ‖(1 : ℂ)‖ / ‖z‖ :=
    norm_div (1 : ℂ) z
  have hnorm_one : ‖(1 : ℂ)‖ = (1 : ℝ) :=
    norm_one
  have hcoeff : ‖-1 / z‖ = 1 / ‖z‖ := by
    calc
      ‖-1 / z‖ = ‖-(1 / z)‖ := by
        exact congrArg (fun w : ℂ => ‖w‖) hneg_div
      _ = ‖1 / z‖ := by
        exact hnorm_neg
      _ = ‖(1 : ℂ) / z‖ := by
        rfl
      _ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact hnorm_div
      _ = 1 / ‖z‖ := by
        exact congrArg (fun x : ℝ => x / ‖z‖) hnorm_one
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1 / (-(1 - F.c)))
    hcoeff.symm
    hrecip

/-- The right affine line stays at least `F.c - 1` away from the `s = 1`
pole in norm. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_sub_one_c_sub_one_le_norm
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    F.c - 1 ≤ ‖zetaCompletedExplicitFormulaRightAffineLine F t - 1‖ := by
  let z : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
  let w : ℂ := z - 1
  have hzre : z.re = F.c :=
    zetaCompletedExplicitFormulaRightAffineLine_re F t
  have hwre : w.re = F.c - 1 := by
    calc
      w.re = (z - 1).re := by
        rfl
      _ = z.re - (1 : ℂ).re := by
        exact Complex.sub_re z 1
      _ = z.re - (1 : ℝ) := by
        exact congrArg (fun x : ℝ => z.re - x) Complex.one_re
      _ = F.c - (1 : ℝ) := by
        exact congrArg (fun x : ℝ => x - 1) hzre
  have hle_abs : w.re ≤ Complex.abs w :=
    Complex.re_le_abs w
  have htarget_abs : F.c - 1 ≤ Complex.abs w :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ Complex.abs w)
      hwre
      hle_abs
  have habs_norm : Complex.abs w = ‖w‖ :=
    (Complex.norm_eq_abs w).symm
  exact Eq.subst
    (motive := fun x : ℝ => F.c - 1 ≤ x)
    habs_norm
    htarget_abs

/-- The isolated `s = 1` correction coefficient is uniformly bounded on the
right affine line by the reciprocal of the distance `F.c - 1`. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_onePoleCoefficient_norm_le
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    ‖-(1 / (zetaCompletedExplicitFormulaRightAffineLine F t - 1))‖
      ≤ 1 / (F.c - 1) := by
  let w : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t - 1
  have hpos : 0 < F.c - 1 :=
    sub_pos.mpr F.c_gt_one
  have hle_norm : F.c - 1 ≤ ‖w‖ :=
    zetaCompletedExplicitFormulaRightAffineLine_sub_one_c_sub_one_le_norm F t
  have hrecip : 1 / ‖w‖ ≤ 1 / (F.c - 1) :=
    one_div_le_one_div_of_le hpos hle_norm
  have hnorm_neg : ‖-(1 / w)‖ = ‖1 / w‖ :=
    norm_neg (1 / w)
  have hnorm_div : ‖(1 : ℂ) / w‖ = ‖(1 : ℂ)‖ / ‖w‖ :=
    norm_div (1 : ℂ) w
  have hnorm_one : ‖(1 : ℂ)‖ = (1 : ℝ) :=
    norm_one
  have hcoeff : ‖-(1 / w)‖ = 1 / ‖w‖ := by
    calc
      ‖-(1 / w)‖ = ‖1 / w‖ := by
        exact hnorm_neg
      _ = ‖(1 : ℂ) / w‖ := by
        rfl
      _ = ‖(1 : ℂ)‖ / ‖w‖ := by
        exact hnorm_div
      _ = 1 / ‖w‖ := by
        exact congrArg (fun x : ℝ => x / ‖w‖) hnorm_one
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1 / (F.c - 1))
    hcoeff.symm
    hrecip

/-- The left affine line stays at least `-((1 - F.c) - 1)` away from the
`s = 1` pole in norm.  This is the positive distance `F.c`. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_sub_one_neg_re_le_norm
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    -((1 - F.c) - 1) ≤
      ‖zetaCompletedExplicitFormulaLeftAffineLine F t - 1‖ := by
  let z : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  let w : ℂ := z - 1
  have hzre : z.re = 1 - F.c :=
    zetaCompletedExplicitFormulaLeftAffineLine_re F t
  have hwre : w.re = (1 - F.c) - 1 := by
    calc
      w.re = (z - 1).re := by
        rfl
      _ = z.re - (1 : ℂ).re := by
        exact Complex.sub_re z 1
      _ = z.re - (1 : ℝ) := by
        exact congrArg (fun x : ℝ => z.re - x) Complex.one_re
      _ = (1 - F.c) - (1 : ℝ) := by
        exact congrArg (fun x : ℝ => x - 1) hzre
  have hwre_neg : (1 - F.c) - 1 < 0 :=
    sub_neg.mpr
      (lt_trans F.one_sub_c_neg zero_lt_one)
  have habs_re : |w.re| ≤ Complex.abs w :=
    Complex.abs_re_le_abs w
  have hleft_abs : |(1 - F.c) - 1| = -((1 - F.c) - 1) :=
    abs_of_neg hwre_neg
  have htarget_abs : -((1 - F.c) - 1) ≤ Complex.abs w :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ Complex.abs w)
      hleft_abs
      (Eq.subst
        (motive := fun x : ℝ => |x| ≤ Complex.abs w)
        hwre
        habs_re)
  have habs_norm : Complex.abs w = ‖w‖ :=
    (Complex.norm_eq_abs w).symm
  exact Eq.subst
    (motive := fun x : ℝ => -((1 - F.c) - 1) ≤ x)
    habs_norm
    htarget_abs

/-- The isolated `s = 1` correction coefficient is uniformly bounded on the
left affine line by the reciprocal of its distance from the pole. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_onePoleCoefficient_norm_le
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    ‖-(1 / (zetaCompletedExplicitFormulaLeftAffineLine F t - 1))‖
      ≤ 1 / (-((1 - F.c) - 1)) := by
  let w : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t - 1
  have hneg : (1 - F.c) - 1 < 0 :=
    sub_neg.mpr
      (lt_trans F.one_sub_c_neg zero_lt_one)
  have hpos : 0 < -((1 - F.c) - 1) :=
    neg_pos.mpr hneg
  have hle_norm : -((1 - F.c) - 1) ≤ ‖w‖ :=
    zetaCompletedExplicitFormulaLeftAffineLine_sub_one_neg_re_le_norm F t
  have hrecip : 1 / ‖w‖ ≤ 1 / (-((1 - F.c) - 1)) :=
    one_div_le_one_div_of_le hpos hle_norm
  have hnorm_neg : ‖-(1 / w)‖ = ‖1 / w‖ :=
    norm_neg (1 / w)
  have hnorm_div : ‖(1 : ℂ) / w‖ = ‖(1 : ℂ)‖ / ‖w‖ :=
    norm_div (1 : ℂ) w
  have hnorm_one : ‖(1 : ℂ)‖ = (1 : ℝ) :=
    norm_one
  have hcoeff : ‖-(1 / w)‖ = 1 / ‖w‖ := by
    calc
      ‖-(1 / w)‖ = ‖1 / w‖ := by
        exact hnorm_neg
      _ = ‖(1 : ℂ) / w‖ := by
        rfl
      _ = ‖(1 : ℂ)‖ / ‖w‖ := by
        exact hnorm_div
      _ = 1 / ‖w‖ := by
        exact congrArg (fun x : ℝ => x / ‖w‖) hnorm_one
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1 / (-((1 - F.c) - 1)))
    hcoeff.symm
    hrecip

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
