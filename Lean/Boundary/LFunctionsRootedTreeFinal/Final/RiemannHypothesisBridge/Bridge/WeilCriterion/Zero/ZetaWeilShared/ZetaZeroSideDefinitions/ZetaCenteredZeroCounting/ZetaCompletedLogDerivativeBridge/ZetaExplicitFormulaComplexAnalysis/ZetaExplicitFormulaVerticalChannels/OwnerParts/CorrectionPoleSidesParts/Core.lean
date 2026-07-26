import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.BasicChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleBoundaryPrimitives

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Pointwise normalization of the correction vertical channel to the explicit two-pole
kernel.  The sign here is inherited from
`explicitFormulaCorrectionLogDerivative_eq_poleCorrection`; the left side is subtracted
with the same orientation convention as the other vertical channels. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_poleCorrectionVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
            1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
              1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) := by
  have hright :
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
        (fun t : ℝ =>
          (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
              1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
    funext t
    exact congrArg
      (fun z : ℂ =>
        z * zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (explicitFormulaCorrectionLogDerivative_eq_poleCorrection
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t))
  have hleft :
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
        (fun t : ℝ =>
          (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
              1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
    funext t
    exact congrArg
      (fun z : ℂ =>
        z * zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (explicitFormulaCorrectionLogDerivative_eq_poleCorrection
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t))
  exact congrArg₂ HSub.hSub
    (congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      hright)
    (congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      hleft)

/-- The corrected contribution is the centered two-pole coefficient applied to the
test transform at the basepoint. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_eq_centeredPolePhi
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionContribution f =
      (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) *
        zetaCompletedExplicitFormulaPhi f 0 := by
  exact zetaCompletedExplicitFormulaCorrectionContribution_eq f

/-- In the pole-enclosing geometry, the unordered horizontal span is the
left-to-right closed interval used by a standard rectangle boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionPoleHorizontal_uIcc_eq_Icc
    (F : ExplicitFormulaContourFamily) :
    Set.uIcc F.c (1 - F.c) = Set.Icc (1 - F.c) F.c := by
  have hleft_le_right : 1 - F.c ≤ F.c :=
    le_of_lt
      (lt_trans F.one_sub_c_neg F.c_pos)
  exact Set.uIcc_of_ge hleft_le_right

/-- The tangent-weighted isolated `s = 0` rectangle boundary integral unfolds to
its four oriented sides. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral f F T := by
  exact Eq.refl _
/-- The right-face `s = 0` correction integrand is the isolated kernel evaluated
on the right path. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) := by
  exact Eq.refl _
/-- The left-face `s = 0` correction integrand is the isolated kernel evaluated
on the left path. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) := by
  exact Eq.refl _
/-- The top-edge `s = 0` correction integrand is the isolated kernel evaluated
on the top path. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    (-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) := by
  exact Eq.refl _
/-- The bottom-edge `s = 0` correction integrand is the isolated kernel evaluated
on the bottom path. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    (-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) := by
  exact Eq.refl _
/-- The tangent-weighted right-side `s = 0` integral is the old real-side
integral multiplied by the vertical tangent `I`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral_eq_vertical_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T * Complex.I := by
  exact
    integral_smul_const
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t))
      Complex.I

/-- The tangent-weighted left-side `s = 0` integral is the old real-side
integral multiplied by the vertical tangent `I`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral_eq_vertical_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T * Complex.I := by
  exact
    integral_smul_const
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t))
      Complex.I

/-- The tangent-weighted top `s = 0` side is definitionally the old top
horizontal integral. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral_eq_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T := by
  exact Eq.refl _
/-- The tangent-weighted bottom `s = 0` side is definitionally the old bottom
horizontal integral before the final boundary orientation sign is applied. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral_eq_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T := by
  exact Eq.refl _
/-- The `s = 0` finite-rectangle single-pole boundary integral unfolds to its four
oriented sides. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T := by
  exact Eq.refl _
/-- The `s = 1` finite-rectangle single-pole boundary integral unfolds to its four
oriented sides. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T := by
  exact Eq.refl _
/-- The scheduled `s = 0` single-pole rectangle boundary integral is the four-side
identity at the scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
            f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
              f F (h.height_schedule.height u) := by
  exact Eq.refl _
/-- The scheduled `s = 1` single-pole rectangle boundary integral is the four-side
identity at the scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
            f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
              f F (h.height_schedule.height u) := by
  exact Eq.refl _
/-- Additive algebra for isolating the left side from an oriented rectangle boundary
identity `C = R - L + H`. -/
theorem leftSide_eq_right_add_horizontal_sub_boundary_of_boundary_eq
    (R L H C : ℂ) (hC : C = R - L + H) :
    L = R + H - C := by
  have hsum : L + C = R + H := by
    calc
      L + C = L + (R - L + H) := by
        exact congrArg (fun x : ℂ => L + x) hC
      _ = L + ((R + -L) + H) := by
        exact congrArg (fun x : ℂ => L + (x + H)) (sub_eq_add_neg R L)
      _ = (L + (R + -L)) + H := by
        exact (add_assoc L (R + -L) H).symm
      _ = ((L + R) + -L) + H := by
        exact congrArg (fun x : ℂ => x + H) (add_assoc L R (-L)).symm
      _ = ((R + L) + -L) + H := by
        exact congrArg (fun x : ℂ => (x + -L) + H) (add_comm L R)
      _ = (R + (L + -L)) + H := by
        exact congrArg (fun x : ℂ => x + H) (add_assoc R L (-L))
      _ = (R + 0) + H := by
        exact congrArg (fun x : ℂ => (R + x) + H) (add_neg_cancel L)
      _ = R + H := by
        exact congrArg (fun x : ℂ => x + H) (add_zero R)
  exact
    eq_sub_iff_add_eq.mpr hsum

/-- Additive algebra for isolating the right side from an oriented rectangle boundary
identity `C = R - L + H`. -/
theorem rightSide_eq_left_sub_horizontal_add_boundary_of_boundary_eq
    (R L H C : ℂ) (hC : C = R - L + H) :
    R = L - H + C := by
  have hsum : R + H = C + L := by
    calc
      R + H = R + (0 + H) := by
        exact congrArg (fun x : ℂ => R + x) (zero_add H).symm
      _ = R + (L + -L + H) := by
        exact congrArg (fun x : ℂ => R + (x + H)) (add_neg_cancel L).symm
      _ = R + (L + (-L + H)) := by
        exact congrArg (fun x : ℂ => R + x) (add_assoc L (-L) H)
      _ = (R + L) + (-L + H) := by
        exact (add_assoc R L (-L + H)).symm
      _ = (L + R) + (-L + H) := by
        exact congrArg (fun x : ℂ => x + (-L + H)) (add_comm R L)
      _ = L + (R + (-L + H)) := by
        exact add_assoc L R (-L + H)
      _ = L + ((R + -L) + H) := by
        exact congrArg (fun x : ℂ => L + x) (add_assoc R (-L) H).symm
      _ = L + (R - L + H) := by
        exact congrArg (fun x : ℂ => L + (x + H)) (sub_eq_add_neg R L).symm
      _ = L + C := by
        exact congrArg (fun x : ℂ => L + x) hC.symm
      _ = C + L := by
        exact add_comm L C
  have hright : R = C + L - H := by
    exact eq_sub_iff_add_eq.mpr hsum
  calc
    R = C + L - H := by
      exact hright
    _ = (C + L) + -H := by
      exact sub_eq_add_neg (C + L) H
    _ = (L + C) + -H := by
      exact congrArg (fun x : ℂ => x + -H) (add_comm C L)
    _ = L + (C + -H) := by
      exact add_assoc L C (-H)
    _ = L + (-H + C) := by
      exact congrArg (fun x : ℂ => L + x) (add_comm C (-H))
    _ = (L + -H) + C := by
      exact (add_assoc L (-H) C).symm
    _ = L - H + C := by
      exact congrArg (fun x : ℂ => x + C) (sub_eq_add_neg L H).symm

/-- The right vertical side never meets the pole at `0`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPath_ne_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t ≠ 0 := by
  have hre :
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re =
        (F.rectangle T).c :=
    zetaCompletedExplicitFormulaRightPath_re (F.rectangle T) t
  have hpos : 0 < (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re :=
    Eq.symm hre ▸ F.c_pos
  exact fun hzero =>
    have hre_zero : (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re = 0 :=
      congrArg Complex.re hzero
    (ne_of_gt hpos) hre_zero

/-- The right vertical side lies strictly to the right of the pole at `1`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPath_re_gt_one
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    1 < (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re := by
  have hre :
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re =
        (F.rectangle T).c :=
    zetaCompletedExplicitFormulaRightPath_re (F.rectangle T) t
  exact Eq.symm hre ▸ F.c_gt_one

/-- The right vertical side never meets the pole at `1`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPath_sub_one_ne_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 ≠ 0 := by
  have hgt :
      1 < (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re :=
    zetaCompletedExplicitFormulaCorrectionRightPath_re_gt_one F T t
  exact fun hzero =>
    have hone : zetaCompletedExplicitFormulaRightPath (F.rectangle T) t = 1 :=
      sub_eq_zero.mp hzero
    have hre_one : (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re = 1 :=
      congrArg Complex.re hone
    (ne_of_gt hgt) hre_one

/-- The left vertical side never meets the pole at `0`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_ne_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t ≠ 0 := by
  exact fun hzero =>
    have hre :
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re =
          1 - F.c :=
      zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
    have hre_zero : (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re = 0 :=
      congrArg Complex.re hzero
    have hsub_zero : 1 - F.c = 0 :=
      hre.symm.trans hre_zero
    have hc_one : F.c = 1 :=
      (sub_eq_zero.mp hsub_zero).symm
    F.c_ne_one hc_one

/-- The left vertical side lies strictly to the left of the pole at `0`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_re_lt_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re < 0 := by
  have hre :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re =
        1 - (F.rectangle T).c :=
    zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
  have hleft : 1 - F.c < 0 :=
    F.one_sub_c_neg
  exact Eq.symm hre ▸ hleft

/-- On the left vertical face, the absolute real coordinate is the fixed
distance from the `s = 0` pole to the line. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_abs_re_eq_c_sub_one
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    |(zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re| =
      F.c - 1 := by
  let z : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
  have hre : z.re = 1 - F.c :=
    zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
  have hneg : z.re < 0 :=
    zetaCompletedExplicitFormulaCorrectionLeftPath_re_lt_zero F T t
  have habs : |z.re| = -z.re :=
    abs_of_neg hneg
  have hneg_re : -z.re = F.c - 1 := by
    calc
      -z.re = -(1 - F.c) := by
        exact congrArg Neg.neg hre
      _ = F.c - 1 := by
        exact neg_sub 1 F.c
  exact Eq.trans habs hneg_re

/-- The left vertical face stays at least `F.c - 1` away from the `s = 0`
correction pole in norm. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_c_sub_one_le_norm
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    F.c - 1 ≤ ‖zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t‖ := by
  let z : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
  have habs_re :
      |z.re| = F.c - 1 :=
    zetaCompletedExplicitFormulaCorrectionLeftPath_abs_re_eq_c_sub_one F T t
  have hle_abs : |z.re| ≤ Complex.abs z :=
    Complex.abs_re_le_abs z
  have hle_abs_target : F.c - 1 ≤ Complex.abs z :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ Complex.abs z)
      habs_re
      hle_abs
  have habs_norm : Complex.abs z = ‖z‖ :=
    (Complex.norm_eq_abs z).symm
  exact Eq.subst
    (motive := fun x : ℝ => F.c - 1 ≤ x)
    habs_norm
    hle_abs_target

/-- The isolated `s = 0` correction coefficient is uniformly bounded on the
left vertical face by the reciprocal of the line's distance from the pole. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleCoefficient_norm_le
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    ‖-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t‖
      ≤ 1 / (F.c - 1) := by
  let z : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
  have hpos : 0 < F.c - 1 :=
    sub_pos.mpr F.c_gt_one
  have hle_norm : F.c - 1 ≤ ‖z‖ :=
    zetaCompletedExplicitFormulaCorrectionLeftPath_c_sub_one_le_norm F T t
  have hrecip : 1 / ‖z‖ ≤ 1 / (F.c - 1) :=
    one_div_le_one_div_of_le hpos hle_norm
  have hneg_div : -1 / z = -(1 / z) :=
    neg_div z (1 : ℂ)
  have hnorm_neg : ‖-(1 / z)‖ = ‖1 / z‖ :=
    norm_neg (1 / z)
  have hnorm_div : ‖(1 : ℂ) / z‖ = ‖(1 : ℂ)‖ / ‖z‖ :=
    norm_div (1 : ℂ) z
  have hnorm_one : ‖(1 : ℂ)‖ = (1 : ℝ) :=
    norm_one
  have hcoeff :
      ‖-1 / z‖ = 1 / ‖z‖ := by
    calc
      ‖-1 / z‖ = ‖-(1 / z)‖ := by
        exact congrArg (fun w : ℂ => ‖w‖) hneg_div
      _ = ‖1 / z‖ := by
        exact hnorm_neg
      _ = ‖(1 : ℂ) / z‖ := by
        exact Eq.refl _
      _ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact hnorm_div
      _ = 1 / ‖z‖ := by
        exact congrArg (fun x : ℝ => x / ‖z‖) hnorm_one
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1 / (F.c - 1))
    hcoeff.symm
    hrecip

/-- The shifted left vertical face lies in the fixed real strip used for the
completed transform estimates. -/
theorem zetaCompletedExplicitFormulaLeftPath_shift_re_mem_strip_bounds
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    min F.c (1 - F.c) - 1 / 2
        ≤ (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re ∧
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re
        ≤ max F.c (1 - F.c) - 1 / 2 := by
  have hre :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re =
        (1 - F.c) - 1 / 2 := by
    have hhalf_re : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by
      calc
        (1 / 2 : ℂ).re = (((1 / 2 : ℝ) : ℂ)).re := by
          exact congrArg Complex.re (Complex.ofReal_div (1 : ℝ) 2).symm
        _ = (1 / 2 : ℝ) := by
          exact Complex.ofReal_re (1 / 2)
    calc
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re =
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re -
            (1 / 2 : ℂ).re := by
        exact Complex.sub_re
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t)
          (1 / 2 : ℂ)
      _ = (1 - F.c) - (1 / 2 : ℂ).re := by
        exact congrArg
          (fun x : ℝ => x - (1 / 2 : ℂ).re)
          (zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t)
      _ = (1 - F.c) - 1 / 2 := by
        exact congrArg (fun x : ℝ => (1 - F.c) - x) hhalf_re
  constructor
  · have hmin : min F.c (1 - F.c) ≤ 1 - F.c :=
      min_le_right F.c (1 - F.c)
    have hsub : min F.c (1 - F.c) - 1 / 2 ≤ (1 - F.c) - 1 / 2 :=
      sub_le_sub_right hmin (1 / 2)
    exact Eq.symm hre ▸ hsub
  · have hmax : 1 - F.c ≤ max F.c (1 - F.c) :=
      le_max_right F.c (1 - F.c)
    have hsub : (1 - F.c) - 1 / 2 ≤ max F.c (1 - F.c) - 1 / 2 :=
      sub_le_sub_right hmax (1 / 2)
    exact Eq.symm hre ▸ hsub

/-- The shifted left vertical face has imaginary coordinate norm `‖t‖`. -/
theorem zetaCompletedExplicitFormulaLeftPath_shift_im_norm
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    ‖(zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).im‖ =
      ‖t‖ := by
  have him :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).im = t := by
    have hhalf_im : (1 / 2 : ℂ).im = (0 : ℝ) := by
      calc
        (1 / 2 : ℂ).im = (((1 / 2 : ℝ) : ℂ)).im := by
          exact congrArg Complex.im (Complex.ofReal_div (1 : ℝ) 2).symm
        _ = (0 : ℝ) := by
          exact Complex.ofReal_im (1 / 2)
    calc
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).im =
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).im -
            (1 / 2 : ℂ).im := by
        exact Complex.sub_im
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t)
          (1 / 2 : ℂ)
      _ = t - (1 / 2 : ℂ).im := by
        exact congrArg
          (fun x : ℝ => x - (1 / 2 : ℂ).im)
          (zetaCompletedExplicitFormulaLeftPath_im (F.rectangle T) t)
      _ = t - 0 := by
        exact congrArg (fun x : ℝ => t - x) hhalf_im
      _ = t := by
        exact sub_zero t
  exact congrArg (fun x : ℝ => ‖x‖) him

/-- Pointwise decay for the left-face isolated `s = 0` correction integrand.

This is the genuine denominator-separation part of the all-height Cauchy
estimate; the remaining finite-window theorem must convert this vertical-line
oscillatory decay into the rectangle cancellation bound. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegrand_norm_le_phiDecay
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T t : ℝ) (N : ℕ) :
    ‖(-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)‖
      ≤
        (1 / (F.c - 1)) *
          (hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
          (1 + ‖t‖) ^ (-(N : ℤ))) := by
  let a : ℂ := -1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
  let b : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
  have ha :
      ‖a‖ ≤ 1 / (F.c - 1) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleCoefficient_norm_le F T t
  have hstrip :
      min F.c (1 - F.c) - 1 / 2
          ≤ (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re
          ≤ max F.c (1 - F.c) - 1 / 2 :=
    zetaCompletedExplicitFormulaLeftPath_shift_re_mem_strip_bounds F T t
  have hb :
      ‖b‖
        ≤
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
          (1 + ‖t‖) ^ (-(N : ℤ)) :=
    (hPhi.verticalStripRapidDecayConstant_bound
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) N
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
        hstrip.1 hstrip.2).trans_eq
      (congrArg
        (fun u : ℝ =>
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
            (1 + u) ^ (-(N : ℤ)))
        (zetaCompletedExplicitFormulaLeftPath_shift_im_norm F T t))
  have hA_nonneg : 0 ≤ 1 / (F.c - 1) :=
    le_of_lt (div_pos zero_lt_one (sub_pos.mpr F.c_gt_one))
  have hproduct :
      ‖a * b‖
        ≤
          (1 / (F.c - 1)) *
            (hPhi.verticalStripRapidDecayConstant
              (min F.c (1 - F.c) - 1 / 2)
              (max F.c (1 - F.c) - 1 / 2) N *
            (1 + ‖t‖) ^ (-(N : ℤ))) := by
    calc
      ‖a * b‖ = ‖a‖ * ‖b‖ := by
        exact norm_mul a b
      _ ≤
          (1 / (F.c - 1)) *
            (hPhi.verticalStripRapidDecayConstant
              (min F.c (1 - F.c) - 1 / 2)
              (max F.c (1 - F.c) - 1 / 2) N *
            (1 + ‖t‖) ^ (-(N : ℤ))) := by
        exact mul_le_mul ha hb (norm_nonneg b) hA_nonneg
  exact hproduct

/-- IBP-backed uniform rapid decay for the left-face isolated `s = 0`
correction integrand.

The denominator is separated from the pole by the fixed distance `F.c - 1`;
the transform decay comes from the Paley-Wiener vertical integration-by-parts
owner theorem. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegrand_uniformRapidDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ T t : ℝ,
        ‖(-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)‖
          ≤ C * (1 + ‖t‖) ^ (-(N : ℤ)) := by
  let lower : ℝ := min F.c (1 - F.c) - 1 / 2
  let upper : ℝ := max F.c (1 - F.c) - 1 / 2
  let Ipw : ZetaPaleyWienerSupportInterval f :=
    canonicalZetaPaleyWienerSupportInterval f
  let Cφ : ℝ :=
    zetaLaplaceTransform_supportInterval_decayConstant f Ipw lower upper N
  let K : ℝ := 1 / (F.c - 1)
  have hCφpos : 0 < Cφ :=
    zetaLaplaceTransform_supportInterval_decayConstant_pos f Ipw lower upper N
  have hKpos : 0 < K :=
    div_pos zero_lt_one (sub_pos.mpr F.c_gt_one)
  have hLaplace :
      zetaLaplaceTransformHasVerticalStripDecayConstant f lower upper N Cφ :=
    And.intro hCφpos
      (zetaLaplaceTransform_supportInterval_decayConstant_bound f Ipw lower upper N)
  have hPhi :
      0 < Cφ ∧
        ∀ z : ℂ,
          lower ≤ z.re →
          z.re ≤ upper →
          ‖zetaCompletedExplicitFormulaPhi f z‖
            ≤ Cφ * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
    zetaPhi_hasVerticalStripDecayConstant_of_laplace
      f lower upper N Cφ hLaplace
  exact ⟨K * Cφ, mul_pos hKpos hCφpos, fun T t =>
    let z : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2
    let a : ℂ := -1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
    let b : ℂ := zetaCompletedExplicitFormulaPhi f z
    let hcoeff : ‖a‖ ≤ K :=
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleCoefficient_norm_le F T t
    let hstrip :
        lower ≤ z.re ∧ z.re ≤ upper :=
      zetaCompletedExplicitFormulaLeftPath_shift_re_mem_strip_bounds F T t
    let hphi_raw :
        ‖b‖ ≤ Cφ * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
      hPhi.2 z hstrip.1 hstrip.2
    let him_norm :
        ‖z.im‖ = ‖t‖ :=
      zetaCompletedExplicitFormulaLeftPath_shift_im_norm F T t
    let hphi :
        ‖b‖ ≤ Cφ * (1 + ‖t‖) ^ (-(N : ℤ)) :=
      Eq.subst
        (motive := fun u : ℝ => ‖b‖ ≤ Cφ * (1 + u) ^ (-(N : ℤ)))
        him_norm
        hphi_raw
    let hK_nonneg : 0 ≤ K :=
      le_of_lt hKpos
    let hprod :
        ‖a * b‖ ≤ K * (Cφ * (1 + ‖t‖) ^ (-(N : ℤ))) := by
      calc
        ‖a * b‖ = ‖a‖ * ‖b‖ := by
          exact norm_mul a b
        _ ≤ K * (Cφ * (1 + ‖t‖) ^ (-(N : ℤ))) := by
          exact mul_le_mul hcoeff hphi (norm_nonneg b) hK_nonneg
    let hassoc :
        K * (Cφ * (1 + ‖t‖) ^ (-(N : ℤ))) =
          (K * Cφ) * (1 + ‖t‖) ^ (-(N : ℤ)) :=
      (mul_assoc K Cφ ((1 + ‖t‖) ^ (-(N : ℤ)))).symm
    le_trans hprod (le_of_eq hassoc)⟩


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
