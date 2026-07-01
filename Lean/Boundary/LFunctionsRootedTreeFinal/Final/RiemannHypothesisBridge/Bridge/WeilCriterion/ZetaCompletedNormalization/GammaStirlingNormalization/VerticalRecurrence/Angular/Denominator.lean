import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Angular.Radius
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Sectorial.Support

/-!
# Vertical recurrence: shifted denominator comparison

This subowner contains the reciprocal denominator comparison used by the shifted Gamma envelope.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Exact reciprocal shape of the normalized-Stirling denominator on a fixed
vertical point, after expanding `‖exp w‖` and the principal-branch power norm. -/
theorem Complex.stirlingDenominator_reciprocal_shape_fixedVertical
    {w : ℂ}
    {y : ℝ}
    (hw_ne : w ≠ 0)
    (hw_im : w.im = y) :
    1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) =
      Real.exp (-(Complex.arg w * y)) *
        ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) := by
  have hR_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne
  have hexp_norm :
      ‖Complex.exp w‖ = Real.exp w.re :=
    Complex.norm_exp_eq_exp_re w
  have hre_exp :
      ((1 / 2 : ℂ) - w).re = 1 / 2 - w.re :=
    Complex.half_minus_self_re w
  have him_exp :
      ((1 / 2 : ℂ) - w).im = -y := by
    exact Eq.trans (Complex.half_minus_self_im w) (congrArg Neg.neg hw_im)
  have hcpow_norm :
      ‖w ^ ((1 / 2 : ℂ) - w)‖ =
        ‖w‖ ^ (1 / 2 - w.re) /
          Real.exp (Complex.arg w * (-y)) := by
    have hraw :
        ‖w ^ ((1 / 2 : ℂ) - w)‖ =
          ‖w‖ ^ (((1 / 2 : ℂ) - w).re) /
            Real.exp (Complex.arg w * (((1 / 2 : ℂ) - w).im)) :=
      Complex.norm_cpow_eq_norm_rpow_div_exp_arg_mul_im_of_ne_zero hw_ne
    exact Eq.trans hraw
      (congrArg₂ HDiv.hDiv
        (congrArg (fun t : ℝ => ‖w‖ ^ t) hre_exp)
        (congrArg (fun t : ℝ => Real.exp (Complex.arg w * t)) him_exp))
  calc
    1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) =
        1 / (Real.exp w.re *
          (‖w‖ ^ (1 / 2 - w.re) /
            Real.exp (Complex.arg w * (-y)))) := by
      exact congrArg
        (fun t : ℝ => 1 / t)
        (congrArg₂ HMul.hMul hexp_norm hcpow_norm)
    _ =
        Real.exp (-(Complex.arg w * y)) *
          ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) :=
      real_stirlingDenominator_reciprocal_shape
        ‖w‖ w.re (Complex.arg w) y hR_pos

/-- Reciprocal denominator comparison for the shifted vertical Stirling
normalization.

For `w = x + N + i y` in a fixed shifted right-half-plane strip, the
principal-branch identity
`log ‖w^(1/2-w)‖ = (1/2 - Re w) log ‖w‖ + arg(w) Im w`, together with
`‖exp w‖ = exp (Re w)`, shows that
`1 / (‖exp w‖ ‖w^(1/2-w)‖)` is comparable to
`exp (-π |y| / 2) (1 + |y|)^(Re w - 1/2)`.  This is the sharp vertical-line
branch comparison left after the normalized sectorial Stirling estimate has
been extracted. -/
theorem Complex.shiftedVerticalStirlingDenominator_reciprocal_comparable
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y;
          0 < ‖Complex.exp w‖ *
                ‖w ^ ((1 / 2 : ℂ) - w)‖ ∧
          1 / (‖Complex.exp w‖ *
                ‖w ^ ((1 / 2 : ℂ) - w)‖) ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y ≤
            1 / (‖Complex.exp w‖ *
                ‖w ^ ((1 / 2 : ℂ) - w)‖) := by
  match Complex.shiftedVertical_arg_exponential_defect_comparable A B with
  | ⟨Ha, Ca, ca, hHa_pos, hCa_pos, hca_pos, harg⟩ =>
  match Complex.shiftedVertical_radiusPower_comparable A B with
  | ⟨Hr, Cr, cr, hHr_pos, hCr_pos, hcr_pos, hradius⟩ =>
  match Complex.shiftedVertical_realPartExp_bounded A B with
  | ⟨Ce, ce, hCe_pos, hce_pos, hexpRe⟩ =>
  let H : ℝ := max Ha Hr
  have hH_pos : 0 < H :=
    lt_of_lt_of_le hHa_pos (le_max_left Ha Hr)
  have hC_pos : 0 < (Ca * Cr) * Ce :=
    mul_pos (mul_pos hCa_pos hCr_pos) hCe_pos
  have hc_pos : 0 < (ca * cr) * ce :=
    mul_pos (mul_pos hca_pos hcr_pos) hce_pos
  exact ⟨H, (Ca * Cr) * Ce, (ca * cr) * ce,
    hH_pos, hC_pos, hc_pos, by
  intro x y hxA hxB hy
  have hy_a : Ha ≤ ‖y‖ :=
    le_trans (le_max_left Ha Hr) hy
  have hy_r : Hr ≤ ‖y‖ :=
    le_trans (le_max_right Ha Hr) hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  let Eexp : ℝ := Real.exp (-(Real.pi / 2) * ‖y‖)
  let P : ℝ := (1 + ‖y‖) ^
    (x + Complex.verticalStripTransportShift A - 1 / 2)
  have harg_xy := harg x y hxA hxB hy_a
  have hradius_xy := hradius x y hxA hxB hy_r
  have hexpRe_xy := hexpRe x y hxA hxB
  have hw_re :
      w.re = x + Complex.verticalStripTransportShift A :=
    Complex.fixedRealPartVerticalPoint_re
      (x + Complex.verticalStripTransportShift A) y
  have hw_ne : w ≠ 0 := by
    have hH_pos : 0 < H :=
      lt_of_lt_of_le hHa_pos (le_max_left Ha Hr)
    have hw_norm_pos : 0 < ‖w‖ :=
      lt_of_lt_of_le hH_pos
        (Complex.verticalStripTransportShift_radius_ge_of_height_ge hy)
    exact norm_pos_iff.mp hw_norm_pos
  have hden_pos :
      0 < ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
    Complex.stirlingDenominator_pos_of_ne_zero hw_ne
  have hcpow_norm :
      ‖w ^ ((1 / 2 : ℂ) - w)‖ =
        ‖w‖ ^ (((1 / 2 : ℂ) - w).re) /
          Real.exp (Complex.arg w * (((1 / 2 : ℂ) - w).im)) :=
    Complex.norm_cpow_eq_norm_rpow_div_exp_arg_mul_im_of_ne_zero hw_ne
  have hreciprocal_shape :
      1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) =
        Real.exp (-(Complex.arg w * y)) *
          ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) := by
    exact
      Complex.stirlingDenominator_reciprocal_shape_fixedVertical
        hw_ne
        (Complex.fixedRealPartVerticalPoint_im
          (x + Complex.verticalStripTransportShift A) y)
  constructor
  · exact hden_pos
  constructor
  · have hrad_upper :
        ‖w‖ ^ (w.re - 1 / 2) ≤ Cr * P := by
      exact hradius_xy.1
    have harg_upper :
        Real.exp (-(Complex.arg w * y)) ≤ Ca * Eexp :=
      harg_xy.1
    have hexpRe_upper :
        Real.exp (-w.re) ≤ Ce :=
      hexpRe_xy.1
    have hshape_bound :
        Real.exp (-(Complex.arg w * y)) *
            ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) ≤
          ((Ca * Cr) * Ce) *
            (Eexp * P) := by
      have harg_nonneg :
          0 ≤ Real.exp (-(Complex.arg w * y)) :=
        le_of_lt (Real.exp_pos (-(Complex.arg w * y)))
      have hrad_nonneg :
          0 ≤ ‖w‖ ^ (w.re - 1 / 2) :=
        Real.rpow_nonneg (norm_nonneg w) (w.re - 1 / 2)
      have hexpRe_nonneg :
          0 ≤ Real.exp (-w.re) :=
        le_of_lt (Real.exp_pos (-w.re))
      have hEexp_nonneg : 0 ≤ Eexp :=
        le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖y‖))
      have hP_nonneg : 0 ≤ P :=
        Real.rpow_nonneg (add_nonneg zero_le_one (norm_nonneg y))
          (x + Complex.verticalStripTransportShift A - 1 / 2)
      have hCrP_nonneg : 0 ≤ Cr * P :=
        mul_nonneg (le_of_lt hCr_pos) hP_nonneg
      have hCaE_nonneg : 0 ≤ Ca * Eexp :=
        mul_nonneg (le_of_lt hCa_pos) hEexp_nonneg
      have hfirst :
          Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) ≤
            (Ca * Eexp) * (Cr * P) :=
        mul_le_mul harg_upper hrad_upper hrad_nonneg hCaE_nonneg
      have htarget_step :
          Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) ≤
            ((Ca * Eexp) * (Cr * P)) * Ce :=
        mul_le_mul hfirst hexpRe_upper hexpRe_nonneg
          (mul_nonneg hCaE_nonneg hCrP_nonneg)
      have htarget_eq :
          ((Ca * Eexp) * (Cr * P)) * Ce =
            ((Ca * Cr) * Ce) * (Eexp * P) := by
        calc
          ((Ca * Eexp) * (Cr * P)) * Ce =
              (Ca * Eexp) * ((Cr * P) * Ce) :=
            mul_assoc (Ca * Eexp) (Cr * P) Ce
          _ = (Ca * Eexp) * (Ce * (Cr * P)) := by
            exact congrArg
              (fun t : ℝ => (Ca * Eexp) * t)
              (mul_comm (Cr * P) Ce)
          _ = ((Ca * Eexp) * Ce) * (Cr * P) :=
            (mul_assoc (Ca * Eexp) Ce (Cr * P)).symm
          _ = (Ca * (Eexp * Ce)) * (Cr * P) := by
            exact congrArg
              (fun t : ℝ => t * (Cr * P))
              (mul_assoc Ca Eexp Ce)
          _ = (Ca * (Ce * Eexp)) * (Cr * P) := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * (Cr * P))
              (mul_comm Eexp Ce)
          _ = ((Ca * Ce) * Eexp) * (Cr * P) := by
            exact congrArg
              (fun t : ℝ => t * (Cr * P))
              (mul_assoc Ca Ce Eexp).symm
          _ = (Ca * Ce) * (Eexp * (Cr * P)) :=
            mul_assoc (Ca * Ce) Eexp (Cr * P)
          _ = (Ca * Ce) * ((Cr * P) * Eexp) := by
            exact congrArg
              (fun t : ℝ => (Ca * Ce) * t)
              (mul_comm Eexp (Cr * P))
          _ = ((Ca * Ce) * (Cr * P)) * Eexp :=
            (mul_assoc (Ca * Ce) (Cr * P) Eexp).symm
          _ = (Ca * (Ce * (Cr * P))) * Eexp := by
            exact congrArg
              (fun t : ℝ => t * Eexp)
              (mul_assoc Ca Ce (Cr * P))
          _ = (Ca * ((Cr * P) * Ce)) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * Eexp)
              (mul_comm Ce (Cr * P))
          _ = (Ca * (Cr * (P * Ce))) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * Eexp)
              (mul_assoc Cr P Ce)
          _ = (Ca * (Cr * (Ce * P))) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * (Cr * t)) * Eexp)
              (mul_comm P Ce)
          _ = (Ca * ((Cr * Ce) * P)) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * Eexp)
              (mul_assoc Cr Ce P).symm
          _ = ((Ca * (Cr * Ce)) * P) * Eexp :=
            congrArg (fun t : ℝ => t * Eexp)
              (mul_assoc Ca (Cr * Ce) P).symm
          _ = (((Ca * Cr) * Ce) * P) * Eexp := by
            exact congrArg
              (fun t : ℝ => (t * P) * Eexp)
              (mul_assoc Ca Cr Ce).symm
          _ = ((Ca * Cr) * Ce) * (P * Eexp) :=
            mul_assoc ((Ca * Cr) * Ce) P Eexp
          _ = ((Ca * Cr) * Ce) * (Eexp * P) := by
            exact congrArg
              (fun t : ℝ => ((Ca * Cr) * Ce) * t)
              (mul_comm P Eexp)
      exact le_trans htarget_step (le_of_eq htarget_eq)
    have henv_eq :
        Eexp * P =
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y := by
      rfl
    calc
      1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) =
          Real.exp (-(Complex.arg w * y)) *
            ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) :=
        hreciprocal_shape
      _ ≤ ((Ca * Cr) * Ce) * (Eexp * P) := hshape_bound
      _ = ((Ca * Cr) * Ce) *
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y :=
        congrArg (fun t : ℝ => ((Ca * Cr) * Ce) * t) henv_eq
  · have hrad_lower :
        cr * P ≤ ‖w‖ ^ (w.re - 1 / 2) := by
      exact hradius_xy.2
    have harg_lower :
        ca * Eexp ≤ Real.exp (-(Complex.arg w * y)) :=
      harg_xy.2
    have hexpRe_lower :
        ce ≤ Real.exp (-w.re) :=
      hexpRe_xy.2
    have hshape_bound :
        ((ca * cr) * ce) *
            (Eexp * P) ≤
          Real.exp (-(Complex.arg w * y)) *
            ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) := by
      have hEexp_nonneg : 0 ≤ Eexp :=
        le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖y‖))
      have hP_nonneg : 0 ≤ P :=
        Real.rpow_nonneg (add_nonneg zero_le_one (norm_nonneg y))
          (x + Complex.verticalStripTransportShift A - 1 / 2)
      have hce_nonneg : 0 ≤ ce :=
        le_of_lt hce_pos
      have hcrP_nonneg : 0 ≤ cr * P :=
        mul_nonneg (le_of_lt hcr_pos) hP_nonneg
      have hcaE_nonneg : 0 ≤ ca * Eexp :=
        mul_nonneg (le_of_lt hca_pos) hEexp_nonneg
      have hleft_eq :
          ((ca * cr) * ce) * (Eexp * P) =
            (ca * Eexp) * (cr * P) * ce := by
        calc
          ((ca * cr) * ce) * (Eexp * P) =
              (ca * cr) * (ce * (Eexp * P)) :=
            mul_assoc (ca * cr) ce (Eexp * P)
          _ = (ca * cr) * ((Eexp * P) * ce) := by
            exact congrArg
              (fun t : ℝ => (ca * cr) * t)
              (mul_comm ce (Eexp * P))
          _ = ((ca * cr) * (Eexp * P)) * ce :=
            (mul_assoc (ca * cr) (Eexp * P) ce).symm
          _ = (ca * (cr * (Eexp * P))) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca cr (Eexp * P))
          _ = (ca * ((Eexp * P) * cr)) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_comm cr (Eexp * P))
          _ = (ca * (Eexp * (P * cr))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_assoc Eexp P cr)
          _ = (ca * (Eexp * (cr * P))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * (Eexp * t)) * ce)
              (mul_comm P cr)
          _ = (ca * ((Eexp * cr) * P)) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_assoc Eexp cr P).symm
          _ = (ca * ((cr * Eexp) * P)) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * (t * P)) * ce)
              (mul_comm Eexp cr)
          _ = (ca * (cr * (Eexp * P))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_assoc cr Eexp P)
          _ = ((ca * cr) * (Eexp * P)) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca cr (Eexp * P)).symm
          _ = ((ca * cr) * (P * Eexp)) * ce := by
            exact congrArg
              (fun t : ℝ => ((ca * cr) * t) * ce)
              (mul_comm Eexp P)
          _ = (ca * cr) * (P * Eexp) * ce := rfl
          _ = (ca * (cr * P) * Eexp) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (by
                calc
                  (ca * cr) * (P * Eexp) =
                      ca * (cr * (P * Eexp)) :=
                    mul_assoc ca cr (P * Eexp)
                  _ = ca * ((cr * P) * Eexp) := by
                    exact congrArg
                      (fun t : ℝ => ca * t)
                      (mul_assoc cr P Eexp).symm
                  _ = ca * (cr * P) * Eexp :=
                    (mul_assoc ca (cr * P) Eexp).symm)
          _ = (Eexp * (ca * (cr * P))) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_comm (ca * (cr * P)) Eexp)
          _ = ((ca * (cr * P)) * Eexp) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_comm Eexp (ca * (cr * P)))
          _ = (ca * ((cr * P) * Eexp)) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca (cr * P) Eexp)
          _ = (ca * (Eexp * (cr * P))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_comm (cr * P) Eexp)
          _ = ((ca * Eexp) * (cr * P)) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca Eexp (cr * P)).symm
          _ = (ca * Eexp) * (cr * P) * ce := rfl
      have hfirst :
          (ca * Eexp) * (cr * P) ≤
            Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) :=
        mul_le_mul harg_lower hrad_lower hcrP_nonneg
          (le_of_lt (Real.exp_pos (-(Complex.arg w * y))))
      have hsecond :
          (ca * Eexp) * (cr * P) * ce ≤
            Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) :=
        mul_le_mul hfirst hexpRe_lower hce_nonneg
          (mul_nonneg
            (le_of_lt (Real.exp_pos (-(Complex.arg w * y))))
            (Real.rpow_nonneg (norm_nonneg w) (w.re - 1 / 2)))
      exact le_trans (le_of_eq hleft_eq) hsecond
    have henv_eq :
        Eexp * P =
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y := by
      rfl
    calc
      ((ca * cr) * ce) *
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y =
          ((ca * cr) * ce) * (Eexp * P) :=
        congrArg (fun t : ℝ => ((ca * cr) * ce) * t) henv_eq.symm
      _ ≤ Real.exp (-(Complex.arg w * y)) *
            ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) :=
        hshape_bound
      _ = 1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) :=
        hreciprocal_shape.symm⟩

end
end LFunctions
end Boundary
