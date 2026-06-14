import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.Owner

/-!
# Completed functional-equation transport

This file is a mechanically split owner layer from the completed normalization
package.  It preserves the original declaration order and keeps downstream
imports routed through `ZetaCompletedNormalization.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_denominator_data
    {z : ℂ}
    (hz_re : z.re ≤ 0)
    (hz_ne_zero : z ≠ 0)
    (hGamma_ne : Complex.Gammaℝ z ≠ 0) :
    z ≠ 1 ∧
      ((1 : ℂ) - z) ≠ 0 ∧
      (((1 : ℂ) - z) - 1) ≠ 0 ∧
      Complex.Gammaℝ z ≠ 0 := by
  have hz_ne_one : z ≠ 1 := by
    intro hz_one
    have hz_re_one : z.re = 1 := by
      calc
        z.re = (1 : ℂ).re := by
          exact congrArg Complex.re hz_one
        _ = 1 := Complex.one_re
    have hone_le_zero : (1 : ℝ) ≤ 0 :=
      Eq.subst
        (motive := fun x : ℝ => x ≤ 0)
        hz_re_one.symm
        hz_re
    exact not_lt_of_ge hone_le_zero zero_lt_one
  have hone_sub_ne_zero : ((1 : ℂ) - z) ≠ 0 := by
    intro hsub
    have hz_one : z = 1 := by
      have hsub_add : ((1 : ℂ) - z) + z = 0 + z :=
        congrArg (fun w : ℂ => w + z) hsub
      have hone_eq_z : (1 : ℂ) = z := by
        exact Eq.trans (sub_add_cancel (1 : ℂ) z).symm hsub_add
      exact hone_eq_z.symm
    exact hz_ne_one hz_one
  have hone_sub_minus_one_ne_zero : (((1 : ℂ) - z) - 1) ≠ 0 := by
    intro hden
    have hneg_zero : -z = 0 := by
      calc
        -z = ((1 : ℂ) - z) - 1 := by
          exact (sub_sub_cancel (1 : ℂ) z).symm
        _ = 0 := hden
    have hz_zero : z = 0 := by
      exact neg_eq_zero.mp hneg_zero
    exact hz_ne_zero hz_zero
  exact ⟨hz_ne_one, hone_sub_ne_zero, hone_sub_minus_one_ne_zero, hGamma_ne⟩

/-- Algebraic division of the completed zeta functional equation into the
raw pole-cleared multiplier, away from Gamma zero faces. -/
theorem riemannZeta_completedFunctionalEquation_quotient_of_gamma_ne_zero
    {z : ℂ}
    (hz_re : z.re ≤ 0)
    (hz_ne_zero : z ≠ 0)
    (hGamma_ne : Complex.Gammaℝ z ≠ 0) :
    riemannZeta z =
      riemannZeta ((1 : ℂ) - z) *
        Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z := by
  rcases poleClearedRiemannZeta_completedFunctionalEquationMultiplier_denominator_data
      hz_re hz_ne_zero hGamma_ne with
    ⟨_, hone_sub_ne_zero, _, _⟩
  have hw_re_eq : ((1 : ℂ) - z).re = 1 - z.re := by
    calc
      ((1 : ℂ) - z).re = (1 : ℂ).re - z.re := by
        exact Complex.sub_re (1 : ℂ) z
      _ = 1 - z.re := by
        exact congrArg (fun x : ℝ => x - z.re) Complex.one_re
  have hz_re_le_one : z.re ≤ 1 :=
    le_trans hz_re zero_le_one
  have hw_re_one_le : 1 ≤ ((1 : ℂ) - z).re := by
    have hone_le_sub : 1 ≤ 1 - z.re := by
      calc
        1 = 1 - 0 := by
          exact (sub_zero 1).symm
        _ ≤ 1 - z.re := by
          exact sub_le_sub_left hz_re 1
    exact Eq.subst
      (motive := fun x : ℝ => 1 ≤ x)
      hw_re_eq.symm
      hone_le_sub
  have hGamma_reflected_ne :
      Complex.Gammaℝ ((1 : ℂ) - z) ≠ 0 := by
    exact Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm
      (le_trans zero_le_one hw_re_one_le)
      (one_le_norm_of_one_le_re hw_re_one_le)
  have hcompleted_symm :
      completedRiemannZeta z = completedRiemannZeta ((1 : ℂ) - z) := by
    exact (completedRiemannZeta_one_sub z).symm
  have hζw := riemannZeta_def_of_ne_zero (s := ((1 : ℂ) - z)) hone_sub_ne_zero
  calc
    riemannZeta z =
        completedRiemannZeta z / Complex.Gammaℝ z := by
      exact riemannZeta_def_of_ne_zero hz_ne_zero
    _ = completedRiemannZeta ((1 : ℂ) - z) / Complex.Gammaℝ z := by
      exact congrArg (fun x : ℂ => x / Complex.Gammaℝ z) hcompleted_symm
    _ = (riemannZeta ((1 : ℂ) - z) * Complex.Gammaℝ ((1 : ℂ) - z)) /
        Complex.Gammaℝ z := by
      have hζw_mul := congrArg
        (fun x : ℂ => x * Complex.Gammaℝ ((1 : ℂ) - z)) hζw
      have hζw_completed :
          riemannZeta ((1 : ℂ) - z) * Complex.Gammaℝ ((1 : ℂ) - z) =
            completedRiemannZeta ((1 : ℂ) - z) := by
        exact hζw_mul.trans (div_mul_cancel₀ _ hGamma_reflected_ne)
      exact congrArg (fun x : ℂ => x / Complex.Gammaℝ z) hζw_completed.symm
    _ = riemannZeta ((1 : ℂ) - z) *
        Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z := by
      exact Eq.refl _

/-- Algebraic transport from the zeta quotient functional equation to the
pole-cleared raw multiplier identity. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_algebra
    {a b c d : ℂ}
    (hb : b ≠ 0) :
    ((a / b) * d) * (b * c) = a * (c * d) := by
  calc
    ((a / b) * d) * (b * c) =
        (((a / b) * d) * b) * c := by
      exact mul_assoc ((a / b) * d) b c
    _ = ((a / b) * (d * b)) * c := by
      exact congrArg (fun x : ℂ => x * c) (mul_assoc (a / b) d b)
    _ = ((a / b) * (b * d)) * c := by
      exact congrArg (fun x : ℂ => ((a / b) * x) * c) (mul_comm d b)
    _ = (((a / b) * b) * d) * c := by
      exact congrArg (fun x : ℂ => x * c) (mul_assoc (a / b) b d).symm
    _ = (a * d) * c := by
      exact congrArg (fun x : ℂ => (x * d) * c) (div_mul_cancel₀ a hb)
    _ = a * (d * c) := by
      exact (mul_assoc a d c).symm
    _ = a * (c * d) := by
      exact congrArg (fun x : ℂ => a * x) (mul_comm d c)

theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_identity_of_zeta_quotient
    {z : ℂ}
    (hz_re : z.re ≤ 0)
    (hz_ne_zero : z ≠ 0)
    (hzeta :
      riemannZeta z =
        riemannZeta ((1 : ℂ) - z) *
          Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) :
    poleClearedRiemannZeta z =
      (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
        poleClearedRiemannZeta ((1 : ℂ) - z) := by
  have hz_ne_one : z ≠ 1 := by
    intro hz_one
    have hz_re_one : z.re = 1 := by
      calc
        z.re = (1 : ℂ).re := by
          exact congrArg Complex.re hz_one
        _ = 1 := Complex.one_re
    have hone_le_zero : (1 : ℝ) ≤ 0 :=
      Eq.subst
        (motive := fun x : ℝ => x ≤ 0)
        hz_re_one.symm
        hz_re
    exact not_lt_of_ge hone_le_zero zero_lt_one
  have hw_minus_one_ne_zero : (((1 : ℂ) - z) - 1) ≠ 0 := by
    intro hden
    have hneg_zero : -z = 0 := by
      calc
        -z = ((1 : ℂ) - z) - 1 := by
          exact (sub_sub_cancel (1 : ℂ) z).symm
        _ = 0 := hden
    exact hz_ne_zero (neg_eq_zero.mp hneg_zero)
  have hw_ne_one : ((1 : ℂ) - z) ≠ 1 := by
    intro hw_one
    have hden_zero : (((1 : ℂ) - z) - 1) = 0 := by
      exact sub_eq_zero.mpr hw_one
    exact hw_minus_one_ne_zero hden_zero
  have hpz :
      poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
    poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  have hpw :
      poleClearedRiemannZeta ((1 : ℂ) - z) =
        (((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z) :=
    poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
  let a : ℂ := z - 1
  let b : ℂ := ((1 : ℂ) - z) - 1
  let c : ℂ := riemannZeta ((1 : ℂ) - z)
  let d : ℂ := Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z
  have halg : ((a / b) * d) * (b * c) = a * (c * d) :=
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_algebra
      hw_minus_one_ne_zero
  have hleft :
      poleClearedRiemannZeta z =
        (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) := by
    calc
      poleClearedRiemannZeta z = (z - 1) * riemannZeta z := hpz
      _ = (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
        exact congrArg (fun x : ℂ => (z - 1) * x) hzeta
      _ = (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) := by
        exact congrArg (fun x : ℂ => (z - 1) * x)
          (mul_div_assoc
            (riemannZeta ((1 : ℂ) - z))
            (Complex.Gammaℝ ((1 : ℂ) - z))
            (Complex.Gammaℝ z))
  calc
    poleClearedRiemannZeta z =
        (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) := hleft
    _ = (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
        ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)) := by
      exact halg.symm
    _ = (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
        poleClearedRiemannZeta ((1 : ℂ) - z) := by
      exact congrArg
        (fun x : ℂ =>
          (((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) * x)
        hpw.symm

theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity_of_gamma_ne_zero
    {z : ℂ}
    (hz_re : z.re ≤ 0)
    (hz_ne_zero : z ≠ 0)
    (hGamma_ne : Complex.Gammaℝ z ≠ 0) :
    poleClearedRiemannZeta z =
      (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
        poleClearedRiemannZeta ((1 : ℂ) - z) := by
  exact
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_identity_of_zeta_quotient
      hz_re hz_ne_zero
      (riemannZeta_completedFunctionalEquation_quotient_of_gamma_ne_zero
        hz_re hz_ne_zero hGamma_ne)

/-- Nonzero `Gammaℝ` zero faces on the left reflect strictly into `Re s > 1`.

Mathlib's finite-valued `Gammaℝ` vanishes exactly at the nonpositive even
integers.  Excluding `z = 0` leaves the negative even integers, whose reflection
`1 - z` is strictly to the right of the line `Re s = 1`. -/
theorem Gammaℝ_zero_nonzero_leftHalfPlane_reflection_one_lt_re
    {z : ℂ}
    (hz_ne_zero : z ≠ 0)
    (hGamma_zero : Complex.Gammaℝ z = 0) :
    1 < ((1 : ℂ) - z).re := by
  rcases Complex.Gammaℝ_eq_zero_iff.mp hGamma_zero with ⟨n, hz_eq⟩
  cases n with
  | zero =>
      have hz_zero : z = 0 := by
        calc
          z = -(2 * ((0 : ℕ) : ℂ)) := hz_eq
          _ = -0 := by
            exact congrArg Neg.neg (mul_zero (2 : ℂ))
          _ = 0 := by
            exact neg_zero
      exact False.elim (hz_ne_zero hz_zero)
  | succ n =>
      have hprod_re :
          (2 * ((Nat.succ n : ℕ) : ℂ)).re =
            (2 : ℝ) * (Nat.succ n : ℝ) := by
        calc
          (2 * ((Nat.succ n : ℕ) : ℂ)).re =
              (2 : ℂ).re * ((Nat.succ n : ℕ) : ℂ).re -
                (2 : ℂ).im * ((Nat.succ n : ℕ) : ℂ).im := by
            exact Complex.mul_re (2 : ℂ) ((Nat.succ n : ℕ) : ℂ)
          _ = (2 : ℝ) * (Nat.succ n : ℝ) -
                (2 : ℂ).im * ((Nat.succ n : ℕ) : ℂ).im := by
            exact congrArg
              (fun x : ℝ =>
                x * ((Nat.succ n : ℕ) : ℂ).re -
                  (2 : ℂ).im * ((Nat.succ n : ℕ) : ℂ).im)
              (Complex.natCast_re 2)
          _ = (2 : ℝ) * (Nat.succ n : ℝ) -
                (2 : ℂ).im * 0 := by
            exact congrArg
              (fun x : ℝ =>
                (2 : ℝ) * (Nat.succ n : ℝ) - (2 : ℂ).im * x)
              (Complex.natCast_im (Nat.succ n))
          _ = (2 : ℝ) * (Nat.succ n : ℝ) - 0 * 0 := by
            exact congrArg
              (fun x : ℝ =>
                (2 : ℝ) * (Nat.succ n : ℝ) - x * 0)
              (Complex.natCast_im 2)
          _ = (2 : ℝ) * (Nat.succ n : ℝ) - 0 := by
            exact congrArg
              (fun x : ℝ => (2 : ℝ) * (Nat.succ n : ℝ) - x)
              (zero_mul 0)
          _ = (2 : ℝ) * (Nat.succ n : ℝ) := by
            exact sub_zero ((2 : ℝ) * (Nat.succ n : ℝ))
      have hz_re_eq :
          z.re = -((2 : ℝ) * (Nat.succ n : ℝ)) := by
        calc
          z.re = (-(2 * ((Nat.succ n : ℕ) : ℂ))).re := by
            exact congrArg Complex.re hz_eq
          _ = -((2 * ((Nat.succ n : ℕ) : ℂ)).re) := by
            exact Complex.neg_re (2 * ((Nat.succ n : ℕ) : ℂ))
          _ = -((2 : ℝ) * (Nat.succ n : ℝ)) := by
            exact congrArg Neg.neg hprod_re
      have hprod_pos : 0 < (2 : ℝ) * (Nat.succ n : ℝ) :=
        mul_pos zero_lt_two (Nat.cast_pos.mpr (Nat.succ_pos n))
      have hz_re_neg : z.re < 0 := by
        exact Eq.subst
          (motive := fun x : ℝ => x < 0)
          hz_re_eq.symm
          (neg_neg_of_pos hprod_pos)
      have hw_re_eq : ((1 : ℂ) - z).re = 1 - z.re := by
        calc
          ((1 : ℂ) - z).re = (1 : ℂ).re - z.re := by
            exact Complex.sub_re (1 : ℂ) z
          _ = 1 - z.re := by
            exact congrArg (fun x : ℝ => x - z.re) Complex.one_re
      have hone_lt_sub : 1 < 1 - z.re := by
        exact lt_sub_iff_add_lt'.2
          (Eq.subst
            (motive := fun x : ℝ => x < 1)
            (zero_add (1 : ℝ)).symm
            (add_lt_add_right hz_re_neg 1))
      exact Eq.subst
        (motive := fun x : ℝ => 1 < x)
        hw_re_eq.symm
        hone_lt_sub

/-- Reflected pole-cleared zeta nonvanishing at the Gamma-zero faces in the
left half-plane.

This is the exact nonvanishing fact needed to unfold the removable multiplier
branch at Gamma-zero points.  Analytically these are the trivial-zero faces on
the left side reflected to the ordinary right half-plane. -/
theorem poleClearedRiemannZeta_reflected_nonzero_of_gamma_zero_leftHalfPlane
    {z : ℂ}
    (hz_re : z.re ≤ 0)
    (hz_ne_zero : z ≠ 0)
    (hGamma_zero : Complex.Gammaℝ z = 0) :
    poleClearedRiemannZeta ((1 : ℂ) - z) ≠ 0 := by
  have hw_re_gt_one :
      1 < ((1 : ℂ) - z).re :=
    Gammaℝ_zero_nonzero_leftHalfPlane_reflection_one_lt_re
      hz_ne_zero hGamma_zero
  have hw_ne_one : ((1 : ℂ) - z) ≠ 1 := by
    intro hw_one
    have hw_re_one : ((1 : ℂ) - z).re = 1 := by
      calc
        ((1 : ℂ) - z).re = (1 : ℂ).re := by
          exact congrArg Complex.re hw_one
        _ = 1 := by
          exact Complex.one_re
    have hone_lt_one : (1 : ℝ) < 1 :=
      Eq.subst
        (motive := fun x : ℝ => 1 < x)
        hw_re_one
        hw_re_gt_one
    exact (lt_irrefl (1 : ℝ)) hone_lt_one
  have hfactor_ne : (((1 : ℂ) - z) - 1) ≠ 0 := by
    intro hfactor
    exact hw_ne_one (sub_eq_zero.mp hfactor)
  have hzeta_reflected_ne :
      riemannZeta ((1 : ℂ) - z) ≠ 0 := by
    intro hzeta_zero
    exact riemannZeta_ne_zero_of_one_lt_re hw_re_gt_one hzeta_zero
  have hproduct_ne :
      (((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z) ≠ 0 :=
    mul_ne_zero hfactor_ne hzeta_reflected_ne
  have hpole :
      poleClearedRiemannZeta ((1 : ℂ) - z) =
        (((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z) :=
    poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
  intro hpole_zero
  exact hproduct_ne (hpole.symm.trans hpole_zero)

/-- Compatibility of the completed-functional-equation multiplier with the
Gamma-zero faces in the left half-plane.

At these points the completed functional equation is not divided by
`Gammaℝ z`; instead the statement is the classical trivial-zero cancellation
of the pole-cleared zeta factor against the Gamma zero. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity_of_gamma_zero
    {z : ℂ}
    (hz_re : z.re ≤ 0)
    (hz_ne_zero : z ≠ 0)
    (hGamma_zero : Complex.Gammaℝ z = 0) :
    poleClearedRiemannZeta z =
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
        poleClearedRiemannZeta ((1 : ℂ) - z) := by
  have hM :
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
        poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z) := by
    unfold poleClearedRiemannZeta_completedFunctionalEquationMultiplier
    exact Eq.trans (if_neg hz_ne_zero) (if_pos hGamma_zero)
  have hreflected_ne :
      poleClearedRiemannZeta ((1 : ℂ) - z) ≠ 0 :=
    poleClearedRiemannZeta_reflected_nonzero_of_gamma_zero_leftHalfPlane
      hz_re hz_ne_zero hGamma_zero
  calc
    poleClearedRiemannZeta z =
        (poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z)) *
          poleClearedRiemannZeta ((1 : ℂ) - z) := by
      exact (div_mul_cancel₀
        (poleClearedRiemannZeta z)
        hreflected_ne).symm
    _ = poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
          poleClearedRiemannZeta ((1 : ℂ) - z) := by
      exact congrArg
        (fun w : ℂ => w * poleClearedRiemannZeta ((1 : ℂ) - z))
        hM.symm

theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity_of_ne_zero
    {z : ℂ}
    (hz_re : z.re ≤ 0)
    (hz_ne_zero : z ≠ 0) :
    poleClearedRiemannZeta z =
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
        poleClearedRiemannZeta ((1 : ℂ) - z) := by
  by_cases hGamma_ne : Complex.Gammaℝ z ≠ 0
  · have hraw :
        poleClearedRiemannZeta z =
          (((z - 1) / (((1 : ℂ) - z) - 1)) *
              (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
            poleClearedRiemannZeta ((1 : ℂ) - z) :=
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity_of_gamma_ne_zero
        hz_re hz_ne_zero hGamma_ne
    have hM :
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
          ((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
      unfold poleClearedRiemannZeta_completedFunctionalEquationMultiplier
      exact Eq.trans (if_neg hz_ne_zero) (if_neg hGamma_ne)
    exact Eq.subst
      (motive := fun w : ℂ =>
        poleClearedRiemannZeta z =
          w * poleClearedRiemannZeta ((1 : ℂ) - z))
      hM.symm
      hraw
  · exact
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity_of_gamma_zero
        hz_re hz_ne_zero (not_not.mp hGamma_ne)

/-- The removable point `z = 0` satisfies the pole-cleared completed-functional
equation identity by the chosen multiplier value. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity_zero :
    poleClearedRiemannZeta 0 =
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier 0 *
        poleClearedRiemannZeta ((1 : ℂ) - 0) := by
  have hM0 :
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier 0 =
        poleClearedRiemannZeta 0 := by
    unfold poleClearedRiemannZeta_completedFunctionalEquationMultiplier
    exact if_pos rfl
  have htarget :
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier 0 *
          poleClearedRiemannZeta ((1 : ℂ) - 0) =
        poleClearedRiemannZeta 0 := by
    calc
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier 0 *
          poleClearedRiemannZeta ((1 : ℂ) - 0) =
          poleClearedRiemannZeta 0 *
            poleClearedRiemannZeta ((1 : ℂ) - 0) := by
        exact congrArg
          (fun w : ℂ => w * poleClearedRiemannZeta ((1 : ℂ) - 0))
          hM0
      _ = poleClearedRiemannZeta 0 * poleClearedRiemannZeta (1 : ℂ) := by
        exact congrArg
          (fun w : ℂ => poleClearedRiemannZeta 0 * poleClearedRiemannZeta w)
          (sub_zero (1 : ℂ))
      _ = poleClearedRiemannZeta 0 * 1 := by
        exact congrArg (fun w : ℂ => poleClearedRiemannZeta 0 * w)
          poleClearedRiemannZeta_one
      _ = poleClearedRiemannZeta 0 := by
        exact mul_one (poleClearedRiemannZeta 0)
  exact htarget.symm

/-- Exact normalization identity for the removable completed-functional-equation
multiplier of the pole-cleared zeta factor.

This is the whole-plane version of the left-boundary factorization, with the
removable value at `z = 0` included in the multiplier. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity
    {z : ℂ}
    (hz : z.re ≤ 0) :
    poleClearedRiemannZeta z =
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
        poleClearedRiemannZeta ((1 : ℂ) - z) := by
  by_cases hz_zero : z = 0
  · exact Eq.subst
      (motive := fun w : ℂ =>
        poleClearedRiemannZeta w =
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier w *
            poleClearedRiemannZeta ((1 : ℂ) - w))
      hz_zero.symm
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity_zero
  · have hraw :
        poleClearedRiemannZeta z =
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
            poleClearedRiemannZeta ((1 : ℂ) - z) :=
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity_of_ne_zero
        hz hz_zero
    exact hraw

/-- Compact norm boundedness from a continuous extension on a closed ball.

This is the reusable local-boundedness API used for removable analytic factors:
once the removable extension is continuous on the compact closed ball, its norm
is bounded there. -/
theorem compact_closedBall_norm_bound_of_continuousOn
    (F : ℂ → ℂ)
    (r : ℝ)
    (hF : ContinuousOn F (Metric.closedBall (0 : ℂ) r)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        ‖z‖ ≤ r →
        ‖F z‖ ≤ C := by
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) r) :=
    ProperSpace.isCompact_closedBall (0 : ℂ) r
  rcases IsCompact.exists_bound_of_continuousOn hcompact hF with
    ⟨C0, hC0⟩
  refine ⟨max C0 0 + 1, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos (le_max_right C0 0) zero_lt_one
  intro z hz_norm
  have hz_mem : z ∈ Metric.closedBall (0 : ℂ) r :=
    mem_closedBall_zero_iff.mpr hz_norm
  have hraw : ‖F z‖ ≤ C0 :=
    hC0 z hz_mem
  exact le_trans hraw
    (le_trans (le_max_left C0 0) (le_add_of_nonneg_right zero_le_one))

/-- A compact removable extension controls the original punctured function on
the same closed ball. -/
theorem compact_closedBall_punctured_norm_bound_of_removable_extension
    (f F : ℂ → ℂ)
    (r : ℝ)
    (hF : ContinuousOn F (Metric.closedBall (0 : ℂ) r))
    (hrem :
      ∀ z : ℂ,
        z ≠ 0 →
        ‖z‖ ≤ r →
        F z = f z) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ≠ 0 →
        ‖z‖ ≤ r →
        ‖f z‖ ≤ C := by
  rcases compact_closedBall_norm_bound_of_continuousOn F r hF with
    ⟨C, hC_pos, hC_bound⟩
  refine ⟨C, hC_pos, ?_⟩
  intro z hz_ne_zero hz_norm
  have hF_eq : F z = f z :=
    hrem z hz_ne_zero hz_norm
  exact Eq.subst
    (motive := fun w : ℂ => ‖w‖ ≤ C)
    hF_eq
    (hC_bound z hz_norm)

/-- A compact removable extension controls the original punctured function on a
specified region inside the closed ball. -/
theorem compact_closedBall_punctured_region_norm_bound_of_removable_extension
    (f F : ℂ → ℂ)
    (r : ℝ)
    (P : ℂ → Prop)
    (hF : ContinuousOn F (Metric.closedBall (0 : ℂ) r))
    (hrem :
      ∀ z : ℂ,
        P z →
        z ≠ 0 →
        ‖z‖ ≤ r →
        F z = f z) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        P z →
        z ≠ 0 →
        ‖z‖ ≤ r →
        ‖f z‖ ≤ C := by
  rcases compact_closedBall_norm_bound_of_continuousOn F r hF with
    ⟨C, hC_pos, hC_bound⟩
  refine ⟨C, hC_pos, ?_⟩
  intro z hzP hz_ne_zero hz_norm
  have hF_eq : F z = f z :=
    hrem z hzP hz_ne_zero hz_norm
  exact Eq.subst
    (motive := fun w : ℂ => ‖w‖ ≤ C)
    hF_eq
    (hC_bound z hz_norm)

/-- The closed left half of the unit ball used for the near-origin multiplier. -/
def poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet :
    Set ℂ :=
  {z : ℂ | z.re ≤ 0 ∧ ‖z‖ ≤ 1}

/-- Compactness of the closed left half-unit ball. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet_isCompact :
    IsCompact poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet := by
  have hclosed_left : IsClosed {z : ℂ | z.re ≤ 0} :=
    isClosed_le Complex.continuous_re continuous_const
  have hclosed_ball : IsClosed {z : ℂ | ‖z‖ ≤ 1} :=
    isClosed_le continuous_norm continuous_const
  have hclosed :
      IsClosed poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet := by
    have hset :
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet =
          {z : ℂ | z.re ≤ 0} ∩ {z : ℂ | ‖z‖ ≤ 1} := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, hz.2⟩
      · intro hz
        exact ⟨hz.1, hz.2⟩
    exact Eq.subst
      (motive := fun S : Set ℂ => IsClosed S)
      hset.symm
      (hclosed_left.inter hclosed_ball)
  have hbounded :
      Bornology.IsBounded
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet := by
    refine isBounded_iff_forall_norm_le.2 ⟨1, ?_⟩
    intro z hz
    exact hz.2
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbounded

/-- Compact norm boundedness from a continuous extension on the closed left
half-unit ball. -/
theorem compact_nearOriginLeftSet_norm_bound_of_continuousOn
    (F : ℂ → ℂ)
    (hF :
      ContinuousOn F
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖z‖ ≤ 1 →
        ‖F z‖ ≤ C := by
  rcases IsCompact.exists_bound_of_continuousOn
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet_isCompact
      hF with
    ⟨C0, hC0⟩
  refine ⟨max C0 0 + 1, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos (le_max_right C0 0) zero_lt_one
  intro z hz_re hz_norm
  have hz_mem :
      z ∈ poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet :=
    ⟨hz_re, hz_norm⟩
  have hraw : ‖F z‖ ≤ C0 :=
    hC0 z hz_mem
  exact le_trans hraw
    (le_trans (le_max_left C0 0) (le_add_of_nonneg_right zero_le_one))

/-- A compact removable extension on the closed left half-unit ball controls
the punctured raw branch there. -/
theorem compact_nearOriginLeftSet_punctured_norm_bound_of_removable_extension
    (f F : ℂ → ℂ)
    (hF :
      ContinuousOn F
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet)
    (hrem :
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        ‖z‖ ≤ 1 →
        F z = f z) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        ‖z‖ ≤ 1 →
        ‖f z‖ ≤ C := by
  rcases compact_nearOriginLeftSet_norm_bound_of_continuousOn F hF with
    ⟨C, hC_pos, hC_bound⟩
  refine ⟨C, hC_pos, ?_⟩
  intro z hz_re hz_ne_zero hz_norm
  have hF_eq : F z = f z :=
    hrem z hz_re hz_ne_zero hz_norm
  exact Eq.subst
    (motive := fun w : ℂ => ‖w‖ ≤ C)
    hF_eq
    (hC_bound z hz_re hz_norm)

/-- The real coordinate is bounded by the complex norm. -/
theorem complex_abs_re_le_norm
    (z : ℂ) :
    |z.re| ≤ ‖z‖ := by
  have habs : |z.re| ≤ Complex.abs z :=
    Complex.abs_re_le_abs z
  have hnorm : ‖z‖ = Complex.abs z :=
    Complex.norm_eq_abs z
  exact Eq.subst
    (motive := fun x : ℝ => |z.re| ≤ x)
    hnorm.symm
    habs

/-- `Gammaℝ` has no zero in the punctured closed unit ball. -/
theorem Gammaℝ_ne_zero_of_ne_zero_norm_le_one
    {z : ℂ}
    (hz_ne_zero : z ≠ 0)
    (hz_norm : ‖z‖ ≤ 1) :
    Complex.Gammaℝ z ≠ 0 := by
  intro hGamma_zero
  rcases Complex.Gammaℝ_eq_zero_iff.mp hGamma_zero with ⟨n, hz_eq⟩
  cases n with
  | zero =>
      have hz_zero : z = 0 := by
        calc
          z = -(2 * ((0 : ℕ) : ℂ)) := hz_eq
          _ = -0 := by
            exact congrArg Neg.neg (mul_zero (2 : ℂ))
          _ = 0 := by
            exact neg_zero
      exact hz_ne_zero hz_zero
  | succ n =>
      have hprod_re :
          (2 * ((Nat.succ n : ℕ) : ℂ)).re =
            (2 : ℝ) * (Nat.succ n : ℝ) := by
        calc
          (2 * ((Nat.succ n : ℕ) : ℂ)).re =
              (2 : ℂ).re * ((Nat.succ n : ℕ) : ℂ).re -
                (2 : ℂ).im * ((Nat.succ n : ℕ) : ℂ).im := by
            exact Complex.mul_re (2 : ℂ) ((Nat.succ n : ℕ) : ℂ)
          _ = (2 : ℝ) * (Nat.succ n : ℝ) -
                (2 : ℂ).im * ((Nat.succ n : ℕ) : ℂ).im := by
            exact congrArg
              (fun x : ℝ =>
                x * ((Nat.succ n : ℕ) : ℂ).re -
                  (2 : ℂ).im * ((Nat.succ n : ℕ) : ℂ).im)
              (Complex.natCast_re 2)
          _ = (2 : ℝ) * (Nat.succ n : ℝ) -
                (2 : ℂ).im * 0 := by
            exact congrArg
              (fun x : ℝ =>
                (2 : ℝ) * (Nat.succ n : ℝ) - (2 : ℂ).im * x)
              (Complex.natCast_im (Nat.succ n))
          _ = (2 : ℝ) * (Nat.succ n : ℝ) - 0 * 0 := by
            exact congrArg
              (fun x : ℝ =>
                (2 : ℝ) * (Nat.succ n : ℝ) - x * 0)
              (Complex.natCast_im 2)
          _ = (2 : ℝ) * (Nat.succ n : ℝ) - 0 := by
            exact congrArg
              (fun x : ℝ => (2 : ℝ) * (Nat.succ n : ℝ) - x)
              (zero_mul 0)
          _ = (2 : ℝ) * (Nat.succ n : ℝ) := by
            exact sub_zero ((2 : ℝ) * (Nat.succ n : ℝ))
      have hz_re_eq :
          z.re = -((2 : ℝ) * (Nat.succ n : ℝ)) := by
        calc
          z.re = (-(2 * ((Nat.succ n : ℕ) : ℂ))).re := by
            exact congrArg Complex.re hz_eq
          _ = -((2 * ((Nat.succ n : ℕ) : ℂ)).re) := by
            exact Complex.neg_re (2 * ((Nat.succ n : ℕ) : ℂ))
          _ = -((2 : ℝ) * (Nat.succ n : ℝ)) := by
            exact congrArg Neg.neg hprod_re
      have hsucc_ge_one : (1 : ℝ) ≤ (Nat.succ n : ℝ) :=
        Nat.cast_le.mpr (Nat.succ_le_succ (Nat.zero_le n))
      have htwo_le_prod : (2 : ℝ) ≤ (2 : ℝ) * (Nat.succ n : ℝ) := by
        calc
          (2 : ℝ) = 2 * 1 := by
            exact (mul_one 2).symm
          _ ≤ 2 * (Nat.succ n : ℝ) := by
            exact mul_le_mul_of_nonneg_left hsucc_ge_one (le_of_lt zero_lt_two)
      have hprod_nonneg : 0 ≤ (2 : ℝ) * (Nat.succ n : ℝ) :=
        le_trans (le_of_lt zero_lt_two) htwo_le_prod
      have habs_eq :
          |z.re| = (2 : ℝ) * (Nat.succ n : ℝ) := by
        calc
          |z.re| = |-((2 : ℝ) * (Nat.succ n : ℝ))| := by
            exact congrArg abs hz_re_eq
          _ = (2 : ℝ) * (Nat.succ n : ℝ) := by
            exact abs_of_nonneg hprod_nonneg
      have htwo_le_norm : (2 : ℝ) ≤ ‖z‖ := by
        exact le_trans
          (Eq.subst
            (motive := fun x : ℝ => (2 : ℝ) ≤ x)
            habs_eq.symm
            htwo_le_prod)
          (complex_abs_re_le_norm z)
      have htwo_le_one : (2 : ℝ) ≤ 1 :=
        le_trans htwo_le_norm hz_norm
      exact not_lt_of_ge htwo_le_one one_lt_two

/-- In the punctured unit ball, `z / 2` avoids the poles of `Complex.Gamma`. -/
theorem Gamma_half_ne_neg_nat_of_ne_zero_norm_le_one
    {z : ℂ}
    (hz_ne_zero : z ≠ 0)
    (hz_norm : ‖z‖ ≤ 1) :
    ∀ m : ℕ, z / 2 ≠ -m := by
  intro m hhalf
  cases m with
  | zero =>
      have hz_div_zero : z / 2 = 0 := by
        calc
          z / 2 = -((0 : ℕ) : ℂ) := hhalf
          _ = -0 := by
            exact congrArg Neg.neg (Nat.cast_zero)
          _ = 0 := by
            exact neg_zero
      have hz_zero : z = 0 := by
        exact div_eq_zero_iff.mp hz_div_zero |>.resolve_right two_ne_zero
      exact hz_ne_zero hz_zero
  | succ n =>
      have hz_eq :
          z = -(2 * ((Nat.succ n : ℕ) : ℂ)) := by
        calc
          z = (z / 2) * 2 := by
            exact (div_mul_cancel₀ z two_ne_zero).symm
          _ = (-((Nat.succ n : ℕ) : ℂ)) * 2 := by
            exact congrArg (fun w : ℂ => w * 2) hhalf
          _ = -(2 * ((Nat.succ n : ℕ) : ℂ)) := by
            calc
              (-((Nat.succ n : ℕ) : ℂ)) * 2 =
                  -( ((Nat.succ n : ℕ) : ℂ) * 2) := by
                exact neg_mul (((Nat.succ n : ℕ) : ℂ)) 2
              _ = -(2 * ((Nat.succ n : ℕ) : ℂ)) := by
                exact congrArg Neg.neg (mul_comm (((Nat.succ n : ℕ) : ℂ)) 2)
      have hGamma_zero : Complex.Gammaℝ z = 0 :=
        Complex.Gammaℝ_eq_zero_iff.mpr ⟨Nat.succ n, hz_eq⟩
      exact Gammaℝ_ne_zero_of_ne_zero_norm_le_one hz_ne_zero hz_norm hGamma_zero

/-- `Gammaℝ` is continuous in the punctured unit ball. -/
theorem Gammaℝ_continuousAt_of_ne_zero_norm_le_one
    {z : ℂ}
    (hz_ne_zero : z ≠ 0)
    (hz_norm : ‖z‖ ≤ 1) :
    ContinuousAt Complex.Gammaℝ z := by
  have hGamma :
      ContinuousAt (fun w : ℂ => Complex.Gamma (w / 2)) z := by
    exact
      (Complex.differentiableAt_Gamma
        (z / 2)
        (Gamma_half_ne_neg_nat_of_ne_zero_norm_le_one hz_ne_zero hz_norm)).continuousAt.comp
        (continuousAt_id.div_const 2)
  have hpow :
      ContinuousAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) z :=
    (continuousAt_id.neg.div_const 2).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact hpow.mul hGamma

/-- `Gammaℝ` is continuous at right-half-plane points. -/
theorem Gammaℝ_continuousAt_of_re_pos
    {z : ℂ}
    (hz_re : 0 < z.re) :
    ContinuousAt Complex.Gammaℝ z := by
  have hGamma :
      ContinuousAt (fun w : ℂ => Complex.Gamma (w / 2)) z := by
    have hpoles : ∀ m : ℕ, z / 2 ≠ -m := by
      intro m hhalf
      have hhalf_re_pos : 0 < (z / 2).re := by
        calc
          0 < z.re / 2 := div_pos hz_re two_pos
          _ = (z / 2).re := by
            exact (Complex.div_re_ofReal z 2).symm
      have hhalf_re_nonpos : (z / 2).re ≤ 0 := by
        have hneg_re :
            (-((m : ℕ) : ℂ)).re ≤ 0 := by
          calc
            (-((m : ℕ) : ℂ)).re = -(((m : ℕ) : ℂ).re) := by
              exact Complex.neg_re (((m : ℕ) : ℂ))
            _ = -((m : ℕ) : ℝ) := by
              exact congrArg Neg.neg (Complex.natCast_re m)
            _ ≤ 0 := by
              exact neg_nonpos.mpr (Nat.cast_nonneg m)
        exact Eq.subst
          (motive := fun w : ℂ => w.re ≤ 0)
          hhalf.symm
          hneg_re
      exact not_le_of_gt hhalf_re_pos hhalf_re_nonpos
    exact (Complex.differentiableAt_Gamma (z / 2) hpoles).continuousAt.comp
      (continuousAt_id.div_const 2)
  have hpow :
      ContinuousAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) z :=
    (continuousAt_id.neg.div_const 2).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact hpow.mul hGamma

/-- On the punctured closed left half-unit ball, the multiplier unfolds to the
raw Gamma-ratio branch. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_eq_raw_on_nearOriginLeftSet_of_ne_zero
    {z : ℂ}
    (hz_mem :
      z ∈ poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet)
    (hz_ne_zero : z ≠ 0) :
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
      ((z - 1) / (((1 : ℂ) - z) - 1)) *
        (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
  have hGamma_ne :
      Complex.Gammaℝ z ≠ 0 :=
    Gammaℝ_ne_zero_of_ne_zero_norm_le_one hz_ne_zero hz_mem.2
  unfold poleClearedRiemannZeta_completedFunctionalEquationMultiplier
  exact Eq.trans (if_neg hz_ne_zero) (if_neg hGamma_ne)

/-- The raw Gamma-ratio branch is continuous at nonzero points of the closed
left half-unit ball. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_continuousAt_nearOriginLeftSet_of_ne_zero
    {z : ℂ}
    (hz_mem :
      z ∈ poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet)
    (hz_ne_zero : z ≠ 0) :
    ContinuousAt
      (fun w : ℂ =>
        ((w - 1) / (((1 : ℂ) - w) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - w) / Complex.Gammaℝ w))
      z := by
  have hden_raw : (((1 : ℂ) - z) - 1) ≠ 0 := by
    intro hden_zero
    have hneg_zero : -z = 0 := by
      exact Eq.trans
        (show -z = ((1 : ℂ) - z) - 1 by
          exact (sub_sub_cancel_left (1 : ℂ) z).symm)
        hden_zero
    exact hz_ne_zero (neg_eq_zero.mp hneg_zero)
  have hGamma_z_ne :
      Complex.Gammaℝ z ≠ 0 :=
    Gammaℝ_ne_zero_of_ne_zero_norm_le_one hz_ne_zero hz_mem.2
  have hreflect_re_pos : 0 < ((1 : ℂ) - z).re := by
    have hsub_pos : 0 < 1 - z.re :=
      sub_pos.mpr (lt_of_lt_of_le zero_lt_one hz_mem.1)
    have hcoord : ((1 : ℂ) - z).re = 1 - z.re := by
      calc
        ((1 : ℂ) - z).re = (1 : ℂ).re - z.re := by
          exact Complex.sub_re (1 : ℂ) z
        _ = 1 - z.re := by
          exact congrArg (fun x : ℝ => x - z.re) Complex.one_re
    exact Eq.subst
      (motive := fun x : ℝ => 0 < x)
      hcoord.symm
      hsub_pos
  have hfactor :
      ContinuousAt
        (fun w : ℂ => (w - 1) / (((1 : ℂ) - w) - 1)) z :=
    (continuousAt_id.sub continuousAt_const).div
      ((continuousAt_const.sub continuousAt_id).sub continuousAt_const)
      hden_raw
  have hGamma_reflect :
      ContinuousAt (fun w : ℂ => Complex.Gammaℝ ((1 : ℂ) - w)) z :=
    (Gammaℝ_continuousAt_of_re_pos hreflect_re_pos).comp
      (continuousAt_const.sub continuousAt_id)
  have hGamma_current :
      ContinuousAt (fun w : ℂ => Complex.Gammaℝ w) z :=
    Gammaℝ_continuousAt_of_ne_zero_norm_le_one hz_ne_zero hz_mem.2
  have hratio :
      ContinuousAt
        (fun w : ℂ => Complex.Gammaℝ ((1 : ℂ) - w) / Complex.Gammaℝ w) z :=
    hGamma_reflect.div hGamma_current hGamma_z_ne
  exact hfactor.mul hratio

/-- Away from `0` inside the closed left half-unit ball, the completed
functional-equation multiplier is locally the raw Gamma-ratio expression and is
continuous there. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_continuousWithinAt_nearOriginLeftSet_of_ne_zero
    {z : ℂ}
    (hz_mem :
      z ∈ poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet)
    (hz_ne_zero : z ≠ 0) :
    ContinuousWithinAt poleClearedRiemannZeta_completedFunctionalEquationMultiplier
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet z := by
  have hraw_cont :
      ContinuousAt
        (fun w : ℂ =>
          ((w - 1) / (((1 : ℂ) - w) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - w) / Complex.Gammaℝ w))
        z :=
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_continuousAt_nearOriginLeftSet_of_ne_zero
      hz_mem hz_ne_zero
  have hbranch :
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier =ᶠ[
        𝓝[
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet] z]
        (fun w : ℂ =>
          ((w - 1) / (((1 : ℂ) - w) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - w) / Complex.Gammaℝ w)) := by
    have hpunctured : ∀ᶠ w in 𝓝 z, w ≠ 0 :=
      eventually_ne_nhds hz_ne_zero
    have hwithin :
        ∀ᶠ w in
          𝓝[
            poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet] z,
          w ≠ 0 :=
      hpunctured.filter_mono nhdsWithin_le_nhds
    have hregional :
        ∀ᶠ w in
          𝓝[
            poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet] z,
          w ≠ 0 ∧
            w ∈
              poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet :=
      hwithin.and self_mem_nhdsWithin
    exact hregional.mono
      (fun w hw =>
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier_eq_raw_on_nearOriginLeftSet_of_ne_zero
          hw.2 hw.1)
  exact
    hraw_cont.continuousWithinAt.congr_of_eventuallyEq
      hbranch
      (poleClearedRiemannZeta_completedFunctionalEquationMultiplier_eq_raw_on_nearOriginLeftSet_of_ne_zero
        hz_mem hz_ne_zero)

/-- The reflected pole-cleared denominator stays nonzero near the origin. -/
theorem poleClearedRiemannZeta_reflected_near_zero_nonzero_eventually :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      poleClearedRiemannZeta ((1 : ℂ) - z) ≠ 0 := by
  have hcont :
      ContinuousAt (fun z : ℂ => poleClearedRiemannZeta ((1 : ℂ) - z)) 0 :=
    (poleClearedRiemannZeta_continuousAt 1).comp
      (continuousAt_const.sub continuousAt_id)
  have hvalue :
      poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) ≠ 0 := by
    have hsub : (1 : ℂ) - (0 : ℂ) = 1 :=
      sub_zero (1 : ℂ)
    have hpole : poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) = 1 :=
      Eq.subst
        (motive := fun w : ℂ => poleClearedRiemannZeta w = 1)
        hsub.symm
        poleClearedRiemannZeta_one
    exact hpole.trans_ne one_ne_zero
  exact hcont.eventually_ne hvalue

/-- Near `0` on the left half-unit ball, the removable multiplier agrees with
the pole-cleared quotient. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_eq_poleCleared_quotient_eventually_zero_nearOriginLeftSet :
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier =ᶠ[
      𝓝[
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet] (0 : ℂ)]
      (fun z : ℂ =>
        poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z)) := by
  have hden_nhds :
      ∀ᶠ z in 𝓝 (0 : ℂ),
        poleClearedRiemannZeta ((1 : ℂ) - z) ≠ 0 :=
    poleClearedRiemannZeta_reflected_near_zero_nonzero_eventually
  have hden_within :
      ∀ᶠ z in
        𝓝[
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet] (0 : ℂ),
        poleClearedRiemannZeta ((1 : ℂ) - z) ≠ 0 :=
    hden_nhds.filter_mono nhdsWithin_le_nhds
  have hregional :
      ∀ᶠ z in
        𝓝[
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet] (0 : ℂ),
        poleClearedRiemannZeta ((1 : ℂ) - z) ≠ 0 ∧
          z ∈
            poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet :=
    hden_within.and self_mem_nhdsWithin
  exact hregional.mono
    (fun z hz =>
      by
        have hden_ne :
            poleClearedRiemannZeta ((1 : ℂ) - z) ≠ 0 := hz.1
        have hz_mem :
            z ∈
              poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet := hz.2
        by_cases hz_zero : z = 0
        · have hM :
              poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
                poleClearedRiemannZeta 0 := by
            exact Eq.subst
              (motive := fun w : ℂ =>
                poleClearedRiemannZeta_completedFunctionalEquationMultiplier w =
                  poleClearedRiemannZeta 0)
              hz_zero.symm
              (by
                unfold poleClearedRiemannZeta_completedFunctionalEquationMultiplier
                exact if_pos rfl)
          have hsub : (1 : ℂ) - z = 1 := by
            exact Eq.subst
              (motive := fun w : ℂ => (1 : ℂ) - w = 1)
              hz_zero.symm
              (sub_zero (1 : ℂ))
          have hnum :
              poleClearedRiemannZeta z = poleClearedRiemannZeta 0 :=
            congrArg poleClearedRiemannZeta hz_zero
          have hden :
              poleClearedRiemannZeta ((1 : ℂ) - z) = 1 :=
            Eq.subst
              (motive := fun w : ℂ => poleClearedRiemannZeta w = 1)
              hsub.symm
              poleClearedRiemannZeta_one
          calc
            poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
                poleClearedRiemannZeta 0 := hM
            _ = poleClearedRiemannZeta 0 / 1 := by
              exact (div_one (poleClearedRiemannZeta 0)).symm
            _ = poleClearedRiemannZeta z /
                  poleClearedRiemannZeta ((1 : ℂ) - z) := by
              exact congrArg₂ HDiv.hDiv hnum.symm hden.symm
        · have hidentity :
              poleClearedRiemannZeta z =
                poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
                  poleClearedRiemannZeta ((1 : ℂ) - z) :=
            poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity_of_ne_zero
              hz_mem.1 hz_zero
          calc
            poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
                (poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
                  poleClearedRiemannZeta ((1 : ℂ) - z)) /
                  poleClearedRiemannZeta ((1 : ℂ) - z) := by
              exact (mul_div_cancel_right₀
                (poleClearedRiemannZeta_completedFunctionalEquationMultiplier z)
                hden_ne).symm
            _ = poleClearedRiemannZeta z /
                  poleClearedRiemannZeta ((1 : ℂ) - z) := by
              exact congrArg
                (fun w : ℂ =>
                  w / poleClearedRiemannZeta ((1 : ℂ) - z))
                hidentity.symm)

/-- The pole-cleared reflected quotient is continuous at the origin. -/
theorem poleClearedRiemannZeta_reflected_quotient_continuousAt_zero :
    ContinuousAt
      (fun z : ℂ =>
        poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z))
      (0 : ℂ) := by
  have hnum : ContinuousAt poleClearedRiemannZeta (0 : ℂ) :=
    poleClearedRiemannZeta_continuousAt 0
  have hden :
      ContinuousAt (fun z : ℂ => poleClearedRiemannZeta ((1 : ℂ) - z)) 0 :=
    (poleClearedRiemannZeta_continuousAt 1).comp
      (continuousAt_const.sub continuousAt_id)
  have hden_ne :
      poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) ≠ 0 := by
    have hsub : (1 : ℂ) - (0 : ℂ) = 1 :=
      sub_zero (1 : ℂ)
    have hpole : poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) = 1 :=
      Eq.subst
        (motive := fun w : ℂ => poleClearedRiemannZeta w = 1)
        hsub.symm
        poleClearedRiemannZeta_one
    exact hpole.trans_ne one_ne_zero
  exact hnum.div hden hden_ne

/-- Removable continuity of the completed-functional-equation multiplier at the
origin on the closed left half-unit ball. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_continuousWithinAt_zero_nearOriginLeftSet :
    ContinuousWithinAt poleClearedRiemannZeta_completedFunctionalEquationMultiplier
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet 0 := by
  have hquotient :
      ContinuousWithinAt
        (fun z : ℂ =>
          poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z))
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet
        (0 : ℂ) :=
    poleClearedRiemannZeta_reflected_quotient_continuousAt_zero.continuousWithinAt
  have hagree :
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier =ᶠ[
        𝓝[
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet] (0 : ℂ)]
        (fun z : ℂ =>
          poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z)) :=
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_eq_poleCleared_quotient_eventually_zero_nearOriginLeftSet
  have hvalue :
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier 0 =
        poleClearedRiemannZeta 0 / poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) := by
    have hM :
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier 0 =
          poleClearedRiemannZeta 0 := by
      unfold poleClearedRiemannZeta_completedFunctionalEquationMultiplier
      exact if_pos rfl
    have hden :
        poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) = 1 := by
      have hsub : (1 : ℂ) - (0 : ℂ) = 1 :=
        sub_zero (1 : ℂ)
      exact Eq.subst
        (motive := fun w : ℂ => poleClearedRiemannZeta w = 1)
        hsub.symm
        poleClearedRiemannZeta_one
    calc
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier 0 =
          poleClearedRiemannZeta 0 := hM
      _ = poleClearedRiemannZeta 0 / 1 := by
        exact (div_one (poleClearedRiemannZeta 0)).symm
      _ = poleClearedRiemannZeta 0 /
            poleClearedRiemannZeta ((1 : ℂ) - (0 : ℂ)) := by
        exact congrArg
          (fun w : ℂ => poleClearedRiemannZeta 0 / w)
          hden.symm
  exact hquotient.congr_of_eventuallyEq hagree hvalue

/-- Trivial-zero cancellation for the pole-cleared zeta factor at nonzero
`Gammaℝ` zero faces in the left half-plane.

This is the standard classical input: `Gammaℝ z = 0` means `z` is a
nonpositive even integer; after excluding `0`, these are exactly the negative
even integers, where `ζ` has its trivial zeros.  The pole-cleared factor has no
pole at such points, so it vanishes. -/
theorem poleClearedRiemannZeta_trivialZero_of_gammaZero_leftHalfPlane
    {z : ℂ}
    (hz_re : z.re ≤ 0)
    (hz_ne_zero : z ≠ 0)
    (hGamma_zero : Complex.Gammaℝ z = 0) :
    poleClearedRiemannZeta z = 0 := by
  rcases Complex.Gammaℝ_eq_zero_iff.mp hGamma_zero with ⟨n, hz_eq⟩
  cases n with
  | zero =>
      have hz_zero : z = 0 := by
        calc
          z = -(2 * ((0 : ℕ) : ℂ)) := hz_eq
          _ = -0 := by
            exact congrArg Neg.neg (mul_zero (2 : ℂ))
          _ = 0 := by
            exact neg_zero
      exact False.elim (hz_ne_zero hz_zero)
  | succ n =>
      have hz_ne_one : z ≠ 1 := by
        intro hz_one
        have hz_re_one : z.re = 1 := by
          calc
            z.re = (1 : ℂ).re := by
              exact congrArg Complex.re hz_one
            _ = 1 := by
              exact Complex.one_re
        have hone_le_zero : (1 : ℝ) ≤ 0 :=
          Eq.subst
            (motive := fun x : ℝ => x ≤ 0)
            hz_re_one.symm
            hz_re
        exact not_lt_of_ge hone_le_zero zero_lt_one
      have hpole :
          poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
        poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
      have hzeta_zero_at :
          riemannZeta (-(2 * ((Nat.succ n : ℕ) : ℂ))) = 0 :=
        riemannZeta_neg_two_mul_nat_add_one n
      have hzeta_zero : riemannZeta z = 0 := by
        exact Eq.subst
          (motive := fun w : ℂ => riemannZeta w = 0)
          hz_eq.symm
          hzeta_zero_at
      calc
        poleClearedRiemannZeta z = (z - 1) * riemannZeta z := hpole
        _ = (z - 1) * 0 := by
          exact congrArg (fun w : ℂ => (z - 1) * w) hzeta_zero
        _ = 0 := by
          exact mul_zero (z - 1)

/-- Finite-order envelope for the removable completed-functional-equation
multiplier on the left half-plane.

Analytically this is exactly the Gamma-ratio/Stirling estimate plus the
removable boundedness at `z = 0`; cf. Titchmarsh, Ch. 2 and Edwards, Ch. 1. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_gammaZeroBranch_leftHalfPlane_growth_from_trivialZero_discrete_localBoundedness :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        Complex.Gammaℝ z = 0 →
        ‖poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  refine ⟨1, 1, 0, zero_lt_one, zero_lt_one, ?_⟩
  intro z hz_re hz_ne_zero hGamma_zero
  have hnumerator_zero :
      poleClearedRiemannZeta z = 0 :=
    poleClearedRiemannZeta_trivialZero_of_gammaZero_leftHalfPlane
      hz_re hz_ne_zero hGamma_zero
  have hquot_zero :
      poleClearedRiemannZeta z /
          poleClearedRiemannZeta ((1 : ℂ) - z) = 0 := by
    calc
      poleClearedRiemannZeta z /
          poleClearedRiemannZeta ((1 : ℂ) - z) =
          0 / poleClearedRiemannZeta ((1 : ℂ) - z) := by
        exact congrArg
          (fun w : ℂ => w / poleClearedRiemannZeta ((1 : ℂ) - z))
          hnumerator_zero
      _ = 0 := by
        exact zero_div (poleClearedRiemannZeta ((1 : ℂ) - z))
  have hnorm_zero :
      ‖poleClearedRiemannZeta z /
          poleClearedRiemannZeta ((1 : ℂ) - z)‖ = 0 :=
    congrArg norm hquot_zero
  have htarget_pos :
      0 < (1 : ℝ) * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) :=
    mul_pos zero_lt_one (Real.exp_pos ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)))
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ (1 : ℝ) * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)))
    hnorm_zero.symm
    (le_of_lt htarget_pos)

/-- Gamma-zero branch growth from discreteness of the trivial-zero faces and
local boundedness of the removable quotient. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_gammaZeroBranch_leftHalfPlane_growth :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        Complex.Gammaℝ z = 0 →
        ‖poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_gammaZeroBranch_leftHalfPlane_growth_from_trivialZero_discrete_localBoundedness

theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_leftHalfPlane_growth_of_raw_and_removable
    (hgammaZero :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          z ≠ 0 →
          Complex.Gammaℝ z = 0 →
          ‖poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hraw :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          z ≠ 0 →
          ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
              (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hgammaZero with ⟨Az, Bz, mz, hAz, hBz, hgammaZero_bound⟩
  rcases hraw with ⟨A, B, m, hA, hB, hraw_bound⟩
  let C : ℝ := ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier 0‖
  refine ⟨Az + A + C + 1, Bz + B, mz + m, ?_, add_pos hBz hB, ?_⟩
  · have hC_one_pos : 0 < C + 1 :=
      add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
    have hA_C_pos : 0 < A + (C + 1) :=
      add_pos hA hC_one_pos
    have hA_add_pos : 0 < Az + (A + (C + 1)) :=
      add_pos hAz hA_C_pos
    exact Eq.subst
      (motive := fun x : ℝ => 0 < x)
      (by
        calc
          Az + (A + (C + 1)) = Az + ((A + C) + 1) := by
            exact congrArg (fun x : ℝ => Az + x) (add_assoc A C 1).symm
          _ = Az + (A + C) + 1 := by
            exact add_assoc Az (A + C) 1
          _ = Az + A + C + 1 := by
            exact congrArg (fun x : ℝ => x + 1) (add_assoc Az A C).symm)
      hA_add_pos
  intro z hz_left
  have hAz_nonneg : 0 ≤ Az := le_of_lt hAz
  have hA_nonneg : 0 ≤ A := le_of_lt hA
  have hC_nonneg : 0 ≤ C := norm_nonneg _
  have hA_le : A ≤ Az + A + C + 1 := by
    calc
      A ≤ Az + A := le_add_of_nonneg_left hAz_nonneg
      _ ≤ Az + A + C := le_add_of_nonneg_right hC_nonneg
      _ ≤ Az + A + C + 1 := le_add_of_nonneg_right zero_le_one
  have hAz_le : Az ≤ Az + A + C + 1 := by
    calc
      Az ≤ Az + A := le_add_of_nonneg_right hA_nonneg
      _ ≤ Az + A + C := le_add_of_nonneg_right hC_nonneg
      _ ≤ Az + A + C + 1 := le_add_of_nonneg_right zero_le_one
  have hB_le : B ≤ Bz + B := le_add_of_nonneg_left (le_of_lt hBz)
  have hBz_le : Bz ≤ Bz + B := le_add_of_nonneg_right (le_of_lt hB)
  by_cases hz_zero : z = 0
  · have hM_zero :
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier 0 := by
      exact congrArg poleClearedRiemannZeta_completedFunctionalEquationMultiplier hz_zero
    have hnorm_eq :
        ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ = C := by
      exact congrArg norm hM_zero
    have hC_le_A : C ≤ Az + A + C + 1 := by
      calc
        C ≤ A + C := le_add_of_nonneg_left hA_nonneg
        _ ≤ Az + (A + C) := le_add_of_nonneg_left hAz_nonneg
        _ = Az + A + C := (add_assoc Az A C).symm
        _ ≤ Az + A + C + 1 := le_add_of_nonneg_right zero_le_one
    have hfactor_ge_one :
        (1 : ℝ) ≤ Real.exp ((Bz + B) * (1 + ‖z‖) ^ (mz + m)) := by
      have hbase_nonneg : 0 ≤ 1 + ‖z‖ :=
        le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
      have hexponent_nonneg : 0 ≤ (Bz + B) * (1 + ‖z‖) ^ (mz + m) :=
        mul_nonneg (le_of_lt (add_pos hBz hB)) (pow_nonneg hbase_nonneg (mz + m))
      exact le_trans (le_of_eq Real.exp_zero.symm)
        (Real.exp_le_exp.mpr hexponent_nonneg)
    have htarget :
        C ≤ (Az + A + C + 1) * Real.exp ((Bz + B) * (1 + ‖z‖) ^ (mz + m)) := by
      calc
        C ≤ Az + A + C + 1 := hC_le_A
        _ = (Az + A + C + 1) * 1 := by
          exact (mul_one (Az + A + C + 1)).symm
        _ ≤ (Az + A + C + 1) * Real.exp ((Bz + B) * (1 + ‖z‖) ^ (mz + m)) :=
          mul_le_mul_of_nonneg_left hfactor_ge_one
            (le_trans hC_nonneg hC_le_A)
    exact Eq.subst
      (motive := fun x : ℝ =>
        x ≤ (Az + A + C + 1) * Real.exp ((Bz + B) * (1 + ‖z‖) ^ (mz + m)))
      hnorm_eq.symm
      htarget
  · by_cases hGamma_zero : Complex.Gammaℝ z = 0
      · have hM_gamma :
            poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
              poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z) := by
          unfold poleClearedRiemannZeta_completedFunctionalEquationMultiplier
          exact Eq.trans (if_neg hz_zero) (if_pos hGamma_zero)
        have hbranch :
            ‖poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
              Az * Real.exp (Bz * (1 + ‖z‖) ^ mz) :=
          hgammaZero_bound z hz_left hz_zero hGamma_zero
        have henlarge :
            Az * Real.exp (Bz * (1 + ‖z‖) ^ mz) ≤
              (Az + A + C + 1) * Real.exp ((Bz + B) * (1 + ‖z‖) ^ (mz + m)) :=
          exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
            (le_of_lt hAz) hAz_le hBz_le (le_of_lt hBz)
            (Nat.le_add_right mz m)
        exact Eq.subst
          (motive := fun w : ℂ =>
            ‖w‖ ≤ (Az + A + C + 1) * Real.exp ((Bz + B) * (1 + ‖z‖) ^ (mz + m)))
          hM_gamma.symm
          (hbranch.trans henlarge)
      · have hM_raw :
            poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
              ((z - 1) / (((1 : ℂ) - z) - 1)) *
                (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
          unfold poleClearedRiemannZeta_completedFunctionalEquationMultiplier
          exact Eq.trans (if_neg hz_zero) (if_neg hGamma_zero)
        have hraw_z :
            ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
                (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
              A * Real.exp (B * (1 + ‖z‖) ^ m) :=
          hraw_bound z hz_left hz_zero
        have henlarge :
            A * Real.exp (B * (1 + ‖z‖) ^ m) ≤
              (Az + A + C + 1) * Real.exp ((Bz + B) * (1 + ‖z‖) ^ (mz + m)) :=
          exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
            hA_nonneg hA_le hB_le (le_of_lt hB)
            (by
              exact Eq.subst
                (motive := fun d : ℕ => m ≤ d)
                (Nat.add_comm m mz)
                (Nat.le_add_right m mz))
        exact Eq.subst
          (motive := fun w : ℂ =>
            ‖w‖ ≤ (Az + A + C + 1) * Real.exp ((Bz + B) * (1 + ‖z‖) ^ (mz + m)))
          hM_raw.symm
          (hraw_z.trans henlarge)

/-- Product-envelope exponential collapse for finite-order growth estimates.

This is the named algebra sink used when multiplying two estimates after both
have been enlarged to the same exponential envelope. -/
theorem finiteOrderGrowthProductEnvelope_exp_collapse
    (a b c : ℝ) :
    (a * Real.exp c) * (b * Real.exp c) =
      a * b * Real.exp (2 * c) := by
  let E : ℝ := Real.exp c
  have hleft :
      (a * E) * (b * E) = (a * b) * (E * E) := by
    calc
      (a * E) * (b * E) = ((a * E) * b) * E := by
        exact mul_assoc (a * E) b E
      _ = (a * (E * b)) * E := by
        exact congrArg (fun y : ℝ => y * E) (mul_assoc a E b)
      _ = (a * (b * E)) * E := by
        exact congrArg (fun y : ℝ => (a * y) * E) (mul_comm E b)
      _ = ((a * b) * E) * E := by
        exact congrArg (fun y : ℝ => y * E) (mul_assoc a b E).symm
      _ = (a * b) * (E * E) := by
        exact (mul_assoc (a * b) E E).symm
  have hdouble : c + c = 2 * c := by
    exact (two_mul c).symm
  calc
    (a * Real.exp c) * (b * Real.exp c) =
        (a * E) * (b * E) := rfl
    _ = (a * b) * (E * E) := hleft
    _ = (a * b) * Real.exp (c + c) := by
      exact congrArg (fun y : ℝ => (a * b) * y)
        (Real.exp_add c c).symm
    _ = (a * b) * Real.exp (2 * c) := by
      exact congrArg (fun y : ℝ => (a * b) * Real.exp y) hdouble
    _ = a * b * Real.exp (2 * c) := by
      exact mul_assoc a b (Real.exp (2 * c))

/-- Product of two left-half-plane finite-order envelopes is again finite-order.

This is the half-plane analogue of the boundary product lemma, used for the
completed-functional-equation multiplier. -/
theorem finiteOrder_leftHalfPlane_product_growth_bound
    {f g : ℂ → ℂ}
    (hf :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hg :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          ‖g z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖f z * g z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hf with ⟨Af, Bf, mf, hAf, hBf, hf_bound⟩
  rcases hg with ⟨Ag, Bg, mg, hAg, hBg, hg_bound⟩
  refine ⟨Af * Ag, 2 * (Bf + Bg + 1), mf + mg,
    mul_pos hAf hAg,
    mul_pos zero_lt_two (add_pos (add_pos hBf hBg) zero_lt_one), ?_⟩
  intro z hz_left
  let H : ℝ := 1 + ‖z‖
  have hBf_nonneg : 0 ≤ Bf := le_of_lt hBf
  have hBg_nonneg : 0 ≤ Bg := le_of_lt hBg
  have hAf_nonneg : 0 ≤ Af := le_of_lt hAf
  have hAg_nonneg : 0 ≤ Ag := le_of_lt hAg
  have hf_enlarge :
      Af * Real.exp (Bf * H ^ mf) ≤
        Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      hAf_nonneg
      (le_refl Af)
      (by
        calc
          Bf ≤ Bf + Bg := le_add_of_nonneg_right hBg_nonneg
          _ ≤ Bf + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBf_nonneg
      (Nat.le_add_right mf mg)
  have hmg_le : mg ≤ mf + mg := by
    exact Eq.subst
      (motive := fun d : ℕ => mg ≤ d)
      (Nat.add_comm mg mf)
      (Nat.le_add_right mg mf)
  have hg_enlarge :
      Ag * Real.exp (Bg * H ^ mg) ≤
        Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      hAg_nonneg
      (le_refl Ag)
      (by
        calc
          Bg ≤ Bf + Bg := le_add_of_nonneg_left hBf_nonneg
          _ ≤ Bf + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBg_nonneg
      hmg_le
  have hf_target :
      ‖f z‖ ≤ Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    (hf_bound z hz_left).trans hf_enlarge
  have hg_target :
      ‖g z‖ ≤ Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    (hg_bound z hz_left).trans hg_enlarge
  have hnorm :
      ‖f z * g z‖ = ‖f z‖ * ‖g z‖ :=
    norm_mul (f z) (g z)
  have hproduct :
      ‖f z‖ * ‖g z‖ ≤
        (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) :=
    mul_le_mul hf_target hg_target (norm_nonneg (g z))
      (mul_nonneg hAf_nonneg
        (le_of_lt (Real.exp_pos ((Bf + Bg + 1) * H ^ (mf + mg)))))
  have hcollapse :
      (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) =
        Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) :=
    finiteOrderGrowthProductEnvelope_exp_collapse
      Af Ag ((Bf + Bg + 1) * H ^ (mf + mg))
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)))
    hnorm.symm
    (hproduct.trans_eq hcollapse)

/-- Elementary finite-order growth of the pole-clearing rational factor on the
left half-plane away from the removable denominator and away from the
removable origin.

The extra hypothesis `1 ≤ ‖z‖` is essential: the rational factor
`(z - 1) / (((1 : ℂ) - z) - 1)` has a pole at `z = 0`.  The completed
multiplier is controlled near `0` only after the Gamma-ratio/removable
normalization is included. -/
theorem leftHalfPlane_completedFunctionalEquation_poleClearing_ratio_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        1 ≤ ‖z‖ →
        ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  refine ⟨2, 1, 1, zero_lt_two, zero_lt_one, ?_⟩
  intro z _hz_re hz_ne_zero hz_norm_ge_one
  have hz_norm_pos : 0 < ‖z‖ :=
    lt_of_le_of_ne (norm_nonneg z) (fun hnorm_zero =>
      hz_ne_zero (norm_eq_zero.mp hnorm_zero))
  have hden_eq : (((1 : ℂ) - z) - 1) = -z := by
    exact sub_sub_cancel (1 : ℂ) z
  have hnum_norm_le : ‖z - 1‖ ≤ ‖z‖ + 1 := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le z (1 : ℂ)
      _ = ‖z‖ + 1 := by
        exact congrArg (fun x : ℝ => ‖z‖ + x)
          (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
  have hnum_norm_le_H : ‖z - 1‖ ≤ 1 + ‖z‖ := by
    exact hnum_norm_le.trans_eq (add_comm ‖z‖ 1)
  have hratio_le_H_over_norm :
      ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤
        (1 + ‖z‖) / ‖z‖ := by
    calc
      ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ =
          ‖z - 1‖ / ‖(((1 : ℂ) - z) - 1)‖ := norm_div (z - 1) (((1 : ℂ) - z) - 1)
      _ = ‖z - 1‖ / ‖z‖ := by
        exact congrArg (fun x : ℝ => ‖z - 1‖ / x)
          (by
            calc
              ‖(((1 : ℂ) - z) - 1)‖ = ‖-z‖ := by
                exact congrArg norm hden_eq
              _ = ‖z‖ := norm_neg z)
      _ ≤ (1 + ‖z‖) / ‖z‖ :=
        div_le_div_of_nonneg_right hnum_norm_le_H (norm_nonneg z)
  have hratio_le_one_plus_inv :
      (1 + ‖z‖) / ‖z‖ = 1 / ‖z‖ + 1 := by
    calc
      (1 + ‖z‖) / ‖z‖ = 1 / ‖z‖ + ‖z‖ / ‖z‖ :=
        (add_div 1 ‖z‖ ‖z‖)
      _ = 1 / ‖z‖ + 1 := by
        exact congrArg (fun x : ℝ => 1 / ‖z‖ + x)
          (div_self (ne_of_gt hz_norm_pos))
  have hratio_poly :
      ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤
        (1 + ‖z‖) / ‖z‖ := hratio_le_H_over_norm
  have htarget_factor : (1 + ‖z‖) / ‖z‖ ≤ 2 := by
    have hnum_le : 1 + ‖z‖ ≤ 2 * ‖z‖ := by
      calc
        1 + ‖z‖ ≤ ‖z‖ + ‖z‖ :=
          add_le_add_right hz_norm_ge_one ‖z‖
        _ = 2 * ‖z‖ :=
          (two_mul ‖z‖).symm
    calc
      (1 + ‖z‖) / ‖z‖ ≤ (2 * ‖z‖) / ‖z‖ :=
        div_le_div_of_nonneg_right hnum_le (norm_nonneg z)
      _ = 2 :=
        mul_div_cancel_right₀ 2 (ne_of_gt hz_norm_pos)
  have hpoly_exp :
      (2 : ℝ) ≤
        2 * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ)) := by
    have hone_le_exp :
        (1 : ℝ) ≤ Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ)) := by
      have hbase_nonneg : 0 ≤ 1 + ‖z‖ :=
        le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
      have hexponent_nonneg :
          0 ≤ (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) :=
        mul_nonneg zero_le_one (pow_nonneg hbase_nonneg 1)
      exact le_trans (le_of_eq Real.exp_zero.symm)
        (Real.exp_le_exp.mpr hexponent_nonneg)
    calc
      (2 : ℝ) = 2 * 1 := (mul_one 2).symm
      _ ≤ 2 * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ)) :=
        mul_le_mul_of_nonneg_left hone_le_exp (le_of_lt zero_lt_two)
  exact hratio_poly.trans (htarget_factor.trans hpoly_exp)

/-- Reflection sends the closed left half-plane into the right half-plane
needed by Deligne's real-Gamma quotient identity. -/
theorem one_sub_leftHalfPlane_re_one_le
    {z : ℂ}
    (hz_re : z.re ≤ 0) :
    1 ≤ ((1 : ℂ) - z).re := by
  have hre_eq : ((1 : ℂ) - z).re = 1 - z.re := by
    calc
      ((1 : ℂ) - z).re = (1 : ℂ).re - z.re := Complex.sub_re (1 : ℂ) z
      _ = 1 - z.re := by
        exact congrArg (fun x : ℝ => x - z.re) Complex.one_re
  have hone_le : (1 : ℝ) ≤ 1 - z.re := by
    calc
      (1 : ℝ) = 1 - 0 := (sub_zero 1).symm
      _ ≤ 1 - z.re := sub_le_sub_left hz_re 1
  exact Eq.subst
    (motive := fun x : ℝ => (1 : ℝ) ≤ x)
    hre_eq.symm
    hone_le

/-- The reflected left-half-plane point is automatically in the
right-half-plane Stirling region at radius at least one. -/
theorem one_sub_leftHalfPlane_norm_one_le
    {z : ℂ}
    (hz_re : z.re ≤ 0) :
    1 ≤ ‖(1 : ℂ) - z‖ :=
  one_le_norm_of_one_le_re (one_sub_leftHalfPlane_re_one_le hz_re)

/-- The reflected point `1 - z` never meets the negative odd integers when
`z` is in the closed left half-plane.  This is exactly the side condition in
mathlib's Deligne identity `Gammaℝ_div_Gammaℝ_one_sub`. -/
theorem one_sub_leftHalfPlane_ne_negative_odd
    {z : ℂ}
    (hz_re : z.re ≤ 0)
    (n : ℕ) :
    (1 : ℂ) - z ≠ -(2 * n + 1) := by
  intro hodd
  have hz_re_eq : z.re = 2 * (n : ℝ) + 2 := by
    have hsub_re :
        ((1 : ℂ) - z).re = (-(2 * n + 1 : ℂ)).re :=
      congrArg Complex.re hodd
    have hleft_re : ((1 : ℂ) - z).re = 1 - z.re := by
      calc
        ((1 : ℂ) - z).re = (1 : ℂ).re - z.re := Complex.sub_re (1 : ℂ) z
        _ = 1 - z.re := by
          exact congrArg (fun x : ℝ => x - z.re) Complex.one_re
    have hright_re : (-(2 * n + 1 : ℂ)).re = -(2 * (n : ℝ) + 1) := by
      calc
        (-(2 * n + 1 : ℂ)).re = -((2 * n + 1 : ℂ).re) :=
          Complex.neg_re (2 * n + 1 : ℂ)
        _ = -(2 * (n : ℝ) + 1) := by
          exact congrArg Neg.neg (by
            calc
              ((2 * n + 1 : ℂ).re) =
                  ((2 : ℂ) * (n : ℂ) + (1 : ℂ)).re := rfl
              _ = ((2 : ℂ) * (n : ℂ)).re + (1 : ℂ).re :=
                  Complex.add_re ((2 : ℂ) * (n : ℂ)) (1 : ℂ)
              _ = ((2 : ℂ).re * (n : ℂ).re - (2 : ℂ).im * (n : ℂ).im) + 1 := by
                  exact congrArg (fun x : ℝ => x + (1 : ℂ).re)
                    (Complex.mul_re (2 : ℂ) (n : ℂ))
              _ = (2 * (n : ℝ) - 0 * 0) + 1 := by
                  exact congrArg (fun x : ℝ => x + 1)
                    (congrArg (fun x : ℝ => 2 * (n : ℝ) - 0 * x)
                      (Complex.ofReal_im (n : ℝ))).symm
              _ = 2 * (n : ℝ) + 1 := by
                  exact congrArg (fun x : ℝ => x + 1) (sub_zero (2 * (n : ℝ)))))
    have hsub_real : 1 - z.re = -(2 * (n : ℝ) + 1) :=
      Eq.trans hleft_re.symm (Eq.trans hsub_re hright_re)
    have hadd : (1 - z.re) + z.re = -(2 * (n : ℝ) + 1) + z.re :=
      congrArg (fun x : ℝ => x + z.re) hsub_real
    have hone_eq : 1 = -(2 * (n : ℝ) + 1) + z.re := by
      exact Eq.trans (sub_add_cancel 1 z.re).symm hadd
    have hsolve :
        z.re = 1 + (2 * (n : ℝ) + 1) := by
      calc
        z.re = z.re + 0 := (add_zero z.re).symm
        _ = z.re + ((2 * (n : ℝ) + 1) + -(2 * (n : ℝ) + 1)) := by
          exact congrArg (fun x : ℝ => z.re + x)
            (add_neg_cancel (2 * (n : ℝ) + 1)).symm
        _ = (z.re + -(2 * (n : ℝ) + 1)) + (2 * (n : ℝ) + 1) := by
          calc
            z.re + ((2 * (n : ℝ) + 1) + -(2 * (n : ℝ) + 1)) =
                z.re + (-(2 * (n : ℝ) + 1) + (2 * (n : ℝ) + 1)) := by
              exact congrArg (fun x : ℝ => z.re + x)
                (add_comm (2 * (n : ℝ) + 1) (-(2 * (n : ℝ) + 1)))
            _ = (z.re + -(2 * (n : ℝ) + 1)) + (2 * (n : ℝ) + 1) :=
              add_assoc z.re (-(2 * (n : ℝ) + 1)) (2 * (n : ℝ) + 1)
        _ = (-(2 * (n : ℝ) + 1) + z.re) + (2 * (n : ℝ) + 1) := by
          exact congrArg (fun x : ℝ => x + (2 * (n : ℝ) + 1))
            (add_comm z.re (-(2 * (n : ℝ) + 1)))
        _ = 1 + (2 * (n : ℝ) + 1) := by
          exact congrArg (fun x : ℝ => x + (2 * (n : ℝ) + 1)) hone_eq.symm
    calc
      z.re = 1 + (2 * (n : ℝ) + 1) := hsolve
      _ = 2 * (n : ℝ) + 2 := by
        calc
          1 + (2 * (n : ℝ) + 1) = (1 + 1) + 2 * (n : ℝ) := by
            exact Eq.trans (add_assoc 1 (2 * (n : ℝ)) 1).symm
              (congrArg (fun x : ℝ => x + 2 * (n : ℝ))
                (add_comm 1 1))
          _ = 2 * (n : ℝ) + 2 := by
            exact add_comm (1 + 1) (2 * (n : ℝ))
  have hz_re_pos : 0 < z.re := by
    have htwo_nonneg : 0 ≤ 2 * (n : ℝ) :=
      mul_nonneg zero_le_two (Nat.cast_nonneg n)
    have hright_pos : 0 < 2 * (n : ℝ) + 2 :=
      add_pos_of_nonneg_of_pos htwo_nonneg zero_lt_two
    exact Eq.subst
      (motive := fun x : ℝ => 0 < x)
      hz_re_eq.symm
      hright_pos
  exact not_lt_of_ge hz_re hz_re_pos

/-- Deligne reflection gives the raw left-half-plane real-Gamma quotient as
a right-half-plane `Gammaℂ` factor times the elementary cosine factor. -/
theorem Gammaℝ_leftHalfPlane_completedFunctionalEquation_ratio_eq_Gammaℂ_cos
    {z : ℂ}
    (hz_re : z.re ≤ 0) :
    Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z =
      Complex.Gammaℂ ((1 : ℂ) - z) *
        Complex.cos (π * ((1 : ℂ) - z) / 2) := by
  have hodd :
      ∀ n : ℕ, (1 : ℂ) - z ≠ -(2 * n + 1) :=
    fun n => one_sub_leftHalfPlane_ne_negative_odd hz_re n
  have hdeligne :
      Complex.Gammaℝ ((1 : ℂ) - z) /
          Complex.Gammaℝ (1 - ((1 : ℂ) - z)) =
        Complex.Gammaℂ ((1 : ℂ) - z) *
          Complex.cos (π * ((1 : ℂ) - z) / 2) :=
    Complex.Gammaℝ_div_Gammaℝ_one_sub hodd
  have hone_sub_sub : (1 : ℂ) - ((1 : ℂ) - z) = z := by
    exact sub_sub_cancel (1 : ℂ) z
  exact Eq.subst
    (motive := fun w : ℂ =>
      Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ w =
        Complex.Gammaℂ ((1 : ℂ) - z) *
          Complex.cos (π * ((1 : ℂ) - z) / 2))
    hone_sub_sub
    hdeligne

/-- Product of two right-half-plane finite-order envelopes is again a
right-half-plane finite-order envelope. -/
theorem finiteOrder_rightHalfPlane_product_growth_bound
    {f g : ℂ → ℂ}
    (hf :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          1 ≤ ‖z‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hg :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          1 ≤ ‖z‖ →
          ‖g z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        ‖f z * g z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hf with ⟨Af, Bf, mf, hAf, hBf, hf_bound⟩
  rcases hg with ⟨Ag, Bg, mg, hAg, hBg, hg_bound⟩
  refine ⟨Af * Ag, 2 * (Bf + Bg + 1), mf + mg,
    mul_pos hAf hAg,
    mul_pos zero_lt_two (add_pos (add_pos hBf hBg) zero_lt_one), ?_⟩
  intro z hz_re hz_norm
  let H : ℝ := 1 + ‖z‖
  have hBf_nonneg : 0 ≤ Bf := le_of_lt hBf
  have hBg_nonneg : 0 ≤ Bg := le_of_lt hBg
  have hAf_nonneg : 0 ≤ Af := le_of_lt hAf
  have hAg_nonneg : 0 ≤ Ag := le_of_lt hAg
  have hf_enlarge :
      Af * Real.exp (Bf * H ^ mf) ≤
        Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      hAf_nonneg
      (le_refl Af)
      (by
        calc
          Bf ≤ Bf + Bg := le_add_of_nonneg_right hBg_nonneg
          _ ≤ Bf + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBf_nonneg
      (Nat.le_add_right mf mg)
  have hmg_le : mg ≤ mf + mg := by
    exact Eq.subst
      (motive := fun d : ℕ => mg ≤ d)
      (Nat.add_comm mg mf)
      (Nat.le_add_right mg mf)
  have hg_enlarge :
      Ag * Real.exp (Bg * H ^ mg) ≤
        Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      hAg_nonneg
      (le_refl Ag)
      (by
        calc
          Bg ≤ Bf + Bg := le_add_of_nonneg_left hBf_nonneg
          _ ≤ Bf + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBg_nonneg
      hmg_le
  have hf_target :
      ‖f z‖ ≤ Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    (hf_bound z hz_re hz_norm).trans hf_enlarge
  have hg_target :
      ‖g z‖ ≤ Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    (hg_bound z hz_re hz_norm).trans hg_enlarge
  have hnorm :
      ‖f z * g z‖ = ‖f z‖ * ‖g z‖ :=
    norm_mul (f z) (g z)
  have hproduct :
      ‖f z‖ * ‖g z‖ ≤
        (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) :=
    mul_le_mul hf_target hg_target (norm_nonneg (g z))
      (mul_nonneg hAf_nonneg
        (le_of_lt (Real.exp_pos ((Bf + Bg + 1) * H ^ (mf + mg)))))
  have hcollapse :
      (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) =
        Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) :=
    finiteOrderGrowthProductEnvelope_exp_collapse
      Af Ag ((Bf + Bg + 1) * H ^ (mf + mg))
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)))
    hnorm.symm
    (hproduct.trans_eq hcollapse)

/-- Right-half-plane finite-order growth for Deligne's complex Gamma factor
`Gammaℂ`. -/
theorem Gammaℂ_rightHalfPlane_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ s : ℂ,
        1 ≤ s.re →
        1 ≤ ‖s‖ →
        ‖Complex.Gammaℂ s‖ ≤ A * Real.exp (B * (1 + ‖s‖) ^ m) := by
  rcases finiteOrder_rightHalfPlane_product_growth_bound
      Gammaℝ_rightHalfPlane_stirling_growth_bound
      (by
        rcases Gammaℝ_rightHalfPlane_stirling_growth_bound with
          ⟨A, B, m, hA, hB, hbound⟩
        refine ⟨A, B, m, hA, hB, ?_⟩
        intro s hs_re _hs_norm
        have hs_add_re : 0 ≤ (s + 1).re := by
          have hs_add_re_eq : (s + 1).re = s.re + 1 := by
            calc
              (s + 1).re = s.re + (1 : ℂ).re := Complex.add_re s (1 : ℂ)
              _ = s.re + 1 := by
                exact congrArg (fun x : ℝ => s.re + x) Complex.one_re
          have hs_add_nonneg : 0 ≤ s.re + 1 :=
            add_nonneg (le_trans zero_le_one hs_re) zero_le_one
          exact Eq.subst
            (motive := fun x : ℝ => 0 ≤ x)
            hs_add_re_eq.symm
            hs_add_nonneg
        have hs_add_norm : 1 ≤ ‖s + 1‖ := by
          have hs_add_re_one : 1 ≤ (s + 1).re := by
            have hs_add_re_eq : (s + 1).re = s.re + 1 := by
              calc
                (s + 1).re = s.re + (1 : ℂ).re := Complex.add_re s (1 : ℂ)
                _ = s.re + 1 := by
                  exact congrArg (fun x : ℝ => s.re + x) Complex.one_re
            have hone_le_add : (1 : ℝ) ≤ s.re + 1 :=
              calc
                (1 : ℝ) = 0 + 1 := (zero_add 1).symm
                _ ≤ s.re + 1 := add_le_add_right (le_trans zero_le_one hs_re) 1
            exact Eq.subst
              (motive := fun x : ℝ => (1 : ℝ) ≤ x)
              hs_add_re_eq.symm
              hone_le_add
          exact one_le_norm_of_one_le_re hs_add_re_one
        exact hbound (s + 1) hs_add_re hs_add_norm) with
    ⟨A, B, m, hA, hB, hproduct⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro s hs_re hs_norm
  have hmul :
      Complex.Gammaℝ s * Complex.Gammaℝ (s + 1) =
        Complex.Gammaℂ s :=
    Complex.Gammaℝ_mul_Gammaℝ_add_one s
  have hnorm_eq :
      ‖Complex.Gammaℂ s‖ =
        ‖Complex.Gammaℝ s * Complex.Gammaℝ (s + 1)‖ :=
    congrArg norm hmul.symm
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.exp (B * (1 + ‖s‖) ^ m))
    hnorm_eq.symm
    (hproduct s (le_trans zero_le_one hs_re) hs_norm)

/-- The norm of a complex exponential is bounded by the exponential of the
norm of its exponent. -/
theorem complex_exp_norm_le_exp_norm
    (w : ℂ) :
    ‖Complex.exp w‖ ≤ Real.exp ‖w‖ := by
  have hnorm_abs : ‖Complex.exp w‖ = Complex.abs (Complex.exp w) :=
    Complex.norm_eq_abs (Complex.exp w)
  have habs_exp : Complex.abs (Complex.exp w) = Real.exp w.re :=
    Complex.abs_exp w
  have hre_le_norm : w.re ≤ ‖w‖ := by
    have hre_abs_le : |w.re| ≤ Complex.abs w :=
      Complex.abs_re_le_abs w
    have hre_le_abs : w.re ≤ |w.re| :=
      le_abs_self w.re
    have habs_eq_norm : Complex.abs w = ‖w‖ :=
      (Complex.norm_eq_abs w).symm
    exact hre_le_abs.trans (hre_abs_le.trans_eq habs_eq_norm)
  calc
    ‖Complex.exp w‖ = Complex.abs (Complex.exp w) := hnorm_abs
    _ = Real.exp w.re := habs_exp
    _ ≤ Real.exp ‖w‖ := Real.exp_le_exp.mpr hre_le_norm

/-- Norm absorption for the affine exponents appearing in
`Complex.cos (πs/2)`. -/
theorem complex_cos_pi_mul_div_two_exp_argument_norm_bound
    (s : ℂ) :
    ‖(π * s / 2) * Complex.I‖ ≤ (Real.pi + 1) * (1 + ‖s‖) ∧
      ‖-(π * s / 2) * Complex.I‖ ≤ (Real.pi + 1) * (1 + ‖s‖) := by
  have hpi_nonneg : 0 ≤ Real.pi :=
    le_of_lt Real.pi_pos
  have hpi_one_nonneg : 0 ≤ Real.pi + 1 :=
    add_nonneg hpi_nonneg zero_le_one
  have hbase_nonneg : 0 ≤ 1 + ‖s‖ :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg s))
  have harg_core :
      ‖(π * s / 2) * Complex.I‖ ≤ (Real.pi + 1) * (1 + ‖s‖) := by
    have hI_norm : ‖Complex.I‖ = (1 : ℝ) :=
      norm_I
    have hmulI :
        ‖(π * s / 2) * Complex.I‖ = ‖π * s / 2‖ := by
      calc
        ‖(π * s / 2) * Complex.I‖ =
            ‖π * s / 2‖ * ‖Complex.I‖ :=
          norm_mul (π * s / 2) Complex.I
        _ = ‖π * s / 2‖ * 1 := by
          exact congrArg (fun x : ℝ => ‖π * s / 2‖ * x) hI_norm
        _ = ‖π * s / 2‖ := mul_one ‖π * s / 2‖
    have hdiv_le : ‖π * s / 2‖ ≤ ‖π * s‖ := by
      have hnorm_div :
          ‖π * s / 2‖ = ‖π * s‖ / ‖(2 : ℂ)‖ :=
        norm_div (π * s) (2 : ℂ)
      have htwo_norm : ‖(2 : ℂ)‖ = (2 : ℝ) :=
        norm_ofNat 2
      have hdiv_two : ‖π * s‖ / ‖(2 : ℂ)‖ = ‖π * s‖ / 2 := by
        exact congrArg (fun x : ℝ => ‖π * s‖ / x) htwo_norm
      have hle_self : ‖π * s‖ / 2 ≤ ‖π * s‖ := by
        have hnorm_nonneg : 0 ≤ ‖π * s‖ :=
          norm_nonneg (π * s)
        calc
          ‖π * s‖ / 2 ≤ ‖π * s‖ / 1 :=
            div_le_div_of_nonneg_left hnorm_nonneg zero_lt_one.le one_le_two
          _ = ‖π * s‖ := div_one ‖π * s‖
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ ‖π * s‖)
        (Eq.trans hnorm_div hdiv_two).symm
        hle_self
    have hmul_norm :
        ‖π * s‖ = Real.pi * ‖s‖ := by
      have hnorm_mul : ‖π * s‖ = ‖(π : ℂ)‖ * ‖s‖ :=
        norm_mul (π : ℂ) s
      have hpi_norm : ‖(π : ℂ)‖ = Real.pi :=
        Complex.norm_ofReal_of_nonneg hpi_nonneg
      calc
        ‖π * s‖ = ‖(π : ℂ)‖ * ‖s‖ := hnorm_mul
        _ = Real.pi * ‖s‖ := by
          exact congrArg (fun x : ℝ => x * ‖s‖) hpi_norm
    have hpi_le :
        Real.pi * ‖s‖ ≤ (Real.pi + 1) * ‖s‖ :=
      mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one)
        (norm_nonneg s)
    have hheight_le :
        (Real.pi + 1) * ‖s‖ ≤ (Real.pi + 1) * (1 + ‖s‖) :=
      mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left zero_le_one)
        hpi_one_nonneg
    have hmid :
        ‖π * s / 2‖ ≤ (Real.pi + 1) * (1 + ‖s‖) :=
      hdiv_le.trans
        (Eq.subst
          (motive := fun x : ℝ => x ≤ (Real.pi + 1) * (1 + ‖s‖))
          hmul_norm.symm
          (hpi_le.trans hheight_le))
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ (Real.pi + 1) * (1 + ‖s‖))
      hmulI.symm
      hmid
  have harg_neg :
      ‖-(π * s / 2) * Complex.I‖ = ‖(π * s / 2) * Complex.I‖ := by
    calc
      ‖-(π * s / 2) * Complex.I‖ = ‖-((π * s / 2) * Complex.I)‖ := by
        exact congrArg norm (neg_mul (π * s / 2) Complex.I).symm
      _ = ‖(π * s / 2) * Complex.I‖ := norm_neg ((π * s / 2) * Complex.I)
  exact ⟨harg_core,
    Eq.subst
      (motive := fun x : ℝ => x ≤ (Real.pi + 1) * (1 + ‖s‖))
      harg_neg.symm
      harg_core⟩

/-- Finite-order growth for the two exponential terms in the definition of
`Complex.cos (πs/2)`.

This is the elementary estimate obtained from
`Complex.abs_exp z = exp z.re`, the formulas for real and imaginary parts of
`(πs/2) * I` and `-(πs/2) * I`, and the bound `|s.im| ≤ ‖s‖`. -/
theorem complex_cos_pi_mul_div_two_exp_terms_rightHalfPlane_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ s : ℂ,
        1 ≤ s.re →
        1 ≤ ‖s‖ →
        ‖Complex.exp ((π * s / 2) * Complex.I)‖ +
            ‖Complex.exp (-(π * s / 2) * Complex.I)‖ ≤
          A * Real.exp (B * (1 + ‖s‖) ^ m) := by
  refine ⟨2, Real.pi + 1, 1, zero_lt_two,
    add_pos Real.pi_pos zero_lt_one, ?_⟩
  intro s _hs_re _hs_norm
  let E : ℝ := (Real.pi + 1) * (1 + ‖s‖)
  rcases complex_cos_pi_mul_div_two_exp_argument_norm_bound s with
    ⟨harg_pos, harg_neg⟩
  have hpos_exp :
      ‖Complex.exp ((π * s / 2) * Complex.I)‖ ≤ Real.exp E :=
    (complex_exp_norm_le_exp_norm ((π * s / 2) * Complex.I)).trans
      (Real.exp_le_exp.mpr harg_pos)
  have hneg_exp :
      ‖Complex.exp (-(π * s / 2) * Complex.I)‖ ≤ Real.exp E :=
    (complex_exp_norm_le_exp_norm (-(π * s / 2) * Complex.I)).trans
      (Real.exp_le_exp.mpr harg_neg)
  have hsum :
      ‖Complex.exp ((π * s / 2) * Complex.I)‖ +
          ‖Complex.exp (-(π * s / 2) * Complex.I)‖ ≤
        Real.exp E + Real.exp E :=
    add_le_add hpos_exp hneg_exp
  have htarget_eq :
      Real.exp E + Real.exp E =
        2 * Real.exp ((Real.pi + 1) * (1 + ‖s‖) ^ (1 : ℕ)) := by
    have hpow_one : (1 + ‖s‖) ^ (1 : ℕ) = 1 + ‖s‖ :=
      pow_one (1 + ‖s‖)
    calc
      Real.exp E + Real.exp E = 2 * Real.exp E := (two_mul (Real.exp E)).symm
      _ = 2 * Real.exp ((Real.pi + 1) * (1 + ‖s‖) ^ (1 : ℕ)) := by
        exact congrArg (fun x : ℝ => 2 * Real.exp ((Real.pi + 1) * x))
          hpow_one.symm
  exact hsum.trans_eq htarget_eq

/-- The exponential-term estimate for `cos` implies the finite-order growth of
the cosine factor itself. -/
theorem complex_cos_pi_mul_div_two_finiteOrder_growth_bound_of_exp_terms
    (hexp :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ s : ℂ,
          1 ≤ s.re →
          1 ≤ ‖s‖ →
          ‖Complex.exp ((π * s / 2) * Complex.I)‖ +
              ‖Complex.exp (-(π * s / 2) * Complex.I)‖ ≤
            A * Real.exp (B * (1 + ‖s‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ s : ℂ,
        1 ≤ s.re →
        1 ≤ ‖s‖ →
        ‖Complex.cos (π * s / 2)‖ ≤
          A * Real.exp (B * (1 + ‖s‖) ^ m) := by
  rcases hexp with ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro s hs_re hs_norm
  let u : ℂ := π * s / 2
  have hcos_def :
      Complex.cos u =
        (Complex.exp (u * Complex.I) + Complex.exp (-u * Complex.I)) / 2 := rfl
  have hnorm_div :
      ‖Complex.cos u‖ ≤
        (‖Complex.exp (u * Complex.I)‖ +
          ‖Complex.exp (-u * Complex.I)‖) / 2 := by
    calc
      ‖Complex.cos u‖ =
          ‖(Complex.exp (u * Complex.I) + Complex.exp (-u * Complex.I)) / 2‖ := by
        exact congrArg norm hcos_def
      _ = ‖Complex.exp (u * Complex.I) + Complex.exp (-u * Complex.I)‖ /
            ‖(2 : ℂ)‖ := norm_div
          (Complex.exp (u * Complex.I) + Complex.exp (-u * Complex.I)) (2 : ℂ)
      _ = ‖Complex.exp (u * Complex.I) + Complex.exp (-u * Complex.I)‖ / 2 := by
        exact congrArg
          (fun x : ℝ =>
            ‖Complex.exp (u * Complex.I) + Complex.exp (-u * Complex.I)‖ / x)
          (show ‖(2 : ℂ)‖ = (2 : ℝ) from norm_ofNat 2)
      _ ≤ (‖Complex.exp (u * Complex.I)‖ +
            ‖Complex.exp (-u * Complex.I)‖) / 2 :=
        div_le_div_of_nonneg_right
          (norm_add_le (Complex.exp (u * Complex.I)) (Complex.exp (-u * Complex.I)))
          zero_le_two
  have hhalf_le :
      (‖Complex.exp (u * Complex.I)‖ +
          ‖Complex.exp (-u * Complex.I)‖) / 2 ≤
        ‖Complex.exp (u * Complex.I)‖ +
          ‖Complex.exp (-u * Complex.I)‖ := by
    have hsum_nonneg :
        0 ≤ ‖Complex.exp (u * Complex.I)‖ +
          ‖Complex.exp (-u * Complex.I)‖ :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    exact div_le_self hsum_nonneg one_le_two
  have hrewrite :
      ‖Complex.exp (u * Complex.I)‖ +
          ‖Complex.exp (-u * Complex.I)‖ =
        ‖Complex.exp ((π * s / 2) * Complex.I)‖ +
          ‖Complex.exp (-(π * s / 2) * Complex.I)‖ := rfl
  exact (hnorm_div.trans hhalf_le).trans
    (Eq.subst
      (motive := fun x : ℝ => x ≤ A * Real.exp (B * (1 + ‖s‖) ^ m))
      hrewrite.symm
      (hbound s hs_re hs_norm))

/-- Elementary finite-order growth of the cosine factor occurring in Deligne's
real-Gamma reflection identity. -/
theorem complex_cos_pi_mul_div_two_rightHalfPlane_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ s : ℂ,
        1 ≤ s.re →
        1 ≤ ‖s‖ →
        ‖Complex.cos (π * s / 2)‖ ≤
          A * Real.exp (B * (1 + ‖s‖) ^ m) := by
  exact
    complex_cos_pi_mul_div_two_finiteOrder_growth_bound_of_exp_terms
      complex_cos_pi_mul_div_two_exp_terms_rightHalfPlane_finiteOrder_growth_bound

/-- Pure affine-norm absorption for finite-order envelopes under
`z ↦ 1 - z` on the left half-plane. -/
theorem finiteOrder_reflectedLeftHalfPlane_affine_norm_absorption
    (f : ℂ → ℂ)
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ s : ℂ,
          1 ≤ s.re →
          1 ≤ ‖s‖ →
          ‖f s‖ ≤ A * Real.exp (B * (1 + ‖s‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖f ((1 : ℂ) - z)‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hright with ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B * (2 : ℝ) ^ m, m, hA, ?_, ?_⟩
  · exact mul_pos hB (pow_pos zero_lt_two m)
  intro z hz_re
  let s : ℂ := (1 : ℂ) - z
  let H : ℝ := 1 + ‖z‖
  have hs_re : 1 ≤ s.re :=
    one_sub_leftHalfPlane_re_one_le hz_re
  have hs_norm : 1 ≤ ‖s‖ :=
    one_sub_leftHalfPlane_norm_one_le hz_re
  have hraw : ‖f s‖ ≤ A * Real.exp (B * (1 + ‖s‖) ^ m) :=
    hbound s hs_re hs_norm
  have hs_norm_le : ‖s‖ ≤ 1 + ‖z‖ := by
    calc
      ‖s‖ = ‖(1 : ℂ) - z‖ := rfl
      _ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le (1 : ℂ) z
      _ = 1 + ‖z‖ := by
        exact congrArg (fun x : ℝ => x + ‖z‖)
          (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
  have hbase_le : 1 + ‖s‖ ≤ 2 * H := by
    calc
      1 + ‖s‖ ≤ 1 + (1 + ‖z‖) :=
        add_le_add_left hs_norm_le 1
      _ = 2 + ‖z‖ := by
        exact add_assoc 1 1 ‖z‖
      _ ≤ 2 + (2 * ‖z‖) := by
        exact add_le_add_left
          (by
            calc
              ‖z‖ ≤ ‖z‖ + ‖z‖ := le_add_of_nonneg_right (norm_nonneg z)
              _ = 2 * ‖z‖ := (two_mul ‖z‖).symm)
          2
      _ = 2 * H := by
        calc
          2 + 2 * ‖z‖ = 2 * 1 + 2 * ‖z‖ := by
            exact congrArg (fun x : ℝ => x + 2 * ‖z‖) (mul_one 2).symm
          _ = 2 * (1 + ‖z‖) := (mul_add 2 1 ‖z‖).symm
          _ = 2 * H := rfl
  have hleft_nonneg : 0 ≤ 1 + ‖s‖ :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg s))
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hpow_le : (1 + ‖s‖) ^ m ≤ (2 * H) ^ m :=
    pow_le_pow_left₀ hleft_nonneg hbase_le m
  have hmul_pow : (2 * H) ^ m = (2 : ℝ) ^ m * H ^ m :=
    mul_pow 2 H m
  have hpow_target : (1 + ‖s‖) ^ m ≤ (2 : ℝ) ^ m * H ^ m :=
    hpow_le.trans_eq hmul_pow
  have hexponent_le :
      B * (1 + ‖s‖) ^ m ≤ (B * (2 : ℝ) ^ m) * H ^ m := by
    calc
      B * (1 + ‖s‖) ^ m ≤ B * ((2 : ℝ) ^ m * H ^ m) :=
        mul_le_mul_of_nonneg_left hpow_target (le_of_lt hB)
      _ = (B * (2 : ℝ) ^ m) * H ^ m := mul_assoc B ((2 : ℝ) ^ m) (H ^ m)
  have henv :
      A * Real.exp (B * (1 + ‖s‖) ^ m) ≤
        A * Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hexponent_le)
      (le_of_lt hA)
  exact hraw.trans henv

/-- Affine reflection transport for right-half-plane finite-order envelopes.

This is the deterministic comparison behind the map `z ↦ 1 - z`: the
reflected point has real part at least one on the closed left half-plane, and
its norm is bounded by a fixed affine function of `‖z‖`, which is absorbed into
the finite-order exponential envelope. -/
theorem finiteOrder_reflectedLeftHalfPlane_growth_bound_of_rightHalfPlane
    (f : ℂ → ℂ)
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ s : ℂ,
          1 ≤ s.re →
          1 ≤ ‖s‖ →
          ‖f s‖ ≤ A * Real.exp (B * (1 + ‖s‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖f ((1 : ℂ) - z)‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact finiteOrder_reflectedLeftHalfPlane_affine_norm_absorption f hright

/-- Right-half-plane finite-order growth for the Deligne quotient factor
`Gammaℂ s * cos (πs/2)`.

The Gamma part is obtained from `Gammaℝ s * Gammaℝ (s+1) = Gammaℂ s` and the
right-half-plane Stirling envelope already proved above.  The cosine part is
the elementary exponential estimate following from the definitions of complex
trigonometric functions. -/
theorem Gammaℂ_cos_rightHalfPlane_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ s : ℂ,
        1 ≤ s.re →
        1 ≤ ‖s‖ →
        ‖Complex.Gammaℂ s * Complex.cos (π * s / 2)‖ ≤
          A * Real.exp (B * (1 + ‖s‖) ^ m) := by
  exact
    finiteOrder_rightHalfPlane_product_growth_bound
      Gammaℂ_rightHalfPlane_finiteOrder_growth_bound
      complex_cos_pi_mul_div_two_rightHalfPlane_finiteOrder_growth_bound

/-- Reflected-left-half-plane finite-order form of the right-half-plane
`Gammaℂ·cos` Deligne factor.

This is the affine-envelope transport `s = 1 - z` applied to
`Gammaℂ_cos_rightHalfPlane_finiteOrder_growth_bound`; the only estimates are
`1 ≤ Re (1-z)` and the elementary norm comparison for `1 - z`. -/
theorem Gammaℂ_cos_reflectedLeftHalfPlane_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖Complex.Gammaℂ ((1 : ℂ) - z) *
            Complex.cos (π * ((1 : ℂ) - z) / 2)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    finiteOrder_reflectedLeftHalfPlane_growth_bound_of_rightHalfPlane
      (fun s : ℂ => Complex.Gammaℂ s * Complex.cos (π * s / 2))
      Gammaℂ_cos_rightHalfPlane_finiteOrder_growth_bound

/-- Deligne reflection/recurrence algebra for the left-half-plane `Gammaℝ`
ratio, isolated from the analytic Stirling estimates.

The proof uses mathlib's `Gamma/Deligne.lean` identities
`Gammaℝ_add_two`, `Gammaℝ_mul_Gammaℝ_add_one`,
`Gammaℝ_one_sub_mul_Gammaℝ_one_add`, `Gammaℝ_div_Gammaℝ_one_sub`,
`inv_Gammaℝ_one_sub`, and `inv_Gammaℝ_two_sub` to rewrite the quotient into
right-half-plane Gamma factors and elementary trigonometric/exponential
factors. -/
theorem Gammaℝ_leftHalfPlane_completedFunctionalEquation_ratio_largeNorm_Deligne_transport_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        1 ≤ ‖z‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases Gammaℂ_cos_reflectedLeftHalfPlane_finiteOrder_growth_bound with
    ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro z hz_re _hz_ne_zero _hz_norm
  have hquot :
      Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z =
        Complex.Gammaℂ ((1 : ℂ) - z) *
          Complex.cos (π * ((1 : ℂ) - z) / 2) :=
    Gammaℝ_leftHalfPlane_completedFunctionalEquation_ratio_eq_Gammaℂ_cos hz_re
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    hquot.symm
    (hbound z hz_re)

/-- Large-radius Stirling branch for the completed-functional-equation real-Gamma
ratio on the closed left half plane.

This branch is name transport from the Deligne reflection/recurrence algebra
plus sectorial/vertical Stirling growth.  The owner proof separates the
sectorial Gamma estimate from the Deligne Gamma bookkeeping; cf. DLMF §5.11
and Titchmarsh, Ch. 2. -/
theorem Gammaℝ_leftHalfPlane_completedFunctionalEquation_ratio_largeNorm_stirling_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        1 ≤ ‖z‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    Gammaℝ_leftHalfPlane_completedFunctionalEquation_ratio_largeNorm_Deligne_transport_growth_bound

/-- Large-radius left-half-plane Gamma-ratio Stirling growth for the
completed-functional-equation multiplier.

This is the raw Gamma-ratio branch used away from the removable zero face.  The
finite-radius branch belongs to the pole-cleared completed multiplier above. -/
theorem Gammaℝ_leftHalfPlane_completedFunctionalEquation_ratio_global_stirling_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        1 ≤ ‖z‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    Gammaℝ_leftHalfPlane_completedFunctionalEquation_ratio_largeNorm_stirling_growth_bound

/-- Large-radius left-half-plane Gamma-ratio Stirling growth for the
completed-functional-equation multiplier.

This public owner theorem is only name transport from the sectorial/strip
Stirling estimate for the raw completed real-Gamma ratio away from the
removable zero face. -/
theorem Gammaℝ_leftHalfPlane_completedFunctionalEquation_ratio_stirling_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        1 ≤ ‖z‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    Gammaℝ_leftHalfPlane_completedFunctionalEquation_ratio_global_stirling_growth_bound

/-- Removable continuous extension of the raw completed-functional-equation
multiplier on the closed unit ball.

This is the local analytic owner input for the near-origin branch: the apparent
pole of `(z - 1) / (((1 : ℂ) - z) - 1)` at `0` is cancelled by the completed
functional-equation Gamma ratio, so the raw product has a continuous removable
extension on `‖z‖ ≤ 1`. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_continuousOn_nearOriginLeftSet :
    ContinuousOn poleClearedRiemannZeta_completedFunctionalEquationMultiplier
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet := by
  intro z hz_mem
  by_cases hz_zero : z = 0
  · exact Eq.subst
      (motive := fun w : ℂ =>
        ContinuousWithinAt
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier
          poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet w)
      hz_zero.symm
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_continuousWithinAt_zero_nearOriginLeftSet
  · exact
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_continuousWithinAt_nearOriginLeftSet_of_ne_zero
        hz_mem hz_zero

theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_nearOrigin_removable_extension :
    ∃ F : ℂ → ℂ,
      ContinuousOn F
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier_nearOriginLeftSet ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        ‖z‖ ≤ 1 →
        F z =
          ((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
  refine ⟨poleClearedRiemannZeta_completedFunctionalEquationMultiplier,
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_continuousOn_nearOriginLeftSet,
    ?_⟩
  intro z _hz_re hz_ne_zero hz_norm
  have hGamma_ne : Complex.Gammaℝ z ≠ 0 :=
    Gammaℝ_ne_zero_of_ne_zero_norm_le_one hz_ne_zero hz_norm
  unfold poleClearedRiemannZeta_completedFunctionalEquationMultiplier
  exact Eq.trans (if_neg hz_ne_zero) (if_neg hGamma_ne)

/-- Compact/removable local boundedness of the raw completed-functional-equation
multiplier near the origin.

This is the true local input: the rational pole at `z = 0` is cancelled by the
Gamma-ratio/trivial-zero normalization, so the product is locally bounded on
the punctured closed unit ball. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_leftHalfPlane_nearOrigin_growth_from_removable_localBoundedness :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        ‖z‖ ≤ 1 →
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_nearOrigin_removable_extension with
    ⟨F, hF_cont, hF_eq⟩
  let f : ℂ → ℂ := fun z : ℂ =>
    ((z - 1) / (((1 : ℂ) - z) - 1)) *
      (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)
  rcases compact_nearOriginLeftSet_punctured_norm_bound_of_removable_extension
      f F hF_cont hF_eq with
    ⟨C, hC_pos, hC_bound⟩
  refine ⟨C, 1, 0, hC_pos, zero_lt_one, ?_⟩
  intro z hz_re hz_ne_zero hz_norm
  have hraw_bound :
      ‖f z‖ ≤ C :=
    hC_bound z hz_re hz_ne_zero hz_norm
  have hfactor_ge_one :
      (1 : ℝ) ≤ Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) := by
    have hexponent_nonneg :
        0 ≤ (1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ) :=
      mul_nonneg zero_le_one
        (pow_nonneg
          (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z)))
          0)
    exact le_trans (le_of_eq Real.exp_zero.symm)
      (Real.exp_le_exp.mpr hexponent_nonneg)
  have hscaled :
      C ≤ C * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) :=
    le_mul_of_one_le_right (le_of_lt hC_pos) hfactor_ge_one
  exact hraw_bound.trans hscaled

theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_leftHalfPlane_nearOrigin_growth :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        ‖z‖ ≤ 1 →
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_leftHalfPlane_nearOrigin_growth_from_removable_localBoundedness

/-- Compact/removable branch for the completed-functional-equation multiplier
on the closed left half-plane.

The raw `Gammaℝ ((1 : ℂ) - z) / Gammaℝ z` quotient is not the compact object at
the zero face `z = 0`; the pole-clearing rational factor supplies the classical
removable cancellation.  This theorem records the compact branch in that
truthful removable form. -/
theorem completedFunctionalEquationMultiplier_Gammaℝ_ratio_compactNorm_removable_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        ‖z‖ ≤ 1 →
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_leftHalfPlane_nearOrigin_growth

/-- Raw multiplier growth from the far-tail pole-clearing ratio, the
Gamma-ratio/Stirling estimate, and the near-origin removable control. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_leftHalfPlane_finiteOrder_growth_of_ratio_and_gamma
    (hnear :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          z ≠ 0 →
          ‖z‖ ≤ 1 →
          ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
              (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hratio :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          z ≠ 0 →
          1 ≤ ‖z‖ →
          ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hgamma :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          z ≠ 0 →
          1 ≤ ‖z‖ →
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hnear with ⟨An, Bn, mn, hAn, hBn, hnear_bound⟩
  rcases hratio with ⟨Ar, Br, mr, hAr, hBr, hratio_bound⟩
  rcases hgamma with ⟨Ag, Bg, mg, hAg, hBg, hgamma_bound⟩
  let Afar : ℝ := Ar * Ag
  let Bfar : ℝ := 2 * (Br + Bg + 1)
  let mfar : ℕ := mr + mg
  let A : ℝ := An + Afar
  let B : ℝ := Bn + Bfar
  let m : ℕ := mn + mfar
  have hAfar_pos : 0 < Afar := mul_pos hAr hAg
  have hBfar_pos : 0 < Bfar :=
    mul_pos zero_lt_two (add_pos (add_pos hBr hBg) zero_lt_one)
  refine ⟨A, B, m, add_pos hAn hAfar_pos, add_pos hBn hBfar_pos, ?_⟩
  intro z hz_left hz_ne_zero
  have hAn_nonneg : 0 ≤ An := le_of_lt hAn
  have hAfar_nonneg : 0 ≤ Afar := le_of_lt hAfar_pos
  have hBn_nonneg : 0 ≤ Bn := le_of_lt hBn
  have hBfar_nonneg : 0 ≤ Bfar := le_of_lt hBfar_pos
  have hAn_le_A : An ≤ A := le_add_of_nonneg_right hAfar_nonneg
  have hAfar_le_A : Afar ≤ A := le_add_of_nonneg_left hAn_nonneg
  have hBn_le_B : Bn ≤ B := le_add_of_nonneg_right hBfar_nonneg
  have hBfar_le_B : Bfar ≤ B := le_add_of_nonneg_left hBn_nonneg
  by_cases hsmall : ‖z‖ ≤ 1
  · have hnear_z :
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
          An * Real.exp (Bn * (1 + ‖z‖) ^ mn) :=
      hnear_bound z hz_left hz_ne_zero hsmall
    exact hnear_z.trans
      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
        hAn_nonneg hAn_le_A hBn_le_B hBn_nonneg
        (Nat.le_add_right mn mfar))
  · have hlarge : 1 ≤ ‖z‖ := le_of_not_ge hsmall
    let R : ℂ := (z - 1) / (((1 : ℂ) - z) - 1)
    let G : ℂ := Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z
    let H : ℝ := 1 + ‖z‖
    have hBr_nonneg : 0 ≤ Br := le_of_lt hBr
    have hBg_nonneg : 0 ≤ Bg := le_of_lt hBg
    have hAr_nonneg : 0 ≤ Ar := le_of_lt hAr
    have hAg_nonneg : 0 ≤ Ag := le_of_lt hAg
    have hratio_z :
        ‖R‖ ≤ Ar * Real.exp (Br * H ^ mr) :=
      hratio_bound z hz_left hz_ne_zero hlarge
    have hgamma_z :
        ‖G‖ ≤ Ag * Real.exp (Bg * H ^ mg) :=
      hgamma_bound z hz_left hz_ne_zero hlarge
    have hratio_enlarge :
        Ar * Real.exp (Br * H ^ mr) ≤
          Ar * Real.exp ((Br + Bg + 1) * H ^ mfar) :=
      exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
        hAr_nonneg
        (le_refl Ar)
        (by
          calc
            Br ≤ Br + Bg := le_add_of_nonneg_right hBg_nonneg
            _ ≤ Br + Bg + 1 := le_add_of_nonneg_right zero_le_one)
        hBr_nonneg
        (Nat.le_add_right mr mg)
    have hmg_le_mfar : mg ≤ mfar := by
      exact Eq.subst
        (motive := fun d : ℕ => mg ≤ d)
        (Nat.add_comm mg mr)
        (Nat.le_add_right mg mr)
    have hgamma_enlarge :
        Ag * Real.exp (Bg * H ^ mg) ≤
          Ag * Real.exp ((Br + Bg + 1) * H ^ mfar) :=
      exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
        hAg_nonneg
        (le_refl Ag)
        (by
          calc
            Bg ≤ Br + Bg := le_add_of_nonneg_left hBr_nonneg
            _ ≤ Br + Bg + 1 := le_add_of_nonneg_right zero_le_one)
        hBg_nonneg
        hmg_le_mfar
    have hR_target :
        ‖R‖ ≤ Ar * Real.exp ((Br + Bg + 1) * H ^ mfar) :=
      hratio_z.trans hratio_enlarge
    have hG_target :
        ‖G‖ ≤ Ag * Real.exp ((Br + Bg + 1) * H ^ mfar) :=
      hgamma_z.trans hgamma_enlarge
    have hproduct :
        ‖R * G‖ ≤
          (Ar * Real.exp ((Br + Bg + 1) * H ^ mfar)) *
            (Ag * Real.exp ((Br + Bg + 1) * H ^ mfar)) := by
      have hnorm : ‖R * G‖ = ‖R‖ * ‖G‖ := norm_mul R G
      have hmul :
          ‖R‖ * ‖G‖ ≤
            (Ar * Real.exp ((Br + Bg + 1) * H ^ mfar)) *
              (Ag * Real.exp ((Br + Bg + 1) * H ^ mfar)) :=
        mul_le_mul hR_target hG_target (norm_nonneg G)
          (mul_nonneg hAr_nonneg
            (le_of_lt (Real.exp_pos ((Br + Bg + 1) * H ^ mfar))))
      exact Eq.subst
        (motive := fun x : ℝ =>
          x ≤
            (Ar * Real.exp ((Br + Bg + 1) * H ^ mfar)) *
              (Ag * Real.exp ((Br + Bg + 1) * H ^ mfar)))
        hnorm.symm
        hmul
    have hcollapse :
        (Ar * Real.exp ((Br + Bg + 1) * H ^ mfar)) *
            (Ag * Real.exp ((Br + Bg + 1) * H ^ mfar)) =
          Afar * Real.exp (Bfar * H ^ mfar) := by
      have hraw :
          (Ar * Real.exp ((Br + Bg + 1) * H ^ mfar)) *
              (Ag * Real.exp ((Br + Bg + 1) * H ^ mfar)) =
            Ar * Ag * Real.exp (2 * ((Br + Bg + 1) * H ^ mfar)) :=
        finiteOrderGrowthProductEnvelope_exp_collapse
          Ar Ag ((Br + Bg + 1) * H ^ mfar)
      have hexponent :
          2 * ((Br + Bg + 1) * H ^ mfar) =
            Bfar * H ^ mfar := by
        calc
          2 * ((Br + Bg + 1) * H ^ mfar) =
              (2 * (Br + Bg + 1)) * H ^ mfar := by
            exact (mul_assoc 2 (Br + Bg + 1) (H ^ mfar)).symm
          _ = Bfar * H ^ mfar := rfl
      calc
        (Ar * Real.exp ((Br + Bg + 1) * H ^ mfar)) *
            (Ag * Real.exp ((Br + Bg + 1) * H ^ mfar)) =
          Ar * Ag * Real.exp (2 * ((Br + Bg + 1) * H ^ mfar)) := hraw
        _ = Afar * Real.exp (Bfar * H ^ mfar) := by
          exact congrArg (fun x : ℝ => Afar * Real.exp x) hexponent
    have hfar :
        ‖R * G‖ ≤ Afar * Real.exp (Bfar * H ^ mfar) :=
      hproduct.trans_eq hcollapse
    have henlarge :
        Afar * Real.exp (Bfar * (1 + ‖z‖) ^ mfar) ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) :=
      exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
        hAfar_nonneg hAfar_le_A hBfar_le_B hBfar_nonneg
        (by
          exact Eq.subst
            (motive := fun d : ℕ => mfar ≤ d)
            (Nat.add_comm mfar mn)
            (Nat.le_add_right mfar mn))
    exact hfar.trans henlarge

/-- Raw multiplier finite-order growth on the left half-plane away from the
removable point.  This is the exact place where Gamma/Stirling and the
elementary pole-clearing factor enter. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_leftHalfPlane_finiteOrder_growth :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        z ≠ 0 →
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_leftHalfPlane_finiteOrder_growth_of_ratio_and_gamma
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_leftHalfPlane_nearOrigin_growth
      leftHalfPlane_completedFunctionalEquation_poleClearing_ratio_growth_bound
      Gammaℝ_leftHalfPlane_completedFunctionalEquation_ratio_stirling_growth_bound

theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_leftHalfPlane_finiteOrder_growth :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_leftHalfPlane_growth_of_raw_and_removable
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_leftHalfPlane_finiteOrder_growth

/-- Finite-order envelopes are stable under the affine reflection `z ↦ 1 - z`
on the left half-plane.

This is the real-variable comparison needed by the completed-functional-equation
transport: `z.re ≤ 0` implies `1 ≤ (1 - z).re`, and the affine height
`1 + ‖1 - z‖` is controlled by a fixed polynomial in `1 + ‖z‖`. -/
theorem finiteOrder_leftHalfPlane_reflection_growth_bound
    (f : ℂ → ℂ)
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          1 ≤ w.re →
          ‖f w‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖f ((1 : ℂ) - z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hright with ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B * (2 : ℝ) ^ m, m, hA, ?_, ?_⟩
  · exact mul_pos hB (pow_pos zero_lt_two m)
  intro z hz_left
  let w : ℂ := (1 : ℂ) - z
  let H : ℝ := 1 + ‖z‖
  have hw_re : 1 ≤ w.re := by
    have hone_re : (1 : ℂ).re = (1 : ℝ) :=
      Complex.one_re
    have hraw : w.re = 1 - z.re := by
      calc
        w.re = (1 : ℂ).re - z.re := by
          exact Complex.sub_re (1 : ℂ) z
        _ = 1 - z.re := by
          exact congrArg (fun x : ℝ => x - z.re) hone_re
    have hle : 1 ≤ 1 - z.re := by
      exact le_sub_iff_add_le'.mpr
        (le_trans (by exact le_add_of_nonneg_right hz_left) (le_refl (1 : ℝ)))
    exact Eq.subst (motive := fun x : ℝ => 1 ≤ x) hraw.symm hle
  have hraw_bound :
      ‖f w‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m) :=
    hbound w hw_re
  have hw_height_nonneg : 0 ≤ 1 + ‖w‖ :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w))
  have htriangle : ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ :=
    norm_sub_le (1 : ℂ) z
  have hone_norm : ‖(1 : ℂ)‖ = (1 : ℝ) :=
    norm_one
  have hw_norm_le : ‖w‖ ≤ 1 + ‖z‖ := by
    exact Eq.subst
      (motive := fun x : ℝ => ‖w‖ ≤ x + ‖z‖)
      hone_norm
      htriangle
  have hheight_le : 1 + ‖w‖ ≤ 2 * H := by
    have hnorm_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
    calc
      1 + ‖w‖ ≤ 1 + (1 + ‖z‖) := by
        exact add_le_add_left hw_norm_le 1
      _ = 2 + ‖z‖ := by
        calc
          1 + (1 + ‖z‖) = (1 + 1) + ‖z‖ := by
            exact (add_assoc 1 1 ‖z‖).symm
          _ = 2 + ‖z‖ := by
            exact congrArg (fun x : ℝ => x + ‖z‖) (one_add_one_eq_two)
      _ ≤ 2 + 2 * ‖z‖ := by
        have hsingle_le_double : ‖z‖ ≤ 2 * ‖z‖ := by
          calc
            ‖z‖ = 1 * ‖z‖ := by
              exact (one_mul ‖z‖).symm
            _ ≤ 2 * ‖z‖ :=
              mul_le_mul_of_nonneg_right one_le_two hnorm_nonneg
        exact add_le_add_left hsingle_le_double 2
      _ = 2 * H := by
        calc
          2 + 2 * ‖z‖ = 2 * 1 + 2 * ‖z‖ := by
            exact congrArg (fun x : ℝ => x + 2 * ‖z‖) (mul_one 2).symm
          _ = 2 * (1 + ‖z‖) := by
            exact (mul_add 2 1 ‖z‖).symm
          _ = 2 * H := rfl
  have hpow_le : (1 + ‖w‖) ^ m ≤ (2 * H) ^ m :=
    pow_le_pow_left₀ hw_height_nonneg hheight_le m
  have hmul_pow : (2 * H) ^ m = (2 : ℝ) ^ m * H ^ m :=
    mul_pow 2 H m
  have hscale :
      B * (1 + ‖w‖) ^ m ≤ (B * (2 : ℝ) ^ m) * H ^ m := by
    have hfirst : B * (1 + ‖w‖) ^ m ≤ B * (2 * H) ^ m :=
      mul_le_mul_of_nonneg_left hpow_le (le_of_lt hB)
    have htarget : B * (2 * H) ^ m = (B * (2 : ℝ) ^ m) * H ^ m := by
      calc
        B * (2 * H) ^ m = B * ((2 : ℝ) ^ m * H ^ m) := by
          exact congrArg (fun x : ℝ => B * x) hmul_pow
        _ = (B * (2 : ℝ) ^ m) * H ^ m := by
          exact (mul_assoc B ((2 : ℝ) ^ m) (H ^ m)).symm
    exact hfirst.trans_eq htarget
  have hexp_le :
      Real.exp (B * (1 + ‖w‖) ^ m) ≤
        Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
    Real.exp_le_exp.mpr hscale
  have htarget_bound :
      A * Real.exp (B * (1 + ‖w‖) ^ m) ≤
        A * Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
    mul_le_mul_of_nonneg_left hexp_le (le_of_lt hA)
  exact hraw_bound.trans htarget_bound

/-- Product transport for a completed-functional-equation identity on a left
half-plane.

Once the multiplier has finite-order growth and the reflected function has
finite-order growth, their product has finite-order growth.  This theorem is
the reusable bookkeeping layer for the pole-cleared zeta transport. -/
theorem finiteOrder_leftHalfPlane_growth_of_multiplier_reflection_identity
    (f M : ℂ → ℂ)
    (hM :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          ‖M z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hreflected :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          ‖f ((1 : ℂ) - z)‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hidentity :
      ∀ z : ℂ,
        z.re ≤ 0 →
        f z = M z * f ((1 : ℂ) - z)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hM with ⟨AM, BM, mM, hAM, hBM, hM_bound⟩
  rcases hreflected with ⟨Af, Bf, mf, hAf, hBf, hf_bound⟩
  refine ⟨AM * Af, 2 * (BM + Bf + 1), mM + mf,
    mul_pos hAM hAf,
    mul_pos zero_lt_two (add_pos (add_pos hBM hBf) zero_lt_one), ?_⟩
  intro z hz_left
  let H : ℝ := 1 + ‖z‖
  have hBM_nonneg : 0 ≤ BM := le_of_lt hBM
  have hBf_nonneg : 0 ≤ Bf := le_of_lt hBf
  have hAM_nonneg : 0 ≤ AM := le_of_lt hAM
  have hAf_nonneg : 0 ≤ Af := le_of_lt hAf
  have hM_enlarge :
      AM * Real.exp (BM * H ^ mM) ≤
        AM * Real.exp ((BM + Bf + 1) * H ^ (mM + mf)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      hAM_nonneg
      (le_refl AM)
      (by
        calc
          BM ≤ BM + Bf := le_add_of_nonneg_right hBf_nonneg
          _ ≤ BM + Bf + 1 := le_add_of_nonneg_right zero_le_one)
      hBM_nonneg
      (Nat.le_add_right mM mf)
  have hmf_le : mf ≤ mM + mf := by
    exact Eq.subst
      (motive := fun d : ℕ => mf ≤ d)
      (Nat.add_comm mf mM)
      (Nat.le_add_right mf mM)
  have hf_enlarge :
      Af * Real.exp (Bf * H ^ mf) ≤
        Af * Real.exp ((BM + Bf + 1) * H ^ (mM + mf)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      hAf_nonneg
      (le_refl Af)
      (by
        calc
          Bf ≤ BM + Bf := le_add_of_nonneg_left hBM_nonneg
          _ ≤ BM + Bf + 1 := le_add_of_nonneg_right zero_le_one)
      hBf_nonneg
      hmf_le
  have hM_target :
      ‖M z‖ ≤ AM * Real.exp ((BM + Bf + 1) * H ^ (mM + mf)) :=
    (hM_bound z hz_left).trans hM_enlarge
  have hf_target :
      ‖f ((1 : ℂ) - z)‖ ≤
        Af * Real.exp ((BM + Bf + 1) * H ^ (mM + mf)) :=
    (hf_bound z hz_left).trans hf_enlarge
  have hidentity_norm :
      ‖f z‖ = ‖M z‖ * ‖f ((1 : ℂ) - z)‖ := by
    have hraw := congrArg norm (hidentity z hz_left)
    exact hraw.trans (norm_mul (M z) (f ((1 : ℂ) - z)))
  have hproduct :
      ‖M z‖ * ‖f ((1 : ℂ) - z)‖ ≤
        (AM * Real.exp ((BM + Bf + 1) * H ^ (mM + mf))) *
          (Af * Real.exp ((BM + Bf + 1) * H ^ (mM + mf))) :=
    mul_le_mul hM_target hf_target (norm_nonneg (f ((1 : ℂ) - z)))
      (mul_nonneg hAM_nonneg
        (le_of_lt (Real.exp_pos ((BM + Bf + 1) * H ^ (mM + mf)))))
  have hcollapse :
      (AM * Real.exp ((BM + Bf + 1) * H ^ (mM + mf))) *
          (Af * Real.exp ((BM + Bf + 1) * H ^ (mM + mf))) =
        AM * Af * Real.exp ((2 * (BM + Bf + 1)) * H ^ (mM + mf)) := by
    exact finiteOrderGrowthProductEnvelope_exp_collapse
      AM Af ((BM + Bf + 1) * H ^ (mM + mf))
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ AM * Af * Real.exp ((2 * (BM + Bf + 1)) * H ^ (mM + mf)))
    hidentity_norm.symm
    (hproduct.trans_eq hcollapse)

/-- Left half-plane finite-order growth for the pole-cleared zeta factor.

This is the functional-equation side of the standard finite-order theorem:
transport the right half-plane Euler-Maclaurin/Dirichlet-series control across
the completed functional equation and use the exposed Gamma/Stirling owner
estimates; cf. Titchmarsh, Ch. 2 and Edwards, Ch. 1. -/
theorem poleClearedRiemannZeta_leftHalfPlane_completedFunctionalEquation_transport_identity :
    ∃ M : ℂ → ℂ,
      (∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          ‖M z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        poleClearedRiemannZeta z =
          M z * poleClearedRiemannZeta ((1 : ℂ) - z) := by
  refine
    ⟨poleClearedRiemannZeta_completedFunctionalEquationMultiplier,
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_leftHalfPlane_finiteOrder_growth,
      ?_⟩
  intro z hz
  exact poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity hz

/-- Functional-equation transport of finite-order growth from the reflected right
half-plane to the left half-plane.

The multiplier `M` is the completed functional-equation/Gamma-ratio factor
together with the pole-clearing rational terms.  This theorem is pure
finite-order bookkeeping once the exact identity and multiplier estimate are
available. -/
theorem poleClearedRiemannZeta_leftHalfPlane_finiteOrder_growth_of_completedFunctionalEquation_transport
    (htransport :
      ∃ M : ℂ → ℂ,
        (∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
          0 < A ∧
          0 < B ∧
          ∀ z : ℂ,
            z.re ≤ 0 →
            ‖M z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          poleClearedRiemannZeta z =
            M z * poleClearedRiemannZeta ((1 : ℂ) - z))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          1 ≤ w.re →
          ‖poleClearedRiemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases htransport with ⟨M, hM, hidentity⟩
  exact
    finiteOrder_leftHalfPlane_growth_of_multiplier_reflection_identity
      poleClearedRiemannZeta M hM
      (finiteOrder_leftHalfPlane_reflection_growth_bound
        poleClearedRiemannZeta hright)
      hidentity

theorem poleClearedRiemannZeta_leftHalfPlane_finiteOrder_growth_from_completedFunctionalEquation_and_GammaStirling :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_leftHalfPlane_finiteOrder_growth_of_completedFunctionalEquation_transport
      poleClearedRiemannZeta_leftHalfPlane_completedFunctionalEquation_transport_identity
      poleClearedRiemannZeta_reflectedRightHalfPlane_finiteOrder_growth_from_EulerMaclaurin

/-- Left half-plane finite-order growth for the pole-cleared zeta factor.

This is only name transport from the completed functional equation plus the
Gamma/Stirling owner estimates. -/
theorem poleClearedRiemannZeta_leftHalfPlane_finiteOrder_growth_from_functionalEquation :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_leftHalfPlane_finiteOrder_growth_from_completedFunctionalEquation_and_GammaStirling

/-- Compact core of the central strip for the pole-cleared zeta factor.

This is the finite-height local boundedness part: continuity of the removable
pole-cleared normalization on the compact rectangle `0 ≤ Re z ≤ 2`,
`|Im z| ≤ 1`, converted to a degree-zero finite-order envelope. -/

end
end LFunctions
end Boundary
