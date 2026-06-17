import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.Owner

/-!
# Completed functional-equation core algebra

This is the core algebraic section of functional-equation transport, containing
denominator data, quotient identities, and raw multiplier algebra.
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

end

end LFunctions
end Boundary
