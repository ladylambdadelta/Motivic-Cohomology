import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.FirstDerivative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Regularity.Owner

/-!
# Reciprocal-density scalar preliminaries
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The canonical Abel/Euler-Maclaurin cutoff is positive as a real endpoint. -/
theorem scalarReciprocalDensity_cutoff_real_pos
    (t : ℝ) :
    0 < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) := by
  exact Nat.cast_pos.mpr (boundaryLineOnePointRealParam_cutoff_pos t)

/-- The canonical Abel/Euler-Maclaurin cutoff is at least two as a real
endpoint. -/
theorem scalarReciprocalDensity_two_le_cutoff_real
    (t : ℝ) :
    (2 : ℝ) ≤ (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) := by
  exact Nat.cast_le.mpr (boundaryLineOnePointRealParam_two_le_cutoff t)

/-- Points in the post-cutoff interval are positive. -/
theorem scalarReciprocalDensity_Ioc_point_pos
    (t : ℝ)
    {M : ℕ}
    {x : ℝ}
    (hx :
      x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)) :
    0 < x := by
  exact lt_trans (scalarReciprocalDensity_cutoff_real_pos t) hx.1

/-- Points in the closed post-cutoff interval are positive. -/
theorem scalarReciprocalDensity_Icc_point_pos
    (t : ℝ)
    {M : ℕ}
    {x : ℝ}
    (hx :
      x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)) :
    0 < x := by
  exact lt_of_lt_of_le (scalarReciprocalDensity_cutoff_real_pos t) hx.1

/-- Positivity of the shifted logarithm on the scalar-calculus range. -/
theorem real_log_two_add_nonneg_of_two_le
    {x : ℝ}
    (hx : (2 : ℝ) ≤ x) :
    0 ≤ Real.log (2 + x) := by
  have hone_le_two : (1 : ℝ) ≤ 2 := by
    calc
      (1 : ℝ) ≤ 1 + 1 := le_add_of_nonneg_right zero_le_one
      _ = 2 := by
        exact one_add_one_eq_two
  have htwo_le_two_add : (2 : ℝ) ≤ 2 + x :=
    le_trans hx (le_add_of_nonneg_left (show (0 : ℝ) ≤ 2 by
      calc
        (0 : ℝ) ≤ 1 := zero_le_one
        _ ≤ 2 := hone_le_two))
  exact Real.log_nonneg (le_trans hone_le_two htwo_le_two_add)

/-- On `2 ≤ x`, `log(2+x)/x` is bounded by the derivative density of
`(log(2+x))²`. -/
theorem real_log_two_add_div_self_le_log_sq_derivative_density
    {x : ℝ}
    (hx : (2 : ℝ) ≤ x) :
    Real.log (2 + x) / x ≤
      2 * Real.log (2 + x) / (2 + x) := by
  have hx_pos : 0 < x :=
    lt_of_lt_of_le zero_lt_two hx
  have hshift_pos : 0 < 2 + x :=
    add_pos_of_pos_of_nonneg zero_lt_two (le_trans (show (0 : ℝ) ≤ 2 by
      exact le_of_lt zero_lt_two) hx)
  have hlog_nonneg : 0 ≤ Real.log (2 + x) :=
    real_log_two_add_nonneg_of_two_le hx
  have hreciprocal :
      (1 : ℝ) / x ≤ 2 / (2 + x) := by
    have hmul :
        (2 + x) ≤ 2 * x := by
      calc
        2 + x ≤ x + x :=
          add_le_add_right hx x
        _ = 2 * x := by
          exact (two_mul x).symm
    have hmul_with_one :
        (1 : ℝ) * (2 + x) ≤ 2 * x :=
      Eq.subst
        (motive := fun y : ℝ => y ≤ 2 * x)
        (one_mul (2 + x)).symm
        hmul
    exact (div_le_div_iff₀ hx_pos hshift_pos).mpr hmul_with_one
  have hscaled :
      Real.log (2 + x) * ((1 : ℝ) / x) ≤
        Real.log (2 + x) * (2 / (2 + x)) :=
    mul_le_mul_of_nonneg_left hreciprocal hlog_nonneg
  have hright :
      Real.log (2 + x) * (2 / (2 + x)) =
        2 * Real.log (2 + x) / (2 + x) := by
    calc
      Real.log (2 + x) * (2 / (2 + x)) =
          Real.log (2 + x) * (2 * ((1 : ℝ) / (2 + x))) := by
        exact congrArg
          (fun y : ℝ => Real.log (2 + x) * y)
          (div_eq_mul_one_div 2 (2 + x))
      _ = (2 * Real.log (2 + x)) * ((1 : ℝ) / (2 + x)) := by
        let L : ℝ := Real.log (2 + x)
        let R : ℝ := (1 : ℝ) / (2 + x)
        calc
          L * (2 * R) = (L * 2) * R := by
            exact (mul_assoc L 2 R).symm
          _ = (2 * L) * R := by
            exact congrArg (fun y : ℝ => y * R) (mul_comm L 2)
      _ = 2 * Real.log (2 + x) / (2 + x) := by
        exact (div_eq_mul_one_div (2 * Real.log (2 + x)) (2 + x)).symm
  calc
    Real.log (2 + x) / x =
        Real.log (2 + x) * ((1 : ℝ) / x) := by
      exact div_eq_mul_one_div (Real.log (2 + x)) x
    _ ≤ Real.log (2 + x) * (2 / (2 + x)) :=
      hscaled
    _ = 2 * Real.log (2 + x) / (2 + x) :=
      hright

/-- Derivative of the square of the shifted logarithm. -/
theorem real_hasDerivAt_log_two_add_sq
    {x : ℝ}
    (hx : (0 : ℝ) < 2 + x) :
    HasDerivAt
      (fun y : ℝ => (Real.log (2 + y)) ^ 2)
      (2 * Real.log (2 + x) / (2 + x))
      x := by
  have hshift_ne : 2 + x ≠ 0 :=
    ne_of_gt hx
  have hshift :
      HasDerivAt (fun y : ℝ => 2 + y) 1 x :=
    (hasDerivAt_id x).const_add 2
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (2 + y)) ((2 + x)⁻¹) x :=
    have hraw :
        HasDerivAt (fun y : ℝ => Real.log (2 + y)) (((2 + x)⁻¹) * 1) x :=
      (Real.hasDerivAt_log hshift_ne).comp x hshift
    have hcoeff_one :
        ((2 + x)⁻¹) * (1 : ℝ) = ((2 + x)⁻¹) :=
      mul_one ((2 + x)⁻¹)
    Eq.subst
      (motive := fun c : ℝ =>
        HasDerivAt (fun y : ℝ => Real.log (2 + y)) c x)
      hcoeff_one
      hraw
  have hpow :
      HasDerivAt
        (fun y : ℝ => (Real.log (2 + y)) ^ 2)
        (((2 : ℝ) * (Real.log (2 + x)) ^ (2 - 1)) * ((2 + x)⁻¹))
        x :=
    (hasDerivAt_pow 2 (Real.log (2 + x))).comp x hlog
  have hcoeff :
      ((2 : ℝ) * (Real.log (2 + x)) ^ (2 - 1)) * ((2 + x)⁻¹) =
        2 * Real.log (2 + x) / (2 + x) := by
    let L : ℝ := Real.log (2 + x)
    have hnat : (2 : ℕ) - 1 = 1 :=
      rfl
    have hpow_one :
        L ^ ((2 : ℕ) - 1) = L := by
      calc
        L ^ ((2 : ℕ) - 1) = L ^ (1 : ℕ) := by
          exact congrArg (fun n : ℕ => L ^ n) hnat
        _ = L := by
          exact pow_one L
    calc
      ((2 : ℝ) * (Real.log (2 + x)) ^ (2 - 1)) * ((2 + x)⁻¹) =
          (2 * Real.log (2 + x)) * ((2 + x)⁻¹) := by
        exact congrArg
          (fun y : ℝ => ((2 : ℝ) * y) * ((2 + x)⁻¹))
          hpow_one
      _ = 2 * Real.log (2 + x) / (2 + x) := by
        exact (div_eq_mul_inv (2 * Real.log (2 + x)) (2 + x)).symm
  exact hcoeff ▸ hpow

end
end LFunctions
end Boundary
