import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroMultiplicityCore.LogSingularity.Owner

/-!
# Jensen radial-gap multiplicity core

This owner layer was split from `ZeroMultiplicityCore.RadialGap.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

/-- The doubled-radius Jensen loss has a positive logarithmic denominator. -/
theorem real_log_two_pos : 0 < Real.log 2 := by
  exact Real.log_pos one_lt_two

/-- The doubled-radius Jensen loss has a nonzero logarithmic denominator. -/
theorem real_log_two_ne_zero : Real.log 2 ≠ 0 := by
  exact real_log_two_pos.ne'

/-- The reciprocal of the doubled-radius Jensen loss is nonnegative. -/
theorem real_log_two_inv_nonneg : 0 ≤ (Real.log 2)⁻¹ := by
  exact inv_nonneg.mpr real_log_two_pos.le

/-- Radii used in the doubled Jensen circle are positive for `R ≥ 1`. -/
theorem doubled_radius_pos_of_one_le {R : ℝ} (hR : 1 ≤ R) :
    0 < 2 * R := by
  exact mul_pos two_pos (lt_of_lt_of_le zero_lt_one hR)

/-- A positive radius is strictly smaller than its double. -/
theorem radius_lt_doubled_radius_of_pos {R : ℝ} (hR : 0 < R) :
    R < 2 * R := by
  calc
    R = 1 * R := (one_mul R).symm
    _ < 2 * R := mul_lt_mul_of_pos_right one_lt_two hR

/-- The doubled radius is at least one for `R ≥ 1`. -/
theorem one_le_doubled_radius_of_one_le {R : ℝ} (hR : 1 ≤ R) :
    1 ≤ 2 * R := by
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  exact le_trans hR (le_of_lt (radius_lt_doubled_radius_of_pos hR_pos))

/-- A nonzero point in the closed disk of radius `R` has at least the standard
`log 2` radial Jensen gap when the boundary radius is `2R`. -/
theorem log_two_le_log_doubled_radius_div_norm
    {R : ℝ}
    {z : ℂ}
    (hR : 1 ≤ R)
    (hz_ne : z ≠ 0)
    (hz_le : ‖z‖ ≤ R) :
    Real.log 2 ≤ Real.log ((2 * R) / ‖z‖) := by
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
  have htwo_le : 2 ≤ (2 * R) / ‖z‖ := by
    have hmul_le : 2 * ‖z‖ ≤ 2 * R := by
      exact mul_le_mul_of_nonneg_left hz_le zero_le_two
    exact (le_div_iff₀ hz_pos).mpr hmul_le
  exact Real.log_le_log zero_lt_two htwo_le

/-- Multiplicity-weighted Jensen radial-gap summand for a zero on the
comparison circle of radius `ρ`.

The zero at the origin is omitted here: in Jensen's formula it is the factored
Taylor root and contributes to the additive constant, not to the radial-gap
sum. -/
noncomputable def entireFunctionJensenRadialGapSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (z : EntireFunctionZero F) : ℝ :=
  if hz₀ : (z : ℂ) = 0 then
    0
  else if ‖(z : ℂ)‖ < ρ then
    (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
      Real.log (ρ / ‖(z : ℂ)‖)
  else
    0

/-- Multiplicity-weighted Jensen radial-gap sum inside the comparison circle. -/
noncomputable def entireFunctionJensenRadialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)] : ℝ :=
  ∑' z : EntireFunctionZero F,
    entireFunctionJensenRadialGapSummand F hF ρ z

/-- Closed-disk multiplicity summand with the origin Taylor factor removed.

The omitted origin contribution is exactly the finite Taylor-root term that is
absorbed into the additive Jensen constant. -/
noncomputable def entireFunctionNonzeroZeroMultiplicityClosedDiskSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)]
    (z : EntireFunctionZero F) : ℝ :=
  if (z : ℂ) = 0 then
    0
  else
    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z

/-- The origin-supported closed-disk multiplicity summand.

This is the finite Taylor-root contribution omitted from the nonzero radial-gap
sum.  It is supported on the unique zero-subtype point whose value is `0`,
when such a point exists. -/
noncomputable def entireFunctionOriginZeroMultiplicityClosedDiskSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)]
    (z : EntireFunctionZero F) : ℝ :=
  if (z : ℂ) = 0 then
    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
  else
    0

/-- The origin-only closed-disk summand has tsum equal to the distinguished
origin zero's closed-disk contribution. -/
theorem entireFunctionOriginZeroMultiplicityClosedDiskSummand_tsum_eq
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)]
    {z₀ : EntireFunctionZero F}
    (hz₀ : (z₀ : ℂ) = 0) :
    (∑' z : EntireFunctionZero F,
        entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) =
      entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀ := by
  have hpoint :
      ∀ z : EntireFunctionZero F,
        entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z =
          if z = z₀ then
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀
          else
            0 := by
    intro z
    show
      (if (z : ℂ) = 0 then
        entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
      else
        0) =
        if z = z₀ then
          entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀
        else
          0
    match (inferInstance : Decidable ((z : ℂ) = 0)) with
    | isTrue hz_origin =>
        have hz_eq : z = z₀ := by
          exact Subtype.ext (Eq.trans hz_origin hz₀.symm)
        have hclosed_eq :
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z =
              entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀ := by
          exact congrArg (fun w : EntireFunctionZero F =>
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R w) hz_eq
        calc
          (if (z : ℂ) = 0 then
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
          else
            0) = entireFunctionZeroMultiplicityClosedDiskSummand F hF R z :=
              if_pos hz_origin
          _ = entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀ := hclosed_eq
          _ = (if z = z₀ then
                entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀
              else
                0) := (if_pos hz_eq).symm
    | isFalse hz_origin =>
        have hz_ne : z ≠ z₀ := by
          intro hz_eq
          exact hz_origin (Eq.trans (congrArg Subtype.val hz_eq) hz₀)
        calc
          (if (z : ℂ) = 0 then
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
          else
            0) = 0 := if_neg hz_origin
          _ = (if z = z₀ then
                entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀
              else
                0) := (if_neg hz_ne).symm
  calc
    (∑' z : EntireFunctionZero F,
      entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z)
        = ∑' z : EntireFunctionZero F,
            if z = z₀ then
              entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀
            else
              0 := by
            exact tsum_congr hpoint
    _ = entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀ :=
      tsum_ite_eq z₀ (entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀)

/-- The closed-disk summand splits into its nonzero and origin-supported
parts. -/
theorem entireFunctionZeroMultiplicityClosedDiskSummand_eq_nonzero_add_origin
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)]
    (z : EntireFunctionZero F) :
    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z =
      entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z +
        entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z := by
  show
    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z =
      (if (z : ℂ) = 0 then
        0
      else
        entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) +
      (if (z : ℂ) = 0 then
        entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
      else
        0)
  match (inferInstance : Decidable ((z : ℂ) = 0)) with
  | isTrue hz₀ =>
      have hnonzero :
          (if (z : ℂ) = 0 then
            0
          else
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) = 0 :=
        if_pos hz₀
      have horigin :
          (if (z : ℂ) = 0 then
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
          else
            0) = entireFunctionZeroMultiplicityClosedDiskSummand F hF R z :=
        if_pos hz₀
      calc
        entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
            = 0 + entireFunctionZeroMultiplicityClosedDiskSummand F hF R z :=
              (zero_add _).symm
        _ = (if (z : ℂ) = 0 then
              0
            else
              entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) +
              entireFunctionZeroMultiplicityClosedDiskSummand F hF R z := by
              exact congrArg
                (fun t : ℝ => t + entireFunctionZeroMultiplicityClosedDiskSummand F hF R z)
                hnonzero.symm
        _ = (if (z : ℂ) = 0 then
              0
            else
              entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) +
              (if (z : ℂ) = 0 then
                entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
              else
                0) := by
              exact congrArg
                (fun t : ℝ =>
                  (if (z : ℂ) = 0 then
                    0
                  else
                    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) + t)
                horigin.symm
  | isFalse hz₀ =>
      have hnonzero :
          (if (z : ℂ) = 0 then
            0
          else
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) =
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z :=
        if_neg hz₀
      have horigin :
          (if (z : ℂ) = 0 then
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
          else
            0) = 0 :=
        if_neg hz₀
      calc
        entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
            = entireFunctionZeroMultiplicityClosedDiskSummand F hF R z + 0 :=
              (add_zero _).symm
        _ = (if (z : ℂ) = 0 then
              0
            else
              entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) + 0 := by
              exact congrArg (fun t : ℝ => t + 0) hnonzero.symm
        _ = (if (z : ℂ) = 0 then
              0
            else
              entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) +
              (if (z : ℂ) = 0 then
                entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
              else
                0) := by
              exact congrArg
                (fun t : ℝ =>
                  (if (z : ℂ) = 0 then
                    0
                  else
                    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) + t)
                horigin.symm


end
end LFunctions
end Boundary
