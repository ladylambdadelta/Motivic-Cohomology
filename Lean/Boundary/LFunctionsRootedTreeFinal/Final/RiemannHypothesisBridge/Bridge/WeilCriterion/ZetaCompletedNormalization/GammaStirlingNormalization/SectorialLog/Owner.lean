import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.NormalizedStirling.Owner

/-!
# Sectorial log-Gamma Stirling normalization

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.GammaStirlingNormalization.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

def Complex.fixedRealPartVerticalPoint (a b : ℝ) : ℂ :=
  (a : ℂ) + (b : ℂ) * Complex.I

/-- The fixed-line point has real coordinate `a`. -/
theorem Complex.fixedRealPartVerticalPoint_re
    (a b : ℝ) :
    (Complex.fixedRealPartVerticalPoint a b).re = a := by
  calc
    (Complex.fixedRealPartVerticalPoint a b).re =
        ((a : ℂ) + (b : ℂ) * Complex.I).re := rfl
    _ = (a : ℂ).re + ((b : ℂ) * Complex.I).re :=
        Complex.add_re (a : ℂ) ((b : ℂ) * Complex.I)
    _ = a + 0 := by
      congr 1
      exact Complex.mul_I_re (b : ℂ)
    _ = a := add_zero a

/-- The fixed-line point has imaginary coordinate `b`. -/
theorem Complex.fixedRealPartVerticalPoint_im
    (a b : ℝ) :
    (Complex.fixedRealPartVerticalPoint a b).im = b := by
  calc
    (Complex.fixedRealPartVerticalPoint a b).im =
        ((a : ℂ) + (b : ℂ) * Complex.I).im := rfl
    _ = (a : ℂ).im + ((b : ℂ) * Complex.I).im :=
        Complex.add_im (a : ℂ) ((b : ℂ) * Complex.I)
    _ = 0 + b := by
      congr 1
      exact Complex.mul_I_im (b : ℂ)
    _ = b := zero_add b

/-- The direct fixed-real-part vertical Stirling envelope. -/
def Complex.fixedRealPartVerticalStirlingEnvelope (a b : ℝ) : ℝ :=
  Real.exp (-(Real.pi / 2) * ‖b‖) * (1 + ‖b‖) ^ (a - 1 / 2)

/-- The reciprocal fixed-real-part vertical Stirling envelope. -/
def Complex.fixedRealPartVerticalReciprocalStirlingEnvelope (a b : ℝ) : ℝ :=
  Real.exp ((Real.pi / 2) * ‖b‖) * (1 + ‖b‖) ^ (1 / 2 - a)

/-- The fixed-real-part direct Stirling envelope is positive. -/
theorem Complex.fixedRealPartVerticalStirlingEnvelope_pos
    (a b : ℝ) :
    0 < Complex.fixedRealPartVerticalStirlingEnvelope a b := by
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  exact mul_pos
    (Real.exp_pos (-(Real.pi / 2) * ‖b‖))
    (Real.rpow_pos_of_pos hbase_pos (a - 1 / 2))

/-- The fixed-real-part direct Stirling envelope is nonnegative. -/
theorem Complex.fixedRealPartVerticalStirlingEnvelope_nonneg
    (a b : ℝ) :
    0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
  le_of_lt (Complex.fixedRealPartVerticalStirlingEnvelope_pos a b)

/-- The fixed-real-part reciprocal Stirling envelope is positive. -/
theorem Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_pos
    (a b : ℝ) :
    0 < Complex.fixedRealPartVerticalReciprocalStirlingEnvelope a b := by
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  exact mul_pos
    (Real.exp_pos ((Real.pi / 2) * ‖b‖))
    (Real.rpow_pos_of_pos hbase_pos (1 / 2 - a))

/-- The fixed-real-part reciprocal Stirling envelope is nonnegative. -/
theorem Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_nonneg
    (a b : ℝ) :
    0 ≤ Complex.fixedRealPartVerticalReciprocalStirlingEnvelope a b :=
  le_of_lt (Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_pos a b)

/-- Shifting the fixed real part by a natural number multiplies the Stirling
envelope by the corresponding power of the vertical polynomial scale. -/
theorem Complex.fixedRealPartVerticalStirlingEnvelope_natShift_eq
    (a b : ℝ)
    (N : ℕ) :
    Complex.fixedRealPartVerticalStirlingEnvelope (a + N) b =
      Complex.fixedRealPartVerticalStirlingEnvelope a b *
        (1 + ‖b‖) ^ (N : ℝ) :=
  let hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  let hexponent :
      a + (N : ℝ) - 1 / 2 = (a - 1 / 2) + (N : ℝ) :=
    calc
      a + (N : ℝ) - 1 / 2 = (a + (N : ℝ)) + -(1 / 2) :=
        sub_eq_add_neg (a + (N : ℝ)) (1 / 2)
      _ = a + ((N : ℝ) + -(1 / 2)) :=
        add_assoc a (N : ℝ) (-(1 / 2))
      _ = a + (-(1 / 2) + (N : ℝ)) :=
        congrArg (fun t : ℝ => a + t) (add_comm (N : ℝ) (-(1 / 2)))
      _ = (a + -(1 / 2)) + (N : ℝ) :=
        (add_assoc a (-(1 / 2)) (N : ℝ)).symm
      _ = (a - 1 / 2) + (N : ℝ) :=
        congrArg (fun t : ℝ => t + (N : ℝ)) (sub_eq_add_neg a (1 / 2)).symm
  calc
    Complex.fixedRealPartVerticalStirlingEnvelope (a + N) b =
        Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a + (N : ℝ) - 1 / 2) :=
      rfl
    _ = Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ ((a - 1 / 2) + (N : ℝ)) :=
      congrArg
        (fun t : ℝ => Real.exp (-(Real.pi / 2) * ‖b‖) * (1 + ‖b‖) ^ t)
        hexponent
    _ = Real.exp (-(Real.pi / 2) * ‖b‖) *
          ((1 + ‖b‖) ^ (a - 1 / 2) * (1 + ‖b‖) ^ (N : ℝ)) :=
      congrArg
        (fun t : ℝ => Real.exp (-(Real.pi / 2) * ‖b‖) * t)
        (Real.rpow_add hbase_pos (a - 1 / 2) (N : ℝ))
    _ = (Real.exp (-(Real.pi / 2) * ‖b‖) * (1 + ‖b‖) ^ (a - 1 / 2)) *
          (1 + ‖b‖) ^ (N : ℝ) :=
      mul_assoc (Real.exp (-(Real.pi / 2) * ‖b‖))
        ((1 + ‖b‖) ^ (a - 1 / 2))
        ((1 + ‖b‖) ^ (N : ℝ))
    _ = Complex.fixedRealPartVerticalStirlingEnvelope a b * (1 + ‖b‖) ^ (N : ℝ) :=
      rfl

/-- Cancelling the polynomial scale introduced by a natural real-part shift in
the vertical Stirling envelope. -/
theorem Complex.fixedRealPartVerticalStirlingEnvelope_natShift_div_scale_eq
    (a b : ℝ)
    (N : ℕ)
    (C d : ℝ)
    (hd_pos : 0 < d) :
    C * Complex.fixedRealPartVerticalStirlingEnvelope (a + N) b /
        (d * (1 + ‖b‖) ^ (N : ℝ)) =
      (C / d) * Complex.fixedRealPartVerticalStirlingEnvelope a b := by
  let E : ℝ := Complex.fixedRealPartVerticalStirlingEnvelope a b
  let T : ℝ := (1 + ‖b‖) ^ (N : ℝ)
  have hbase_pos : 0 < 1 + ‖b‖ :=
    add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg b)
  have hT_pos : 0 < T :=
    Real.rpow_pos_of_pos hbase_pos (N : ℝ)
  have hT_ne : T ≠ 0 :=
    ne_of_gt hT_pos
  have hshift :
      Complex.fixedRealPartVerticalStirlingEnvelope (a + N) b = E * T :=
    Complex.fixedRealPartVerticalStirlingEnvelope_natShift_eq a b N
  have hmul_div :
      C * (E * T) / (d * T) = C * E / d := by
    calc
      C * (E * T) / (d * T) = (C * E) * T / (d * T) := by
        exact congrArg (fun u : ℝ => u / (d * T)) (mul_assoc C E T).symm
      _ = C * E / d := by
        exact mul_div_mul_right (C * E) d hT_ne
  have hdiv_mul :
      C * E / d = (C / d) * E := by
    calc
      C * E / d = (C * E) * d⁻¹ := by
        exact div_eq_mul_inv (C * E) d
      _ = C * (E * d⁻¹) := by
        exact mul_assoc C E d⁻¹
      _ = C * (d⁻¹ * E) := by
        exact congrArg (fun u : ℝ => C * u) (mul_comm E d⁻¹)
      _ = (C * d⁻¹) * E := by
        exact (mul_assoc C d⁻¹ E).symm
      _ = (C / d) * E := by
        exact congrArg (fun u : ℝ => u * E) (div_eq_mul_inv C d).symm
  calc
    C * Complex.fixedRealPartVerticalStirlingEnvelope (a + N) b /
        (d * (1 + ‖b‖) ^ (N : ℝ)) =
      C * (E * T) / (d * T) := by
      exact congrArg
        (fun u : ℝ => C * u / (d * T))
        hshift
    _ = C * E / d := hmul_div
    _ = (C / d) * E := hdiv_mul

/-- Sectorial Stirling estimate for the normalized Gamma factor on the closed
right half-plane.

This is the canonical sectorial Stirling input in the exact normalized form
used by the owner API:
`Γ(w) exp(w) w^(1/2-w) = sqrt(2π) + O(1/‖w‖)`, uniformly in the closed
right half-plane for large radius; cf. DLMF §5.11 and Whittaker-Watson,
Ch. XII. -/
theorem Complex.sectorialStirling_normalizedGamma_closedRightHalfPlane :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖ := by
  exact
    Complex.sectorialStirling_normalizedGamma_closedRightHalfPlane_from_binetSecondFormula

/-- Classical sectorial Stirling estimate for the normalized Gamma factor on
the closed right half-plane.

This is only name transport to the canonical sectorial Stirling theorem above. -/
theorem Complex.classical_sectorialStirling_normalizedGamma_closedRightHalfPlane :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖ := by
  exact Complex.sectorialStirling_normalizedGamma_closedRightHalfPlane

/-- Sectorial logarithmic Stirling expansion for `Complex.Gamma` on the closed
right half-plane.

This public owner theorem is the normalized-factor consequence of the canonical
sectorial Stirling estimate.  The logarithmic formulation and this exponential
normalization are equivalent on the large closed right-half-plane sector. -/
theorem Complex.sectorialLogGammaAsymptotic_closedRightHalfPlane :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖ := by
  exact Complex.classical_sectorialStirling_normalizedGamma_closedRightHalfPlane

/-- If a complex number is within `sqrt (2π)` of `sqrt (2π)`, then its norm is
bounded by `2 sqrt (2π)`.

This is the elementary triangle-inequality extraction used to pass from the
exponential Stirling remainder to a uniform bound for the normalized Gamma
factor. -/
theorem Complex.norm_le_two_sqrt_two_pi_of_norm_sub_sqrt_two_pi_le_sqrt_two_pi
    (A : ℂ)
    (hA :
      ‖A - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤ Real.sqrt (2 * Real.pi)) :
    ‖A‖ ≤ 2 * Real.sqrt (2 * Real.pi) := by
  have htriangle :
      ‖A‖ ≤
        ‖A - (Real.sqrt (2 * Real.pi) : ℂ)‖ +
          ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ := by
    calc
      ‖A‖ =
          ‖(A - (Real.sqrt (2 * Real.pi) : ℂ)) +
            (Real.sqrt (2 * Real.pi) : ℂ)‖ := by
        exact congrArg norm (sub_add_cancel A (Real.sqrt (2 * Real.pi) : ℂ)).symm
      _ ≤
          ‖A - (Real.sqrt (2 * Real.pi) : ℂ)‖ +
            ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ :=
        norm_add_le (A - (Real.sqrt (2 * Real.pi) : ℂ))
          (Real.sqrt (2 * Real.pi) : ℂ)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * Real.pi) :=
    Real.sqrt_nonneg (2 * Real.pi)
  have hnorm_sqrt :
      ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ = Real.sqrt (2 * Real.pi) := by
    exact Complex.norm_ofReal_of_nonneg hsqrt_nonneg
  calc
    ‖A‖ ≤
        ‖A - (Real.sqrt (2 * Real.pi) : ℂ)‖ +
          ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ := htriangle
    _ ≤ Real.sqrt (2 * Real.pi) +
          ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ :=
        add_le_add_right hA ‖(Real.sqrt (2 * Real.pi) : ℂ)‖
    _ = Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) :=
        congrArg (fun x : ℝ => Real.sqrt (2 * Real.pi) + x) hnorm_sqrt
    _ = 2 * Real.sqrt (2 * Real.pi) := by
        exact (two_mul (Real.sqrt (2 * Real.pi))).symm

/-- Pointwise normalized Gamma-factor bound extracted from an exponential
Stirling estimate once the error term is at most `sqrt (2π)`. -/
theorem Complex.normalizedGammaFactor_norm_le_two_sqrt_two_pi_of_exponentialStirling_error
    (R K : ℝ)
    (hStirling :
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (w : ℂ)
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_R : R ≤ ‖w‖)
    (hw_error : K / ‖w‖ ≤ Real.sqrt (2 * Real.pi)) :
    ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ ≤
      2 * Real.sqrt (2 * Real.pi) := by
  have herror :
      ‖Complex.Gamma w * Complex.exp w *
          w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
        Real.sqrt (2 * Real.pi) :=
    le_trans (hStirling w hw_sector hw_R) hw_error
  exact
    Complex.norm_le_two_sqrt_two_pi_of_norm_sub_sqrt_two_pi_le_sqrt_two_pi
      (Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w))
      herror

/-- If a complex number is within half of `sqrt (2π)` from `sqrt (2π)`, then
its norm is bounded below by the same half-constant. -/
theorem Complex.half_sqrt_two_pi_le_norm_of_norm_sub_sqrt_two_pi_le_half
    (A : ℂ)
    (hA :
      ‖A - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
        Real.sqrt (2 * Real.pi) / 2) :
    Real.sqrt (2 * Real.pi) / 2 ≤ ‖A‖ := by
  let s : ℝ := Real.sqrt (2 * Real.pi)
  have hs_nonneg : 0 ≤ s :=
    Real.sqrt_nonneg (2 * Real.pi)
  have hs_norm : ‖(s : ℂ)‖ = s :=
    Complex.norm_ofReal_of_nonneg hs_nonneg
  have htriangle :
      ‖(s : ℂ)‖ ≤ ‖A‖ + ‖A - (s : ℂ)‖ := by
    calc
      ‖(s : ℂ)‖ = ‖A - (A - (s : ℂ))‖ := by
        exact congrArg norm (sub_sub_cancel A (s : ℂ)).symm
      _ ≤ ‖A‖ + ‖A - (s : ℂ)‖ :=
        norm_sub_le A (A - (s : ℂ))
  have hs_le_sum : s ≤ ‖A‖ + s / 2 := by
    calc
      s = ‖(s : ℂ)‖ := hs_norm.symm
      _ ≤ ‖A‖ + ‖A - (s : ℂ)‖ := htriangle
      _ ≤ ‖A‖ + s / 2 := add_le_add_left hA ‖A‖
  have hhalf_le_sub : s - s / 2 ≤ ‖A‖ :=
    sub_le_iff_le_add.mpr hs_le_sum
  have hhalf_eq : s - s / 2 = s / 2 := by
    calc
      s - s / 2 = s * 1 - s * (1 / 2) := by
        exact congrArg₂ HSub.hSub (mul_one s).symm (mul_one_div s 2).symm
      _ = s * (1 - 1 / 2) := by
        exact (mul_sub s 1 (1 / 2)).symm
      _ = s * (1 / 2) := by
        exact congrArg (fun t : ℝ => s * t) (sub_eq_self.mpr ?_)
      _ = s / 2 := by
        exact mul_one_div s 2
    · exact sub_eq_zero.mpr (one_div_two_add_one_div_two.symm)
  exact
    Eq.subst
      (motive := fun t : ℝ => t ≤ ‖A‖)
      hhalf_eq
      hhalf_le_sub

/-- Pointwise lower normalized Gamma-factor bound extracted from an exponential
Stirling estimate once the error term is at most half of `sqrt (2π)`. -/
theorem Complex.half_sqrt_two_pi_le_normalizedGammaFactor_norm_of_exponentialStirling_error
    (R K : ℝ)
    (hStirling :
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (w : ℂ)
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_R : R ≤ ‖w‖)
    (hw_error : K / ‖w‖ ≤ Real.sqrt (2 * Real.pi) / 2) :
    Real.sqrt (2 * Real.pi) / 2 ≤
      ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ := by
  have herror :
      ‖Complex.Gamma w * Complex.exp w *
          w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
        Real.sqrt (2 * Real.pi) / 2 :=
    le_trans (hStirling w hw_sector hw_R) hw_error
  exact
    Complex.half_sqrt_two_pi_le_norm_of_norm_sub_sqrt_two_pi_le_half
      (Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w))
      herror

/-- A cutoff radius that makes `K / r` at most half of `sqrt (2π)`. -/
theorem real_stirlingError_div_norm_le_half_sqrt_two_pi_of_cutoff
    (K r : ℝ)
    (hK_pos : 0 < K)
    (hr_pos : 0 < r)
    (hr_cutoff : 4 * K / Real.sqrt (2 * Real.pi) ≤ r) :
    K / r ≤ Real.sqrt (2 * Real.pi) / 2 := by
  let s : ℝ := Real.sqrt (2 * Real.pi)
  have hs_pos : 0 < s :=
    Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos)
  have hcutoff_mul : 4 * K ≤ r * s :=
    (div_le_iff₀ hs_pos).mp hr_cutoff
  have htwoK_le_fourK : 2 * K ≤ 4 * K := by
    have hK_nonneg : 0 ≤ K :=
      le_of_lt hK_pos
    have htwo_le_four : (2 : ℝ) ≤ 4 := by
      calc
        (2 : ℝ) ≤ 2 + 2 := le_add_of_nonneg_right (le_of_lt two_pos)
        _ = 4 := rfl
    calc
      2 * K ≤ 4 * K :=
        mul_le_mul_of_nonneg_right htwo_le_four hK_nonneg
  have htwoK_le_rs : 2 * K ≤ r * s :=
    le_trans htwoK_le_fourK hcutoff_mul
  have htwoK_div_r_le_s : 2 * K / r ≤ s :=
    (div_le_iff₀ hr_pos).mpr
      (Eq.subst
        (motive := fun t : ℝ => 2 * K ≤ t)
        (mul_comm s r)
        htwoK_le_rs)
  have htwo_pos : 0 < (2 : ℝ) :=
    two_pos
  have hK_div_eq : 2 * (K / r) = 2 * K / r := by
    calc
      2 * (K / r) = (2 * K) / r := by
        exact (mul_div_assoc 2 K r).symm
  have htwice_le : 2 * (K / r) ≤ s :=
    Eq.subst
      (motive := fun t : ℝ => t ≤ s)
      hK_div_eq.symm
      htwoK_div_r_le_s
  exact
    (le_div_iff₀ htwo_pos).mpr
      (Eq.subst
        (motive := fun t : ℝ => t ≤ s)
        (mul_comm (K / r) 2)
        htwice_le)

/-- The normalized factor appearing in sectorial exponential Stirling for
`Complex.Gamma`. -/
def Complex.normalizedGammaStirlingFactor (w : ℂ) : ℂ :=
  Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)

/-- The logarithmic denominator loss incurred when solving the normalized
Stirling factor for `log ‖Γ(w)‖`. -/
def Complex.normalizedGammaStirlingLogLoss (w : ℂ) : ℝ :=
  -w.re - Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖

/-- A norm bound for the normalized Stirling factor gives the corresponding
logarithmic bound. -/
theorem Complex.normalizedGammaStirlingFactor_log_le_of_norm_bound
    (B : ℝ)
    {w : ℂ}
    (hfactor_pos : 0 < ‖Complex.normalizedGammaStirlingFactor w‖)
    (hbound : ‖Complex.normalizedGammaStirlingFactor w‖ ≤ B) :
    Real.log ‖Complex.normalizedGammaStirlingFactor w‖ ≤ Real.log B :=
  Real.log_le_log hfactor_pos hbound

/-- `Gamma` is nonzero at nonzero points in the closed right half-plane.

The only zeros of mathlib's completed finite-valued `Gamma` are the
nonpositive integers; the closed right half-plane excludes the negative
integers, and the explicit nonzero hypothesis excludes `0`. -/
theorem Complex.Gamma_ne_zero_of_closedRightHalfPlaneSector_of_ne_zero
    {w : ℂ}
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_ne : w ≠ 0) :
    Complex.Gamma w ≠ 0 :=
  fun hzero =>
    match (Complex.Gamma_eq_zero_iff w).mp hzero with
    | ⟨0, hn⟩ => hw_ne (hn.trans (neg_zero : -((0 : ℂ)) = 0))
    | ⟨Nat.succ n, hn⟩ =>
        let hw_sector' : Complex.closedRightHalfPlaneSector (-(((Nat.succ n : ℕ) : ℂ))) :=
          Eq.subst hn hw_sector
        let hre_eq :
            (-(((Nat.succ n : ℕ) : ℂ))).re = -(((Nat.succ n : ℕ) : ℝ)) :=
          calc
            (-(((Nat.succ n : ℕ) : ℂ))).re =
                -(((Nat.succ n : ℕ) : ℂ).re) :=
              Complex.neg_re (((Nat.succ n : ℕ) : ℂ))
            _ = -(((Nat.succ n : ℕ) : ℝ)) :=
              congrArg Neg.neg (Complex.natCast_re (Nat.succ n))
        let hre_nonneg : (0 : ℝ) ≤ -(((Nat.succ n : ℕ) : ℝ)) :=
          Eq.subst
            (motive := fun x : ℝ => (0 : ℝ) ≤ x)
            hre_eq
            hw_sector'
        let hsucc_pos : (0 : ℝ) < ((Nat.succ n : ℕ) : ℝ) :=
          Nat.cast_pos.mpr (Nat.succ_pos n)
        let hneg_lt_zero : -(((Nat.succ n : ℕ) : ℝ)) < 0 :=
          neg_neg_of_pos hsucc_pos
        (not_lt_of_ge hre_nonneg) hneg_lt_zero

/-- Nonvanishing of the normalized Stirling factor in the closed right
half-plane away from the origin.

This is the exact nonvanishing input for the large-radius extraction: `Γ` has
no zeros off the nonpositive integers, `exp` never vanishes, and `w^α` is
nonzero for `w ≠ 0`. -/
theorem Complex.normalizedGammaStirlingFactor_ne_zero_of_closedRightHalfPlaneSector_largeRadius
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀)
    {w : ℂ}
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_radius : R₀ ≤ ‖w‖) :
    Complex.normalizedGammaStirlingFactor w ≠ 0 := by
  have hw_norm_pos : 0 < ‖w‖ :=
    lt_of_lt_of_le hR₀_pos hw_radius
  have hw_ne : w ≠ 0 :=
    norm_pos_iff.mp hw_norm_pos
  have hGamma_ne : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero_of_closedRightHalfPlaneSector_of_ne_zero
      hw_sector hw_ne
  have hexp_ne : Complex.exp w ≠ 0 :=
    Complex.exp_ne_zero w
  have hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0 := by
    intro hzero
    have hbase_zero : w = 0 :=
      ((cpow_eq_zero_iff w ((1 / 2 : ℂ) - w)).mp hzero).1
    exact hw_ne hbase_zero
  show
      Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w) ≠ 0
  exact mul_ne_zero (mul_ne_zero hGamma_ne hexp_ne) hcpow_ne

/-- Norm expansion for the normalized Gamma Stirling factor. -/
theorem Complex.normalizedGammaStirlingFactor_norm_eq
    (w : ℂ) :
    ‖Complex.normalizedGammaStirlingFactor w‖ =
      ‖Complex.Gamma w‖ * ‖Complex.exp w‖ *
        ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
  calc
    ‖Complex.normalizedGammaStirlingFactor w‖ =
        ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ := rfl
    _ = ‖Complex.Gamma w * Complex.exp w‖ *
          ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
      norm_mul (Complex.Gamma w * Complex.exp w)
        (w ^ ((1 / 2 : ℂ) - w))
    _ = ‖Complex.Gamma w‖ * ‖Complex.exp w‖ *
          ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
      exact congrArg
        (fun x : ℝ => x * ‖w ^ ((1 / 2 : ℂ) - w)‖)
        (norm_mul (Complex.Gamma w) (Complex.exp w))

/-- Log norm of the complex exponential is its real part. -/
theorem Complex.log_norm_exp_eq_re
    (w : ℂ) :
    Real.log ‖Complex.exp w‖ = w.re := by
  have hnorm_eq_abs :
      ‖Complex.exp w‖ = Complex.abs (Complex.exp w) :=
    norm_eq_abs (Complex.exp w)
  have habs_eq_exp :
      Complex.abs (Complex.exp w) = Real.exp w.re :=
    Complex.abs_exp w
  calc
    Real.log ‖Complex.exp w‖ =
        Real.log (Complex.abs (Complex.exp w)) :=
      congrArg Real.log hnorm_eq_abs
    _ = Real.log (Real.exp w.re) :=
      congrArg Real.log habs_eq_exp
    _ = w.re :=
      Real.log_exp w.re

/-- Norm of the complex exponential. -/
theorem Complex.norm_exp_eq_exp_re
    (w : ℂ) :
    ‖Complex.exp w‖ = Real.exp w.re := by
  have hnorm_eq_abs :
      ‖Complex.exp w‖ = Complex.abs (Complex.exp w) :=
    norm_eq_abs (Complex.exp w)
  calc
    ‖Complex.exp w‖ = Complex.abs (Complex.exp w) :=
      hnorm_eq_abs
    _ = Real.exp w.re :=
      Complex.abs_exp w

/-- Exact log expansion of the normalized Gamma Stirling factor. -/
theorem Complex.normalizedGammaStirlingFactor_log_eq
    (w : ℂ)
    (hGamma_ne : Complex.Gamma w ≠ 0)
    (hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0) :
    Real.log ‖Complex.normalizedGammaStirlingFactor w‖ =
      Real.log ‖Complex.Gamma w‖ + w.re +
        Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
  have hGamma_norm_ne : ‖Complex.Gamma w‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr hGamma_ne)
  have hexp_norm_ne : ‖Complex.exp w‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr (Complex.exp_ne_zero w))
  have hcpow_norm_ne : ‖w ^ ((1 / 2 : ℂ) - w)‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr hcpow_ne)
  have hGamma_exp_norm_ne :
      ‖Complex.Gamma w‖ * ‖Complex.exp w‖ ≠ 0 :=
    mul_ne_zero hGamma_norm_ne hexp_norm_ne
  calc
    Real.log ‖Complex.normalizedGammaStirlingFactor w‖ =
        Real.log
          (‖Complex.Gamma w‖ * ‖Complex.exp w‖ *
            ‖w ^ ((1 / 2 : ℂ) - w)‖) :=
      congrArg Real.log (Complex.normalizedGammaStirlingFactor_norm_eq w)
    _ =
        Real.log (‖Complex.Gamma w‖ * ‖Complex.exp w‖) +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
      Real.log_mul hGamma_exp_norm_ne hcpow_norm_ne
    _ =
        (Real.log ‖Complex.Gamma w‖ + Real.log ‖Complex.exp w‖) +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
      exact congrArg
        (fun x : ℝ => x + Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
        (Real.log_mul hGamma_norm_ne hexp_norm_ne)
    _ =
        (Real.log ‖Complex.Gamma w‖ + w.re) +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
      exact congrArg
        (fun x : ℝ => (Real.log ‖Complex.Gamma w‖ + x) +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
        (Complex.log_norm_exp_eq_re w)
    _ =
        Real.log ‖Complex.Gamma w‖ + w.re +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := rfl

/-- Real cancellation used when solving the normalized Stirling-factor logarithm
for the original Gamma logarithm. -/
theorem real_add_add_add_neg_add_neg_cancel
    (A B C : ℝ) :
    (A + B + C) + (-B + -C) = A := by
  have hC_cancel :
      C + (-B + -C) = -B := by
    calc
      C + (-B + -C) =
          C + (-C + -B) :=
        congrArg (fun x : ℝ => C + x) (add_comm (-B) (-C))
      _ = (C + -C) + -B :=
        (add_assoc C (-C) (-B)).symm
      _ = 0 + -B :=
        congrArg (fun x : ℝ => x + -B) (add_right_neg C)
      _ = -B :=
        zero_add (-B)
  calc
    (A + B + C) + (-B + -C) =
        (A + B) + (C + (-B + -C)) :=
      add_assoc (A + B) C (-B + -C)
    _ = (A + B) + -B :=
      congrArg (fun x : ℝ => (A + B) + x) hC_cancel
    _ = A + (B + -B) :=
      add_assoc A B (-B)
    _ = A + 0 :=
      congrArg (fun x : ℝ => A + x) (add_right_neg B)
    _ = A :=
      add_zero A

/-- Exact logarithmic extraction identity from the normalized Stirling factor. -/
theorem Complex.Gamma_log_norm_eq_normalizedGammaStirlingFactor_log_add_loss
    (w : ℂ)
    (hGamma_ne : Complex.Gamma w ≠ 0)
    (hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0) :
    Real.log ‖Complex.Gamma w‖ =
      Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
        Complex.normalizedGammaStirlingLogLoss w := by
  let A : ℝ := Real.log ‖Complex.Gamma w‖
  let B : ℝ := w.re
  let C : ℝ := Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖
  have hfactor :
      Real.log ‖Complex.normalizedGammaStirlingFactor w‖ =
        A + B + C :=
    Complex.normalizedGammaStirlingFactor_log_eq w hGamma_ne hcpow_ne
  have hloss :
      Complex.normalizedGammaStirlingLogLoss w = -B + -C := by
    exact sub_eq_add_neg (-w.re) (Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
  calc
    Real.log ‖Complex.Gamma w‖ = A := rfl
    _ = (A + B + C) + (-B + -C) :=
      (real_add_add_add_neg_add_neg_cancel A B C).symm
    _ =
        Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
          (-B + -C) :=
      congrArg (fun x : ℝ => x + (-B + -C)) hfactor.symm
    _ =
        Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
          Complex.normalizedGammaStirlingLogLoss w :=
      congrArg
        (fun x : ℝ =>
          Real.log ‖Complex.normalizedGammaStirlingFactor w‖ + x)
        hloss.symm

/-- Exact logarithmic extraction from the normalized Stirling factor.

After expanding
`‖Γ(w) exp(w) w^(1/2-w)‖`, this inequality solves for
`log ‖Γ(w)‖`.  The loss term is precisely the exponential denominator
`log ‖exp w‖ = w.re` and the principal-power denominator
`log ‖w^(1/2-w)‖`. -/
theorem Complex.Gamma_log_norm_le_normalizedGammaStirlingFactor_log_add_loss
    (w : ℂ)
    (hfactor_ne : Complex.normalizedGammaStirlingFactor w ≠ 0) :
    Real.log ‖Complex.Gamma w‖ ≤
      Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
        Complex.normalizedGammaStirlingLogLoss w := by
  have hGamma_ne : Complex.Gamma w ≠ 0 := by
    intro hGamma_zero
    have hfactor_zero :
        Complex.normalizedGammaStirlingFactor w = 0 := by
      calc
        Complex.normalizedGammaStirlingFactor w =
            Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w) := rfl
        _ = 0 * Complex.exp w * w ^ ((1 / 2 : ℂ) - w) :=
          congrArg
            (fun x : ℂ => x * Complex.exp w * w ^ ((1 / 2 : ℂ) - w))
            hGamma_zero
        _ = (0 : ℂ) * w ^ ((1 / 2 : ℂ) - w) := by
          exact congrArg
            (fun x : ℂ => x * w ^ ((1 / 2 : ℂ) - w))
            (zero_mul (Complex.exp w))
        _ = 0 :=
          zero_mul (w ^ ((1 / 2 : ℂ) - w))
    exact hfactor_ne hfactor_zero
  have hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0 := by
    intro hcpow_zero
    have hfactor_zero :
        Complex.normalizedGammaStirlingFactor w = 0 := by
      calc
        Complex.normalizedGammaStirlingFactor w =
            Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w) := rfl
        _ = Complex.Gamma w * Complex.exp w * 0 :=
          congrArg
            (fun x : ℂ => Complex.Gamma w * Complex.exp w * x)
            hcpow_zero
        _ = 0 :=
          mul_zero (Complex.Gamma w * Complex.exp w)
    exact hfactor_ne hfactor_zero
  exact le_of_eq
    (Complex.Gamma_log_norm_eq_normalizedGammaStirlingFactor_log_add_loss
      w hGamma_ne hcpow_ne)

/-- Solving the normalized Stirling factor for an upper bound on `‖Γ(w)‖`.

The denominator is `‖exp w‖ * ‖w^(1/2-w)‖`, positive away from `w = 0`. -/
theorem Complex.Gamma_norm_le_of_normalizedGammaStirlingFactor_norm_le
    (w : ℂ)
    (B : ℝ)
    (hbound : ‖Complex.normalizedGammaStirlingFactor w‖ ≤ B)
    (hden_pos :
      0 < ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) :
    ‖Complex.Gamma w‖ ≤
      B / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) := by
  have hnorm :
      ‖Complex.normalizedGammaStirlingFactor w‖ =
        ‖Complex.Gamma w‖ *
          (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) := by
    calc
      ‖Complex.normalizedGammaStirlingFactor w‖ =
          ‖Complex.Gamma w‖ * ‖Complex.exp w‖ *
            ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
        Complex.normalizedGammaStirlingFactor_norm_eq w
      _ =
          ‖Complex.Gamma w‖ *
            (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) :=
        mul_assoc ‖Complex.Gamma w‖ ‖Complex.exp w‖
          ‖w ^ ((1 / 2 : ℂ) - w)‖
  have hmul_le :
      ‖Complex.Gamma w‖ *
          (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) ≤ B :=
    Eq.subst
      (motive := fun t : ℝ => t ≤ B)
      hnorm
      hbound
  exact (le_div_iff₀ hden_pos).mpr hmul_le

/-- Solving the normalized Stirling factor for a lower bound on `‖Γ(w)‖`. -/
theorem Complex.Gamma_norm_ge_of_normalizedGammaStirlingFactor_norm_ge
    (w : ℂ)
    (b : ℝ)
    (hlower : b ≤ ‖Complex.normalizedGammaStirlingFactor w‖)
    (hden_pos :
      0 < ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) :
    b / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) ≤
      ‖Complex.Gamma w‖ := by
  have hnorm :
      ‖Complex.normalizedGammaStirlingFactor w‖ =
        ‖Complex.Gamma w‖ *
          (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) := by
    calc
      ‖Complex.normalizedGammaStirlingFactor w‖ =
          ‖Complex.Gamma w‖ * ‖Complex.exp w‖ *
            ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
        Complex.normalizedGammaStirlingFactor_norm_eq w
      _ =
          ‖Complex.Gamma w‖ *
            (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) :=
        mul_assoc ‖Complex.Gamma w‖ ‖Complex.exp w‖
          ‖w ^ ((1 / 2 : ℂ) - w)‖
  have hle_mul :
      b ≤ ‖Complex.Gamma w‖ *
          (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) :=
    le_trans hlower (le_of_eq hnorm)
  exact (div_le_iff₀ hden_pos).mpr hle_mul

/-- Constant logarithmic terms are absorbed by the large-radius log-linear
envelope on the closed right half-plane. -/
theorem Complex.constant_log_absorbed_by_largeRadius_logLinearEnvelope
    (B R₀ : ℝ)
    (hB_pos : 0 < B)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Real.log B ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
  let δ : ℝ := Real.log 2
  let C : ℝ := max (Real.log B / δ) 1
  let hδ_pos : 0 < δ :=
    Real.log_pos one_lt_two
  let hC_pos : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_right (Real.log B / δ) 1)
  ⟨C, hC_pos, fun w _hw_sector _hw_radius =>
    let htwo_norm_nonneg : 0 ≤ 2 * ‖w‖ :=
      mul_nonneg zero_le_two (norm_nonneg w)
    let hH_ge_one : (1 : ℝ) ≤ 1 + 2 * ‖w‖ :=
      le_add_of_nonneg_right htwo_norm_nonneg
    let harg_ge_two : (2 : ℝ) ≤ 2 + 2 * ‖w‖ :=
      le_add_of_nonneg_right htwo_norm_nonneg
    let hlog_ge_delta : δ ≤ Real.log (2 + 2 * ‖w‖) :=
      Real.log_le_log zero_lt_two harg_ge_two
    let hlog_nonneg : 0 ≤ Real.log (2 + 2 * ‖w‖) :=
      le_trans (le_of_lt hδ_pos) hlog_ge_delta
    let hdelta_le_envelope :
        δ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
      let hlog_le_envelope :
          Real.log (2 + 2 * ‖w‖) ≤
            (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
        calc
          Real.log (2 + 2 * ‖w‖) =
              1 * Real.log (2 + 2 * ‖w‖) :=
            (one_mul (Real.log (2 + 2 * ‖w‖))).symm
          _ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
            mul_le_mul_of_nonneg_right hH_ge_one hlog_nonneg
      le_trans hlog_ge_delta hlog_le_envelope
    let hlogB_div_le_C : Real.log B / δ ≤ C :=
      le_max_left (Real.log B / δ) 1
    let hlogB_le_Cδ : Real.log B ≤ C * δ :=
      (div_le_iff₀ hδ_pos).mp hlogB_div_le_C
    let hCδ_le_Cenv :
        C * δ ≤ C * ((1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :=
      mul_le_mul_of_nonneg_left hdelta_le_envelope (le_of_lt hC_pos)
    let hCenv_eq :
        C * ((1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) =
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
      mul_assoc C (1 + 2 * ‖w‖) (Real.log (2 + 2 * ‖w‖))
    le_trans hlogB_le_Cδ
      (le_trans hCδ_le_Cenv (le_of_eq hCenv_eq))⟩

/-- In the closed right half-plane, the real-part contribution to the
normalized Stirling loss is nonpositive, so the loss is bounded by the
principal-power logarithmic loss alone. -/
theorem Complex.normalizedGammaStirlingLogLoss_le_neg_cpow_log
    {w : ℂ}
    (hw_sector : Complex.closedRightHalfPlaneSector w) :
    Complex.normalizedGammaStirlingLogLoss w ≤
      -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
  have hneg_re_nonpos : -w.re ≤ 0 :=
    neg_nonpos.mpr hw_sector
  calc
    Complex.normalizedGammaStirlingLogLoss w =
        -w.re + -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
      exact sub_eq_add_neg (-w.re) (Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
    _ ≤ 0 + -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
      add_le_add_right hneg_re_nonpos
        (-Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
    _ = -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
      zero_add (-Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)

/-- Positive radius lower bound excludes the origin. -/
theorem Complex.ne_zero_of_pos_le_norm
    {R : ℝ}
    (hR_pos : 0 < R)
    {z : ℂ}
    (hz_radius : R ≤ ‖z‖) :
    z ≠ 0 :=
  norm_pos_iff.mp (lt_of_lt_of_le hR_pos hz_radius)

/-- The closed right half-plane is exactly the principal-argument sector
`|arg z| ≤ π / 2`. -/
theorem Complex.abs_arg_le_pi_div_two_of_closedRightHalfPlaneSector
    {z : ℂ}
    (hz_sector : Complex.closedRightHalfPlaneSector z) :
    |Complex.arg z| ≤ Real.pi / 2 :=
  Complex.abs_arg_le_pi_div_two_iff.mpr hz_sector

/-- Principal-branch absolute-value formula for complex powers in logarithmic
form. -/
theorem Complex.log_abs_cpow_eq_re_mul_log_abs_sub_arg_mul_im_of_ne_zero
    {z a : ℂ}
    (hz_ne : z ≠ 0) :
    Real.log (Complex.abs (z ^ a)) =
      a.re * Real.log (Complex.abs z) - Complex.arg z * a.im := by
  have hz_abs_pos : 0 < Complex.abs z :=
    Complex.abs.pos hz_ne
  have hpow_pos : 0 < Complex.abs z ^ a.re :=
    Real.rpow_pos_of_pos hz_abs_pos a.re
  have hexp_pos : 0 < Real.exp (Complex.arg z * a.im) :=
    Real.exp_pos (Complex.arg z * a.im)
  have hcpow_abs :
      Complex.abs (z ^ a) =
        Complex.abs z ^ a.re / Real.exp (Complex.arg z * a.im) :=
    Complex.abs_cpow_of_ne_zero hz_ne a
  calc
    Real.log (Complex.abs (z ^ a)) =
        Real.log
          (Complex.abs z ^ a.re / Real.exp (Complex.arg z * a.im)) :=
      congrArg Real.log hcpow_abs
    _ =
        Real.log (Complex.abs z ^ a.re) -
          Real.log (Real.exp (Complex.arg z * a.im)) :=
      Real.log_div (ne_of_gt hpow_pos) (ne_of_gt hexp_pos)
    _ =
        a.re * Real.log (Complex.abs z) -
          Real.log (Real.exp (Complex.arg z * a.im)) := by
      exact congrArg
        (fun x : ℝ => x - Real.log (Real.exp (Complex.arg z * a.im)))
        (Real.log_rpow hz_abs_pos a.re)
    _ =
        a.re * Real.log (Complex.abs z) - Complex.arg z * a.im := by
      exact congrArg
        (fun x : ℝ => a.re * Real.log (Complex.abs z) - x)
        (Real.log_exp (Complex.arg z * a.im))

/-- Principal-branch norm formula for complex powers. -/
theorem Complex.norm_cpow_eq_norm_rpow_div_exp_arg_mul_im_of_ne_zero
    {z a : ℂ}
    (hz_ne : z ≠ 0) :
    ‖z ^ a‖ =
      ‖z‖ ^ a.re / Real.exp (Complex.arg z * a.im) := by
  have hnorm_cpow_abs :
      ‖z ^ a‖ = Complex.abs (z ^ a) :=
    Complex.norm_eq_abs (z ^ a)
  have hnorm_z_abs :
      ‖z‖ = Complex.abs z :=
    Complex.norm_eq_abs z
  have habs_cpow :
      Complex.abs (z ^ a) =
        Complex.abs z ^ a.re / Real.exp (Complex.arg z * a.im) :=
    Complex.abs_cpow_of_ne_zero hz_ne a
  calc
    ‖z ^ a‖ = Complex.abs (z ^ a) :=
      hnorm_cpow_abs
    _ = Complex.abs z ^ a.re / Real.exp (Complex.arg z * a.im) :=
      habs_cpow
    _ = ‖z‖ ^ a.re / Real.exp (Complex.arg z * a.im) := by
      exact congrArg
        (fun r : ℝ => r ^ a.re / Real.exp (Complex.arg z * a.im))
        hnorm_z_abs.symm

/-- Principal-branch norm formula for complex powers in logarithmic form. -/
theorem Complex.log_norm_cpow_eq_re_mul_log_norm_sub_arg_mul_im_of_ne_zero
    {z a : ℂ}
    (hz_ne : z ≠ 0) :
    Real.log ‖z ^ a‖ =
      a.re * Real.log ‖z‖ - Complex.arg z * a.im := by
  have hnorm_cpow_abs :
      ‖z ^ a‖ = Complex.abs (z ^ a) :=
    Complex.norm_eq_abs (z ^ a)
  have hnorm_z_abs :
      ‖z‖ = Complex.abs z :=
    Complex.norm_eq_abs z
  calc
    Real.log ‖z ^ a‖ =
        Real.log (Complex.abs (z ^ a)) :=
      congrArg Real.log hnorm_cpow_abs
    _ =
        a.re * Real.log (Complex.abs z) - Complex.arg z * a.im :=
      Complex.log_abs_cpow_eq_re_mul_log_abs_sub_arg_mul_im_of_ne_zero
        hz_ne
    _ =
        a.re * Real.log ‖z‖ - Complex.arg z * a.im := by
      exact congrArg
        (fun x : ℝ => a.re * Real.log x - Complex.arg z * a.im)
        hnorm_z_abs.symm

/-- Real coordinate of the Stirling power exponent `(1/2) - w`. -/
theorem Complex.half_minus_self_re
    (w : ℂ) :
    ((1 / 2 : ℂ) - w).re = (1 / 2 : ℝ) - w.re := by
  calc
    ((1 / 2 : ℂ) - w).re =
        (1 / 2 : ℂ).re - w.re :=
      Complex.sub_re (1 / 2 : ℂ) w
    _ = (1 / 2 : ℝ) - w.re := by
      exact congrArg (fun x : ℝ => x - w.re) (Complex.ofReal_re (1 / 2))

/-- Imaginary coordinate of the Stirling power exponent `(1/2) - w`. -/
theorem Complex.half_minus_self_im
    (w : ℂ) :
    ((1 / 2 : ℂ) - w).im = -w.im := by
  calc
    ((1 / 2 : ℂ) - w).im =
        (1 / 2 : ℂ).im - w.im :=
      Complex.sub_im (1 / 2 : ℂ) w
    _ = 0 - w.im := by
      exact congrArg (fun x : ℝ => x - w.im) (Complex.ofReal_im (1 / 2))
    _ = -w.im :=
      zero_sub w.im

/-- Algebraic rearrangement of the cpow logarithmic formula for the Stirling
exponent. -/
theorem Complex.neg_log_norm_cpow_half_minus_self_eq_radiusArgumentLoss_of_log_norm_cpow
    {w : ℂ}
    (hw_ne : w ≠ 0)
    (hlog :
      Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ =
        ((1 / 2 : ℂ) - w).re * Real.log ‖w‖ -
          Complex.arg w * ((1 / 2 : ℂ) - w).im) :
    -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ =
      (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im := by
  have hre :
      ((1 / 2 : ℂ) - w).re = (1 / 2 : ℝ) - w.re :=
    Complex.half_minus_self_re w
  have him :
      ((1 / 2 : ℂ) - w).im = -w.im :=
    Complex.half_minus_self_im w
  have hcoordinate :
      ((1 / 2 : ℂ) - w).re * Real.log ‖w‖ -
          Complex.arg w * ((1 / 2 : ℂ) - w).im =
        ((1 / 2 : ℝ) - w.re) * Real.log ‖w‖ -
          Complex.arg w * (-w.im) := by
    exact congrArg₂
      (fun x y : ℝ => x * Real.log ‖w‖ - Complex.arg w * y)
      hre
      him
  have hneg_coordinate :
      -(((1 / 2 : ℝ) - w.re) * Real.log ‖w‖ -
          Complex.arg w * (-w.im)) =
        (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im := by
    calc
      -(((1 / 2 : ℝ) - w.re) * Real.log ‖w‖ -
          Complex.arg w * (-w.im)) =
          -(((1 / 2 : ℝ) - w.re) * Real.log ‖w‖) +
            Complex.arg w * (-w.im) := by
        exact neg_sub
          (((1 / 2 : ℝ) - w.re) * Real.log ‖w‖)
          (Complex.arg w * (-w.im))
      _ = (-((1 / 2 : ℝ) - w.re)) * Real.log ‖w‖ +
            Complex.arg w * (-w.im) := by
        exact congrArg
          (fun x : ℝ => x + Complex.arg w * (-w.im))
          (neg_mul ((1 / 2 : ℝ) - w.re) (Real.log ‖w‖))
      _ = (-(1 / 2 : ℝ) + w.re) * Real.log ‖w‖ +
            Complex.arg w * (-w.im) := by
        exact congrArg
          (fun x : ℝ => x * Real.log ‖w‖ + Complex.arg w * (-w.im))
          (neg_sub (1 / 2 : ℝ) w.re)
      _ = (w.re - 1 / 2) * Real.log ‖w‖ +
            Complex.arg w * (-w.im) := by
        exact congrArg
          (fun x : ℝ => x * Real.log ‖w‖ + Complex.arg w * (-w.im))
          (sub_eq_add_neg w.re (1 / 2)).symm
      _ = (w.re - 1 / 2) * Real.log ‖w‖ +
            (-(Complex.arg w * w.im)) := by
        exact congrArg
          (fun x : ℝ => (w.re - 1 / 2) * Real.log ‖w‖ + x)
          (mul_neg (Complex.arg w) w.im)
      _ = (w.re - 1 / 2) * Real.log ‖w‖ -
            Complex.arg w * w.im := by
        exact sub_eq_add_neg
          ((w.re - 1 / 2) * Real.log ‖w‖)
          (Complex.arg w * w.im)
  calc
    -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ =
        -(((1 / 2 : ℂ) - w).re * Real.log ‖w‖ -
          Complex.arg w * ((1 / 2 : ℂ) - w).im) :=
      congrArg Neg.neg hlog
    _ =
        -(((1 / 2 : ℝ) - w.re) * Real.log ‖w‖ -
          Complex.arg w * (-w.im)) :=
      congrArg Neg.neg hcoordinate
    _ = (w.re - 1 / 2) * Real.log ‖w‖ -
          Complex.arg w * w.im :=
      hneg_coordinate

/-- The exact branch-loss expression for `w^(1/2-w)`.  This is the
coordinate form of the principal logarithm contribution: the radius part is
`(Re w - 1/2) log ‖w‖`, and the angular part is `- arg(w) Im w`. -/
theorem Complex.neg_log_norm_cpow_half_minus_self_eq_radiusArgumentLoss
    {w : ℂ}
    (hw_ne : w ≠ 0) :
    -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ =
      (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im := by
  exact
    Complex.neg_log_norm_cpow_half_minus_self_eq_radiusArgumentLoss_of_log_norm_cpow
      hw_ne
      (Complex.log_norm_cpow_eq_re_mul_log_norm_sub_arg_mul_im_of_ne_zero
        hw_ne)

/-- The real coordinate is bounded by the complex norm. -/
theorem Complex.re_le_norm
    (w : ℂ) :
    w.re ≤ ‖w‖ := by
  have hre_abs_le_abs : |w.re| ≤ Complex.abs w :=
    Complex.abs_re_le_abs w
  have hnorm_eq_abs : ‖w‖ = Complex.abs w :=
    Complex.norm_eq_abs w
  have hre_abs_le_norm : |w.re| ≤ ‖w‖ :=
    Eq.subst
      (motive := fun x : ℝ => |w.re| ≤ x)
      hnorm_eq_abs.symm
      hre_abs_le_abs
  exact le_trans (le_abs_self w.re) hre_abs_le_norm

/-- The imaginary coordinate absolute value is bounded by the complex norm. -/
theorem Complex.abs_im_le_norm
    (w : ℂ) :
    |w.im| ≤ ‖w‖ := by
  have him_abs_le_abs : |w.im| ≤ Complex.abs w :=
    Complex.abs_im_le_abs w
  have hnorm_eq_abs : ‖w‖ = Complex.abs w :=
    Complex.norm_eq_abs w
  exact
    Eq.subst
      (motive := fun x : ℝ => |w.im| ≤ x)
      hnorm_eq_abs.symm
      him_abs_le_abs

/-- Fixed vertical points lie in the closed right half-plane exactly when their
fixed real part is nonnegative. -/
theorem Complex.fixedRealPartVerticalPoint_closedRightHalfPlaneSector
    {a b : ℝ}
    (ha : 0 ≤ a) :
    Complex.closedRightHalfPlaneSector
      (Complex.fixedRealPartVerticalPoint a b) := by
  exact
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (Complex.fixedRealPartVerticalPoint_re a b).symm
      ha

/-- The imaginary height is bounded by the complex norm of a fixed vertical
point. -/
theorem Complex.fixedRealPartVerticalPoint_abs_im_le_norm
    (a b : ℝ) :
    ‖b‖ ≤ ‖Complex.fixedRealPartVerticalPoint a b‖ := by
  have him :
      (Complex.fixedRealPartVerticalPoint a b).im = b :=
    Complex.fixedRealPartVerticalPoint_im a b
  have hbasic :
      |(Complex.fixedRealPartVerticalPoint a b).im| ≤
        ‖Complex.fixedRealPartVerticalPoint a b‖ :=
    Complex.abs_im_le_norm (Complex.fixedRealPartVerticalPoint a b)
  have hnorm_eq_abs : ‖b‖ = |b| :=
    Real.norm_eq_abs b
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖Complex.fixedRealPartVerticalPoint a b‖)
      hnorm_eq_abs.symm
      (Eq.subst
        (motive := fun x : ℝ =>
          |x| ≤ ‖Complex.fixedRealPartVerticalPoint a b‖)
        him
        hbasic)

/-- A large imaginary height forces a large complex radius on a fixed vertical
line. -/
theorem Complex.fixedRealPartVerticalPoint_radius_ge_of_height_ge
    {a b H : ℝ}
    (hH : H ≤ ‖b‖) :
    H ≤ ‖Complex.fixedRealPartVerticalPoint a b‖ :=
  le_trans hH (Complex.fixedRealPartVerticalPoint_abs_im_le_norm a b)

/-- If `H` dominates a sectorial radius cutoff, then a height cutoff by `H`
dominates the corresponding complex radius cutoff. -/
theorem Complex.fixedRealPartVerticalPoint_sectorialRadius_ge_of_height_ge
    {a b H R : ℝ}
    (hR_le_H : R ≤ H)
    (hH : H ≤ ‖b‖) :
    R ≤ ‖Complex.fixedRealPartVerticalPoint a b‖ :=
  le_trans hR_le_H
    (Complex.fixedRealPartVerticalPoint_radius_ge_of_height_ge hH)

/-- Shifting a fixed vertical point by a natural number shifts only its real
coordinate. -/
theorem Complex.fixedRealPartVerticalPoint_natShift_re
    (x y : ℝ)
    (N : ℕ) :
    (Complex.fixedRealPartVerticalPoint (x + N) y).re =
      x + (N : ℝ) := by
  exact Complex.fixedRealPartVerticalPoint_re (x + N) y

/-- Shifting a fixed vertical point by a natural number preserves its imaginary
coordinate. -/
theorem Complex.fixedRealPartVerticalPoint_natShift_im
    (x y : ℝ)
    (N : ℕ) :
    (Complex.fixedRealPartVerticalPoint (x + N) y).im = y := by
  exact Complex.fixedRealPartVerticalPoint_im (x + N) y

/-- A natural right shift moves the whole real strip into the closed right
half-plane. -/
theorem Complex.fixedRealPartVerticalPoint_natShift_closedRightHalfPlaneSector
    {A x y : ℝ}
    {N : ℕ}
    (hA : -A ≤ (N : ℝ))
    (hx : A ≤ x) :
    Complex.closedRightHalfPlaneSector
      (Complex.fixedRealPartVerticalPoint (x + N) y) := by
  have hnonneg : 0 ≤ x + (N : ℝ) := by
    have hneg_x_le_N : -x ≤ (N : ℝ) :=
      le_trans (neg_le_neg hx) hA
    exact neg_le.mp hneg_x_le_N
  exact
    Complex.fixedRealPartVerticalPoint_closedRightHalfPlaneSector hnonneg

/-- The shifted vertical point has radius bounded below by the same height. -/
theorem Complex.fixedRealPartVerticalPoint_natShift_radius_ge_of_height_ge
    {x y H : ℝ}
    {N : ℕ}
    (hH : H ≤ ‖y‖) :
    H ≤ ‖Complex.fixedRealPartVerticalPoint (x + N) y‖ :=
  Complex.fixedRealPartVerticalPoint_radius_ge_of_height_ge hH

/-- Bounded real part in a strip remains bounded after a fixed natural shift. -/
theorem real_natShift_mem_strip_of_mem_strip
    {A B x : ℝ}
    (N : ℕ)
    (hxA : A ≤ x)
    (hxB : x ≤ B) :
    A + (N : ℝ) ≤ x + (N : ℝ) ∧
      x + (N : ℝ) ≤ B + (N : ℝ) :=
  ⟨add_le_add_right hxA (N : ℝ),
    add_le_add_right hxB (N : ℝ)⟩

/-- Deterministic right shift for a vertical strip.  It is the least natural
integer produced by the floor API which is at least `max 0 (-A)`, hence it
moves the strip lower edge `A` into the closed right half-plane. -/
def Complex.verticalStripRightShift (A : ℝ) : ℕ :=
  Nat.ceil (max 0 (-A))

/-- The deterministic strip shift dominates the negative lower endpoint. -/
theorem Complex.neg_lower_le_verticalStripRightShift
    (A : ℝ) :
    -A ≤ (Complex.verticalStripRightShift A : ℝ) :=
  let hmax : -A ≤ max 0 (-A) :=
    le_max_right 0 (-A)
  let hceil : max 0 (-A) ≤ (Complex.verticalStripRightShift A : ℝ) :=
    Nat.le_ceil (max 0 (-A))
  le_trans hmax hceil

/-- The deterministic strip shift is nonnegative as a real number. -/
theorem Complex.verticalStripRightShift_nonneg
    (A : ℝ) :
    (0 : ℝ) ≤ (Complex.verticalStripRightShift A : ℝ) :=
  Nat.cast_nonneg (Complex.verticalStripRightShift A)

/-- The deterministic shift moves every point in the strip into the closed
right half-plane. -/
theorem Complex.fixedRealPartVerticalPoint_verticalStripRightShift_closedRightHalfPlaneSector
    {A x y : ℝ}
    (hx : A ≤ x) :
    Complex.closedRightHalfPlaneSector
      (Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripRightShift A) y) :=
  Complex.fixedRealPartVerticalPoint_natShift_closedRightHalfPlaneSector
    (Complex.neg_lower_le_verticalStripRightShift A) hx

/-- The deterministic shift preserves the large-height-to-large-radius lower
bound. -/
theorem Complex.fixedRealPartVerticalPoint_verticalStripRightShift_radius_ge_of_height_ge
    {A x y H : ℝ}
    (hH : H ≤ ‖y‖) :
    H ≤
      ‖Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripRightShift A) y‖ :=
  Complex.fixedRealPartVerticalPoint_natShift_radius_ge_of_height_ge hH

/-- A positive lower radius cutoff makes the logarithmic envelope positive. -/
theorem real_largeRadius_log_envelope_pos
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    0 < Real.log (2 + 2 * r) := by
  have hr_pos : 0 < r :=
    lt_of_lt_of_le hR₀_pos hr
  have htwo_r_pos : 0 < 2 * r :=
    mul_pos two_pos hr_pos
  have hone_lt_arg : (1 : ℝ) < 2 + 2 * r := by
    calc
      (1 : ℝ) < 2 := one_lt_two
      _ ≤ 2 + 2 * r := le_add_of_nonneg_right (le_of_lt htwo_r_pos)
  exact Real.log_pos hone_lt_arg

/-- The large-radius log envelope is nonnegative. -/
theorem real_largeRadius_log_envelope_nonneg
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    0 ≤ Real.log (2 + 2 * r) :=
  le_of_lt (real_largeRadius_log_envelope_pos R₀ r hR₀_pos hr)

/-- On a positive large-radius region, the log envelope is at least `log 2`. -/
theorem real_log_two_le_largeRadius_log_envelope
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    Real.log 2 ≤ Real.log (2 + 2 * r) := by
  have hr_nonneg : 0 ≤ r :=
    le_of_lt (lt_of_lt_of_le hR₀_pos hr)
  have harg_le : (2 : ℝ) ≤ 2 + 2 * r :=
    le_add_of_nonneg_right (mul_nonneg zero_le_two hr_nonneg)
  exact Real.log_le_log zero_lt_two harg_le

/-- Positive lower radius cutoff gives nonnegative radius. -/
theorem real_nonneg_of_largeRadius
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    0 ≤ r :=
  le_of_lt (lt_of_lt_of_le hR₀_pos hr)

/-- The linear factor `r + 1/2` is dominated by the standard height factor
`1 + 2r` on nonnegative radii. -/
theorem real_radius_add_half_le_one_add_two_mul
    (r : ℝ)
    (hr_nonneg : 0 ≤ r) :
    r + 1 / 2 ≤ 1 + 2 * r := by
  have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 :=
    one_half_le_one
  have hr_le_two_r : r ≤ 2 * r := by
    calc
      r = 1 * r := (one_mul r).symm
      _ ≤ 2 * r := mul_le_mul_of_nonneg_right one_le_two hr_nonneg
  calc
    r + 1 / 2 ≤ 2 * r + 1 :=
      add_le_add hr_le_two_r hhalf_le_one
    _ = 1 + 2 * r :=
      add_comm (2 * r) 1

/-- The radius itself is dominated by the standard height factor. -/
theorem real_radius_le_one_add_two_mul
    (r : ℝ)
    (hr_nonneg : 0 ≤ r) :
    r ≤ 1 + 2 * r := by
  calc
    r ≤ 2 * r :=
      calc
        r = 1 * r := (one_mul r).symm
        _ ≤ 2 * r := mul_le_mul_of_nonneg_right one_le_two hr_nonneg
    _ ≤ 1 + 2 * r :=
      le_add_of_nonneg_left zero_le_one

/-- The angular linear term is absorbed by the standard log-linear envelope on
any positive large-radius region. -/
theorem real_pi_radius_absorbed_by_logLinearEnvelope_uniform
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ r : ℝ,
        R₀ ≤ r →
        (Real.pi / 2) * r ≤
          C * (1 + 2 * r) * Real.log (2 + 2 * r) :=
  let C : ℝ := (Real.pi / 2) / Real.log 2
  let hlog_two_pos : 0 < Real.log 2 :=
    Real.log_pos one_lt_two
  let hpi_half_pos : 0 < Real.pi / 2 :=
    div_pos Real.pi_pos two_pos
  let hC_pos : 0 < C :=
    div_pos hpi_half_pos hlog_two_pos
  ⟨C, hC_pos, fun r hr =>
    let hr_nonneg : 0 ≤ r :=
      real_nonneg_of_largeRadius R₀ r hR₀_pos hr
    let hH_nonneg : 0 ≤ 1 + 2 * r :=
      add_nonneg zero_le_one (mul_nonneg zero_le_two hr_nonneg)
    let hr_le_H : r ≤ 1 + 2 * r :=
      real_radius_le_one_add_two_mul r hr_nonneg
    let hL_lower : Real.log 2 ≤ Real.log (2 + 2 * r) :=
      real_log_two_le_largeRadius_log_envelope R₀ r hR₀_pos hr
    let hC_log_two : C * Real.log 2 = Real.pi / 2 :=
      calc
        C * Real.log 2 =
            ((Real.pi / 2) / Real.log 2) * Real.log 2 := rfl
        _ = Real.pi / 2 :=
          div_mul_cancel₀ (Real.pi / 2) (ne_of_gt hlog_two_pos)
    let hpi_half_le_CL : Real.pi / 2 ≤ C * Real.log (2 + 2 * r) :=
      let hmul : C * Real.log 2 ≤ C * Real.log (2 + 2 * r) :=
        mul_le_mul_of_nonneg_left hL_lower (le_of_lt hC_pos)
      le_trans (le_of_eq hC_log_two.symm) hmul
    let hleft_to_H :
        (Real.pi / 2) * r ≤ (Real.pi / 2) * (1 + 2 * r) :=
      mul_le_mul_of_nonneg_left hr_le_H (le_of_lt hpi_half_pos)
    let hH_scale :
        (Real.pi / 2) * (1 + 2 * r) ≤
          (C * Real.log (2 + 2 * r)) * (1 + 2 * r) :=
      mul_le_mul_of_nonneg_right hpi_half_le_CL hH_nonneg
    let htarget_eq :
        (C * Real.log (2 + 2 * r)) * (1 + 2 * r) =
          C * (1 + 2 * r) * Real.log (2 + 2 * r) :=
      calc
        (C * Real.log (2 + 2 * r)) * (1 + 2 * r) =
            C * (Real.log (2 + 2 * r) * (1 + 2 * r)) :=
          (mul_assoc C (Real.log (2 + 2 * r)) (1 + 2 * r)).symm
        _ = C * ((1 + 2 * r) * Real.log (2 + 2 * r)) :=
          congrArg
            (fun x : ℝ => C * x)
            (mul_comm (Real.log (2 + 2 * r)) (1 + 2 * r))
        _ = C * (1 + 2 * r) * Real.log (2 + 2 * r) :=
          mul_assoc C (1 + 2 * r) (Real.log (2 + 2 * r))
    le_trans hleft_to_H
      (le_trans hH_scale (le_of_eq htarget_eq))⟩

/-- Uniform version of the real logarithmic envelope on a large-radius region. -/
theorem real_abs_log_le_largeRadius_log_envelope_uniform
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ r : ℝ,
        R₀ ≤ r →
        ‖Real.log r‖ ≤ C * Real.log (2 + 2 * r) :=
  let C : ℝ := max 1 (R₀⁻¹ / Real.log 2)
  let hlog_two_pos : 0 < Real.log 2 :=
    Real.log_pos one_lt_two
  let hR₀_inv_nonneg : 0 ≤ R₀⁻¹ :=
    inv_nonneg.mpr (le_of_lt hR₀_pos)
  let hC_pos : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 (R₀⁻¹ / Real.log 2))
  ⟨C, hC_pos, fun r hr =>
    let hr_pos : 0 < r :=
      lt_of_lt_of_le hR₀_pos hr
    let hr_nonneg : 0 ≤ r :=
      le_of_lt hr_pos
    let hL_nonneg : 0 ≤ Real.log (2 + 2 * r) :=
      real_largeRadius_log_envelope_nonneg R₀ r hR₀_pos hr
    let hL_lower : Real.log 2 ≤ Real.log (2 + 2 * r) :=
      real_log_two_le_largeRadius_log_envelope R₀ r hR₀_pos hr
    if hone_le_r : (1 : ℝ) ≤ r then
      let hlog_nonneg : 0 ≤ Real.log r :=
        Real.log_nonneg hone_le_r
      let hnorm_log : ‖Real.log r‖ = Real.log r :=
        Real.norm_of_nonneg hlog_nonneg
      let hr_le_arg : r ≤ 2 + 2 * r :=
        calc
          r ≤ 2 * r :=
            calc
              r = 1 * r := (one_mul r).symm
              _ ≤ 2 * r := mul_le_mul_of_nonneg_right one_le_two hr_nonneg
          _ ≤ 2 + 2 * r :=
            le_add_of_nonneg_left zero_le_two
      let hlog_le_L : Real.log r ≤ Real.log (2 + 2 * r) :=
        Real.log_le_log hr_pos hr_le_arg
      let hC_ge_one : (1 : ℝ) ≤ C :=
        le_max_left 1 (R₀⁻¹ / Real.log 2)
      let hL_le_CL : Real.log (2 + 2 * r) ≤ C * Real.log (2 + 2 * r) :=
        calc
          Real.log (2 + 2 * r) =
              1 * Real.log (2 + 2 * r) :=
            (one_mul (Real.log (2 + 2 * r))).symm
          _ ≤ C * Real.log (2 + 2 * r) :=
            mul_le_mul_of_nonneg_right hC_ge_one hL_nonneg
      le_trans (le_of_eq hnorm_log)
        (le_trans hlog_le_L hL_le_CL)
    else
      let hr_le_one : r ≤ 1 :=
        le_of_not_ge hone_le_r
      let hlog_nonpos : Real.log r ≤ 0 :=
        (Real.log_nonpos_iff hr_pos).mpr hr_le_one
      let hnorm_log : ‖Real.log r‖ = -Real.log r :=
        Real.norm_of_nonpos hlog_nonpos
      let hneg_log_le_inv : -Real.log r ≤ r⁻¹ :=
        neg_le.mp (Real.neg_inv_le_log hr_nonneg)
      let hinv_le_R₀_inv : r⁻¹ ≤ R₀⁻¹ :=
        one_div_le_one_div_of_le hR₀_pos hr
      let hsmall : ‖Real.log r‖ ≤ R₀⁻¹ :=
        le_trans (le_of_eq hnorm_log) (le_trans hneg_log_le_inv hinv_le_R₀_inv)
      let hratio_le_C : R₀⁻¹ / Real.log 2 ≤ C :=
        le_max_right 1 (R₀⁻¹ / Real.log 2)
      let hR₀_inv_le_ratio_L :
          R₀⁻¹ ≤ (R₀⁻¹ / Real.log 2) * Real.log (2 + 2 * r) :=
        let hR₀_inv_div_mul :
            R₀⁻¹ = (R₀⁻¹ / Real.log 2) * Real.log 2 :=
          (div_mul_cancel₀ R₀⁻¹ (ne_of_gt hlog_two_pos)).symm
        let hmul :
            (R₀⁻¹ / Real.log 2) * Real.log 2 ≤
              (R₀⁻¹ / Real.log 2) * Real.log (2 + 2 * r) :=
          mul_le_mul_of_nonneg_left hL_lower
            (div_nonneg hR₀_inv_nonneg (le_of_lt hlog_two_pos))
        le_trans (le_of_eq hR₀_inv_div_mul) hmul
      let hratio_L_le_CL :
          (R₀⁻¹ / Real.log 2) * Real.log (2 + 2 * r) ≤
            C * Real.log (2 + 2 * r) :=
        mul_le_mul_of_nonneg_right hratio_le_C hL_nonneg
      le_trans hsmall
        (le_trans hR₀_inv_le_ratio_L hratio_L_le_CL)⟩

/-- Pure real logarithmic envelope for a radius bounded below away from zero. -/
theorem real_abs_log_le_largeRadius_log_envelope
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    ∃ C : ℝ,
      0 < C ∧
      ‖Real.log r‖ ≤ C * Real.log (2 + 2 * r) :=
  let ⟨C, hC_pos, hC⟩ := real_abs_log_le_largeRadius_log_envelope_uniform R₀ hR₀_pos
  ⟨C, hC_pos, hC r hr⟩

/-- The logarithm of the radius is absorbed by the logarithmic envelope on any
large-radius region bounded away from zero. -/
theorem Complex.log_norm_le_log_envelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        R₀ ≤ ‖w‖ →
        ‖Real.log ‖w‖‖ ≤ C * Real.log (2 + 2 * ‖w‖) := by
  exact real_abs_log_le_largeRadius_log_envelope_uniform R₀ hR₀_pos

/-- If `0 ≤ x ≤ r`, then the shifted coordinate `x - 1/2` is bounded by
`r + 1/2` in absolute value. -/
theorem real_abs_sub_half_le_radius_add_half
    (x r : ℝ)
    (hx_nonneg : 0 ≤ x)
    (hx_le_r : x ≤ r) :
    |x - 1 / 2| ≤ r + 1 / 2 := by
  have hr_nonneg : 0 ≤ r :=
    le_trans hx_nonneg hx_le_r
  have hneg_r_le_x : -r ≤ x :=
    le_trans (neg_nonpos.mpr hr_nonneg) hx_nonneg
  have hneg_half_le_half : -(1 / 2 : ℝ) ≤ 1 / 2 :=
    neg_le_self (le_of_lt one_half_pos)
  have hlower : -(r + 1 / 2) ≤ x - 1 / 2 := by
    calc
      -(r + 1 / 2) = -r + -(1 / 2 : ℝ) :=
        neg_add r (1 / 2)
      _ ≤ x + -(1 / 2 : ℝ) :=
        add_le_add_right hneg_r_le_x (-(1 / 2 : ℝ))
      _ = x - 1 / 2 :=
        (sub_eq_add_neg x (1 / 2)).symm
  have hupper : x - 1 / 2 ≤ r + 1 / 2 := by
    calc
      x - 1 / 2 ≤ r - 1 / 2 :=
        sub_le_sub_right hx_le_r (1 / 2)
      _ = r + -(1 / 2 : ℝ) :=
        sub_eq_add_neg r (1 / 2)
      _ ≤ r + 1 / 2 :=
        add_le_add_left hneg_half_le_half r
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Radius part of the branch loss is bounded by the norm-log majorant. -/
theorem real_radiusTerm_le_norm_log_majorant
    (x r : ℝ)
    (hx_nonneg : 0 ≤ x)
    (hx_le_r : x ≤ r) :
    (x - 1 / 2) * Real.log r ≤
      (r + 1 / 2) * ‖Real.log r‖ := by
  have hterm_le_abs :
      (x - 1 / 2) * Real.log r ≤
        |(x - 1 / 2) * Real.log r| :=
    le_abs_self ((x - 1 / 2) * Real.log r)
  have habs_mul :
      |(x - 1 / 2) * Real.log r| =
        |x - 1 / 2| * |Real.log r| :=
    abs_mul (x - 1 / 2) (Real.log r)
  have habs_log_eq_norm :
      |Real.log r| = ‖Real.log r‖ :=
    (Real.norm_eq_abs (Real.log r)).symm
  have hshift :
      |x - 1 / 2| ≤ r + 1 / 2 :=
    real_abs_sub_half_le_radius_add_half x r hx_nonneg hx_le_r
  have hmajor :
      |x - 1 / 2| * |Real.log r| ≤
        (r + 1 / 2) * ‖Real.log r‖ := by
    have hlog_nonneg : 0 ≤ ‖Real.log r‖ :=
      norm_nonneg (Real.log r)
    have hmul :
        |x - 1 / 2| * ‖Real.log r‖ ≤
          (r + 1 / 2) * ‖Real.log r‖ :=
      mul_le_mul_of_nonneg_right hshift hlog_nonneg
    exact
      Eq.subst
        (motive := fun y : ℝ =>
          |x - 1 / 2| * y ≤ (r + 1 / 2) * ‖Real.log r‖)
        habs_log_eq_norm.symm
        hmul
  exact le_trans hterm_le_abs
    (le_trans (le_of_eq habs_mul) hmajor)

/-- Angular part of the branch loss is bounded by the sectorial angle majorant. -/
theorem real_argumentTerm_le_sectorial_majorant
    (θ y r : ℝ)
    (hy_abs_le_r : |y| ≤ r)
    (hθ_abs_le : |θ| ≤ Real.pi / 2) :
    -θ * y ≤ (Real.pi / 2) * r := by
  have hneg_product_le_abs :
      -θ * y ≤ |θ * y| := by
    calc
      -θ * y = -(θ * y) :=
        (neg_mul θ y).symm
      _ ≤ |θ * y| :=
        neg_le_abs (θ * y)
  have habs_product :
      |θ * y| = |θ| * |y| :=
    abs_mul θ y
  have hpi_half_nonneg : 0 ≤ Real.pi / 2 :=
    le_of_lt (div_pos Real.pi_pos two_pos)
  have habs_product_le :
      |θ| * |y| ≤ (Real.pi / 2) * r :=
    mul_le_mul hθ_abs_le hy_abs_le_r (abs_nonneg y) hpi_half_nonneg
  exact le_trans hneg_product_le_abs
    (le_trans (le_of_eq habs_product) habs_product_le)

/-- Pure real radius/argument majorization after replacing coordinates by norm
bounds and the argument by its sectorial bound. -/
theorem real_radiusArgumentLoss_le_norm_log_majorant
    (x y θ r : ℝ)
    (hx_nonneg : 0 ≤ x)
    (hx_le_r : x ≤ r)
    (hy_abs_le_r : |y| ≤ r)
    (hθ_abs_le : |θ| ≤ Real.pi / 2) :
    (x - 1 / 2) * Real.log r - θ * y ≤
      (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r := by
  have hradius :
      (x - 1 / 2) * Real.log r ≤
        (r + 1 / 2) * ‖Real.log r‖ :=
    real_radiusTerm_le_norm_log_majorant x r hx_nonneg hx_le_r
  have hangle :
      -θ * y ≤ (Real.pi / 2) * r :=
    real_argumentTerm_le_sectorial_majorant θ y r hy_abs_le_r hθ_abs_le
  have hleft_eq :
      (x - 1 / 2) * Real.log r - θ * y =
        (x - 1 / 2) * Real.log r + (-θ * y) := by
    exact sub_eq_add_neg ((x - 1 / 2) * Real.log r) (θ * y)
  have hsum :
      (x - 1 / 2) * Real.log r + (-θ * y) ≤
        (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r :=
    add_le_add hradius hangle
  exact le_trans (le_of_eq hleft_eq) hsum

/-- Coordinate domination of the Stirling radius/argument loss by the elementary
norm majorant. -/
theorem Complex.radiusArgumentLoss_le_norm_log_majorant
    (w : ℂ)
    (hw_sector : Complex.closedRightHalfPlaneSector w) :
    (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im ≤
      (‖w‖ + 1 / 2) * ‖Real.log ‖w‖‖ + (Real.pi / 2) * ‖w‖ := by
  exact
    real_radiusArgumentLoss_le_norm_log_majorant
      w.re w.im (Complex.arg w) ‖w‖
      hw_sector
      (Complex.re_le_norm w)
      (Complex.abs_im_le_norm w)
      (Complex.abs_arg_le_pi_div_two_of_closedRightHalfPlaneSector hw_sector)

/-- Uniform pure real absorption of the norm-log majorant into the standard
log-linear envelope on a large-radius region. -/
theorem real_linear_log_absorption_uniform
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ r : ℝ,
        R₀ ≤ r →
        (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r ≤
          C * (1 + 2 * r) * Real.log (2 + 2 * r) :=
  let ⟨Clog, hClog_pos, hlog⟩ := real_abs_log_le_largeRadius_log_envelope_uniform R₀ hR₀_pos
  let ⟨Cpi, hCpi_pos, hpi⟩ := real_pi_radius_absorbed_by_logLinearEnvelope_uniform R₀ hR₀_pos
  ⟨Clog + Cpi, add_pos hClog_pos hCpi_pos, fun r hr =>
    let hr_nonneg : 0 ≤ r :=
      real_nonneg_of_largeRadius R₀ r hR₀_pos hr
    let hH_nonneg : 0 ≤ 1 + 2 * r :=
      add_nonneg zero_le_one (mul_nonneg zero_le_two hr_nonneg)
    let hL_nonneg : 0 ≤ Real.log (2 + 2 * r) :=
      real_largeRadius_log_envelope_nonneg R₀ r hR₀_pos hr
    let hfactor_nonneg : 0 ≤ r + 1 / 2 :=
      add_nonneg hr_nonneg (le_of_lt one_half_pos)
    let hfactor_le_H : r + 1 / 2 ≤ 1 + 2 * r :=
      real_radius_add_half_le_one_add_two_mul r hr_nonneg
    let hlog_bound : ‖Real.log r‖ ≤ Clog * Real.log (2 + 2 * r) :=
      hlog r hr
    let hfirst_step :
        (r + 1 / 2) * ‖Real.log r‖ ≤
          (r + 1 / 2) * (Clog * Real.log (2 + 2 * r)) :=
      mul_le_mul_of_nonneg_left hlog_bound hfactor_nonneg
    let hClogL_nonneg : 0 ≤ Clog * Real.log (2 + 2 * r) :=
      mul_nonneg (le_of_lt hClog_pos) hL_nonneg
    let hfirst_factor :
        (r + 1 / 2) * (Clog * Real.log (2 + 2 * r)) ≤
          (1 + 2 * r) * (Clog * Real.log (2 + 2 * r)) :=
      mul_le_mul_of_nonneg_right hfactor_le_H hClogL_nonneg
    let hfirst_assoc :
        (1 + 2 * r) * (Clog * Real.log (2 + 2 * r)) =
          Clog * (1 + 2 * r) * Real.log (2 + 2 * r) :=
      calc
        (1 + 2 * r) * (Clog * Real.log (2 + 2 * r)) =
            ((1 + 2 * r) * Clog) * Real.log (2 + 2 * r) :=
          mul_assoc (1 + 2 * r) Clog (Real.log (2 + 2 * r))
        _ = (Clog * (1 + 2 * r)) * Real.log (2 + 2 * r) :=
          congrArg
            (fun x : ℝ => x * Real.log (2 + 2 * r))
            (mul_comm (1 + 2 * r) Clog)
        _ = Clog * (1 + 2 * r) * Real.log (2 + 2 * r) := rfl
    let hfirst :
        (r + 1 / 2) * ‖Real.log r‖ ≤
          Clog * (1 + 2 * r) * Real.log (2 + 2 * r) :=
      le_trans hfirst_step
        (le_trans hfirst_factor (le_of_eq hfirst_assoc))
    let hsecond :
        (Real.pi / 2) * r ≤
          Cpi * (1 + 2 * r) * Real.log (2 + 2 * r) :=
      hpi r hr
    let hsum :
        (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r ≤
          Clog * (1 + 2 * r) * Real.log (2 + 2 * r) +
            Cpi * (1 + 2 * r) * Real.log (2 + 2 * r) :=
      add_le_add hfirst hsecond
    let hcombine :
        Clog * (1 + 2 * r) * Real.log (2 + 2 * r) +
            Cpi * (1 + 2 * r) * Real.log (2 + 2 * r) =
          (Clog + Cpi) * (1 + 2 * r) * Real.log (2 + 2 * r) :=
      logLinearEnvelope_add_constants
        Clog Cpi (1 + 2 * r) (Real.log (2 + 2 * r))
    le_trans hsum (le_of_eq hcombine)⟩

/-- Pure real absorption of the norm-log majorant into the standard log-linear
envelope, using a lower radius cutoff. -/
theorem real_linear_log_absorption
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    ∃ C : ℝ,
      0 < C ∧
      (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r ≤
        C * (1 + 2 * r) * Real.log (2 + 2 * r) :=
  let ⟨C, hC_pos, hC⟩ := real_linear_log_absorption_uniform R₀ hR₀_pos
  ⟨C, hC_pos, hC r hr⟩

/-- The elementary norm-log majorant is absorbed by the standard log-linear
envelope on every large-radius region. -/
theorem Complex.linear_log_absorption
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        R₀ ≤ ‖w‖ →
        (‖w‖ + 1 / 2) * ‖Real.log ‖w‖‖ + (Real.pi / 2) * ‖w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact real_linear_log_absorption_uniform R₀ hR₀_pos

/-- Pure real domination of the radius/argument loss by the standard
log-linear envelope on the closed right half-plane.

This is now the deepest real-inequality sink in the normalized Stirling
extraction.  It combines `0 ≤ Re w`, `|arg w| ≤ π/2`, `|Re w|, |Im w| ≤ ‖w‖`,
and lower-radius control to absorb the possible small-radius logarithmic term
into a constant multiple of `(1 + 2 ‖w‖) log (2 + 2 ‖w‖)`. -/
theorem Complex.radiusArgumentLoss_absorbed_by_largeRadius_logLinearEnvelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
  let ⟨C, hC_pos, hlinear⟩ := Complex.linear_log_absorption R₀ hR₀_pos
  ⟨C, hC_pos, fun w hw_sector hw_radius =>
    le_trans
      (Complex.radiusArgumentLoss_le_norm_log_majorant w hw_sector)
      (hlinear w hw_radius)⟩

/-- The branch-loss radius/argument expression is absorbed by the standard
large-radius log-linear envelope on the closed right half-plane. -/
theorem Complex.cpow_half_minus_self_radiusArgumentLoss_absorbed_by_largeRadius_logLinearEnvelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact
    Complex.radiusArgumentLoss_absorbed_by_largeRadius_logLinearEnvelope
      R₀ hR₀_pos

/-- Principal-power logarithmic loss for `w^(1/2-w)` is absorbed by the
large-radius log-linear envelope. -/
theorem Complex.neg_log_norm_cpow_half_minus_self_absorbed_by_largeRadius_logLinearEnvelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
  let ⟨C, hC_pos, hbranch_bound⟩ :=
    Complex.cpow_half_minus_self_radiusArgumentLoss_absorbed_by_largeRadius_logLinearEnvelope
      R₀ hR₀_pos
  ⟨C, hC_pos, fun w hw_sector hw_radius =>
    let hw_ne : w ≠ 0 :=
      Complex.ne_zero_of_pos_le_norm hR₀_pos hw_radius
    le_trans
      (le_of_eq
        (Complex.neg_log_norm_cpow_half_minus_self_eq_radiusArgumentLoss hw_ne))
      (hbranch_bound w hw_sector hw_radius)⟩

/-- The principal-branch logarithmic loss in normalized Stirling is absorbed by
the large-radius log-linear envelope. -/
theorem Complex.normalizedGammaStirlingLogLoss_absorbed_by_largeRadius_logLinearEnvelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Complex.normalizedGammaStirlingLogLoss w ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
  let ⟨C, hC_pos, hcpow⟩ :=
    Complex.neg_log_norm_cpow_half_minus_self_absorbed_by_largeRadius_logLinearEnvelope
      R₀ hR₀_pos
  ⟨C, hC_pos, fun w hw_sector hw_radius =>
    le_trans
      (Complex.normalizedGammaStirlingLogLoss_le_neg_cpow_log hw_sector)
      (hcpow w hw_sector hw_radius)⟩

/-- Assembly of constant-log absorption and principal-branch loss absorption. -/
theorem Complex.normalizedGammaStirlingLogLoss_absorbs_logBound_of_constant_and_loss
    (B R₀ : ℝ)
    (hconstant :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R₀ ≤ ‖w‖ →
          Real.log B ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖))
    (hloss :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R₀ ≤ ‖w‖ →
          Complex.normalizedGammaStirlingLogLoss w ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Real.log B + Complex.normalizedGammaStirlingLogLoss w ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
  let ⟨Cconstant, hCconstant_pos, hconstant_bound⟩ := hconstant
  let ⟨Closs, hCloss_pos, hloss_bound⟩ := hloss
  ⟨Cconstant + Closs, add_pos hCconstant_pos hCloss_pos,
    fun w hw_sector hw_radius =>
      let hsum :
          Real.log B + Complex.normalizedGammaStirlingLogLoss w ≤
            Cconstant * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) +
              Closs * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
        add_le_add
          (hconstant_bound w hw_sector hw_radius)
          (hloss_bound w hw_sector hw_radius)
      let hcombine :
          Cconstant * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) +
              Closs * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) =
            (Cconstant + Closs) * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
        logLinearEnvelope_add_constants
          Cconstant Closs (1 + 2 * ‖w‖) (Real.log (2 + 2 * ‖w‖))
      le_trans hsum (le_of_eq hcombine)⟩

/-- The branch/cpow logarithmic loss from normalized Stirling is absorbed by
the standard log-linear envelope on the large-radius closed right half-plane. -/
theorem Complex.normalizedGammaStirlingLogLoss_absorbs_logBound
    (B R₀ : ℝ)
    (hB_pos : 0 < B)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Real.log B + Complex.normalizedGammaStirlingLogLoss w ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact
    Complex.normalizedGammaStirlingLogLoss_absorbs_logBound_of_constant_and_loss
      B R₀
      (Complex.constant_log_absorbed_by_largeRadius_logLinearEnvelope
        B R₀ hB_pos hR₀_pos)
      (Complex.normalizedGammaStirlingLogLoss_absorbed_by_largeRadius_logLinearEnvelope
        R₀ hR₀_pos)

/-- Large-radius extraction from a normalized Stirling-factor bound to a
logarithmic Gamma envelope.

This is the branch-sensitive analytic core of the normalized-factor route:
from
`‖Γ(w) exp(w) w^(1/2-w)‖ ≤ B`, one expands the norm of `exp(w)` and the
principal-branch norm of `w^(1/2-w)`, then bounds the resulting real part by
`(1 + 2 ‖w‖) log (2 + 2 ‖w‖)` on the closed right half-plane. -/
theorem Complex.Gamma_log_norm_bound_of_normalizedStirlingFactor_bound_largeRadius
    (B R₀ : ℝ)
    (hB_pos : 0 < B)
    (hR₀_pos : 0 < R₀)
    (hfactor :
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ ≤ B) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
  let ⟨C, hC_pos, hloss⟩ :=
    Complex.normalizedGammaStirlingLogLoss_absorbs_logBound B R₀ hB_pos hR₀_pos
  ⟨C, hC_pos, fun w hw_sector hw_radius =>
    let hfactor_ne :
        Complex.normalizedGammaStirlingFactor w ≠ 0 :=
      Complex.normalizedGammaStirlingFactor_ne_zero_of_closedRightHalfPlaneSector_largeRadius
        R₀ hR₀_pos hw_sector hw_radius
    let hfactor_pos :
        0 < ‖Complex.normalizedGammaStirlingFactor w‖ :=
      norm_pos_iff.mpr hfactor_ne
    let hfactor_bound :
        ‖Complex.normalizedGammaStirlingFactor w‖ ≤ B :=
      hfactor w hw_sector hw_radius
    let hfactor_log :
        Real.log ‖Complex.normalizedGammaStirlingFactor w‖ ≤ Real.log B :=
      Complex.normalizedGammaStirlingFactor_log_le_of_norm_bound
        B hfactor_pos hfactor_bound
    let hgamma_extract :
        Real.log ‖Complex.Gamma w‖ ≤
          Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
            Complex.normalizedGammaStirlingLogLoss w :=
      Complex.Gamma_log_norm_le_normalizedGammaStirlingFactor_log_add_loss
        w hfactor_ne
    let hlog_plus_loss :
        Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
            Complex.normalizedGammaStirlingLogLoss w ≤
          Real.log B + Complex.normalizedGammaStirlingLogLoss w :=
      add_le_add_right hfactor_log
        (Complex.normalizedGammaStirlingLogLoss w)
    le_trans hgamma_extract
      (le_trans hlog_plus_loss (hloss w hw_sector hw_radius))⟩

/-- The closed right-half-plane Gamma annulus used to absorb small radii in the
normalized Stirling extraction. -/
def Complex.closedRightHalfPlaneGammaAnnulus (R₀ : ℝ) : Set ℂ :=
  {w : ℂ | Complex.closedRightHalfPlaneSector w ∧ (1 / 2 : ℝ) ≤ ‖w‖ ∧ ‖w‖ ≤ R₀}

/-- The closed right-half-plane Gamma annulus is closed. -/
theorem Complex.closedRightHalfPlaneGammaAnnulus_isClosed
    (R₀ : ℝ) :
    IsClosed (Complex.closedRightHalfPlaneGammaAnnulus R₀) := by
  have hsector : IsClosed {w : ℂ | Complex.closedRightHalfPlaneSector w} := by
    exact isClosed_le continuous_const Complex.continuous_re
  have hinner : IsClosed {w : ℂ | (1 / 2 : ℝ) ≤ ‖w‖} := by
    exact isClosed_le continuous_const continuous_norm
  have houter : IsClosed {w : ℂ | ‖w‖ ≤ R₀} := by
    exact isClosed_le continuous_norm continuous_const
  have hset :
      Complex.closedRightHalfPlaneGammaAnnulus R₀ =
        {w : ℂ | Complex.closedRightHalfPlaneSector w} ∩
          {w : ℂ | (1 / 2 : ℝ) ≤ ‖w‖} ∩
            {w : ℂ | ‖w‖ ≤ R₀} := by
    ext w
    constructor
    · intro hw
      exact ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩
    · intro hw
      exact ⟨hw.1.1, hw.1.2, hw.2⟩
  exact Eq.subst
    (motive := fun S : Set ℂ => IsClosed S)
    hset.symm
    ((hsector.inter hinner).inter houter)

/-- The closed right-half-plane Gamma annulus is bounded. -/
theorem Complex.closedRightHalfPlaneGammaAnnulus_isBounded
    (R₀ : ℝ) :
    Bornology.IsBounded (Complex.closedRightHalfPlaneGammaAnnulus R₀) :=
  isBounded_iff_forall_norm_le.2 ⟨max R₀ 0 + 1, fun w hw =>
    let hraw : ‖w‖ ≤ R₀ := hw.2.2
    le_trans hraw
      (le_trans (le_max_left R₀ 0) (le_add_of_nonneg_right zero_le_one))⟩

/-- The closed right-half-plane Gamma annulus is compact. -/
theorem Complex.closedRightHalfPlaneGammaAnnulus_isCompact
    (R₀ : ℝ) :
    IsCompact (Complex.closedRightHalfPlaneGammaAnnulus R₀) :=
  Metric.isCompact_of_isClosed_isBounded
    (Complex.closedRightHalfPlaneGammaAnnulus_isClosed R₀)
    (Complex.closedRightHalfPlaneGammaAnnulus_isBounded R₀)

/-- `Gamma` is nonzero on the closed right-half-plane Gamma annulus. -/
theorem Complex.Gamma_ne_zero_on_closedRightHalfPlaneGammaAnnulus
    (R₀ : ℝ)
    {w : ℂ}
    (hw : w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀) :
    Complex.Gamma w ≠ 0 :=
  fun hzero =>
    match (Complex.Gamma_eq_zero_iff w).mp hzero with
    | ⟨0, hn⟩ =>
        let hnorm_zero : ‖(-((0 : ℕ) : ℂ))‖ = 0 :=
          calc
            ‖(-((0 : ℕ) : ℂ))‖ = ‖(-(0 : ℂ))‖ := rfl
            _ = ‖(0 : ℂ)‖ :=
              congrArg norm (neg_zero : -((0 : ℂ)) = 0)
            _ = 0 := norm_zero
        let hhalf_le_norm : (1 / 2 : ℝ) ≤ ‖w‖ := hw.2.1
        let hhalf_le_hn : (1 / 2 : ℝ) ≤ ‖(-((0 : ℕ) : ℂ))‖ :=
          Eq.subst hn hhalf_le_norm
        let hhalf_le_zero : (1 / 2 : ℝ) ≤ 0 :=
          Eq.subst
            (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x)
            hnorm_zero
            hhalf_le_hn
        (not_lt_of_ge hhalf_le_zero) one_half_pos
    | ⟨Nat.succ n, hn⟩ =>
        let hw_sector' : Complex.closedRightHalfPlaneSector (-(((Nat.succ n : ℕ) : ℂ))) :=
          Eq.subst hn hw.1
        let hre_eq :
            (-(((Nat.succ n : ℕ) : ℂ))).re = -(((Nat.succ n : ℕ) : ℝ)) :=
          calc
            (-(((Nat.succ n : ℕ) : ℂ))).re =
                -(((Nat.succ n : ℕ) : ℂ).re) :=
              Complex.neg_re (((Nat.succ n : ℕ) : ℂ))
            _ = -(((Nat.succ n : ℕ) : ℝ)) :=
              congrArg Neg.neg (Complex.natCast_re (Nat.succ n))
        let hre_nonneg : (0 : ℝ) ≤ -(((Nat.succ n : ℕ) : ℝ)) :=
          Eq.subst
            (motive := fun x : ℝ => (0 : ℝ) ≤ x)
            hre_eq
            hw_sector'
        let hsucc_pos : (0 : ℝ) < ((Nat.succ n : ℕ) : ℝ) :=
          Nat.cast_pos.mpr (Nat.succ_pos n)
        let hneg_lt_zero : -(((Nat.succ n : ℕ) : ℝ)) < 0 :=
          neg_neg_of_pos hsucc_pos
        (not_lt_of_ge hre_nonneg) hneg_lt_zero

/-- The function `w ↦ log ‖Γ(w)‖` is continuous on the closed right-half-plane
Gamma annulus. -/
theorem Complex.continuousOn_log_norm_Gamma_closedRightHalfPlaneGammaAnnulus
    (R₀ : ℝ) :
    ContinuousOn
      (fun w : ℂ => Real.log ‖Complex.Gamma w‖)
      (Complex.closedRightHalfPlaneGammaAnnulus R₀) := by
  intro w hw
  have hgamma_ne : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero_on_closedRightHalfPlaneGammaAnnulus R₀ hw
  have hnot_pole : ∀ m : ℕ, w ≠ -m := by
    intro m hwm
    exact hgamma_ne ((Complex.Gamma_eq_zero_iff w).mpr ⟨m, hwm⟩)
  have hgamma_cont : ContinuousAt Complex.Gamma w :=
    (Complex.differentiableAt_Gamma w hnot_pole).continuousAt
  have hnorm_cont :
      ContinuousWithinAt (fun z : ℂ => ‖Complex.Gamma z‖)
        (Complex.closedRightHalfPlaneGammaAnnulus R₀) w :=
    hgamma_cont.norm.continuousWithinAt
  have hnorm_ne : ‖Complex.Gamma w‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr hgamma_ne)
  exact hnorm_cont.log hnorm_ne

/-- Compact boundedness of `log ‖Γ(w)‖` on the closed right-half-plane Gamma
annulus. -/
theorem Complex.log_norm_Gamma_closedRightHalfPlaneGammaAnnulus_bound
    (R₀ : ℝ) :
    ∃ M : ℝ,
      ∀ w : ℂ,
        w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ →
        Real.log ‖Complex.Gamma w‖ ≤ M :=
  let ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn
      (Complex.closedRightHalfPlaneGammaAnnulus_isCompact R₀)
      (Complex.continuousOn_log_norm_Gamma_closedRightHalfPlaneGammaAnnulus R₀)
  ⟨M, fun w hw => hM w hw⟩

/-- The log-linear Gamma envelope has a positive lower bound on the compact
annulus. -/
theorem Complex.logLinearEnvelope_closedRightHalfPlaneGammaAnnulus_lower_bound
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ w : ℂ,
        w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ →
        δ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
  ⟨Real.log 3, Real.log_pos one_lt_three, fun w hw =>
    let htwo_norm_ge_one : (1 : ℝ) ≤ 2 * ‖w‖ :=
      (div_le_iff₀' zero_lt_two).mp hw.2.1
    let hH_ge_one : (1 : ℝ) ≤ 1 + 2 * ‖w‖ :=
      le_add_of_nonneg_right (mul_nonneg zero_le_two (norm_nonneg w))
    let harg_ge_three : (3 : ℝ) ≤ 2 + 2 * ‖w‖ :=
      calc
        (3 : ℝ) = 2 + 1 := rfl
        _ ≤ 2 + 2 * ‖w‖ :=
          add_le_add_left htwo_norm_ge_one 2
    let hlog_le : Real.log 3 ≤ Real.log (2 + 2 * ‖w‖) :=
      Real.log_le_log zero_lt_three harg_ge_three
    let hlog_nonneg : 0 ≤ Real.log (2 + 2 * ‖w‖) :=
      le_trans (le_of_lt (Real.log_pos one_lt_three)) hlog_le
    let hone_mul :
        Real.log (2 + 2 * ‖w‖) ≤
          (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
      calc
        Real.log (2 + 2 * ‖w‖) = 1 * Real.log (2 + 2 * ‖w‖) :=
          (one_mul (Real.log (2 + 2 * ‖w‖))).symm
        _ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
          mul_le_mul_of_nonneg_right hH_ge_one hlog_nonneg
    le_trans hlog_le hone_mul⟩

/-- A bounded numerator and positive envelope lower bound give a constant
multiple bound on the compact Gamma annulus. -/
theorem Complex.Gamma_log_norm_bound_closedRightHalfPlaneSector_compactAnnulus_of_bound_and_lower
    (R₀ M δ : ℝ)
    (hδ_pos : 0 < δ)
    (hM :
      ∀ w : ℂ,
        w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ →
        Real.log ‖Complex.Gamma w‖ ≤ M)
    (hδ :
      ∀ w : ℂ,
        w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ →
        δ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        ‖w‖ ≤ R₀ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
  let C : ℝ := max (M / δ) 1
  let hC_pos : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_right (M / δ) 1)
  ⟨C, hC_pos, fun w hw_sector hw_inner hw_outer =>
    let hw_annulus : w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ :=
      ⟨hw_sector, hw_inner, hw_outer⟩
    let hraw : Real.log ‖Complex.Gamma w‖ ≤ M :=
      hM w hw_annulus
    let hM_div_le_C : M / δ ≤ C :=
      le_max_left (M / δ) 1
    let hM_le_Cδ : M ≤ C * δ :=
      (div_le_iff₀ hδ_pos).mp hM_div_le_C
    let hδ_le_env : δ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
      hδ w hw_annulus
    let hCδ_le_Cenv :
        C * δ ≤ C * ((1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :=
      mul_le_mul_of_nonneg_left hδ_le_env (le_of_lt hC_pos)
    let hCenv_eq :
        C * ((1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) =
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
      mul_assoc C (1 + 2 * ‖w‖) (Real.log (2 + 2 * ‖w‖))
    le_trans hraw
      (le_trans hM_le_Cδ
        (le_trans hCδ_le_Cenv (le_of_eq hCenv_eq)))⟩

/-- Compact annulus absorption for the logarithmic Gamma envelope in the closed
right half-plane sector.

This owns the local boundedness part omitted by the large-radius normalized
Stirling estimate: on the compact annulus
`0 ≤ re w`, `1 / 2 ≤ ‖w‖`, `‖w‖ ≤ R₀`, continuity of `Γ` and nonvanishing of
`Γ` give a finite bound for `log ‖Γ(w)‖`, which is absorbed by the positive
logarithmic envelope. -/
theorem Complex.Gamma_log_norm_bound_closedRightHalfPlaneSector_compactAnnulus
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        ‖w‖ ≤ R₀ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
  let ⟨M, hM⟩ := Complex.log_norm_Gamma_closedRightHalfPlaneGammaAnnulus_bound R₀
  let ⟨δ, hδ_pos, hδ⟩ :=
    Complex.logLinearEnvelope_closedRightHalfPlaneGammaAnnulus_lower_bound R₀ hR₀_pos
  Complex.Gamma_log_norm_bound_closedRightHalfPlaneSector_compactAnnulus_of_bound_and_lower
    R₀ M δ hδ_pos hM hδ

/-- Assembly of large-radius extraction and compact-annulus absorption. -/
theorem Complex.Gamma_log_norm_bound_of_largeRadius_and_compactAnnulus
    (R₀ : ℝ)
    (hlarge :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R₀ ≤ ‖w‖ →
          Real.log ‖Complex.Gamma w‖ ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖))
    (hannulus :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          (1 / 2 : ℝ) ≤ ‖w‖ →
          ‖w‖ ≤ R₀ →
          Real.log ‖Complex.Gamma w‖ ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
  let ⟨Clarge, hClarge_pos, hlarge_bound⟩ := hlarge
  let ⟨Cannulus, _hCannulus_pos, hannulus_bound⟩ := hannulus
  ⟨max Clarge Cannulus,
    lt_of_lt_of_le hClarge_pos (le_max_left Clarge Cannulus),
    fun w hw_sector hw_norm =>
      let htwo_norm_nonneg : 0 ≤ 2 * ‖w‖ :=
        mul_nonneg zero_le_two (norm_nonneg w)
      let hH_nonneg : 0 ≤ 1 + 2 * ‖w‖ :=
        add_nonneg zero_le_one htwo_norm_nonneg
      let hlog_arg_ge_one : (1 : ℝ) ≤ 2 + 2 * ‖w‖ :=
        le_trans one_le_two (le_add_of_nonneg_right htwo_norm_nonneg)
      let hL_nonneg : 0 ≤ Real.log (2 + 2 * ‖w‖) :=
        Real.log_nonneg hlog_arg_ge_one
      if hlarge_radius : R₀ ≤ ‖w‖ then
        let hraw :
            Real.log ‖Complex.Gamma w‖ ≤
              Clarge * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
          hlarge_bound w hw_sector hlarge_radius
        let hmono :
            Clarge * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) ≤
              max Clarge Cannulus * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
          logLinearEnvelope_mono_constant
            (le_max_left Clarge Cannulus)
            hH_nonneg
            hL_nonneg
        le_trans hraw hmono
      else
        let hannulus_radius : ‖w‖ ≤ R₀ :=
          le_of_not_ge hlarge_radius
        let hraw :
            Real.log ‖Complex.Gamma w‖ ≤
              Cannulus * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
          hannulus_bound w hw_sector hw_norm hannulus_radius
        let hmono :
            Cannulus * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) ≤
              max Clarge Cannulus * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
          logLinearEnvelope_mono_constant
            (le_max_right Clarge Cannulus)
            hH_nonneg
            hL_nonneg
        le_trans hraw hmono⟩

/-- The remaining real/branch extraction from a uniform bound for
`Γ(w) exp(w) w^(1/2-w)` to the logarithmic Gamma norm envelope.

This is deliberately isolated as the deepest nontrivial extraction root: it is
where the norm identities for `Complex.exp`, the closed-right-half-plane branch
control for `w ^ (1/2-w)`, and the elementary real domination by
`(1 + 2 ‖w‖) log (2 + 2 ‖w‖)` are used. -/
theorem Complex.Gamma_log_norm_bound_of_normalizedStirlingFactor_bound
    (B R₀ : ℝ)
    (hB_pos : 0 < B)
    (hR₀_pos : 0 < R₀)
    (hfactor :
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ ≤ B) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  have hlarge :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R₀ ≤ ‖w‖ →
          Real.log ‖Complex.Gamma w‖ ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    Complex.Gamma_log_norm_bound_of_normalizedStirlingFactor_bound_largeRadius
      B R₀ hB_pos hR₀_pos hfactor
  have hannulus :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          (1 / 2 : ℝ) ≤ ‖w‖ →
          ‖w‖ ≤ R₀ →
          Real.log ‖Complex.Gamma w‖ ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    Complex.Gamma_log_norm_bound_closedRightHalfPlaneSector_compactAnnulus
      R₀ hR₀_pos
  exact
    Complex.Gamma_log_norm_bound_of_largeRadius_and_compactAnnulus
      R₀ hlarge hannulus

/-- The elementary cutoff inequality used in the exponential-Stirling extraction:
if the radius dominates `2K / sqrt (2π)`, then the normalized error term
`K / r` is at most `sqrt (2π)`.

This is a pure real-inequality sink; it is separated from the Gamma theorem so
the analytic owner theorem only assembles named estimates. -/
theorem real_stirlingError_div_norm_le_sqrt_two_pi_of_cutoff
    (K r : ℝ)
    (hK_pos : 0 < K)
    (hr_pos : 0 < r)
    (hr_cutoff : 2 * K / Real.sqrt (2 * Real.pi) ≤ r) :
    K / r ≤ Real.sqrt (2 * Real.pi) := by
  let s : ℝ := Real.sqrt (2 * Real.pi)
  have hs_pos : 0 < s :=
    Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos)
  have hcutoff_mul : 2 * K ≤ r * s :=
    (div_le_iff₀ hs_pos).mp hr_cutoff
  have hK_le_twoK : K ≤ 2 * K := by
    calc
      K = 1 * K := (one_mul K).symm
      _ ≤ 2 * K := mul_le_mul_of_nonneg_right one_le_two (le_of_lt hK_pos)
  have hK_le_rs : K ≤ r * s :=
    le_trans hK_le_twoK hcutoff_mul
  have hK_le_sr : K ≤ s * r :=
    Eq.subst
      (motive := fun x : ℝ => K ≤ x)
      (mul_comm r s)
      hK_le_rs
  exact (div_le_iff₀ hr_pos).mpr hK_le_sr

/-- Log-norm envelope extracted from the closed-right-half-plane exponential
Stirling expansion.

This is the exact reusable Gamma/Stirling API boundary between the normalized
exponential asymptotic and the downstream finite-order estimates.  Its proof is
the analytic extraction step: compare
`Γ(w) exp(w) w^(1/2-w)` with `sqrt (2π)`, bound the normalized factor away from
zero for large `‖w‖`, and transport through the branch-sensitive norm identities
for `Complex.exp` and `Complex.cpow`; cf. DLMF §5.11. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_log_norm_bound_of_exponential_stirling
    (hStirling :
      ∃ R : ℝ, ∃ K : ℝ,
        0 < R ∧
        0 < K ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R ≤ ‖w‖ →
          ‖Complex.Gamma w * Complex.exp w *
              w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
            K / ‖w‖) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
  let ⟨R, K, hR_pos, hK_pos, hStirling_pointwise⟩ := hStirling
  let R₀ : ℝ :=
    max R (max (2 * K / Real.sqrt (2 * Real.pi)) 1)
  let hR₀_pos : 0 < R₀ :=
    lt_of_lt_of_le zero_lt_one (le_max_right R (max (2 * K / Real.sqrt (2 * Real.pi)) 1))
  let hfactor :
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ ≤
          2 * Real.sqrt (2 * Real.pi) :=
    fun w hw_sector hw_R₀ =>
      let hw_R : R ≤ ‖w‖ :=
        le_trans (le_max_left R (max (2 * K / Real.sqrt (2 * Real.pi)) 1)) hw_R₀
      let hw_one : 1 ≤ ‖w‖ :=
        le_trans (le_trans (le_max_right (2 * K / Real.sqrt (2 * Real.pi)) 1)
          (le_max_right R (max (2 * K / Real.sqrt (2 * Real.pi)) 1))) hw_R₀
      let hw_norm_pos : 0 < ‖w‖ :=
        lt_of_lt_of_le zero_lt_one hw_one
      let hw_cutoff : 2 * K / Real.sqrt (2 * Real.pi) ≤ ‖w‖ :=
        le_trans (le_trans
          (le_max_left (2 * K / Real.sqrt (2 * Real.pi)) 1)
          (le_max_right R (max (2 * K / Real.sqrt (2 * Real.pi)) 1))) hw_R₀
      let hK_div_le : K / ‖w‖ ≤ Real.sqrt (2 * Real.pi) :=
        real_stirlingError_div_norm_le_sqrt_two_pi_of_cutoff
          K ‖w‖ hK_pos hw_norm_pos hw_cutoff
      Complex.normalizedGammaFactor_norm_le_two_sqrt_two_pi_of_exponentialStirling_error
        R K hStirling_pointwise w hw_sector hw_R hK_div_le
  let hB_pos : 0 < 2 * Real.sqrt (2 * Real.pi) :=
    mul_pos two_pos (Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos))
  Complex.Gamma_log_norm_bound_of_normalizedStirlingFactor_bound
    (2 * Real.sqrt (2 * Real.pi)) R₀ hB_pos hR₀_pos hfactor

/-- The sectorial exponential Stirling asymptotic gives the standard logarithmic
norm envelope on the closed right half-plane.

This is still part of the classical complex-Gamma Stirling input: it is the
real-part extraction and elementary domination step from the sectorial
asymptotic above, using nonnegative standard comparison envelopes.  Once
mathlib has a sectorial complex Stirling theorem, this is the single local
corollary that should be proved from it. -/
theorem Complex.sectorialGammaExponentialEnvelope_closedRightHalfPlane_of_asymptotic
    (hStirling :
      ∃ R : ℝ, ∃ K : ℝ,
        0 < R ∧
        0 < K ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R ≤ ‖w‖ →
          ‖Complex.Gamma w * Complex.exp w *
              w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
            K / ‖w‖) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact
    Complex.Gamma_closedRightHalfPlane_sectorial_log_norm_bound_of_exponential_stirling
      hStirling

/-- Classical closed-sector exponential Stirling expansion for `Complex.Gamma`.

This is the formula-level sectorial asymptotic root for the Gamma lane:
Stirling's expansion with a uniform `O(1 / ‖w‖)` remainder on the closed right
half-plane, viewed as a closed sector avoiding the negative real axis; cf. DLMF
§5.11 and Whittaker-Watson, Ch. XII. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_exponential_stirling_expansion_classical :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖ := by
  exact Complex.sectorialLogGammaAsymptotic_closedRightHalfPlane

/-- Sectorial Gamma exponential envelope on the closed right half-plane.

This is the classical growth consequence of sectorial logarithmic Stirling:
the real part of `log Γ(w)` is bounded by a linear-logarithmic envelope on the
closed right half-plane, uniformly away from the origin; cf. DLMF §5.11. -/
theorem Complex.sectorialGammaExponentialEnvelope_closedRightHalfPlane :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact
    Complex.sectorialGammaExponentialEnvelope_closedRightHalfPlane_of_asymptotic
      Complex.sectorialLogGammaAsymptotic_closedRightHalfPlane

/-- The finite recurrence product relating `Γ z` and `Γ (z + N)`. -/

end
end LFunctions
end Boundary
