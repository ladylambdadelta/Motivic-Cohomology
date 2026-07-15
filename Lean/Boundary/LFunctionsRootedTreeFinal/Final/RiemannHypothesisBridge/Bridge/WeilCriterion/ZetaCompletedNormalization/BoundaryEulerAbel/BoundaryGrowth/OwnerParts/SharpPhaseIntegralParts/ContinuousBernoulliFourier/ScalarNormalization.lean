import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.NormalizedPeriodicIntegral

/-!
# Scalar normalization of the periodic centered-Bernoulli bound
-/

namespace Boundary
namespace LFunctions

noncomputable section

local notation "π" => Real.pi

private theorem realTwoMulTwoEqFour : (2 : ℝ) * 2 = 4 := by
  have hnat : ((2 * 2 : ℕ) : ℝ) = ((4 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ))
      (show (2 * 2 : ℕ) = 4 from rfl)
  have hleft : ((2 * 2 : ℕ) : ℝ) = (2 : ℝ) * 2 :=
    Nat.cast_mul 2 2
  have hright : ((4 : ℕ) : ℝ) = (4 : ℝ) :=
    rfl
  exact Eq.trans hleft.symm (Eq.trans hnat hright)

private theorem realTwoAddFourEqSix : (2 : ℝ) + 4 = 6 := by
  have hnat : ((2 + 4 : ℕ) : ℝ) = ((6 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ))
      (show (2 + 4 : ℕ) = 6 from rfl)
  have hleft : ((2 + 4 : ℕ) : ℝ) = (2 : ℝ) + 4 :=
    Nat.cast_add 2 4
  have hright : ((6 : ℕ) : ℝ) = (6 : ℝ) :=
    rfl
  exact Eq.trans hleft.symm (Eq.trans hnat hright)

/-- The norm of the canonical second-Bernoulli Fourier normalization is
`4π²`. -/
theorem norm_centeredQuadraticPrimitiveFourierNormalization :
    ‖centeredQuadraticPrimitiveFourierNormalization‖ =
      4 * π ^ (2 : ℕ) := by
  have htwoComplex : ‖(2 : ℂ)‖ = (2 : ℝ) :=
    Complex.norm_ofNat 2
  have hpiComplex : ‖(π : ℂ)‖ = π :=
    Eq.trans (Complex.norm_real π) (Real.norm_of_nonneg (le_of_lt Real.pi_pos))
  have hI : ‖Complex.I‖ = 1 :=
    Complex.norm_I
  have hbase :
      ‖(2 : ℂ) * (π : ℂ) * Complex.I‖ = 2 * π := by
    exact Eq.trans
      (norm_mul ((2 : ℂ) * (π : ℂ)) Complex.I)
      (Eq.trans
        (congrArg₂ Mul.mul
          (Eq.trans
            (norm_mul (2 : ℂ) (π : ℂ))
            (congrArg₂ Mul.mul htwoComplex hpiComplex))
          hI)
        (mul_one (2 * π)))
  have hfactorialNat : Nat.factorial 2 = 2 :=
    rfl
  have hfactorialCast : ((Nat.factorial 2 : ℕ) : ℂ) = (2 : ℂ) :=
    Eq.trans (congrArg (fun n : ℕ => (n : ℂ)) hfactorialNat) rfl
  have hfactorialNorm : ‖((Nat.factorial 2 : ℕ) : ℂ)‖ = (2 : ℝ) :=
    Eq.trans (congrArg Norm.norm hfactorialCast) htwoComplex
  have hraw :
      ‖centeredQuadraticPrimitiveFourierNormalization‖ =
        ((2 * π) ^ (2 : ℕ) / 2) * 2 := by
    unfold centeredQuadraticPrimitiveFourierNormalization
    exact Eq.trans
      (norm_mul
        (-((2 : ℂ) * (π : ℂ) * Complex.I) ^ (2 : ℕ) /
          (Nat.factorial 2 : ℕ))
        (2 : ℂ))
      (Eq.trans
        (congrArg₂ Mul.mul
          (Eq.trans
            (norm_div
              (-((2 : ℂ) * (π : ℂ) * Complex.I) ^ (2 : ℕ))
              ((Nat.factorial 2 : ℕ) : ℂ))
            (congrArg₂ Div.div
              (Eq.trans
                (norm_neg (((2 : ℂ) * (π : ℂ) * Complex.I) ^ (2 : ℕ)))
                (Eq.trans
                  (norm_pow ((2 : ℂ) * (π : ℂ) * Complex.I) (2 : ℕ))
                  (congrArg (fun r : ℝ => r ^ (2 : ℕ)) hbase)))
              hfactorialNorm))
          htwoComplex)
        rfl)
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    two_ne_zero
  have hcancel : ((2 * π) ^ (2 : ℕ) / 2) * 2 = (2 * π) ^ (2 : ℕ) :=
    div_mul_cancel₀ ((2 * π) ^ (2 : ℕ)) htwo_ne
  have hsquare : (2 * π) ^ (2 : ℕ) = 4 * π ^ (2 : ℕ) := by
    calc
      (2 * π) ^ (2 : ℕ) = (2 * π) * (2 * π) := pow_two (2 * π)
      _ = (2 * 2) * (π * π) := mul_mul_mul_comm 2 π 2 π
      _ = 4 * (π * π) := by
        exact congrArg (fun r : ℝ => r * (π * π))
          realTwoMulTwoEqFour
      _ = 4 * π ^ (2 : ℕ) := by
        exact congrArg (fun r : ℝ => 4 * r) (pow_two π).symm
  exact Eq.trans hraw (Eq.trans hcancel hsquare)

/-- The norm of the inverse normalization is the reciprocal of `4π²`. -/
theorem norm_centeredQuadraticPrimitiveFourierNormalization_inv :
    ‖(centeredQuadraticPrimitiveFourierNormalization)⁻¹‖ =
      (4 * π ^ (2 : ℕ))⁻¹ := by
  exact Eq.trans
    (norm_inv centeredQuadraticPrimitiveFourierNormalization)
    (congrArg Inv.inv norm_centeredQuadraticPrimitiveFourierNormalization)

/-- The bilateral Basel mass is bounded by `π²`. -/
theorem centeredQuadraticPrimitive_fourier_coefficient_mass_le_pi_sq :
    π ^ (2 : ℕ) / 6 + π ^ (2 : ℕ) / 6 ≤ π ^ (2 : ℕ) := by
  let x : ℝ := π ^ (2 : ℕ)
  have hx : 0 ≤ x :=
    sq_nonneg π
  have htwo_pos : (0 : ℝ) < 2 :=
    zero_lt_two
  have hsix_le : (2 : ℝ) ≤ 6 :=
    Eq.subst
      (motive := fun value : ℝ => 2 ≤ value)
      realTwoAddFourEqSix
      (le_add_of_nonneg_right zero_le_four)
  have hhalf : x / 6 ≤ x / 2 :=
    div_le_div_of_nonneg_left hx htwo_pos hsix_le
  have hsum : x / 6 + x / 6 ≤ x / 2 + x / 2 :=
    add_le_add hhalf hhalf
  have haddHalves : x / 2 + x / 2 = x :=
    add_halves x
  exact le_trans hsum (le_of_eq haddHalves)

/-- The bilateral Basel mass is already bounded by half of `π²`. -/
theorem centeredQuadraticPrimitive_fourier_coefficient_mass_le_pi_sq_div_two :
    π ^ (2 : ℕ) / 6 + π ^ (2 : ℕ) / 6 ≤ π ^ (2 : ℕ) / 2 := by
  let x : ℝ := π ^ (2 : ℕ)
  have hx : 0 ≤ x :=
    sq_nonneg π
  have hfour_pos : (0 : ℝ) < 4 :=
    zero_lt_four
  have hsix_le : (4 : ℝ) ≤ 6 :=
    Eq.subst
      (motive := fun value : ℝ => 4 ≤ value)
      (Eq.trans
        (add_comm (4 : ℝ) 2)
        realTwoAddFourEqSix)
      (le_add_of_nonneg_right (le_of_lt zero_lt_two))
  have hquarter : x / 6 ≤ x / 4 :=
    div_le_div_of_nonneg_left hx hfour_pos hsix_le
  have hsum : x / 6 + x / 6 ≤ x / 4 + x / 4 :=
    add_le_add hquarter hquarter
  have htwo_mul_two : (2 : ℝ) * 2 = 4 :=
    realTwoMulTwoEqFour
  have hquarterEq : x / 4 = (x / 2) / 2 := by
    exact Eq.symm
      (Eq.trans
        (div_div x 2 2)
        (congrArg (fun r : ℝ => x / r) htwo_mul_two))
  have haddQuarters : x / 4 + x / 4 = x / 2 :=
    Eq.trans
      (congrArg₂ Add.add hquarterEq hquarterEq)
      (add_halves (x / 2))
  exact le_trans hsum (le_of_eq haddQuarters)

/-- The raw scalar multiplier in the periodic centered-primitive estimate is
at most one. -/
theorem centeredQuadraticPrimitive_rawFourierBound_le_one :
    ‖(centeredQuadraticPrimitiveFourierNormalization)⁻¹‖ *
        (4 * (π ^ (2 : ℕ) / 6 + π ^ (2 : ℕ) / 6)) ≤ 1 := by
  let x : ℝ := π ^ (2 : ℕ)
  have hx_pos : 0 < x :=
    sq_pos_of_pos Real.pi_pos
  have hfour_x_pos : 0 < 4 * x :=
    mul_pos zero_lt_four hx_pos
  have hmass :=
    centeredQuadraticPrimitive_fourier_coefficient_mass_le_pi_sq
  have hscaled :
      4 * (π ^ (2 : ℕ) / 6 + π ^ (2 : ℕ) / 6) ≤ 4 * x :=
    mul_le_mul_of_nonneg_left hmass
      zero_le_four
  have hinverseNonnegative : 0 ≤ (4 * x)⁻¹ :=
    inv_nonneg.mpr (le_of_lt hfour_x_pos)
  have hproduct :
      (4 * x)⁻¹ *
          (4 * (π ^ (2 : ℕ) / 6 + π ^ (2 : ℕ) / 6)) ≤
        (4 * x)⁻¹ * (4 * x) :=
    mul_le_mul_of_nonneg_left hscaled hinverseNonnegative
  have hcancellation : (4 * x)⁻¹ * (4 * x) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hfour_x_pos)
  exact Eq.subst
    (motive := fun value : ℝ =>
      value * (4 * (π ^ (2 : ℕ) / 6 + π ^ (2 : ℕ) / 6)) ≤ 1)
    norm_centeredQuadraticPrimitiveFourierNormalization_inv.symm
    (le_trans hproduct (le_of_eq hcancellation))

/-- The raw scalar multiplier is at most one half. -/
theorem centeredQuadraticPrimitive_rawFourierBound_le_one_half :
    ‖(centeredQuadraticPrimitiveFourierNormalization)⁻¹‖ *
        (4 * (π ^ (2 : ℕ) / 6 + π ^ (2 : ℕ) / 6)) ≤ (1 : ℝ) / 2 := by
  let x : ℝ := π ^ (2 : ℕ)
  have hx_pos : 0 < x :=
    sq_pos_of_pos Real.pi_pos
  have hfour_x_pos : 0 < 4 * x :=
    mul_pos zero_lt_four hx_pos
  have hmass :=
    centeredQuadraticPrimitive_fourier_coefficient_mass_le_pi_sq_div_two
  have hscaled :
      4 * (π ^ (2 : ℕ) / 6 + π ^ (2 : ℕ) / 6) ≤ 4 * (x / 2) :=
    mul_le_mul_of_nonneg_left hmass
      zero_le_four
  have hinverseNonnegative : 0 ≤ (4 * x)⁻¹ :=
    inv_nonneg.mpr (le_of_lt hfour_x_pos)
  have hproduct :
      (4 * x)⁻¹ *
          (4 * (π ^ (2 : ℕ) / 6 + π ^ (2 : ℕ) / 6)) ≤
        (4 * x)⁻¹ * (4 * (x / 2)) :=
    mul_le_mul_of_nonneg_left hscaled hinverseNonnegative
  have hscaledHalf : 4 * (x / 2) = (4 * x) / 2 :=
    (mul_div_assoc 4 x 2).symm
  have hcancellation : (4 * x)⁻¹ * (4 * (x / 2)) = (1 : ℝ) / 2 := by
    exact Eq.trans
      (congrArg (fun r : ℝ => (4 * x)⁻¹ * r) hscaledHalf)
      (Eq.trans
        (mul_div_assoc (4 * x)⁻¹ (4 * x) 2).symm
        (congrArg (fun r : ℝ => r / 2)
          (inv_mul_cancel₀ (ne_of_gt hfour_x_pos))))
  exact Eq.subst
    (motive := fun value : ℝ =>
      value * (4 * (π ^ (2 : ℕ) / 6 + π ^ (2 : ℕ) / 6)) ≤ (1 : ℝ) / 2)
    norm_centeredQuadraticPrimitiveFourierNormalization_inv.symm
    (le_trans hproduct (le_of_eq hcancellation))

/-- Uniform bound one for the periodic centered quadratic remainder integral. -/
theorem norm_intervalIntegral_boundaryLineOnePointRealParam_periodicCenteredQuadraticPrimitive_le_one
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    ‖∫ u in (0 : ℝ)..L,
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
          periodicCenteredQuadraticPrimitive u‖ ≤ 1 := by
  exact le_trans
    (norm_intervalIntegral_boundaryLineOnePointRealParam_periodicCenteredQuadraticPrimitive_le_raw
      t ha hL)
    centeredQuadraticPrimitive_rawFourierBound_le_one

/-- Half-unit bound for the periodic centered quadratic remainder integral. -/
theorem norm_intervalIntegral_boundaryLineOnePointRealParam_periodicCenteredQuadraticPrimitive_le_one_half
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    ‖∫ u in (0 : ℝ)..L,
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
          periodicCenteredQuadraticPrimitive u‖ ≤ (1 : ℝ) / 2 := by
  exact le_trans
    (norm_intervalIntegral_boundaryLineOnePointRealParam_periodicCenteredQuadraticPrimitive_le_raw
      t ha hL)
    centeredQuadraticPrimitive_rawFourierBound_le_one_half

end
end LFunctions
end Boundary
