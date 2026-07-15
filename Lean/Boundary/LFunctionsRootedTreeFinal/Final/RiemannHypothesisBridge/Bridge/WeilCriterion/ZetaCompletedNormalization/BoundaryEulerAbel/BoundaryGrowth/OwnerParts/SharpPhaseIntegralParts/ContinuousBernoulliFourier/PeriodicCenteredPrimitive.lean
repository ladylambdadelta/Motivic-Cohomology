import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.CoefficientNormSum

/-!
# Periodic centered quadratic primitive

The periodic primitive is defined from the canonical Mathlib Fourier series.
On a fundamental interval it is proved equal to the project's centered
quadratic polynomial by cancellation of the exact Bernoulli normalization.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Canonical scalar relating the bilateral reciprocal-square Fourier series
to the centered quadratic primitive. -/
noncomputable def centeredQuadraticPrimitiveFourierNormalization : ℂ :=
  (-(2 * Real.pi * Complex.I) ^ (2 : ℕ) / Nat.factorial 2) * 2

/-- Periodic realization of the centered quadratic primitive on the real
line. -/
noncomputable def periodicCenteredQuadraticPrimitive (x : ℝ) : ℂ :=
  (centeredQuadraticPrimitiveFourierNormalization)⁻¹ *
    ∑' m : ℤ, centeredQuadraticPrimitiveFourierMode m x

/-- The canonical Fourier normalization is nonzero. -/
theorem centeredQuadraticPrimitiveFourierNormalization_ne_zero :
    centeredQuadraticPrimitiveFourierNormalization ≠ 0 := by
  have htwo : (2 : ℂ) ≠ 0 :=
    OfNat.ofNat_ne_zero 2
  have hpiReal : Real.pi ≠ 0 :=
    ne_of_gt Real.pi_pos
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hpiReal
  have hbase : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero htwo hpi) Complex.I_ne_zero
  have hpower :
      ((2 : ℂ) * Real.pi * Complex.I) ^ (2 : ℕ) ≠ 0 :=
    pow_ne_zero 2 hbase
  have hnegative :
      -(((2 : ℂ) * Real.pi * Complex.I) ^ (2 : ℕ)) ≠ 0 :=
    neg_ne_zero.mpr hpower
  have hfactorialNat : Nat.factorial 2 ≠ 0 :=
    Nat.factorial_ne_zero 2
  have hfactorial : ((Nat.factorial 2 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hfactorialNat
  unfold centeredQuadraticPrimitiveFourierNormalization
  exact mul_ne_zero (div_ne_zero hnegative hfactorial) htwo

/-- On the fundamental interval, the periodic Fourier realization equals the
centered quadratic primitive. -/
theorem periodicCenteredQuadraticPrimitive_eq
    {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    periodicCenteredQuadraticPrimitive x =
      (eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x : ℂ) := by
  let q : ℂ :=
    (eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x : ℂ)
  let N : ℂ :=
    -(2 * Real.pi * Complex.I) ^ (2 : ℕ) / Nat.factorial 2
  have hsum :
      (∑' m : ℤ, centeredQuadraticPrimitiveFourierMode m x) =
        N * ((eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x *
          2 : ℝ) : ℂ) :=
    tsum_centeredQuadraticPrimitiveFourierMode_eq hx
  have hcastProduct :
      ((eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x *
          2 : ℝ) : ℂ) = q * (2 : ℂ) :=
    map_mul Complex.ofRealHom _ _
  have hreorder : N * (q * (2 : ℂ)) = (N * (2 : ℂ)) * q := by
    exact Eq.trans
      (mul_assoc N q (2 : ℂ)).symm
      (Eq.trans
        (congrArg (fun z : ℂ => z * (2 : ℂ)) (mul_comm N q))
        (Eq.trans
          (mul_assoc q N (2 : ℂ))
          (mul_comm q (N * (2 : ℂ)))))
  have hnormalizedSum :
      (∑' m : ℤ, centeredQuadraticPrimitiveFourierMode m x) =
        centeredQuadraticPrimitiveFourierNormalization * q := by
    exact Eq.trans hsum
      (Eq.trans
        (congrArg (fun z : ℂ => N * z) hcastProduct)
        (Eq.trans hreorder rfl))
  have hcancellation :
      (centeredQuadraticPrimitiveFourierNormalization)⁻¹ *
          (centeredQuadraticPrimitiveFourierNormalization * q) = q := by
    exact Eq.trans
      (mul_assoc
        (centeredQuadraticPrimitiveFourierNormalization)⁻¹
        centeredQuadraticPrimitiveFourierNormalization q).symm
      (Eq.trans
        (congrArg (fun z : ℂ => z * q)
          (inv_mul_cancel₀ centeredQuadraticPrimitiveFourierNormalization_ne_zero))
        (one_mul q))
  unfold periodicCenteredQuadraticPrimitive
  exact Eq.trans
    (congrArg
      (fun z : ℂ =>
        (centeredQuadraticPrimitiveFourierNormalization)⁻¹ * z)
      hnormalizedSum)
    hcancellation

end
end LFunctions
end Boundary
