import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.BernoulliTwoNormalization

/-!
# Fourier series of the centered quadratic Bernoulli primitive

The coefficient normalization is deliberately kept in Mathlib's canonical
form.  This avoids duplicating complex factorial and `2πi` algebra in the
analytic owner; later mode estimates see only the absolutely summable
`1 / n²` factor.
-/

namespace Boundary
namespace LFunctions

noncomputable section

local notation "π" => Real.pi

/-- The centered quadratic primitive is represented pointwise on the unit
interval by Mathlib's absolutely summable second-Bernoulli Fourier series. -/
theorem hasSum_centeredQuadraticPrimitive_fourier
    {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum
      (fun n : ℤ =>
        (1 : ℂ) / (n : ℂ) ^ (2 : ℕ) *
          fourier n (x : UnitAddCircle))
      (-(2 * π * Complex.I) ^ (2 : ℕ) / Nat.factorial 2 *
        ((eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x *
          2 : ℝ) : ℂ)) := by
  have hmathlib :=
    hasSum_one_div_pow_mul_fourier_mul_bernoulliFun
      (show 2 ≤ (2 : ℕ) from le_rfl)
      hx
  have hnormalization :
      bernoulliFun 2 x / 2 =
        eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x :=
    bernoulliFun_two_div_two_eq_centeredQuadraticPrimitive x
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    two_ne_zero
  have hreal :
      bernoulliFun 2 x =
        eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x * 2 :=
    (div_eq_iff htwo_ne).mp hnormalization
  have hcast :
      ((bernoulliFun 2 x : ℝ) : ℂ) =
        ((eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x *
          2 : ℝ) : ℂ) :=
    congrArg (fun r : ℝ => (r : ℂ)) hreal
  have hsumValue :
      (-(2 * π * Complex.I) ^ (2 : ℕ) / Nat.factorial 2 *
          ((bernoulliFun 2 x : ℝ) : ℂ)) =
        (-(2 * π * Complex.I) ^ (2 : ℕ) / Nat.factorial 2 *
          ((eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x *
            2 : ℝ) : ℂ)) :=
    congrArg
      (fun z : ℂ =>
        (-(2 * π * Complex.I) ^ (2 : ℕ) / Nat.factorial 2) * z)
      hcast
  exact Eq.subst
    (motive := fun value : ℂ =>
      HasSum
        (fun n : ℤ =>
          (1 : ℂ) / (n : ℂ) ^ (2 : ℕ) *
            fourier n (x : UnitAddCircle))
        value)
    hsumValue
    hmathlib

/-- The second-Bernoulli Fourier modes are summable at every unit coordinate. -/
theorem summable_centeredQuadraticPrimitive_fourier
    {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Summable
      (fun n : ℤ =>
        (1 : ℂ) / (n : ℂ) ^ (2 : ℕ) *
          fourier n (x : UnitAddCircle)) := by
  exact (hasSum_centeredQuadraticPrimitive_fourier hx).summable

/-- The norms of the quadratic Fourier coefficients are summable uniformly in
the unit coordinate.  This is the domination input for commuting the Fourier
series with an interval integral. -/
theorem summable_centeredQuadraticPrimitive_fourier_coefficient_norm :
    Summable
      (fun n : ℤ =>
        ‖(1 : ℂ) / (n : ℂ) ^ (2 : ℕ)‖) := by
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    And.intro (le_refl 0) zero_le_one
  have hseries :=
    (summable_centeredQuadraticPrimitive_fourier hzero_mem).norm
  have hterm :
      ∀ n : ℤ,
        ‖(1 : ℂ) / (n : ℂ) ^ (2 : ℕ) *
            fourier n ((0 : ℝ) : UnitAddCircle)‖ =
          ‖(1 : ℂ) / (n : ℂ) ^ (2 : ℕ)‖ := by
    intro n
    have hfourierNorm :
        ‖fourier n ((0 : ℝ) : UnitAddCircle)‖ = 1 :=
      Circle.abs_coe _
    exact Eq.trans
      (norm_mul
        ((1 : ℂ) / (n : ℂ) ^ (2 : ℕ))
        (fourier n ((0 : ℝ) : UnitAddCircle)))
      (Eq.trans
        (congrArg
          (fun r : ℝ =>
            ‖(1 : ℂ) / (n : ℂ) ^ (2 : ℕ)‖ * r)
          hfourierNorm)
        (mul_one ‖(1 : ℂ) / (n : ℂ) ^ (2 : ℕ)‖))
  exact hseries.congr hterm

end
end LFunctions
end Boundary
