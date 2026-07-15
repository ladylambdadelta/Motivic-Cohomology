import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.BernoulliTwoFourierSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integral interchange for the quadratic Bernoulli Fourier series

The second Bernoulli series is absolutely and uniformly convergent on the real
line.  This file packages each mode as a continuous real-line function and
owns the resulting interval-integral interchange.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

/-- A quadratic Bernoulli Fourier mode, pulled back from the unit additive
circle to the real line. -/
noncomputable def centeredQuadraticPrimitiveFourierMode
    (n : ℤ) : C(ℝ, ℂ) where
  toFun x :=
    (1 : ℂ) / (n : ℂ) ^ (2 : ℕ) *
      fourier n (x : UnitAddCircle)
  continuous_toFun :=
    continuous_const.mul
      ((map_continuous (fourier n)).comp continuous_quotient_mk')

/-- Evaluation of the bundled real-line Fourier mode. -/
theorem centeredQuadraticPrimitiveFourierMode_apply
    (n : ℤ)
    (x : ℝ) :
    centeredQuadraticPrimitiveFourierMode n x =
      (1 : ℂ) / (n : ℂ) ^ (2 : ℕ) *
        fourier n (x : UnitAddCircle) := by
  rfl

/-- Every quadratic Fourier mode has constant pointwise norm equal to the norm
of its coefficient. -/
theorem norm_centeredQuadraticPrimitiveFourierMode_apply
    (n : ℤ)
    (x : ℝ) :
    ‖centeredQuadraticPrimitiveFourierMode n x‖ =
      ‖(1 : ℂ) / (n : ℂ) ^ (2 : ℕ)‖ := by
  have hfourier : ‖fourier n (x : UnitAddCircle)‖ = 1 :=
    Circle.abs_coe _
  exact Eq.trans
    (norm_mul
      ((1 : ℂ) / (n : ℂ) ^ (2 : ℕ))
      (fourier n (x : UnitAddCircle)))
    (Eq.trans
      (congrArg
        (fun r : ℝ =>
          ‖(1 : ℂ) / (n : ℂ) ^ (2 : ℕ)‖ * r)
        hfourier)
      (mul_one ‖(1 : ℂ) / (n : ℂ) ^ (2 : ℕ)‖))

/-- Restriction to any compact interval preserves the exact coefficient norm. -/
theorem norm_centeredQuadraticPrimitiveFourierMode_restrict_uIcc
    (n : ℤ)
    (left right : ℝ) :
    ‖(centeredQuadraticPrimitiveFourierMode n).restrict
        (⟨Set.uIcc left right, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ =
      ‖(1 : ℂ) / (n : ℂ) ^ (2 : ℕ)‖ := by
  let restricted :=
    (centeredQuadraticPrimitiveFourierMode n).restrict
      (⟨Set.uIcc left right, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)
  let coefficientNorm : ℝ :=
    ‖(1 : ℂ) / (n : ℂ) ^ (2 : ℕ)‖
  have hcoefficient_nonneg : 0 ≤ coefficientNorm :=
    norm_nonneg _
  have hupper : ‖restricted‖ ≤ coefficientNorm := by
    exact (ContinuousMap.norm_le restricted hcoefficient_nonneg).mpr
      (fun x =>
        le_of_eq
          (norm_centeredQuadraticPrimitiveFourierMode_apply n x.1))
  let leftPoint :
      ↑(⟨Set.uIcc left right, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ) :=
    ⟨left, Set.left_mem_uIcc⟩
  have hpoint : ‖restricted leftPoint‖ = coefficientNorm :=
    norm_centeredQuadraticPrimitiveFourierMode_apply n left
  have hlowerPoint : ‖restricted leftPoint‖ ≤ ‖restricted‖ :=
    ContinuousMap.norm_coe_le_norm restricted leftPoint
  have hlower : coefficientNorm ≤ ‖restricted‖ :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ ‖restricted‖)
      hpoint
      hlowerPoint
  exact le_antisymm hupper hlower

/-- The compact-interval supremum norms of the quadratic Fourier modes are
summable. -/
theorem summable_centeredQuadraticPrimitiveFourierMode_restrict_uIcc_norm
    (left right : ℝ) :
    Summable
      (fun n : ℤ =>
        ‖(centeredQuadraticPrimitiveFourierMode n).restrict
          (⟨Set.uIcc left right, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
  exact summable_centeredQuadraticPrimitive_fourier_coefficient_norm.congr
    (fun n =>
      (norm_centeredQuadraticPrimitiveFourierMode_restrict_uIcc
        n left right).symm)

/-- The quadratic Fourier series may be integrated mode-by-mode on every
finite real interval. -/
theorem hasSum_intervalIntegral_centeredQuadraticPrimitiveFourierMode
    (left right : ℝ) :
    HasSum
      (fun n : ℤ =>
        ∫ x in left..right,
          centeredQuadraticPrimitiveFourierMode n x)
      (∫ x in left..right,
        ∑' n : ℤ, centeredQuadraticPrimitiveFourierMode n x) := by
  exact intervalIntegral.hasSum_intervalIntegral_of_summable_norm
    (summable_centeredQuadraticPrimitiveFourierMode_restrict_uIcc_norm
      left right)

/-- On the closed unit interval, the real-line mode `tsum` has exactly
Mathlib's canonical second-Bernoulli normalization. -/
theorem tsum_centeredQuadraticPrimitiveFourierMode_eq
    {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∑' n : ℤ, centeredQuadraticPrimitiveFourierMode n x) =
      (-(2 * Real.pi * Complex.I) ^ (2 : ℕ) / Nat.factorial 2 *
        ((eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x *
          2 : ℝ) : ℂ)) := by
  exact (hasSum_centeredQuadraticPrimitive_fourier hx).tsum_eq

/-- The normalized quadratic Bernoulli Fourier series may be integrated
mode-by-mode across a complete unit block. -/
theorem hasSum_unitIntervalIntegral_centeredQuadraticPrimitiveFourierMode :
    HasSum
      (fun n : ℤ =>
        ∫ x in (0 : ℝ)..1,
          centeredQuadraticPrimitiveFourierMode n x)
      (∫ x in (0 : ℝ)..1,
        (-(2 * Real.pi * Complex.I) ^ (2 : ℕ) / Nat.factorial 2 *
          ((eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x *
            2 : ℝ) : ℂ))) := by
  have hraw :=
    hasSum_intervalIntegral_centeredQuadraticPrimitiveFourierMode
      (0 : ℝ) 1
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 :=
    Set.uIcc_of_le zero_le_one
  have hpoint :
      Set.EqOn
        (fun x : ℝ =>
          ∑' n : ℤ, centeredQuadraticPrimitiveFourierMode n x)
        (fun x : ℝ =>
          (-(2 * Real.pi * Complex.I) ^ (2 : ℕ) / Nat.factorial 2 *
            ((eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x *
              2 : ℝ) : ℂ)))
        (Set.uIcc (0 : ℝ) 1) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 :=
      Eq.subst (motive := fun s : Set ℝ => x ∈ s) huIcc hx
    exact tsum_centeredQuadraticPrimitiveFourierMode_eq hxIcc
  have hintegral :
      (∫ x in (0 : ℝ)..1,
        ∑' n : ℤ, centeredQuadraticPrimitiveFourierMode n x) =
        (∫ x in (0 : ℝ)..1,
          (-(2 * Real.pi * Complex.I) ^ (2 : ℕ) / Nat.factorial 2 *
            ((eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x *
              2 : ℝ) : ℂ))) :=
    intervalIntegral.integral_congr
      (a := (0 : ℝ)) (b := 1) (f := fun x : ℝ =>
        ∑' n : ℤ, centeredQuadraticPrimitiveFourierMode n x)
      (g := fun x : ℝ =>
        (-(2 * Real.pi * Complex.I) ^ (2 : ℕ) / Nat.factorial 2 *
          ((eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x *
            2 : ℝ) : ℂ)))
      (μ := volume) hpoint
  exact Eq.subst
    (motive := fun value : ℂ =>
      HasSum
        (fun n : ℤ =>
          ∫ x in (0 : ℝ)..1,
            centeredQuadraticPrimitiveFourierMode n x)
        value)
    hintegral
    hraw

end
end LFunctions
end Boundary
