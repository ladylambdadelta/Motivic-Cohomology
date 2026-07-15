import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.LocalCenteredSplit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.ScalarNormalization

/-!
# Translation from local blocks to the global post-cutoff coordinate
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Adding a natural block offset before a local real coordinate agrees with
adding that offset in the real coordinate. -/
theorem natCast_add_natCast_add_real
    (C k : ℕ)
    (u : ℝ) :
    (((C + k : ℕ) : ℝ) + u) = (C : ℝ) + ((k : ℝ) + u) := by
  have hcast : (((C + k : ℕ) : ℝ)) = (C : ℝ) + (k : ℝ) :=
    Nat.cast_add C k
  exact Eq.trans
    (congrArg (fun r : ℝ => r + u) hcast)
    (add_assoc (C : ℝ) (k : ℝ) u)

/-- The logarithmic derivative amplitude is compatible with block
translation. -/
theorem boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude_natAdd
    (t : ℝ)
    (C k : ℕ)
    (u : ℝ) :
    boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
        t (C + k) u =
      boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
        t C ((k : ℝ) + u) := by
  unfold boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
  exact congrArg
    (fun x : ℝ => ((t / x : ℝ) : ℂ) * (-Complex.I))
    (natCast_add_natCast_add_real C k u)

/-- The zero-mode combined phase is compatible with block translation. -/
theorem boundaryLineOnePointRealParam_unitBlockCombinedPhase_zero_natAdd
    (t : ℝ)
    (C k : ℕ)
    (u : ℝ) :
    boundaryLineOnePointRealParam_unitBlockCombinedPhase
        t 0 (C + k) u =
      boundaryLineOnePointRealParam_unitBlockCombinedPhase
        t 0 C ((k : ℝ) + u) := by
  unfold boundaryLineOnePointRealParam_unitBlockCombinedPhase
  have hcoordinate :
      (((C + k : ℕ) : ℝ) + u) = (C : ℝ) + ((k : ℝ) + u) :=
    natCast_add_natCast_add_real C k u
  have hzeroCast : ((0 : ℤ) : ℝ) = 0 :=
    Int.cast_zero
  have hlinearLocal : 2 * Real.pi * ((0 : ℤ) : ℝ) * u = 0 := by
    exact Eq.trans
      (congrArg (fun r : ℝ => 2 * Real.pi * r * u) hzeroCast)
      (Eq.trans (congrArg (fun r : ℝ => r * u) (mul_zero (2 * Real.pi)))
        (zero_mul u))
  have hlinearGlobal :
      2 * Real.pi * ((0 : ℤ) : ℝ) * ((k : ℝ) + u) = 0 := by
    exact Eq.trans
      (congrArg
        (fun r : ℝ => 2 * Real.pi * r * ((k : ℝ) + u))
        hzeroCast)
      (Eq.trans
        (congrArg (fun r : ℝ => r * ((k : ℝ) + u))
          (mul_zero (2 * Real.pi)))
        (zero_mul ((k : ℝ) + u)))
  exact Eq.trans
    (congrArg
      (fun r : ℝ =>
        r - t * Real.log (((C + k : ℕ) : ℝ) + u))
      hlinearLocal)
    (Eq.trans
      (congrArg (fun x : ℝ => 0 - t * Real.log x) hcoordinate)
      (congrArg
        (fun r : ℝ => r - t * Real.log ((C : ℝ) + ((k : ℝ) + u)))
        hlinearGlobal.symm))

/-- The zero-mode oscillator is compatible with block translation. -/
theorem boundaryLineOnePointRealParam_zeroModeOscillation_natAdd
    (t : ℝ)
    (C k : ℕ)
    (u : ℝ) :
    Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 (C + k)) u =
      Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 C)
        ((k : ℝ) + u) := by
  unfold Complex.realPhaseOscillation
  exact congrArg
    (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ)))
    (boundaryLineOnePointRealParam_unitBlockCombinedPhase_zero_natAdd
      t C k u)

/-- The complete centered weighted derivative integrand translates from a
local block to the global post-cutoff coordinate. -/
theorem boundaryLineOnePointRealParam_centeredDerivativeIntegrand_natAdd
    (t : ℝ)
    (C k : ℕ)
    {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
          t (C + k) u *
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 (C + k)) u) *
        eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u =
      (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
          t C ((k : ℝ) + u) *
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 C)
          ((k : ℝ) + u)) *
        periodicCenteredQuadraticPrimitive ((k : ℝ) + u) := by
  have hamplitude :
      boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
          t (C + k) u =
        boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
          t C ((k : ℝ) + u) :=
    boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude_natAdd
      t C k u
  have hoscillation :
      Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 (C + k)) u =
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 C)
          ((k : ℝ) + u) :=
    boundaryLineOnePointRealParam_zeroModeOscillation_natAdd t C k u
  have hcentered :
      eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u =
        periodicCenteredQuadraticPrimitive ((k : ℝ) + u) := by
    unfold eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex
    exact (periodicCenteredQuadraticPrimitive_natAdd_eq k hu).symm
  exact congrArg₂ Mul.mul
    (congrArg₂ Mul.mul hamplitude hoscillation)
    hcentered

end
end LFunctions
end Boundary
