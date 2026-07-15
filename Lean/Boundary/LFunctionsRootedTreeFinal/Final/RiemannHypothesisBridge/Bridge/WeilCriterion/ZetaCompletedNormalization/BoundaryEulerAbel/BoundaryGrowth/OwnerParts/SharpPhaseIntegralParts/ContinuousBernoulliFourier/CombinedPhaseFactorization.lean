import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.WeightedIntegralInterchange

/-!
# Factorization of a combined Fourier/logarithmic phase
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The additive-circle Fourier character is the exponential of the real
linear phase in the combined-phase convention. -/
theorem fourier_eq_realPhaseLinearOscillation
    (m : ℤ)
    (u : ℝ) :
    fourier m (u : UnitAddCircle) =
      Complex.exp
        (Complex.I * (((2 * Real.pi * (m : ℝ) * u : ℝ)) : ℂ)) := by
  have hfourier :=
    fourier_coe_apply (T := (1 : ℝ)) (n := m) (x := u)
  have hdivision :
      (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (u : ℂ)) / (1 : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (u : ℂ) :=
    div_one _
  have hcastLinear :
      (((2 * Real.pi * (m : ℝ) * u : ℝ)) : ℂ) =
        ((2 : ℂ) * (Real.pi : ℂ)) * (m : ℂ) * (u : ℂ) := by
    exact Eq.trans
      (map_mul Complex.ofRealHom (2 * Real.pi * (m : ℝ)) u)
      (Eq.trans
        (congrArg (fun z : ℂ => z * (u : ℂ))
          (map_mul Complex.ofRealHom (2 * Real.pi) (m : ℝ)))
        (congrArg
          (fun z : ℂ => (z * (m : ℂ)) * (u : ℂ))
          (map_mul Complex.ofRealHom 2 Real.pi)))
  have hreorder :
      2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (u : ℂ) =
        Complex.I *
          (((2 : ℂ) * (Real.pi : ℂ)) * (m : ℂ) * (u : ℂ)) := by
    let p : ℂ := (2 : ℂ) * (Real.pi : ℂ)
    let z : ℂ := (m : ℂ)
    let w : ℂ := (u : ℂ)
    calc
      p * Complex.I * z * w = (Complex.I * p) * z * w := by
        exact congrArg (fun value : ℂ => value * z * w)
          (mul_comm p Complex.I)
      _ = Complex.I * (p * z) * w := by
        exact congrArg (fun value : ℂ => value * w)
          (mul_assoc Complex.I p z)
      _ = Complex.I * (p * z * w) :=
        mul_assoc Complex.I (p * z) w
  have hexponent :
      (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (u : ℂ)) / (1 : ℂ) =
        Complex.I * (((2 * Real.pi * (m : ℝ) * u : ℝ)) : ℂ) :=
    Eq.trans hdivision
      (Eq.trans hreorder
        (congrArg (fun z : ℂ => Complex.I * z) hcastLinear.symm))
  exact Eq.trans hfourier (congrArg Complex.exp hexponent)

/-- The combined oscillator factors into its Fourier character and its
zero-mode logarithmic oscillator. -/
theorem boundaryLineOnePointRealParam_unitBlockCombinedOscillation_factor
    (t : ℝ)
    (m : ℤ)
    (a : ℕ)
    (u : ℝ) :
    Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) u =
      fourier m (u : UnitAddCircle) *
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u := by
  let linear : ℝ := 2 * Real.pi * (m : ℝ) * u
  let logarithmic : ℝ := t * Real.log ((a : ℝ) + u)
  have hcombined :
      boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a u =
        linear - logarithmic :=
    rfl
  have hzero :
      boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a u =
        -logarithmic := by
    unfold boundaryLineOnePointRealParam_unitBlockCombinedPhase
    have hcastZero : ((0 : ℤ) : ℝ) = 0 :=
      Int.cast_zero
    exact Eq.trans
      (congrArg
        (fun r : ℝ => 2 * Real.pi * r * u - t * Real.log ((a : ℝ) + u))
        hcastZero)
      (Eq.trans
        (congrArg
          (fun r : ℝ => r - t * Real.log ((a : ℝ) + u))
          (Eq.trans
            (congrArg (fun r : ℝ => r * u) (mul_zero (2 * Real.pi)))
            (zero_mul u)))
        (zero_sub logarithmic))
  have hcastSub :
      ((linear - logarithmic : ℝ) : ℂ) =
        (linear : ℂ) - (logarithmic : ℂ) :=
    map_sub Complex.ofRealHom linear logarithmic
  have hexponentSplit :
      Complex.I * ((linear - logarithmic : ℝ) : ℂ) =
        Complex.I * (linear : ℂ) +
          Complex.I * ((-logarithmic : ℝ) : ℂ) := by
    have hcastNeg : ((-logarithmic : ℝ) : ℂ) = -(logarithmic : ℂ) :=
      map_neg Complex.ofRealHom logarithmic
    exact Eq.trans
      (congrArg (fun z : ℂ => Complex.I * z) hcastSub)
      (Eq.trans
        (mul_sub Complex.I (linear : ℂ) (logarithmic : ℂ))
        (Eq.trans
          (sub_eq_add_neg
            (Complex.I * (linear : ℂ))
            (Complex.I * (logarithmic : ℂ)))
          (congrArg
            (fun z : ℂ => Complex.I * (linear : ℂ) + z)
            (Eq.trans
              (mul_neg Complex.I (logarithmic : ℂ)).symm
              (congrArg (fun z : ℂ => Complex.I * z) hcastNeg.symm)))))
  have hexponential :
      Complex.exp (Complex.I * ((linear - logarithmic : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (linear : ℂ)) *
          Complex.exp (Complex.I * ((-logarithmic : ℝ) : ℂ)) :=
    Eq.trans (congrArg Complex.exp hexponentSplit)
      (Complex.exp_add _ _)
  have hfourier :
      Complex.exp (Complex.I * (linear : ℂ)) =
        fourier m (u : UnitAddCircle) :=
    (fourier_eq_realPhaseLinearOscillation m u).symm
  unfold Complex.realPhaseOscillation
  exact Eq.trans
    (congrArg
      (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ)))
      hcombined)
    (Eq.trans hexponential
      (congrArg₂ Mul.mul hfourier
        (congrArg
          (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ)))
          hzero.symm)))

end
end LFunctions
end Boundary
