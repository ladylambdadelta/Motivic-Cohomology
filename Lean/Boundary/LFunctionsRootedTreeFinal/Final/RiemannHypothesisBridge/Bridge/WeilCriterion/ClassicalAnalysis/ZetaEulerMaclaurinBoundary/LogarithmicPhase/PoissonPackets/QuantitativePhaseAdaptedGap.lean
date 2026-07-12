import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedCalculus

/-!
# Explicit derivative gaps for phase-adapted logarithmic packets

The Fourier mode is kept inside the phase.  Positive modes therefore have no
stationary point, while a negative mode is nonstationary precisely when its
stationary center lies outside the cutoff support.  The lemmas below expose
the resulting gaps in forms suitable for the two-step majorant.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhasePositiveModeGap (m : ℤ) : ℝ :=
  2 * Real.pi * (m : ℝ)

def Complex.logarithmicPhaseLeftInactiveGap
    (t : ℝ) (m : ℤ) (left : ℝ) : ℝ :=
  2 * Real.pi * (-(m : ℝ)) - ‖t‖ / left

def Complex.logarithmicPhaseRightInactiveGap
    (t : ℝ) (m : ℤ) (right : ℝ) : ℝ :=
  ‖t‖ / right - 2 * Real.pi * (-(m : ℝ))

theorem Complex.logarithmicPhasePositiveModeGap_nonneg
    (m : ℤ) (hm : 0 ≤ m) :
    0 ≤ Complex.logarithmicPhasePositiveModeGap m := by
  unfold Complex.logarithmicPhasePositiveModeGap
  have hpi : 0 ≤ 2 * Real.pi :=
    mul_nonneg (by exact OfNat.zero_le 2) Real.pi_pos.le
  have hmReal : 0 ≤ (m : ℝ) := Int.cast_nonneg.mpr hm
  exact mul_nonneg hpi hmReal

theorem Complex.logarithmicPhasePositiveModeDerivative_nonpos
    (t x : ℝ) (m : ℤ)
    (hx : 0 < x) (hm : 0 ≤ m) :
    Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x ≤ 0 := by
  unfold Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative
  have ht : 0 ≤ ‖t‖ := norm_nonneg t
  have hxle : 0 ≤ x := hx.le
  have hquotient : 0 ≤ ‖t‖ / x := div_nonneg ht hxle
  have hfirst : -‖t‖ / x ≤ 0 := neg_nonpos.mpr hquotient
  have hpi : 0 ≤ 2 * Real.pi :=
    mul_nonneg (by exact OfNat.zero_le 2) Real.pi_pos.le
  have hmReal : 0 ≤ (m : ℝ) := Int.cast_nonneg.mpr hm
  have hfrequency : 0 ≤ 2 * Real.pi * (m : ℝ) := mul_nonneg hpi hmReal
  exact sub_nonpos.mpr (le_trans hfirst hfrequency)

theorem Complex.abs_logarithmicPhasePositiveModeDerivative
    (t x : ℝ) (m : ℤ)
    (hx : 0 < x) (hm : 0 ≤ m) :
    |Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x| =
      ‖t‖ / x + Complex.logarithmicPhasePositiveModeGap m := by
  have hnonpos :=
    Complex.logarithmicPhasePositiveModeDerivative_nonpos t x m hx hm
  have habs := abs_of_nonpos hnonpos
  unfold Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative at habs
  unfold Complex.logarithmicPhasePositiveModeGap
  exact Eq.trans habs
    (Eq.trans
      (neg_sub (-‖t‖ / x) (2 * Real.pi * (m : ℝ)))
      (congrArg (fun value : ℝ => value + 2 * Real.pi * (m : ℝ))
        (neg_div (-‖t‖) x).trans
          (congrArg (fun value : ℝ => value / x) (neg_neg ‖t‖)))))

theorem Complex.logarithmicPhasePositiveModeDerivative_gap
    (t x : ℝ) (m : ℤ)
    (hx : 0 < x) (hm : 0 ≤ m) :
    Complex.logarithmicPhasePositiveModeGap m ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ := by
  have habs :=
    Complex.abs_logarithmicPhasePositiveModeDerivative t x m hx hm
  have ht : 0 ≤ ‖t‖ := norm_nonneg t
  have hxle : 0 ≤ x := hx.le
  have hquotient : 0 ≤ ‖t‖ / x := div_nonneg ht hxle
  have hle :
      Complex.logarithmicPhasePositiveModeGap m ≤
        ‖t‖ / x + Complex.logarithmicPhasePositiveModeGap m :=
    le_add_of_nonneg_left hquotient
  exact le_trans hle (le_of_eq habs.symm)

theorem Complex.logarithmicPhaseNegativeModeDerivative_normalize
    (t x : ℝ) (m : ℤ) :
    Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x =
      2 * Real.pi * (-(m : ℝ)) - ‖t‖ / x := by
  unfold Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative
  have hfrequency :
      -(2 * Real.pi * (m : ℝ)) = 2 * Real.pi * (-(m : ℝ)) :=
    (mul_neg (2 * Real.pi) (m : ℝ)).symm
  exact Eq.trans (sub_eq_add_neg (-‖t‖ / x) (2 * Real.pi * (m : ℝ)))
    (Eq.trans
      (congrArg (fun value : ℝ => -‖t‖ / x + value) hfrequency)
      (Eq.trans (add_comm (-‖t‖ / x) (2 * Real.pi * (-(m : ℝ))))
        (congrArg (fun value : ℝ => 2 * Real.pi * (-(m : ℝ)) + value)
          (neg_div ‖t‖ x).symm)))

theorem Real.div_antitone_on_pos
    {u x y : ℝ}
    (hu : 0 ≤ u) (hx : 0 < x) (hxy : x ≤ y) :
    u / y ≤ u / x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hinv : y⁻¹ ≤ x⁻¹ := inv_anti₀ hx hy hxy
  have hmul := mul_le_mul_of_nonneg_left hinv hu
  exact Eq.subst (div_eq_mul_inv u y).symm
    (Eq.subst (div_eq_mul_inv u x).symm hmul)

theorem Complex.logarithmicPhaseLeftInactiveDerivative_lower
    (t x left : ℝ) (m : ℤ)
    (hleft : 0 < left) (hleftx : left ≤ x) :
    Complex.logarithmicPhaseLeftInactiveGap t m left ≤
      Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x := by
  unfold Complex.logarithmicPhaseLeftInactiveGap
  have hquotient := Real.div_antitone_on_pos (norm_nonneg t) hleft hleftx
  have hnegative : -‖t‖ / left ≤ -‖t‖ / x := neg_le_neg hquotient
  have hadd := add_le_add_left hnegative (2 * Real.pi * (-(m : ℝ)))
  have hnormalize :=
    Complex.logarithmicPhaseNegativeModeDerivative_normalize t x m
  exact le_trans hadd (le_of_eq hnormalize.symm)

theorem Complex.logarithmicPhaseLeftInactiveDerivative_gap
    (t x left : ℝ) (m : ℤ)
    (hleft : 0 < left) (hleftx : left ≤ x)
    (hgap : 0 ≤ Complex.logarithmicPhaseLeftInactiveGap t m left) :
    Complex.logarithmicPhaseLeftInactiveGap t m left ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ := by
  have hlower :=
    Complex.logarithmicPhaseLeftInactiveDerivative_lower
      t x left m hleft hleftx
  have hphaseNonneg := le_trans hgap hlower
  have habs := abs_of_nonneg hphaseNonneg
  exact le_trans hlower (le_of_eq habs.symm)

theorem Complex.logarithmicPhaseRightInactiveDerivative_upper
    (t x right : ℝ) (m : ℤ)
    (hx : 0 < x) (hxright : x ≤ right) :
    Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x ≤
      -Complex.logarithmicPhaseRightInactiveGap t m right := by
  unfold Complex.logarithmicPhaseRightInactiveGap
  have hquotient := Real.div_antitone_on_pos (norm_nonneg t) hx hxright
  have hnegative : -‖t‖ / x ≤ -‖t‖ / right := neg_le_neg hquotient
  have hadd := add_le_add_left hnegative (2 * Real.pi * (-(m : ℝ)))
  have hnormalize :=
    Complex.logarithmicPhaseNegativeModeDerivative_normalize t x m
  have htarget :
      2 * Real.pi * (-(m : ℝ)) - ‖t‖ / right =
        -(‖t‖ / right - 2 * Real.pi * (-(m : ℝ))) := by
    exact (neg_sub (‖t‖ / right) (2 * Real.pi * (-(m : ℝ)))).symm
  exact le_trans (le_of_eq hnormalize) (le_trans hadd (le_of_eq htarget))

theorem Complex.logarithmicPhaseRightInactiveDerivative_gap
    (t x right : ℝ) (m : ℤ)
    (hx : 0 < x) (hxright : x ≤ right)
    (hgap : 0 ≤ Complex.logarithmicPhaseRightInactiveGap t m right) :
    Complex.logarithmicPhaseRightInactiveGap t m right ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ := by
  have hupper :=
    Complex.logarithmicPhaseRightInactiveDerivative_upper
      t x right m hx hxright
  have hphaseNonpos :
      Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x ≤ 0 :=
    le_trans hupper (neg_nonpos.mpr hgap)
  have habs := abs_of_nonpos hphaseNonpos
  have hneg := neg_le_neg hupper
  exact le_trans hneg (le_of_eq habs.symm)

theorem Complex.abs_logarithmicPhaseAdaptedSecondDerivative
    (t x : ℝ) (hx : 0 < x) :
    |Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t x| =
      ‖t‖ / x ^ 2 := by
  unfold Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative
  have hxpow : 0 ≤ x ^ 2 := sq_nonneg x
  have hquotient : 0 ≤ ‖t‖ / x ^ 2 :=
    div_nonneg (norm_nonneg t) hxpow
  exact abs_of_nonneg hquotient

theorem Complex.abs_logarithmicPhaseAdaptedThirdDerivative
    (t x : ℝ) (hx : 0 < x) :
    |Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t x| =
      2 * ‖t‖ / x ^ 3 := by
  unfold Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative
  have hxpow : 0 ≤ x ^ 3 := (pow_nonneg hx.le 3)
  have hnumerator : 0 ≤ 2 * ‖t‖ :=
    mul_nonneg (by exact OfNat.zero_le 2) (norm_nonneg t)
  have hquotient : 0 ≤ 2 * ‖t‖ / x ^ 3 :=
    div_nonneg hnumerator hxpow
  exact Eq.trans (abs_neg (2 * ‖t‖ / x ^ 3)) (abs_of_nonneg hquotient)

def Complex.logarithmicPhaseAdaptedPointwiseMajorant
    (t : ℝ) (a b m : ℤ) (x : ℝ) : ℝ :=
  Complex.nonstationarySecondTransformMajorant
    |Real.quantitativeLogarithmicBlockCutoff a b x|
    |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|
    |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x|
    (‖t‖ / x ^ 2)
    (2 * ‖t‖ / x ^ 3)
    ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖

theorem Complex.logarithmicPhaseAdaptedSecondTransform_pointwise_le
    (t : ℝ) (a b m : ℤ) (x : ℝ)
    (hx : 0 < x) :
    ‖Complex.nonstationarySecondTransformedAmplitude
        (Complex.nonstationaryFirstTransformedDerivativeExplicit
          (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
          (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
          (Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b)
          (Complex.realPhaseIntegrationCoefficient
            (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
          (Complex.realPhaseIntegrationCoefficientDerivative
            (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
            (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t))
          (Complex.realPhaseIntegrationCoefficientSecondDerivative
            (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
            (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)
            (Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t)))
        (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
        (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
        (Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
        (Complex.realPhaseIntegrationCoefficientDerivative
          (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
          (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)) x‖ ≤
      Complex.logarithmicPhaseAdaptedPointwiseMajorant t a b m x := by
  have hcanonical :=
    Complex.norm_nonstationarySecondTransform_le_canonicalMajorant
      (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
      (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
      (Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b)
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
      (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)
      (Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t) x
  have hA := Complex.norm_logarithmicPhaseAdaptedCutoffAmplitude a b x
  have hA₁ := Complex.norm_logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b x
  have hA₂ := Complex.norm_logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b x
  have hphase₂ := Complex.abs_logarithmicPhaseAdaptedSecondDerivative t x hx
  have hphase₃ := Complex.abs_logarithmicPhaseAdaptedThirdDerivative t x hx
  unfold Complex.logarithmicPhaseAdaptedPointwiseMajorant
  exact le_trans hcanonical
    (le_of_eq
      (congrArg
        (fun values : ℝ × ℝ × ℝ × ℝ × ℝ =>
          Complex.nonstationarySecondTransformMajorant
            values.1 values.2.1 values.2.2.1 values.2.2.2.1 values.2.2.2.2
            ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖)
        (Prod.ext hA
          (Prod.ext hA₁
            (Prod.ext hA₂ (Prod.ext hphase₂ hphase₃))))))

end
end LFunctions
end Boundary
