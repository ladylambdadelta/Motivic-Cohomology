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
  have htwo : (0 : ℝ) ≤ 2 := zero_le_two
  have hpi : 0 ≤ 2 * Real.pi :=
    mul_nonneg htwo Real.pi_pos.le
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
  have hnegQuotient : -(‖t‖ / x) ≤ 0 := neg_nonpos.mpr hquotient
  have hnegDiv : -‖t‖ / x = -(‖t‖ / x) := neg_div x ‖t‖
  have hfirst : -‖t‖ / x ≤ 0 :=
    le_trans (le_of_eq hnegDiv) hnegQuotient
  have htwo : (0 : ℝ) ≤ 2 := zero_le_two
  have hpi : 0 ≤ 2 * Real.pi :=
    mul_nonneg htwo Real.pi_pos.le
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
  have hdoubleNeg :
      -(-‖t‖ / x) = ‖t‖ / x :=
    Eq.trans (congrArg Neg.neg (neg_div x ‖t‖)) (neg_neg (‖t‖ / x))
  have hsubNormalize :
      2 * Real.pi * (m : ℝ) - (-‖t‖ / x) =
        2 * Real.pi * (m : ℝ) + -(-‖t‖ / x) :=
    sub_eq_add_neg (2 * Real.pi * (m : ℝ)) (-‖t‖ / x)
  have hdoubleNegTransport :
      2 * Real.pi * (m : ℝ) + -(-‖t‖ / x) =
        2 * Real.pi * (m : ℝ) + ‖t‖ / x :=
    congrArg (fun value : ℝ => 2 * Real.pi * (m : ℝ) + value) hdoubleNeg
  exact Eq.trans habs
    (Eq.trans
      (neg_sub (-‖t‖ / x) (2 * Real.pi * (m : ℝ)))
      (Eq.trans hsubNormalize
        (Eq.trans hdoubleNegTransport
          (add_comm (2 * Real.pi * (m : ℝ)) (‖t‖ / x)))))

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
          (neg_div x ‖t‖))))

theorem Real.div_antitone_on_pos
    {u x y : ℝ}
    (hu : 0 ≤ u) (hx : 0 < x) (hxy : x ≤ y) :
    u / y ≤ u / x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hinv : y⁻¹ ≤ x⁻¹ := inv_anti₀ hx hxy
  have hmul := mul_le_mul_of_nonneg_left hinv hu
  exact le_trans (le_of_eq (div_eq_mul_inv u y))
    (le_trans hmul (le_of_eq (div_eq_mul_inv u x).symm))

theorem Complex.logarithmicPhaseLeftInactiveDerivative_lower
    (t x left : ℝ) (m : ℤ)
    (hleft : 0 < left) (hleftx : left ≤ x) :
    Complex.logarithmicPhaseLeftInactiveGap t m left ≤
      Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x := by
  unfold Complex.logarithmicPhaseLeftInactiveGap
  have hquotient := Real.div_antitone_on_pos (norm_nonneg t) hleft hleftx
  have hnegativeRaw : -(‖t‖ / left) ≤ -(‖t‖ / x) := neg_le_neg hquotient
  have haddRaw :=
    add_le_add_left hnegativeRaw (2 * Real.pi * (-(m : ℝ)))
  have hleftNormalize :
      2 * Real.pi * (-(m : ℝ)) - ‖t‖ / left =
        2 * Real.pi * (-(m : ℝ)) + -(‖t‖ / left) :=
    sub_eq_add_neg (2 * Real.pi * (-(m : ℝ))) (‖t‖ / left)
  have hxNormalize :
      2 * Real.pi * (-(m : ℝ)) + -(‖t‖ / x) =
        2 * Real.pi * (-(m : ℝ)) - ‖t‖ / x :=
    (sub_eq_add_neg (2 * Real.pi * (-(m : ℝ))) (‖t‖ / x)).symm
  have hadd :
      2 * Real.pi * (-(m : ℝ)) - ‖t‖ / left ≤
        2 * Real.pi * (-(m : ℝ)) - ‖t‖ / x :=
    le_trans (le_of_eq hleftNormalize)
      (le_trans haddRaw (le_of_eq hxNormalize))
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
  have hnegativeRaw : -(‖t‖ / x) ≤ -(‖t‖ / right) := neg_le_neg hquotient
  have haddRaw :=
    add_le_add_left hnegativeRaw (2 * Real.pi * (-(m : ℝ)))
  have hxNormalize :
      2 * Real.pi * (-(m : ℝ)) - ‖t‖ / x =
        2 * Real.pi * (-(m : ℝ)) + -(‖t‖ / x) :=
    sub_eq_add_neg (2 * Real.pi * (-(m : ℝ))) (‖t‖ / x)
  have hrightNormalize :
      2 * Real.pi * (-(m : ℝ)) + -(‖t‖ / right) =
        2 * Real.pi * (-(m : ℝ)) - ‖t‖ / right :=
    (sub_eq_add_neg (2 * Real.pi * (-(m : ℝ))) (‖t‖ / right)).symm
  have hadd :
      2 * Real.pi * (-(m : ℝ)) - ‖t‖ / x ≤
        2 * Real.pi * (-(m : ℝ)) - ‖t‖ / right :=
    le_trans (le_of_eq hxNormalize)
      (le_trans haddRaw (le_of_eq hrightNormalize))
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
  have hdoubleNeg :
      Complex.logarithmicPhaseRightInactiveGap t m right =
        - -Complex.logarithmicPhaseRightInactiveGap t m right :=
    (neg_neg (Complex.logarithmicPhaseRightInactiveGap t m right)).symm
  have hgapToNegPhase :
      Complex.logarithmicPhaseRightInactiveGap t m right ≤
        -Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x :=
    le_trans (le_of_eq hdoubleNeg) hneg
  exact le_trans hgapToNegPhase (le_of_eq habs.symm)

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
    mul_nonneg zero_le_two (norm_nonneg t)
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
  have htransportA :
      Complex.nonstationarySecondTransformMajorant
          ‖Complex.logarithmicPhaseAdaptedCutoffAmplitude a b x‖
          ‖Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b x‖
          ‖Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b x‖
          |Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t x|
          |Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t x|
          ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ =
        Complex.nonstationarySecondTransformMajorant
          |Real.quantitativeLogarithmicBlockCutoff a b x|
          ‖Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b x‖
          ‖Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b x‖
          |Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t x|
          |Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t x|
          ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ :=
    congrArg
      (fun value : ℝ =>
        Complex.nonstationarySecondTransformMajorant value
          ‖Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b x‖
          ‖Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b x‖
          |Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t x|
          |Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t x|
          ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) hA
  have htransportA₁ := congrArg
    (fun value : ℝ =>
      Complex.nonstationarySecondTransformMajorant
        |Real.quantitativeLogarithmicBlockCutoff a b x| value
        ‖Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b x‖
        |Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t x|
        |Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t x|
        ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) hA₁
  have htransportA₂ := congrArg
    (fun value : ℝ =>
      Complex.nonstationarySecondTransformMajorant
        |Real.quantitativeLogarithmicBlockCutoff a b x|
        |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| value
        |Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t x|
        |Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t x|
        ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) hA₂
  have htransportPhase₂ := congrArg
    (fun value : ℝ =>
      Complex.nonstationarySecondTransformMajorant
        |Real.quantitativeLogarithmicBlockCutoff a b x|
        |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|
        |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x| value
        |Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t x|
        ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) hphase₂
  have htransportPhase₃ := congrArg
    (fun value : ℝ =>
      Complex.nonstationarySecondTransformMajorant
        |Real.quantitativeLogarithmicBlockCutoff a b x|
        |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|
        |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x|
        (‖t‖ / x ^ 2) value
        ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) hphase₃
  have hmajorantNormalize :=
    Eq.trans htransportA
      (Eq.trans htransportA₁
        (Eq.trans htransportA₂
          (Eq.trans htransportPhase₂ htransportPhase₃)))
  unfold Complex.logarithmicPhaseAdaptedPointwiseMajorant
  exact le_trans hcanonical (le_of_eq hmajorantNormalize)

end
end LFunctions
end Boundary
