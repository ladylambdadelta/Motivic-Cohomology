import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedPacketEstimate

/-!
# Integration of the phase-adapted pointwise majorant

The canonical four-term majorant is continuous on every positive compact
interval.  This owner integrates the pointwise transform estimate and thereby
removes the complex transformed amplitude from the public packet bound.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

theorem Complex.continuousAt_logarithmicPhaseAdaptedTwistedPhaseDerivative
    (t : ℝ) (m : ℤ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m) x := by
  exact (Complex.hasDerivAt_logarithmicPhaseAdaptedTwistedPhaseDerivative
    t m hx).continuousAt

theorem Complex.continuousAt_logarithmicPhaseAdaptedCurvatureDensity
    (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun y : ℝ => ‖t‖ / y ^ 2) x := by
  have hpower : ContinuousAt (fun y : ℝ => y ^ 2) x :=
    continuousAt_id.pow 2
  have hnonzero : x ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hx)
  exact continuousAt_const.div hpower hnonzero

theorem Complex.continuousAt_logarithmicPhaseAdaptedThirdDensity
    (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun y : ℝ => 2 * ‖t‖ / y ^ 3) x := by
  have hpower : ContinuousAt (fun y : ℝ => y ^ 3) x :=
    continuousAt_id.pow 3
  have hnonzero : x ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hx)
  exact continuousAt_const.div hpower hnonzero

theorem Complex.continuousAt_norm_logarithmicPhaseAdaptedDerivative
    (t : ℝ) (m : ℤ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt
      (fun y : ℝ =>
        ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m y‖) x := by
  exact (Complex.continuousAt_logarithmicPhaseAdaptedTwistedPhaseDerivative
    t m hx).norm

theorem Complex.continuousAt_abs_quantitativeLogarithmicBlockCutoff
    (a b : ℤ) (x : ℝ) :
    ContinuousAt
      (fun y : ℝ => |Real.quantitativeLogarithmicBlockCutoff a b y|) x := by
  exact (Real.contDiff_quantitativeLogarithmicBlockCutoff a b)
    .continuous.continuousAt.abs

theorem Complex.continuousAt_abs_quantitativeLogarithmicBlockCutoffDerivative
    (a b : ℤ) (x : ℝ) :
    ContinuousAt
      (fun y : ℝ =>
        |Real.quantitativeLogarithmicBlockCutoffDerivative a b y|) x := by
  exact (Real.contDiff_quantitativeLogarithmicBlockCutoffDerivative a b)
    .continuous.continuousAt.abs

theorem Complex.continuousAt_abs_quantitativeLogarithmicBlockCutoffSecondDerivative
    (a b : ℤ) (x : ℝ) :
    ContinuousAt
      (fun y : ℝ =>
        |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b y|) x := by
  exact (Real.contDiff_quantitativeLogarithmicBlockCutoffSecondDerivative a b)
    .continuous.continuousAt.abs

theorem Complex.continuousAt_nonstationarySecondTransformMajorant_comp
    {A A₁ A₂ v w g : ℝ → ℝ} {x : ℝ}
    (hA : ContinuousAt A x)
    (hA₁ : ContinuousAt A₁ x)
    (hA₂ : ContinuousAt A₂ x)
    (hv : ContinuousAt v x)
    (hw : ContinuousAt w x)
    (hg : ContinuousAt g x)
    (hgne : g x ≠ 0) :
    ContinuousAt
      (fun y : ℝ =>
        Complex.nonstationarySecondTransformMajorant
          (A y) (A₁ y) (A₂ y) (v y) (w y) (g y)) x := by
  unfold Complex.nonstationarySecondTransformMajorant
  have hgTwo : ContinuousAt (fun y : ℝ => g y ^ 2) x := hg.pow 2
  have hgThree : ContinuousAt (fun y : ℝ => g y ^ 3) x := hg.pow 3
  have hgFour : ContinuousAt (fun y : ℝ => g y ^ 4) x := hg.pow 4
  have hgTwoNe : g x ^ 2 ≠ 0 := pow_ne_zero 2 hgne
  have hgThreeNe : g x ^ 3 ≠ 0 := pow_ne_zero 3 hgne
  have hgFourNe : g x ^ 4 ≠ 0 := pow_ne_zero 4 hgne
  have hfirst := hA₂.div hgTwo hgTwoNe
  have hsecondNumerator := (continuousAt_const.mul hA₁).mul hv
  have hsecond := hsecondNumerator.div hgThree hgThreeNe
  have hthirdNumerator := hA.mul hw
  have hthird := hthirdNumerator.div hgThree hgThreeNe
  have hfourthNumerator :=
    (continuousAt_const.mul hA).mul (hv.pow 2)
  have hfourth := hfourthNumerator.div hgFour hgFourNe
  exact ((hfirst.add hsecond).add hthird).add hfourth

theorem Complex.continuousAt_logarithmicPhaseAdaptedPointwiseMajorant
    (t : ℝ) (a b m : ℤ) {x : ℝ}
    (hx : 0 < x)
    (hphase :
      Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x ≠ 0) :
    ContinuousAt
      (Complex.logarithmicPhaseAdaptedPointwiseMajorant t a b m) x := by
  unfold Complex.logarithmicPhaseAdaptedPointwiseMajorant
  have hA :=
    Complex.continuousAt_abs_quantitativeLogarithmicBlockCutoff a b x
  have hA₁ :=
    Complex.continuousAt_abs_quantitativeLogarithmicBlockCutoffDerivative a b x
  have hA₂ :=
    Complex.continuousAt_abs_quantitativeLogarithmicBlockCutoffSecondDerivative
      a b x
  have hv :=
    Complex.continuousAt_logarithmicPhaseAdaptedCurvatureDensity t hx
  have hw :=
    Complex.continuousAt_logarithmicPhaseAdaptedThirdDensity t hx
  have hg :=
    Complex.continuousAt_norm_logarithmicPhaseAdaptedDerivative t m hx
  have hgNe :
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hphase
  exact Complex.continuousAt_nonstationarySecondTransformMajorant_comp
    hA hA₁ hA₂ hv hw hg hgNe

theorem Complex.continuousOn_logarithmicPhaseAdaptedPointwiseMajorant_of_gap
    (t : ℝ) (a b m : ℤ) (gap : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hgap : 0 < gap)
    (hlower : ∀ x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ContinuousOn
      (Complex.logarithmicPhaseAdaptedPointwiseMajorant t a b m)
      [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]] := by
  intro x hx
  have hxPos :=
    Complex.logarithmicPhaseQuantitativeSupport_mem_positive a b ha hab hx
  have hphase :=
    Complex.logarithmicPhaseAdaptedDerivative_ne_zero_of_gap
      t m x gap hgap (hlower x hx)
  exact (Complex.continuousAt_logarithmicPhaseAdaptedPointwiseMajorant
    t a b m hxPos hphase).continuousWithinAt

theorem Complex.intervalIntegrable_logarithmicPhaseAdaptedPointwiseMajorant
    (t : ℝ) (a b m : ℤ) (gap : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hgap : 0 < gap)
    (hlower : ∀ x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    IntervalIntegrable
      (Complex.logarithmicPhaseAdaptedPointwiseMajorant t a b m)
      volume
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b) := by
  exact (Complex.continuousOn_logarithmicPhaseAdaptedPointwiseMajorant_of_gap
    t a b m gap ha hab hgap hlower).intervalIntegrable

theorem Complex.norm_logarithmicPhaseAdaptedPacket_le_pointwiseMajorantIntegral
    (t : ℝ) (a b m : ℤ) (gap : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hgap : 0 < gap)
    (hlower : ∀ x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        Complex.logarithmicPhaseAdaptedPointwiseMajorant t a b m x := by
  have hpacket :=
    Complex.norm_logarithmicPhaseAdaptedPacket_le_secondTransform
      t a b m gap ha hab hgap hlower
  have hleftRight :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hsecondIntegrable :=
    (Complex.continuousOn_logarithmicPhaseAdaptedSecondTransform
      t a b m gap ha hab hgap hlower).norm.intervalIntegrable
  have hmajorantIntegrable :=
    Complex.intervalIntegrable_logarithmicPhaseAdaptedPointwiseMajorant
      t a b m gap ha hab hgap hlower
  have hpointwise : ∀ x ∈ Set.Icc
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b),
      ‖Complex.logarithmicPhaseAdaptedSecondTransform t a b m x‖ ≤
        Complex.logarithmicPhaseAdaptedPointwiseMajorant t a b m x := by
    intro x hx
    have hxU : x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]] :=
      (Set.uIcc_of_le hleftRight).mpr hx
    have hxPos :=
      Complex.logarithmicPhaseQuantitativeSupport_mem_positive a b ha hab hxU
    unfold Complex.logarithmicPhaseAdaptedSecondTransform
    exact Complex.logarithmicPhaseAdaptedSecondTransform_pointwise_le
      t a b m x hxPos
  have hintegral := intervalIntegral.integral_mono_on hleftRight
    hsecondIntegrable hmajorantIntegrable hpointwise
  exact le_trans hpacket hintegral

end
end LFunctions
end Boundary
