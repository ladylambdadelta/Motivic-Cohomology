import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionVariation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeCrossings
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeFarFrequency

/-!
# Pointwise quantitative packet decay

This owner connects the exact Poisson packet normalization to the generic
two-step linear Fourier estimate.  The logarithmic oscillation is absorbed
into the compact amplitude; the remaining oscillation has real linear phase
`(-2 * π * m) * x`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

theorem Complex.logarithmicPhasePoissonAngularFrequency_mul
    (m : ℤ) (x : ℝ) :
    Complex.logarithmicPhasePoissonAngularFrequency m * x =
      -(2 * Real.pi * (m : ℝ) * x) := by
  unfold Complex.logarithmicPhasePoissonAngularFrequency
  exact neg_mul (2 * Real.pi * (m : ℝ)) x

theorem Complex.logarithmicPhasePoissonAngularFrequency_phase_value
    (m : ℤ) (x : ℝ) :
    Complex.linearFourierPhase
        (Complex.logarithmicPhasePoissonAngularFrequency m) x =
      -(2 * Real.pi * (m : ℝ) * x) := by
  unfold Complex.linearFourierPhase
  exact Complex.logarithmicPhasePoissonAngularFrequency_mul m x

theorem Complex.logarithmicPhaseFrequencyTwist_eq_phase_add_linear
    (t : ℝ) (m : ℤ) (x : ℝ) :
    Complex.realPhaseFrequencyTwist
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        m x =
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x +
        Complex.linearFourierPhase
          (Complex.logarithmicPhasePoissonAngularFrequency m) x := by
  unfold Complex.realPhaseFrequencyTwist
  have hlinear :=
    Complex.logarithmicPhasePoissonAngularFrequency_phase_value m x
  calc
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x -
        2 * Real.pi * (m : ℝ) * x =
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x +
        (-(2 * Real.pi * (m : ℝ) * x)) :=
      sub_eq_add_neg _ _
    _ = Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x +
        Complex.linearFourierPhase
          (Complex.logarithmicPhasePoissonAngularFrequency m) x :=
      congrArg
        (fun value : ℝ =>
          Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x + value)
        hlinear.symm

theorem Complex.logarithmicPhaseFrequencyTwist_exponent_eq_add
    (t : ℝ) (m : ℤ) (x : ℝ) :
    Complex.I *
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m x : ℂ) =
      Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x : ℂ) +
        Complex.I *
          (Complex.linearFourierPhase
            (Complex.logarithmicPhasePoissonAngularFrequency m) x : ℂ) := by
  have hreal :=
    Complex.logarithmicPhaseFrequencyTwist_eq_phase_add_linear t m x
  have hcast :
      (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m x : ℂ) =
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x : ℂ) +
          (Complex.linearFourierPhase
            (Complex.logarithmicPhasePoissonAngularFrequency m) x : ℂ) :=
    (congrArg (fun value : ℝ => (value : ℂ)) hreal).trans
      (Complex.ofReal_add _ _)
  exact
    (congrArg (fun value : ℂ => Complex.I * value) hcast).trans
      (mul_add Complex.I _ _)

theorem Complex.logarithmicPhaseFrequencyTwist_exp_eq_product
    (t : ℝ) (m : ℤ) (x : ℝ) :
    Complex.exp
        (Complex.I *
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m x : ℂ)) =
      Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x : ℂ)) *
        Complex.realPhaseOscillation
          (Complex.linearFourierPhase
            (Complex.logarithmicPhasePoissonAngularFrequency m)) x := by
  have hexponent :=
    Complex.logarithmicPhaseFrequencyTwist_exponent_eq_add t m x
  have hexponential := congrArg Complex.exp hexponent
  unfold Complex.realPhaseOscillation
  exact hexponential.trans (Complex.exp_add _ _)

theorem Complex.logarithmicPhaseQuantitativeAmplitude_mul_linearOscillation
    (t : ℝ) (a b m : ℤ) (x : ℝ) :
    Complex.logarithmicPhaseQuantitativeAmplitude t a b x *
        Complex.realPhaseOscillation
          (Complex.linearFourierPhase
            (Complex.logarithmicPhasePoissonAngularFrequency m)) x =
      Real.quantitativeLogarithmicBlockCutoff a b x •
        Complex.exp
          (Complex.I *
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m x : ℂ)) := by
  unfold Complex.logarithmicPhaseQuantitativeAmplitude
  unfold Complex.phaseCutoffFunction
  have hexponential :=
    Complex.logarithmicPhaseFrequencyTwist_exp_eq_product t m x
  have hscalarProduct :
      (Real.quantitativeLogarithmicBlockCutoff a b x •
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x : ℂ))) *
          Complex.realPhaseOscillation
            (Complex.linearFourierPhase
              (Complex.logarithmicPhasePoissonAngularFrequency m)) x =
        Real.quantitativeLogarithmicBlockCutoff a b x •
          (Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x : ℂ)) *
            Complex.realPhaseOscillation
              (Complex.linearFourierPhase
                (Complex.logarithmicPhasePoissonAngularFrequency m)) x) := by
    have hleftScalar :
        Real.quantitativeLogarithmicBlockCutoff a b x •
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t x : ℂ)) =
          (Real.quantitativeLogarithmicBlockCutoff a b x : ℂ) *
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t x : ℂ)) :=
      Complex.real_smul
    have hrightScalar :
        Real.quantitativeLogarithmicBlockCutoff a b x •
            (Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                    t x : ℂ)) *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase
                  (Complex.logarithmicPhasePoissonAngularFrequency m)) x) =
          (Real.quantitativeLogarithmicBlockCutoff a b x : ℂ) *
            (Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                    t x : ℂ)) *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase
                  (Complex.logarithmicPhasePoissonAngularFrequency m)) x) :=
      Complex.real_smul
    exact
      (congrArg
        (fun value : ℂ =>
          value *
            Complex.realPhaseOscillation
              (Complex.linearFourierPhase
                (Complex.logarithmicPhasePoissonAngularFrequency m)) x)
        hleftScalar).trans
        ((mul_assoc
          (Real.quantitativeLogarithmicBlockCutoff a b x : ℂ)
          (Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                t x : ℂ)))
          (Complex.realPhaseOscillation
            (Complex.linearFourierPhase
              (Complex.logarithmicPhasePoissonAngularFrequency m)) x)).trans
          hrightScalar.symm)
  exact
    hscalarProduct.trans
      (congrArg
        (fun value : ℂ =>
          Real.quantitativeLogarithmicBlockCutoff a b x • value)
        hexponential.symm)

theorem Complex.phaseCutoffFrequencyTwistIntegrand_eq_quantitativeAmplitude_mul_linear
    (t : ℝ) (a b m : ℤ) (x : ℝ) :
    Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.quantitativeLogarithmicBlockCutoff a b) m x =
      Complex.logarithmicPhaseQuantitativeAmplitude t a b x *
        Complex.realPhaseOscillation
          (Complex.linearFourierPhase
            (Complex.logarithmicPhasePoissonAngularFrequency m)) x := by
  unfold Complex.phaseCutoffFrequencyTwistIntegrand
  exact
    (Complex.logarithmicPhaseQuantitativeAmplitude_mul_linearOscillation
      t a b m x).symm

theorem Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_amplitude_linear_interval
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m =
      ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        Complex.logarithmicPhaseQuantitativeAmplitude t a b x *
          Complex.realPhaseOscillation
            (Complex.linearFourierPhase
              (Complex.logarithmicPhasePoissonAngularFrequency m)) x := by
  have hpacket :=
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_interval
      t a b m ha hab
  have hintegrand : Set.EqOn
      (Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.quantitativeLogarithmicBlockCutoff a b) m)
      (fun x : ℝ =>
        Complex.logarithmicPhaseQuantitativeAmplitude t a b x *
          Complex.realPhaseOscillation
            (Complex.linearFourierPhase
              (Complex.logarithmicPhasePoissonAngularFrequency m)) x)
      [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]] := by
    intro x hx
    exact
      Complex.phaseCutoffFrequencyTwistIntegrand_eq_quantitativeAmplitude_mul_linear
        t a b m x
  have hintegral :
      (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.quantitativeLogarithmicBlockCutoff a b) m x ∂volume) =
        ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
            Complex.logarithmicPhaseQuantitativeSupportRight b,
          Complex.logarithmicPhaseQuantitativeAmplitude t a b x *
            Complex.realPhaseOscillation
              (Complex.linearFourierPhase
                (Complex.logarithmicPhasePoissonAngularFrequency m)) x ∂volume :=
    intervalIntegral.integral_congr (μ := volume) hintegrand
  have hendpointsLeft :
      Complex.logarithmicPhaseQuantitativeSupportLeft a =
        (a : ℝ) - 1 / 3 := rfl
  have hendpointsRight :
      Complex.logarithmicPhaseQuantitativeSupportRight b =
        (b : ℝ) + 1 / 3 := rfl
  have hnormalized :
      (∫ x in ((a : ℝ) - 1 / 3)..((b : ℝ) + 1 / 3),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.quantitativeLogarithmicBlockCutoff a b) m x) =
        ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
            Complex.logarithmicPhaseQuantitativeSupportRight b,
          Complex.logarithmicPhaseQuantitativeAmplitude t a b x *
            Complex.realPhaseOscillation
              (Complex.linearFourierPhase
                (Complex.logarithmicPhasePoissonAngularFrequency m)) x := by
    exact Eq.subst
      (motive := fun left : ℝ =>
        (∫ x in left..((b : ℝ) + 1 / 3),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.quantitativeLogarithmicBlockCutoff a b) m x) =
          ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
              Complex.logarithmicPhaseQuantitativeSupportRight b,
            Complex.logarithmicPhaseQuantitativeAmplitude t a b x *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase
                  (Complex.logarithmicPhasePoissonAngularFrequency m)) x)
      hendpointsLeft.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..right,
            Complex.phaseCutoffFrequencyTwistIntegrand
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              (Real.quantitativeLogarithmicBlockCutoff a b) m x) =
            ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
                Complex.logarithmicPhaseQuantitativeSupportRight b,
              Complex.logarithmicPhaseQuantitativeAmplitude t a b x *
                Complex.realPhaseOscillation
                  (Complex.linearFourierPhase
                    (Complex.logarithmicPhasePoissonAngularFrequency m)) x)
        hendpointsRight.symm
        hintegral)
  exact hpacket.trans hnormalized

theorem Complex.hasDerivAt_logarithmicPhaseQuantitativeAmplitude
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (x : ℝ) :
    HasDerivAt
      (Complex.logarithmicPhaseQuantitativeAmplitude t a b)
      (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b x)
      x := by
  have hdegree :
      1 ≤ (((⊤ : ℕ∞) : WithTop ℕ∞)) :=
    WithTop.coe_le_coe.mpr (OrderTop.le_top (1 : ℕ∞))
  have hdifferentiable :
      Differentiable ℝ
        (Complex.logarithmicPhaseQuantitativeAmplitude t a b) :=
    (Complex.contDiff_logarithmicPhaseQuantitativeAmplitude t a b ha).differentiable
      hdegree
  unfold Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative
  exact hdifferentiable.differentiableAt.hasDerivAt

theorem Complex.hasDerivAt_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (x : ℝ) :
    HasDerivAt
      (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b)
      (Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b x)
      x := by
  have hdegree :
      1 ≤ (((⊤ : ℕ∞) : WithTop ℕ∞)) :=
    WithTop.coe_le_coe.mpr (OrderTop.le_top (1 : ℕ∞))
  have hdifferentiable :
      Differentiable ℝ
        (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b) :=
    (Complex.contDiff_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
      t a b ha).differentiable hdegree
  unfold Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative
  exact hdifferentiable.differentiableAt.hasDerivAt

theorem Complex.hasDerivAt_phaseCutoffFunction_explicit
    (phase cutoff phaseDerivative cutoffDerivative : ℝ → ℝ)
    (x : ℝ)
    (hphase : HasDerivAt phase (phaseDerivative x) x)
    (hcutoff : HasDerivAt cutoff (cutoffDerivative x) x) :
    HasDerivAt
      (Complex.phaseCutoffFunction phase cutoff)
      ((cutoffDerivative x : ℂ) *
          Complex.exp (Complex.I * (phase x : ℂ)) +
        (cutoff x : ℂ) *
          (Complex.exp (Complex.I * (phase x : ℂ)) *
            (Complex.I * (phaseDerivative x : ℂ))))
      x := by
  have hphaseComplex :
      HasDerivAt (fun y : ℝ => (phase y : ℂ)) (phaseDerivative x : ℂ) x :=
    hphase.ofReal_comp
  have hexponent :
      HasDerivAt
        (fun y : ℝ => Complex.I * (phase y : ℂ))
        (Complex.I * (phaseDerivative x : ℂ)) x :=
    hphaseComplex.const_mul Complex.I
  have hexponential :
      HasDerivAt
        (fun y : ℝ => Complex.exp (Complex.I * (phase y : ℂ)))
        (Complex.exp (Complex.I * (phase x : ℂ)) *
          (Complex.I * (phaseDerivative x : ℂ))) x :=
    hexponent.cexp
  have hcutoffComplex :
      HasDerivAt (fun y : ℝ => (cutoff y : ℂ)) (cutoffDerivative x : ℂ) x :=
    hcutoff.ofReal_comp
  have hproduct := hcutoffComplex.mul hexponential
  have hfunction :
      (fun y : ℝ => (cutoff y : ℂ) *
        Complex.exp (Complex.I * (phase y : ℂ))) =
        Complex.phaseCutoffFunction phase cutoff := by
    funext y
    unfold Complex.phaseCutoffFunction
    exact rfl
  exact Eq.subst
    (motive := fun function : ℝ → ℂ =>
      HasDerivAt function
        ((cutoffDerivative x : ℂ) *
            Complex.exp (Complex.I * (phase x : ℂ)) +
          (cutoff x : ℂ) *
            (Complex.exp (Complex.I * (phase x : ℂ)) *
              (Complex.I * (phaseDerivative x : ℂ)))) x)
    hfunction hproduct

theorem Complex.logarithmicPhaseQuantitativeSupportLeft_pos
    (a : ℤ)
    (ha : 1 ≤ a) :
    0 < Complex.logarithmicPhaseQuantitativeSupportLeft a := by
  unfold Complex.logarithmicPhaseQuantitativeSupportLeft
  have haCast : ((1 : ℤ) : ℝ) = (1 : ℝ) := Int.cast_one
  have haRealCast : ((1 : ℤ) : ℝ) ≤ (a : ℝ) := Int.cast_le.mpr ha
  have haReal : (1 : ℝ) ≤ (a : ℝ) :=
    Eq.subst (motive := fun left : ℝ => left ≤ (a : ℝ)) haCast haRealCast
  have hthirdLtOne : (1 / 3 : ℝ) < 1 := by
    have hthreePos : (0 : ℝ) < 3 :=
      Nat.cast_pos.mpr (Nat.succ_pos 2)
    have htwoPos : (0 : ℝ) < 2 :=
      Nat.cast_pos.mpr (Nat.succ_pos 1)
    have honeLtThree : (1 : ℝ) < 3 := by
      calc
        (1 : ℝ) = 1 + 0 := (add_zero 1).symm
        _ < 1 + 2 := add_lt_add_left htwoPos 1
        _ = 2 + 1 := add_comm 1 2
        _ = 3 := two_add_one_eq_three
    exact (div_lt_one hthreePos).mpr honeLtThree
  have hthirdLtA : (1 / 3 : ℝ) < (a : ℝ) := lt_of_lt_of_le hthirdLtOne haReal
  exact sub_pos.mpr hthirdLtA

theorem Complex.logarithmicPhaseQuantitativeSupportRight_pos
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    0 < Complex.logarithmicPhaseQuantitativeSupportRight b := by
  unfold Complex.logarithmicPhaseQuantitativeSupportRight
  have haCast : ((1 : ℤ) : ℝ) = (1 : ℝ) := Int.cast_one
  have haRealCast : ((1 : ℤ) : ℝ) ≤ (a : ℝ) := Int.cast_le.mpr ha
  have haReal : (1 : ℝ) ≤ (a : ℝ) :=
    Eq.subst (motive := fun left : ℝ => left ≤ (a : ℝ)) haCast haRealCast
  have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  have hbPositive : (0 : ℝ) < (b : ℝ) :=
    lt_of_lt_of_le zero_lt_one (le_trans haReal habReal)
  have hthirdNonneg : (0 : ℝ) ≤ 1 / 3 := le_of_lt Real.one_div_three_pos
  exact lt_of_lt_of_le hbPositive (le_add_of_nonneg_right hthirdNonneg)

theorem Complex.logarithmicPhaseQuantitativeAmplitude_supportLeft_eq_zero
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseQuantitativeAmplitude t a b
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) = 0 := by
  unfold Complex.logarithmicPhaseQuantitativeAmplitude
  unfold Complex.phaseCutoffFunction
  unfold Complex.logarithmicPhaseQuantitativeSupportLeft
  have hcutoff :=
    Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_left a b
      (le_refl ((a : ℝ) - 1 / 3))
  exact
    (congrArg
      (fun value : ℝ => value •
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t ((a : ℝ) - 1 / 3) : ℂ)))
      hcutoff).trans
      (zero_smul ℝ _)

theorem Complex.logarithmicPhaseQuantitativeAmplitude_supportRight_eq_zero
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseQuantitativeAmplitude t a b
        (Complex.logarithmicPhaseQuantitativeSupportRight b) = 0 := by
  unfold Complex.logarithmicPhaseQuantitativeAmplitude
  unfold Complex.phaseCutoffFunction
  unfold Complex.logarithmicPhaseQuantitativeSupportRight
  have hcutoff :=
    Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_right a b
      (le_refl ((b : ℝ) + 1 / 3))
  exact
    (congrArg
      (fun value : ℝ => value •
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t ((b : ℝ) + 1 / 3) : ℂ)))
      hcutoff).trans
      (zero_smul ℝ _)

theorem Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative_supportLeft_eq_zero
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) :
    Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) = 0 := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  have hleftPos : 0 < left :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hphase :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_hasDerivAt
      t hleftPos
  have hcutoff :=
    Real.hasDerivAt_quantitativeLogarithmicBlockCutoff a b left
  have hproduct :=
    Complex.hasDerivAt_phaseCutoffFunction_explicit
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.quantitativeLogarithmicBlockCutoff a b)
      (fun x : ℝ => -t / x)
      (Real.quantitativeLogarithmicBlockCutoffDerivative a b)
      left hphase hcutoff
  have hcutoffValue : Real.quantitativeLogarithmicBlockCutoff a b left = 0 := by
    unfold left
    unfold Complex.logarithmicPhaseQuantitativeSupportLeft
    exact Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_left a b
      (le_refl ((a : ℝ) - 1 / 3))
  have hcutoffDerivative :
      Real.quantitativeLogarithmicBlockCutoffDerivative a b left = 0 := by
    unfold left
    unfold Complex.logarithmicPhaseQuantitativeSupportLeft
    exact Real.quantitativeLogarithmicBlockCutoffDerivative_at_supportLeft a b
  have hderivativeValue :
      ((Real.quantitativeLogarithmicBlockCutoffDerivative a b left : ℂ) *
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                t left : ℂ)) +
        (Real.quantitativeLogarithmicBlockCutoff a b left : ℂ) *
          (Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t left : ℂ)) *
            (Complex.I * ((-t / left : ℝ) : ℂ)))) = 0 := by
    have hderivativeCast := congrArg (fun value : ℝ => (value : ℂ)) hcutoffDerivative
    have hcutoffCast := congrArg (fun value : ℝ => (value : ℂ)) hcutoffValue
    calc
      ((Real.quantitativeLogarithmicBlockCutoffDerivative a b left : ℂ) *
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t left : ℂ)) +
          (Real.quantitativeLogarithmicBlockCutoff a b left : ℂ) *
            (Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                    t left : ℂ)) *
              (Complex.I * ((-t / left : ℝ) : ℂ)))) =
        0 * Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t left : ℂ)) +
          0 *
            (Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                    t left : ℂ)) *
              (Complex.I * ((-t / left : ℝ) : ℂ))) :=
        congrArg₂ (fun first second : ℂ =>
          first * Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t left : ℂ)) +
            second *
              (Complex.exp
                  (Complex.I *
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                      t left : ℂ)) *
                (Complex.I * ((-t / left : ℝ) : ℂ))))
          hderivativeCast hcutoffCast
      _ = 0 + 0 := congrArg₂ (fun first second : ℂ => first + second)
        (zero_mul _) (zero_mul _)
      _ = 0 := zero_add 0
  have hzeroDerivative :
      HasDerivAt
        (Complex.logarithmicPhaseQuantitativeAmplitude t a b) 0 left :=
    Eq.subst
      (motive := fun value : ℂ =>
        HasDerivAt
          (Complex.logarithmicPhaseQuantitativeAmplitude t a b) value left)
      hderivativeValue hproduct
  unfold Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative
  exact hzeroDerivative.deriv

theorem Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative_supportRight_eq_zero
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b
        (Complex.logarithmicPhaseQuantitativeSupportRight b) = 0 := by
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hrightPos : 0 < right :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos a b ha hab
  have hphase :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_hasDerivAt
      t hrightPos
  have hcutoff :=
    Real.hasDerivAt_quantitativeLogarithmicBlockCutoff a b right
  have hproduct :=
    Complex.hasDerivAt_phaseCutoffFunction_explicit
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.quantitativeLogarithmicBlockCutoff a b)
      (fun x : ℝ => -t / x)
      (Real.quantitativeLogarithmicBlockCutoffDerivative a b)
      right hphase hcutoff
  have hcutoffValue : Real.quantitativeLogarithmicBlockCutoff a b right = 0 := by
    unfold right
    unfold Complex.logarithmicPhaseQuantitativeSupportRight
    exact Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_right a b
      (le_refl ((b : ℝ) + 1 / 3))
  have hcutoffDerivative :
      Real.quantitativeLogarithmicBlockCutoffDerivative a b right = 0 := by
    unfold right
    unfold Complex.logarithmicPhaseQuantitativeSupportRight
    exact Real.quantitativeLogarithmicBlockCutoffDerivative_at_supportRight a b
  have hderivativeValue :
      ((Real.quantitativeLogarithmicBlockCutoffDerivative a b right : ℂ) *
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                t right : ℂ)) +
        (Real.quantitativeLogarithmicBlockCutoff a b right : ℂ) *
          (Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t right : ℂ)) *
            (Complex.I * ((-t / right : ℝ) : ℂ)))) = 0 := by
    have hderivativeCast := congrArg (fun value : ℝ => (value : ℂ)) hcutoffDerivative
    have hcutoffCast := congrArg (fun value : ℝ => (value : ℂ)) hcutoffValue
    exact
      Eq.trans
        (congrArg₂ (fun first second : ℂ =>
          first * Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t right : ℂ)) +
            second *
              (Complex.exp
                  (Complex.I *
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                      t right : ℂ)) *
                (Complex.I * ((-t / right : ℝ) : ℂ))))
          hderivativeCast hcutoffCast)
        (Eq.trans
          (congrArg₂ (fun first second : ℂ => first + second)
            (zero_mul _) (zero_mul _))
          (zero_add 0))
  have hzeroDerivative :
      HasDerivAt
        (Complex.logarithmicPhaseQuantitativeAmplitude t a b) 0 right :=
    Eq.subst
      (motive := fun value : ℂ =>
        HasDerivAt
          (Complex.logarithmicPhaseQuantitativeAmplitude t a b) value right)
      hderivativeValue hproduct
  unfold Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative
  exact hzeroDerivative.deriv

theorem Complex.intervalIntegrable_logarithmicPhaseQuantitativeFirstCoefficientDerivative
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a) :
    IntervalIntegrable
      (Complex.realPhaseAmplitudeCoefficientDerivative
        (Complex.logarithmicPhaseQuantitativeAmplitude t a b)
        (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b)
        (fun _x : ℝ => 0)
        (Complex.linearFourierPhaseDerivative
          (Complex.logarithmicPhasePoissonAngularFrequency m)))
      volume
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b) := by
  have hamplitude :
      Continuous (Complex.logarithmicPhaseQuantitativeAmplitude t a b) :=
    Complex.continuous_logarithmicPhaseQuantitativeAmplitude t a b ha
  have hfirst :
      Continuous
        (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b) :=
    Complex.continuous_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
      t a b ha
  have hcoefficient :
      Continuous
        (Complex.realPhaseIntegrationCoefficient
          (Complex.linearFourierPhaseDerivative
            (Complex.logarithmicPhasePoissonAngularFrequency m))) := by
    have hconstant :
        Complex.realPhaseIntegrationCoefficient
            (Complex.linearFourierPhaseDerivative
              (Complex.logarithmicPhasePoissonAngularFrequency m)) =
          fun _x : ℝ =>
            Complex.linearFourierCoefficient
              (Complex.logarithmicPhasePoissonAngularFrequency m) := by
      funext x
      exact
        (Complex.linearFourierCoefficient_eq_integrationCoefficient
          (Complex.logarithmicPhasePoissonAngularFrequency m) x).symm
    exact Eq.subst
      (motive := fun function : ℝ → ℂ => Continuous function)
      hconstant.symm continuous_const
  have hzero : Continuous (fun _x : ℝ => (0 : ℂ)) := continuous_const
  have hfirstProduct : Continuous (fun x : ℝ =>
      Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b x *
        Complex.realPhaseIntegrationCoefficient
          (Complex.linearFourierPhaseDerivative
            (Complex.logarithmicPhasePoissonAngularFrequency m)) x) :=
    hfirst.mul hcoefficient
  have hsecondProduct : Continuous (fun x : ℝ =>
      Complex.logarithmicPhaseQuantitativeAmplitude t a b x * 0) :=
    hamplitude.mul hzero
  have hsum := hfirstProduct.add hsecondProduct
  have hfunction :
      (fun x : ℝ =>
        Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b x *
            Complex.realPhaseIntegrationCoefficient
              (Complex.linearFourierPhaseDerivative
                (Complex.logarithmicPhasePoissonAngularFrequency m)) x +
          Complex.logarithmicPhaseQuantitativeAmplitude t a b x * 0) =
        Complex.realPhaseAmplitudeCoefficientDerivative
          (Complex.logarithmicPhaseQuantitativeAmplitude t a b)
          (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b)
          (fun _x : ℝ => 0)
          (Complex.linearFourierPhaseDerivative
            (Complex.logarithmicPhasePoissonAngularFrequency m)) := by
    funext x
    rfl
  have hcontinuous := Eq.subst
    (motive := fun function : ℝ → ℂ => Continuous function)
    hfunction hsum
  exact hcontinuous.intervalIntegrable _ _

theorem Complex.intervalIntegrable_logarithmicPhaseQuantitativeSecondCoefficientDerivative
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a) :
    IntervalIntegrable
      (Complex.realPhaseAmplitudeCoefficientDerivative
        (Complex.linearFourierFirstAmplitude
          (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b)
          (Complex.logarithmicPhasePoissonAngularFrequency m))
        (Complex.linearFourierSecondAmplitude
          (Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b)
          (Complex.logarithmicPhasePoissonAngularFrequency m))
        (fun _x : ℝ => 0)
        (Complex.linearFourierPhaseDerivative
          (Complex.logarithmicPhasePoissonAngularFrequency m)))
      volume
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b) := by
  have hfirst :
      Continuous
        (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b) :=
    Complex.continuous_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
      t a b ha
  have hsecond :
      Continuous
        (Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b) :=
    Complex.continuous_logarithmicPhaseQuantitativeAmplitudeSecondDerivative
      t a b ha
  have hcoefficient :
      Continuous (fun _x : ℝ =>
        Complex.linearFourierCoefficient
          (Complex.logarithmicPhasePoissonAngularFrequency m)) :=
    continuous_const
  have hfirstAmplitude : Continuous
      (Complex.linearFourierFirstAmplitude
        (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b)
        (Complex.logarithmicPhasePoissonAngularFrequency m)) := by
    unfold Complex.linearFourierFirstAmplitude
    exact hfirst.mul hcoefficient
  have hsecondAmplitude : Continuous
      (Complex.linearFourierSecondAmplitude
        (Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b)
        (Complex.logarithmicPhasePoissonAngularFrequency m)) := by
    unfold Complex.linearFourierSecondAmplitude
    exact hsecond.mul hcoefficient
  have hintegrationCoefficient : Continuous
      (Complex.realPhaseIntegrationCoefficient
        (Complex.linearFourierPhaseDerivative
          (Complex.logarithmicPhasePoissonAngularFrequency m))) := by
    have hfunction :
        Complex.realPhaseIntegrationCoefficient
            (Complex.linearFourierPhaseDerivative
              (Complex.logarithmicPhasePoissonAngularFrequency m)) =
          fun _x : ℝ =>
            Complex.linearFourierCoefficient
              (Complex.logarithmicPhasePoissonAngularFrequency m) := by
      funext x
      exact
        (Complex.linearFourierCoefficient_eq_integrationCoefficient
          (Complex.logarithmicPhasePoissonAngularFrequency m) x).symm
    exact Eq.subst
      (motive := fun function : ℝ → ℂ => Continuous function)
      hfunction.symm continuous_const
  have hfirstProduct := hsecondAmplitude.mul hintegrationCoefficient
  have hsecondProduct := hfirstAmplitude.mul (continuous_const :
    Continuous (fun _x : ℝ => (0 : ℂ)))
  have hsum := hfirstProduct.add hsecondProduct
  exact hsum.intervalIntegrable _ _

theorem Complex.intervalIntegrable_logarithmicPhaseLinearOscillationDerivative
    (m : ℤ)
    (left right : ℝ) :
    IntervalIntegrable
      (Complex.linearFourierOscillationDerivative
        (Complex.logarithmicPhasePoissonAngularFrequency m))
      volume left right := by
  have hphase : Continuous
      (Complex.linearFourierPhase
        (Complex.logarithmicPhasePoissonAngularFrequency m)) := by
    unfold Complex.linearFourierPhase
    exact continuous_const.mul continuous_id
  have hphaseComplex : Continuous (fun x : ℝ =>
      (Complex.linearFourierPhase
        (Complex.logarithmicPhasePoissonAngularFrequency m) x : ℂ)) :=
    Complex.continuous_ofReal.comp hphase
  have himaginaryConstant :
      Continuous (fun _x : ℝ => Complex.I) :=
    continuous_const
  have hexponent : Continuous (fun x : ℝ =>
      Complex.I *
        (Complex.linearFourierPhase
          (Complex.logarithmicPhasePoissonAngularFrequency m) x : ℂ)) :=
    himaginaryConstant.mul hphaseComplex
  have hoscillation : Continuous
      (Complex.realPhaseOscillation
        (Complex.linearFourierPhase
          (Complex.logarithmicPhasePoissonAngularFrequency m))) := by
    unfold Complex.realPhaseOscillation
    exact Complex.continuous_exp.comp hexponent
  have hdenominator : Continuous
      (Complex.realPhaseDerivativeDenominator
        (Complex.linearFourierPhaseDerivative
          (Complex.logarithmicPhasePoissonAngularFrequency m))) := by
    unfold Complex.realPhaseDerivativeDenominator
    unfold Complex.linearFourierPhaseDerivative
    exact continuous_const
  unfold Complex.linearFourierOscillationDerivative
  exact (hoscillation.mul hdenominator).intervalIntegrable left right

theorem Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_twiceIntegrated
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hm : m ≠ 0) :
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m =
      ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b x *
          (Complex.linearFourierCoefficient
            (Complex.logarithmicPhasePoissonAngularFrequency m)) ^ 2 *
          Complex.realPhaseOscillation
            (Complex.linearFourierPhase
              (Complex.logarithmicPhasePoissonAngularFrequency m)) x := by
  have hpacket :=
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_amplitude_linear_interval
      t a b m ha hab
  have hfrequency :=
    Complex.logarithmicPhasePoissonAngularFrequency_ne_zero m hm
  have hidentity :=
    Complex.intervalIntegral_linearFourier_eq_secondDerivative
      (Complex.logarithmicPhaseQuantitativeAmplitude t a b)
      (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b)
      (Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b)
      (Complex.logarithmicPhasePoissonAngularFrequency m)
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b)
      hfrequency
      (fun x hx =>
        Complex.hasDerivAt_logarithmicPhaseQuantitativeAmplitude t a b ha x)
      (fun x hx =>
        Complex.hasDerivAt_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
          t a b ha x)
      (Complex.intervalIntegrable_logarithmicPhaseQuantitativeFirstCoefficientDerivative
        t a b m ha)
      (Complex.intervalIntegrable_logarithmicPhaseQuantitativeSecondCoefficientDerivative
        t a b m ha)
      (Complex.intervalIntegrable_logarithmicPhaseLinearOscillationDerivative
        m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)
        (Complex.logarithmicPhaseQuantitativeSupportRight b))
      (Complex.logarithmicPhaseQuantitativeAmplitude_supportLeft_eq_zero t a b)
      (Complex.logarithmicPhaseQuantitativeAmplitude_supportRight_eq_zero t a b)
      (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative_supportLeft_eq_zero
        t a b ha)
      (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative_supportRight_eq_zero
        t a b ha hab)
  exact hpacket.trans hidentity

theorem Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_angularInverseSquare
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hm : m ≠ 0) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        ‖Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b x‖ *
          ‖Complex.logarithmicPhasePoissonAngularFrequency m‖⁻¹ ^ 2 := by
  have hleftRight :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hpacket :=
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_amplitude_linear_interval
      t a b m ha hab
  have htwice :=
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_twiceIntegrated
      t a b m ha hab hm
  have hidentity :
      (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        Complex.logarithmicPhaseQuantitativeAmplitude t a b x *
          Complex.realPhaseOscillation
            (Complex.linearFourierPhase
              (Complex.logarithmicPhasePoissonAngularFrequency m)) x) =
        ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
            Complex.logarithmicPhaseQuantitativeSupportRight b,
          Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b x *
            (Complex.linearFourierCoefficient
              (Complex.logarithmicPhasePoissonAngularFrequency m)) ^ 2 *
            Complex.realPhaseOscillation
              (Complex.linearFourierPhase
                (Complex.logarithmicPhasePoissonAngularFrequency m)) x :=
    hpacket.symm.trans htwice
  have hbound :=
    Complex.norm_intervalIntegral_linearFourier_le_inverseSquare_integral
      (Complex.logarithmicPhaseQuantitativeAmplitude t a b)
      (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b)
      (Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b)
      (Complex.logarithmicPhasePoissonAngularFrequency m)
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b)
      hleftRight hidentity
  exact le_trans (le_of_eq (congrArg norm hpacket)) hbound

theorem Complex.abs_intCast_pos
    (m : ℤ)
    (hm : m ≠ 0) :
    0 < |(m : ℝ)| := by
  have hmCast : (m : ℝ) ≠ 0 := by
    intro hmReal
    exact hm (Int.cast_eq_zero.mp hmReal)
  exact abs_pos.mpr hmCast

theorem Complex.abs_intCast_rpow_neg_two_eq_inv_sq
    (m : ℤ)
    (hm : m ≠ 0) :
    |(m : ℝ)| ^ (-2 : ℝ) = |(m : ℝ)|⁻¹ ^ 2 := by
  have habsPos : (0 : ℝ) < |(m : ℝ)| :=
    Complex.abs_intCast_pos m hm
  have habsNonneg : (0 : ℝ) ≤ |(m : ℝ)| := le_of_lt habsPos
  have hrpowNeg :
      |(m : ℝ)| ^ (-((2 : ℕ) : ℝ)) =
        (|(m : ℝ)| ^ ((2 : ℕ) : ℝ))⁻¹ :=
    Real.rpow_neg habsNonneg ((2 : ℕ) : ℝ)
  have htwoCast : ((2 : ℕ) : ℝ) = (2 : ℝ) :=
    Nat.cast_ofNat (R := ℝ)
  have hnegativeCast : (-((2 : ℕ) : ℝ) : ℝ) = -2 :=
    congrArg (fun value : ℝ => -value) htwoCast
  have hrpowNat : |(m : ℝ)| ^ ((2 : ℕ) : ℝ) = |(m : ℝ)| ^ 2 :=
    Real.rpow_natCast |(m : ℝ)| 2
  have hinversePower : (|(m : ℝ)| ^ 2)⁻¹ = |(m : ℝ)|⁻¹ ^ 2 :=
    (inv_pow |(m : ℝ)| 2).symm
  exact Eq.subst
    (motive := fun exponent : ℝ =>
      |(m : ℝ)| ^ exponent = |(m : ℝ)|⁻¹ ^ 2)
    hnegativeCast.symm
    (hrpowNeg.trans
      ((congrArg Inv.inv hrpowNat).trans hinversePower))

theorem Complex.two_mul_pi_pos :
    (0 : ℝ) < 2 * Real.pi := by
  exact mul_pos
    (Nat.cast_pos.mpr (Nat.succ_pos 1))
    Real.pi_pos

theorem Complex.two_mul_pi_ne_zero :
    (2 * Real.pi : ℝ) ≠ 0 :=
  ne_of_gt Complex.two_mul_pi_pos

theorem Complex.angularInverseSquare_eq_integerInverseSquareCoefficient
    (m : ℤ)
    (hm : m ≠ 0) :
    ‖Complex.logarithmicPhasePoissonAngularFrequency m‖⁻¹ ^ 2 =
      ((2 * Real.pi) ^ 2)⁻¹ * |(m : ℝ)| ^ (-2 : ℝ) := by
  let base : ℝ := 2 * Real.pi
  let magnitude : ℝ := |(m : ℝ)|
  have hnorm :
      ‖Complex.logarithmicPhasePoissonAngularFrequency m‖ =
        base * magnitude :=
    Complex.norm_logarithmicPhasePoissonAngularFrequency m
  have hinverseProduct : (base * magnitude)⁻¹ = base⁻¹ * magnitude⁻¹ := by
    exact
      (mul_inv_rev base magnitude).trans
        (mul_comm magnitude⁻¹ base⁻¹)
  have hsquareProduct :
      (base⁻¹ * magnitude⁻¹) ^ 2 =
        base⁻¹ ^ 2 * magnitude⁻¹ ^ 2 :=
    mul_pow base⁻¹ magnitude⁻¹ 2
  have hbaseInverseSquare : base⁻¹ ^ 2 = (base ^ 2)⁻¹ :=
    inv_pow base 2
  have hmagnitudePower : magnitude⁻¹ ^ 2 = magnitude ^ (-2 : ℝ) := by
    unfold magnitude
    exact
      (Complex.abs_intCast_rpow_neg_two_eq_inv_sq m hm).symm
  exact
    (congrArg (fun value : ℝ => value⁻¹ ^ 2) hnorm).trans
      ((congrArg (fun value : ℝ => value ^ 2) hinverseProduct).trans
        (hsquareProduct.trans
          (congrArg₂ (fun first second : ℝ => first * second)
            hbaseInverseSquare hmagnitudePower)))

theorem Complex.logarithmicPhaseQuantitativeInverseSquareIntegral_eq_majorant
    (t : ℝ) (a b m : ℤ)
    (hm : m ≠ 0) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      ‖Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b x‖ *
        ‖Complex.logarithmicPhasePoissonAngularFrequency m‖⁻¹ ^ 2) =
      Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
        t a b m := by
  let angularCoefficient : ℝ :=
    ‖Complex.logarithmicPhasePoissonAngularFrequency m‖⁻¹ ^ 2
  have hpull :
      (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        ‖Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b x‖ *
          angularCoefficient) =
        Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b *
          angularCoefficient := by
    unfold Complex.logarithmicPhaseQuantitativeSecondDerivativeMass
    exact intervalIntegral.integral_mul_const angularCoefficient
      (fun x : ℝ =>
        ‖Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b x‖)
  have hcoefficient :
      angularCoefficient =
        ((2 * Real.pi) ^ 2)⁻¹ * |(m : ℝ)| ^ (-2 : ℝ) := by
    unfold angularCoefficient
    exact
      Complex.angularInverseSquare_eq_integerInverseSquareCoefficient m hm
  have halgebra :
      Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b *
          (((2 * Real.pi) ^ 2)⁻¹ * |(m : ℝ)| ^ (-2 : ℝ)) =
        (Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b /
          (2 * Real.pi) ^ 2) * |(m : ℝ)| ^ (-2 : ℝ) := by
    calc
      Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b *
          (((2 * Real.pi) ^ 2)⁻¹ * |(m : ℝ)| ^ (-2 : ℝ)) =
        (Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b *
          ((2 * Real.pi) ^ 2)⁻¹) * |(m : ℝ)| ^ (-2 : ℝ) :=
        (mul_assoc _ _ _).symm
      _ = (Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b /
          (2 * Real.pi) ^ 2) * |(m : ℝ)| ^ (-2 : ℝ) :=
        congrArg
          (fun value : ℝ => value * |(m : ℝ)| ^ (-2 : ℝ))
          (div_eq_mul_inv _ _).symm
  unfold Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
  exact hpull.trans
    ((congrArg
      (fun value : ℝ =>
        Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b * value)
      hcoefficient).trans halgebra)

theorem Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_integerInverseSquare
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hm : m ≠ 0) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
        t a b m := by
  exact le_trans
    (Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_angularInverseSquare
      t a b m ha hab hm)
    (le_of_eq
      (Complex.logarithmicPhaseQuantitativeInverseSquareIntegral_eq_majorant
        t a b m hm))

theorem Complex.logarithmicPhaseQuantitativeNegativeTail_tsum_norm_le_unconditional
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖∑' m : Complex.logarithmicPhasePoissonNegativeTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeNegativeTailBudget t a b := by
  exact
    Complex.logarithmicPhaseQuantitativeNegativeTail_tsum_norm_le
      t a b
      (fun m =>
        Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_integerInverseSquare
          t a b m ha hab
          (Complex.logarithmicPhasePoissonNegativeTailModes_subset_nonzero m.property))

theorem Complex.logarithmicPhaseQuantitativePositiveTail_tsum_norm_le_unconditional
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativePositiveTailBudget t a b := by
  exact
    Complex.logarithmicPhaseQuantitativePositiveTail_tsum_norm_le
      t a b
      (fun m =>
        Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_integerInverseSquare
          t a b m ha hab
          (Complex.logarithmicPhasePoissonPositiveTailModes_subset_nonzero m.property))

end
end LFunctions
end Boundary
