import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePacketDecay

/-!
# Explicit second derivative of the quantitative logarithmic amplitude

The deterministic far-tail constant is the `L¹` mass of the second derivative
of the compact logarithmic amplitude.  This owner expands that derivative into
cutoff curvature, mixed cutoff-phase variation, and pure logarithmic phase
curvature terms.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Real.quantitativeLogarithmicBlockCutoffSecondDerivative
    (a b : ℤ) : ℝ → ℝ :=
  deriv (Real.quantitativeLogarithmicBlockCutoffDerivative a b)

def Complex.logarithmicPhaseOscillator
    (t : ℝ) (x : ℝ) : ℂ :=
  Complex.exp
    (Complex.I *
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x : ℂ))

def Complex.logarithmicPhaseOscillatorFirstDerivative
    (t : ℝ) (x : ℝ) : ℂ :=
  Complex.logarithmicPhaseOscillator t x *
    (Complex.I * ((-t / x : ℝ) : ℂ))

def Complex.logarithmicPhaseOscillatorSecondDerivative
    (t : ℝ) (x : ℝ) : ℂ :=
  Complex.logarithmicPhaseOscillator t x *
      (Complex.I * ((-t / x : ℝ) : ℂ)) *
      (Complex.I * ((-t / x : ℝ) : ℂ)) +
    Complex.logarithmicPhaseOscillator t x *
      (Complex.I * ((t / x ^ 2 : ℝ) : ℂ))

def Complex.logarithmicPhaseQuantitativeAmplitudeExplicitFirstDerivative
    (t : ℝ) (a b : ℤ) (x : ℝ) : ℂ :=
  (Real.quantitativeLogarithmicBlockCutoffDerivative a b x : ℂ) *
      Complex.logarithmicPhaseOscillator t x +
    (Real.quantitativeLogarithmicBlockCutoff a b x : ℂ) *
      Complex.logarithmicPhaseOscillatorFirstDerivative t x

def Complex.logarithmicPhaseQuantitativeAmplitudeExplicitSecondDerivative
    (t : ℝ) (a b : ℤ) (x : ℝ) : ℂ :=
  (Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x : ℂ) *
      Complex.logarithmicPhaseOscillator t x +
    (Real.quantitativeLogarithmicBlockCutoffDerivative a b x : ℂ) *
      Complex.logarithmicPhaseOscillatorFirstDerivative t x +
    ((Real.quantitativeLogarithmicBlockCutoffDerivative a b x : ℂ) *
        Complex.logarithmicPhaseOscillatorFirstDerivative t x +
      (Real.quantitativeLogarithmicBlockCutoff a b x : ℂ) *
        Complex.logarithmicPhaseOscillatorSecondDerivative t x)

theorem Real.contDiff_quantitativeLogarithmicBlockCutoffDerivative
    (a b : ℤ) :
    ContDiff ℝ ∞ (Real.quantitativeLogarithmicBlockCutoffDerivative a b) := by
  have hcutoff := Real.contDiff_quantitativeLogarithmicBlockCutoff a b
  have hderivative :
      ContDiff ℝ ∞ (deriv (Real.quantitativeLogarithmicBlockCutoff a b)) :=
    (contDiff_infty_iff_deriv.mp hcutoff).2
  have hfunction :
      deriv (Real.quantitativeLogarithmicBlockCutoff a b) =
        Real.quantitativeLogarithmicBlockCutoffDerivative a b := by
    funext x
    exact Real.deriv_quantitativeLogarithmicBlockCutoff a b x
  exact Eq.subst
    (motive := fun function : ℝ → ℝ => ContDiff ℝ ∞ function)
    hfunction hderivative

theorem Real.contDiff_quantitativeLogarithmicBlockCutoffSecondDerivative
    (a b : ℤ) :
    ContDiff ℝ ∞
      (Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b) := by
  unfold Real.quantitativeLogarithmicBlockCutoffSecondDerivative
  exact
    (contDiff_infty_iff_deriv.mp
      (Real.contDiff_quantitativeLogarithmicBlockCutoffDerivative a b)).2

theorem Real.hasDerivAt_quantitativeLogarithmicBlockCutoffDerivative
    (a b : ℤ) (x : ℝ) :
    HasDerivAt
      (Real.quantitativeLogarithmicBlockCutoffDerivative a b)
      (Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x)
      x := by
  have hdifferentiable :=
    (Real.contDiff_quantitativeLogarithmicBlockCutoffDerivative a b)
      .differentiable le_top
  unfold Real.quantitativeLogarithmicBlockCutoffSecondDerivative
  exact hdifferentiable.differentiableAt.hasDerivAt

theorem Complex.hasDerivAt_logarithmicPhaseDerivative
    (t : ℝ) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -t / y) (t / x ^ 2) x := by
  have hinverse : HasDerivAt (fun y : ℝ => y⁻¹) (-x⁻¹ ^ 2) x :=
    (hasDerivAt_id x).inv hx.ne'
  have hscaled := hinverse.const_mul (-t)
  have hfunction :
      (fun y : ℝ => -t * y⁻¹) = (fun y : ℝ => -t / y) := by
    funext y
    exact (div_eq_mul_inv (-t) y).symm
  have hvalue : (-t) * (-x⁻¹ ^ 2) = t / x ^ 2 := by
    calc
      (-t) * (-x⁻¹ ^ 2) = t * x⁻¹ ^ 2 :=
        (neg_mul_neg t (x⁻¹ ^ 2))
      _ = t * (x ^ 2)⁻¹ :=
        congrArg (fun value : ℝ => t * value) (inv_pow x 2)
      _ = t / x ^ 2 := (div_eq_mul_inv t (x ^ 2)).symm
  exact Eq.subst
    (motive := fun function : ℝ → ℝ =>
      HasDerivAt function (t / x ^ 2) x)
    hfunction
    (Eq.subst
      (motive := fun value : ℝ =>
        HasDerivAt (fun y : ℝ => -t * y⁻¹) value x)
      hvalue hscaled)

theorem Complex.hasDerivAt_logarithmicPhaseOscillator
    (t : ℝ) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (Complex.logarithmicPhaseOscillator t)
      (Complex.logarithmicPhaseOscillatorFirstDerivative t x)
      x := by
  have hphase :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_hasDerivAt
      t hx
  have hphaseComplex := hphase.ofReal_comp
  have hexponent := hphaseComplex.const_mul Complex.I
  have hexponential := hexponent.cexp
  exact hexponential

theorem Complex.hasDerivAt_logarithmicPhaseOscillatorFirstDerivative
    (t : ℝ) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (Complex.logarithmicPhaseOscillatorFirstDerivative t)
      (Complex.logarithmicPhaseOscillatorSecondDerivative t x)
      x := by
  have hoscillator := Complex.hasDerivAt_logarithmicPhaseOscillator t hx
  have hphaseDerivative := Complex.hasDerivAt_logarithmicPhaseDerivative t hx
  have hphaseDerivativeComplex := hphaseDerivative.ofReal_comp
  have hfactor := hphaseDerivativeComplex.const_mul Complex.I
  have hproduct := hoscillator.mul hfactor
  exact hproduct

theorem Complex.hasDerivAt_logarithmicPhaseQuantitativeAmplitude_explicit
    (t : ℝ) (a b : ℤ) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (Complex.logarithmicPhaseQuantitativeAmplitude t a b)
      (Complex.logarithmicPhaseQuantitativeAmplitudeExplicitFirstDerivative
        t a b x)
      x := by
  have hcutoff := Real.hasDerivAt_quantitativeLogarithmicBlockCutoff a b x
  have hoscillator := Complex.hasDerivAt_logarithmicPhaseOscillator t hx
  have hcutoffComplex := hcutoff.ofReal_comp
  have hproduct := hcutoffComplex.mul hoscillator
  exact hproduct

theorem Complex.hasDerivAt_logarithmicPhaseQuantitativeAmplitudeExplicitFirstDerivative
    (t : ℝ) (a b : ℤ) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (Complex.logarithmicPhaseQuantitativeAmplitudeExplicitFirstDerivative t a b)
      (Complex.logarithmicPhaseQuantitativeAmplitudeExplicitSecondDerivative
        t a b x)
      x := by
  have hcutoff := Real.hasDerivAt_quantitativeLogarithmicBlockCutoff a b x
  have hcutoffDerivative :=
    Real.hasDerivAt_quantitativeLogarithmicBlockCutoffDerivative a b x
  have hoscillator := Complex.hasDerivAt_logarithmicPhaseOscillator t hx
  have hoscillatorFirst :=
    Complex.hasDerivAt_logarithmicPhaseOscillatorFirstDerivative t hx
  have hfirstProduct := hcutoffDerivative.ofReal_comp.mul hoscillator
  have hsecondProduct := hcutoff.ofReal_comp.mul hoscillatorFirst
  have hsum := hfirstProduct.add hsecondProduct
  exact hsum

theorem Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative_eq_explicit
    (t : ℝ) (a b : ℤ) {x : ℝ}
    (hx : 0 < x) :
    Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b x =
      Complex.logarithmicPhaseQuantitativeAmplitudeExplicitFirstDerivative
        t a b x := by
  unfold Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative
  exact
    (Complex.hasDerivAt_logarithmicPhaseQuantitativeAmplitude_explicit
      t a b hx).deriv

theorem Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative_eq_explicit
    (t : ℝ) (a b : ℤ) {x : ℝ}
    (hx : 0 < x) :
    Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b x =
      Complex.logarithmicPhaseQuantitativeAmplitudeExplicitSecondDerivative
        t a b x := by
  have hfirstEventually :
      Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b =ᶠ[nhds x]
        Complex.logarithmicPhaseQuantitativeAmplitudeExplicitFirstDerivative
          t a b := by
    exact Filter.mem_of_superset
      (Ioi_mem_nhds hx)
      (fun y hy =>
        Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative_eq_explicit
          t a b hy)
  have hexplicit :=
    Complex.hasDerivAt_logarithmicPhaseQuantitativeAmplitudeExplicitFirstDerivative
      t a b hx
  unfold Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative
  exact hfirstEventually.deriv_eq.trans hexplicit.deriv

theorem Complex.norm_logarithmicPhaseOscillator
    (t x : ℝ) :
    ‖Complex.logarithmicPhaseOscillator t x‖ = 1 := by
  unfold Complex.logarithmicPhaseOscillator
  exact
    Complex.norm_realPhaseOscillation
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x

theorem Complex.norm_logarithmicPhaseOscillatorFirstDerivative
    (t : ℝ) {x : ℝ}
    (hx : 0 < x) :
    ‖Complex.logarithmicPhaseOscillatorFirstDerivative t x‖ = ‖t‖ / x := by
  unfold Complex.logarithmicPhaseOscillatorFirstDerivative
  have hoscillator := Complex.norm_logarithmicPhaseOscillator t x
  have hfactor : ‖Complex.I * ((-t / x : ℝ) : ℂ)‖ = ‖t‖ / x := by
    have hproduct := norm_mul Complex.I ((-t / x : ℝ) : ℂ)
    have hreal := Complex.norm_real (-t / x)
    have hnegative : ‖-t‖ = ‖t‖ := norm_neg t
    have hxNorm : ‖x‖ = x := Real.norm_of_nonneg hx.le
    exact hproduct.trans
      ((congrArg₂ (fun first second : ℝ => first * second)
        Complex.norm_I
        (hreal.trans
          ((norm_div (-t) x).trans
            (congrArg₂ (fun first second : ℝ => first / second)
              hnegative hxNorm)))).trans
        (one_mul _))
  exact
    (norm_mul _ _).trans
      ((congrArg₂ (fun first second : ℝ => first * second)
        hoscillator hfactor).trans (one_mul _))

end
end LFunctions
end Boundary
