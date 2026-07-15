import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.TwoStepNonstationaryMajorantArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeAmplitudeSecondDerivative
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeReconstruction

/-!
# Phase-adapted logarithmic packet calculus

The amplitude is only the real cutoff, coerced to `ℂ`.  The complete
logarithmic and Fourier oscillation remains in the twisted real phase.  This
separation removes the spurious `t²/a²` amplitude mass from far-tail bounds.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseAdaptedCutoffAmplitude
    (a b : ℤ) (x : ℝ) : ℂ :=
  (Real.quantitativeLogarithmicBlockCutoff a b x : ℂ)

def Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative
    (a b : ℤ) (x : ℝ) : ℂ :=
  (Real.quantitativeLogarithmicBlockCutoffDerivative a b x : ℂ)

def Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative
    (a b : ℤ) (x : ℝ) : ℂ :=
  (Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x : ℂ)

def Complex.logarithmicPhaseAdaptedTwistedPhase
    (t : ℝ) (m : ℤ) (x : ℝ) : ℝ :=
  -‖t‖ * Real.log x - 2 * Real.pi * (m : ℝ) * x

def Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative
    (t : ℝ) (m : ℤ) (x : ℝ) : ℝ :=
  -‖t‖ / x - 2 * Real.pi * (m : ℝ)

def Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative
    (t : ℝ) (x : ℝ) : ℝ :=
  ‖t‖ / x ^ 2

def Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative
    (t : ℝ) (x : ℝ) : ℝ :=
  -(2 * ‖t‖ / x ^ 3)

theorem Complex.hasDerivAt_logarithmicPhaseAdaptedCutoffAmplitude
    (a b : ℤ) (x : ℝ) :
    HasDerivAt
      (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
      (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b x) x := by
  unfold Complex.logarithmicPhaseAdaptedCutoffAmplitude
  unfold Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative
  exact (Real.hasDerivAt_quantitativeLogarithmicBlockCutoff a b x).ofReal_comp

theorem Complex.hasDerivAt_logarithmicPhaseAdaptedCutoffAmplitudeDerivative
    (a b : ℤ) (x : ℝ) :
    HasDerivAt
      (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
      (Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b x) x := by
  unfold Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative
  unfold Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative
  exact
    (Real.hasDerivAt_quantitativeLogarithmicBlockCutoffDerivative
      a b x).ofReal_comp

theorem Complex.hasDerivAt_logarithmicPhaseAdaptedTwistedPhase
    (t : ℝ) (m : ℤ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (Complex.logarithmicPhaseAdaptedTwistedPhase t m)
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x) x := by
  unfold Complex.logarithmicPhaseAdaptedTwistedPhase
  unfold Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative
  have hlog := Real.hasDerivAt_log hx.ne'
  have hlogScaled := hlog.const_mul (-‖t‖)
  have hlinear := (hasDerivAt_id x).const_mul
    (-(2 * Real.pi * (m : ℝ)))
  have hsum := hlogScaled.add hlinear
  have hfunction :
      (fun y : ℝ => -‖t‖ * Real.log y +
        (-(2 * Real.pi * (m : ℝ))) * y) =
      Complex.logarithmicPhaseAdaptedTwistedPhase t m := by
    funext y
    unfold Complex.logarithmicPhaseAdaptedTwistedPhase
    exact congrArg (fun value : ℝ => -‖t‖ * Real.log y + value)
      (neg_mul (2 * Real.pi * (m : ℝ)) y)
  have hderivative :
      -‖t‖ * x⁻¹ + (-(2 * Real.pi * (m : ℝ))) * 1 =
        -‖t‖ / x - 2 * Real.pi * (m : ℝ) := by
    exact congrArg₂ (fun first second : ℝ => first + second)
      (div_eq_mul_inv (-‖t‖) x).symm
      (mul_one (-(2 * Real.pi * (m : ℝ))))
  exact Eq.subst
    (motive := fun function : ℝ → ℝ =>
      HasDerivAt function
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x) x)
    hfunction
    (Eq.subst
      (motive := fun value : ℝ =>
        HasDerivAt
          (fun y : ℝ => -‖t‖ * Real.log y +
            (-(2 * Real.pi * (m : ℝ))) * y) value x)
      hderivative
      hsum)

theorem Complex.hasDerivAt_logarithmicPhaseAdaptedTwistedPhaseDerivative
    (t : ℝ) (m : ℤ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
      (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t x) x := by
  unfold Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative
  unfold Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative
  have hinverse := hasDerivAt_inv hx.ne'
  have hscaled := hinverse.const_mul (-‖t‖)
  have hconstant := hasDerivAt_const x (-(2 * Real.pi * (m : ℝ)))
  have hsum := hscaled.add hconstant
  have hnormalize :
      -‖t‖ * (-(x ^ 2)⁻¹) + 0 = ‖t‖ / x ^ 2 := by
    exact Eq.trans (add_zero _)
      (Eq.trans (neg_mul_neg ‖t‖ ((x ^ 2)⁻¹))
        (div_eq_mul_inv ‖t‖ (x ^ 2)).symm)
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt
        (fun y : ℝ => -‖t‖ * y⁻¹ - 2 * Real.pi * (m : ℝ))
        value x)
    hnormalize
    hsum

theorem Complex.hasDerivAt_logarithmicPhaseAdaptedInvSquare
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y⁻¹ ^ 2) (-2 * x⁻¹ ^ 3) x := by
  have hinverse :
      HasDerivAt (fun y : ℝ => (id y)⁻¹) (-1 / (id x) ^ 2) x :=
    (hasDerivAt_id x).inv hx.ne'
  have hsquare := hinverse.pow 2
  have hinverseDerivative :
      -1 / (id x) ^ 2 = -x⁻¹ ^ 2 := by
    calc
      -1 / (id x) ^ 2 = -1 / x ^ 2 := rfl
      _ = -(1 / x ^ 2) := neg_div (x ^ 2) 1
      _ = -((x ^ 2)⁻¹) :=
        congrArg Neg.neg (one_div (x ^ 2))
      _ = -x⁻¹ ^ 2 :=
        congrArg Neg.neg (inv_pow x 2).symm
  have hraw :
      (2 : ℝ) * x⁻¹ ^ (2 - 1) * (-x⁻¹ ^ 2) =
        -2 * x⁻¹ ^ 3 := by
    have hpower : x⁻¹ * x⁻¹ ^ 2 = x⁻¹ ^ 3 :=
      Eq.trans (mul_comm x⁻¹ (x⁻¹ ^ 2)) (pow_succ x⁻¹ 2).symm
    calc
      (2 : ℝ) * x⁻¹ ^ (2 - 1) * (-x⁻¹ ^ 2) =
          2 * x⁻¹ * (-x⁻¹ ^ 2) :=
        congrArg (fun value : ℝ => 2 * value * (-x⁻¹ ^ 2))
          (pow_one x⁻¹)
      _ = -(2 * x⁻¹ * x⁻¹ ^ 2) :=
        mul_neg (2 * x⁻¹) (x⁻¹ ^ 2)
      _ = -(2 * (x⁻¹ * x⁻¹ ^ 2)) :=
        congrArg Neg.neg (mul_assoc 2 x⁻¹ (x⁻¹ ^ 2))
      _ = -(2 * x⁻¹ ^ 3) :=
        congrArg (fun value : ℝ => -(2 * value)) hpower
      _ = -2 * x⁻¹ ^ 3 := (neg_mul 2 (x⁻¹ ^ 3)).symm
  have hsquareDerivativeEquality :
      (2 : ℝ) * (id x)⁻¹ ^ (2 - 1) * (-1 / (id x) ^ 2) =
        (2 : ℝ) * x⁻¹ ^ (2 - 1) * (-x⁻¹ ^ 2) := by
    exact congrArg
      (fun derivative : ℝ =>
        (2 : ℝ) * (id x)⁻¹ ^ (2 - 1) * derivative)
      hinverseDerivative
  have hsquareDerivativeNormalized :
      HasDerivAt
        (fun y : ℝ => (id y)⁻¹ ^ 2)
        ((2 : ℝ) * x⁻¹ ^ (2 - 1) * (-x⁻¹ ^ 2)) x :=
    hsquare.congr_deriv hsquareDerivativeEquality
  have hfunction :
      (fun y : ℝ => (id y)⁻¹ ^ 2) =
        (fun y : ℝ => y⁻¹ ^ 2) := by
    funext y
    rfl
  have hsquareFunctionNormalized :
      HasDerivAt
        (fun y : ℝ => y⁻¹ ^ 2)
        ((2 : ℝ) * x⁻¹ ^ (2 - 1) * (-x⁻¹ ^ 2)) x :=
    Eq.subst
      (motive := fun function : ℝ → ℝ =>
        HasDerivAt function
          ((2 : ℝ) * x⁻¹ ^ (2 - 1) * (-x⁻¹ ^ 2)) x)
      hfunction hsquareDerivativeNormalized
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt (fun y : ℝ => y⁻¹ ^ 2) value x)
    hraw hsquareFunctionNormalized

theorem Complex.hasDerivAt_logarithmicPhaseAdaptedTwistedPhaseSecondDerivative
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)
      (Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t x) x := by
  unfold Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative
  unfold Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative
  have hinverseSquare :
      HasDerivAt (fun y : ℝ => y⁻¹ ^ 2) (-2 * x⁻¹ ^ 3) x :=
    Complex.hasDerivAt_logarithmicPhaseAdaptedInvSquare hx
  have hscaled :
      HasDerivAt
        (fun y : ℝ => ‖t‖ * y⁻¹ ^ 2)
        (‖t‖ * (-2 * x⁻¹ ^ 3)) x :=
    hinverseSquare.const_mul ‖t‖
  have hnormalize :
      ‖t‖ * (-2 * x⁻¹ ^ 3) =
        -(2 * ‖t‖ / x ^ 3) := by
    have hcoefficient : ‖t‖ * (-2) = -(2 * ‖t‖) := by
      exact
        (mul_neg ‖t‖ 2).trans
          (congrArg Neg.neg (mul_comm ‖t‖ 2))
    have hinverseCube : (x ^ 3)⁻¹ = x⁻¹ ^ 3 := (inv_pow x 3).symm
    have hdivision :
        2 * ‖t‖ / x ^ 3 = (2 * ‖t‖) * x⁻¹ ^ 3 := by
      exact
        (div_eq_mul_inv (2 * ‖t‖) (x ^ 3)).trans
          (congrArg (fun value : ℝ => (2 * ‖t‖) * value)
            hinverseCube)
    exact
      (mul_assoc ‖t‖ (-2) (x⁻¹ ^ 3)).symm.trans
        ((congrArg (fun value : ℝ => value * x⁻¹ ^ 3)
          hcoefficient).trans
          ((neg_mul (2 * ‖t‖) (x⁻¹ ^ 3)).trans
            (congrArg Neg.neg hdivision.symm)))
  have hscaledNormalized :
      HasDerivAt
        (fun y : ℝ => ‖t‖ * y⁻¹ ^ 2)
        (-(2 * ‖t‖ / x ^ 3)) x :=
    Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt (fun y : ℝ => ‖t‖ * y⁻¹ ^ 2) value x)
    hnormalize
    hscaled
  have hfunction :
      (fun y : ℝ => ‖t‖ * y⁻¹ ^ 2) =
        (fun y : ℝ => ‖t‖ / y ^ 2) := by
    funext y
    exact
      (congrArg (fun value : ℝ => ‖t‖ * value) (inv_pow y 2)).trans
        (div_eq_mul_inv ‖t‖ (y ^ 2)).symm
  exact Eq.subst
    (motive := fun function : ℝ → ℝ =>
      HasDerivAt function (-(2 * ‖t‖ / x ^ 3)) x)
    hfunction hscaledNormalized

theorem Complex.norm_logarithmicPhaseAdaptedCutoffAmplitude
    (a b : ℤ) (x : ℝ) :
    ‖Complex.logarithmicPhaseAdaptedCutoffAmplitude a b x‖ =
      |Real.quantitativeLogarithmicBlockCutoff a b x| := by
  exact Complex.norm_real _

theorem Complex.norm_logarithmicPhaseAdaptedCutoffAmplitudeDerivative
    (a b : ℤ) (x : ℝ) :
    ‖Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b x‖ =
      |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| := by
  exact Complex.norm_real _

theorem Complex.norm_logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative
    (a b : ℤ) (x : ℝ) :
    ‖Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b x‖ =
      |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x| := by
  exact Complex.norm_real _

end
end LFunctions
end Boundary
