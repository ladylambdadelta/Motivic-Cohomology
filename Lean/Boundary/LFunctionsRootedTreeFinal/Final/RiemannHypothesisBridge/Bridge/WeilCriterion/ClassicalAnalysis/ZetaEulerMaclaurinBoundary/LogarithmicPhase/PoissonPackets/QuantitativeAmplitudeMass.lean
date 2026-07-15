import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeAmplitudeSecondDerivative

/-!
# Decomposed second-derivative mass

The second derivative of the quantitative amplitude is bounded by three
nonnegative terms: cutoff curvature, mixed cutoff variation, and logarithmic
phase curvature.  Keeping these terms separate permits independent numerical
bounds for the two fixed transition collars and the principal block.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

def Complex.logarithmicPhaseQuantitativeCutoffCurvatureDensity
    (a b : ℤ) (x : ℝ) : ℝ :=
  |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x|

def Complex.logarithmicPhaseQuantitativeMixedVariationDensity
    (t : ℝ) (a b : ℤ) (x : ℝ) : ℝ :=
  2 * |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
    (‖t‖ / x)

def Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity
    (t : ℝ) (a b : ℤ) (x : ℝ) : ℝ :=
  Real.quantitativeLogarithmicBlockCutoff a b x *
    ((‖t‖ / x) ^ 2 + ‖t‖ / x ^ 2)

def Complex.logarithmicPhaseQuantitativeSecondDerivativeDensityMajorant
    (t : ℝ) (a b : ℤ) (x : ℝ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeCutoffCurvatureDensity a b x +
    Complex.logarithmicPhaseQuantitativeMixedVariationDensity t a b x +
      Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity t a b x

def Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass
    (a b : ℤ) : ℝ :=
  ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
      Complex.logarithmicPhaseQuantitativeSupportRight b,
    Complex.logarithmicPhaseQuantitativeCutoffCurvatureDensity a b x

def Complex.logarithmicPhaseQuantitativeMixedVariationMass
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
      Complex.logarithmicPhaseQuantitativeSupportRight b,
    Complex.logarithmicPhaseQuantitativeMixedVariationDensity t a b x

def Complex.logarithmicPhaseQuantitativePhaseCurvatureMass
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
      Complex.logarithmicPhaseQuantitativeSupportRight b,
    Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity t a b x

def Complex.logarithmicPhaseQuantitativeDecomposedSecondDerivativeMass
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b +
    Complex.logarithmicPhaseQuantitativeMixedVariationMass t a b +
      Complex.logarithmicPhaseQuantitativePhaseCurvatureMass t a b

theorem Complex.logarithmicPhaseQuantitativeCutoffCurvatureDensity_nonneg
    (a b : ℤ) (x : ℝ) :
    0 ≤ Complex.logarithmicPhaseQuantitativeCutoffCurvatureDensity a b x := by
  unfold Complex.logarithmicPhaseQuantitativeCutoffCurvatureDensity
  exact abs_nonneg _

theorem Complex.logarithmicPhaseQuantitativeMixedVariationDensity_nonneg
    (t : ℝ) (a b : ℤ) {x : ℝ}
    (hx : 0 < x) :
    0 ≤ Complex.logarithmicPhaseQuantitativeMixedVariationDensity t a b x := by
  unfold Complex.logarithmicPhaseQuantitativeMixedVariationDensity
  have htwo : (0 : ℝ) ≤ 2 := Nat.cast_nonneg 2
  have hcutoff : (0 : ℝ) ≤
      |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| := abs_nonneg _
  have hphase : (0 : ℝ) ≤ ‖t‖ / x :=
    div_nonneg (norm_nonneg t) hx.le
  exact mul_nonneg (mul_nonneg htwo hcutoff) hphase

theorem Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity_nonneg
    (t : ℝ) (a b : ℤ) {x : ℝ}
    (hx : 0 < x) :
    0 ≤ Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity t a b x := by
  unfold Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity
  have hcutoff := Real.quantitativeLogarithmicBlockCutoff_nonneg a b x
  have hfirst : (0 : ℝ) ≤ (‖t‖ / x) ^ 2 := sq_nonneg _
  have hsecond : (0 : ℝ) ≤ ‖t‖ / x ^ 2 :=
    div_nonneg (norm_nonneg t) (sq_nonneg x)
  exact mul_nonneg hcutoff (add_nonneg hfirst hsecond)

theorem Complex.norm_logarithmicPhaseOscillatorSecondDerivative_le
    (t : ℝ) {x : ℝ}
    (hx : 0 < x) :
    ‖Complex.logarithmicPhaseOscillatorSecondDerivative t x‖ ≤
      (‖t‖ / x) ^ 2 + ‖t‖ / x ^ 2 := by
  unfold Complex.logarithmicPhaseOscillatorSecondDerivative
  have htriangle := norm_add_le
    (Complex.logarithmicPhaseOscillator t x *
      (Complex.I * ((-t / x : ℝ) : ℂ)) *
      (Complex.I * ((-t / x : ℝ) : ℂ)))
    (Complex.logarithmicPhaseOscillator t x *
      (Complex.I * ((t / x ^ 2 : ℝ) : ℂ)))
  have hfirstFactor :=
    Complex.norm_logarithmicPhaseOscillatorFirstDerivative t hx
  have hlinearFactor :
      ‖Complex.I * ((-t / x : ℝ) : ℂ)‖ = ‖t‖ / x := by
    have hproduct := norm_mul Complex.I ((-t / x : ℝ) : ℂ)
    have hreal := Complex.norm_real (-t / x)
    have hnegative := norm_neg t
    have hxNorm := Real.norm_of_nonneg hx.le
    exact hproduct.trans
      ((congrArg₂ (fun first second : ℝ => first * second)
        Complex.norm_I
        (hreal.trans
          ((norm_div (-t) x).trans
            (congrArg₂ (fun first second : ℝ => first / second)
              hnegative hxNorm)))).trans
        (one_mul _))
  have hfirst :
      ‖Complex.logarithmicPhaseOscillator t x *
          (Complex.I * ((-t / x : ℝ) : ℂ)) *
          (Complex.I * ((-t / x : ℝ) : ℂ))‖ =
        (‖t‖ / x) ^ 2 := by
    have houter := norm_mul
      (Complex.logarithmicPhaseOscillator t x *
        (Complex.I * ((-t / x : ℝ) : ℂ)))
      (Complex.I * ((-t / x : ℝ) : ℂ))
    exact houter.trans
      ((congrArg₂ (fun first second : ℝ => first * second)
        hfirstFactor hlinearFactor).trans
        (pow_two (‖t‖ / x)).symm)
  have hsecondFactor :
      ‖Complex.I * ((t / x ^ 2 : ℝ) : ℂ)‖ = ‖t‖ / x ^ 2 := by
    have hproduct := norm_mul Complex.I ((t / x ^ 2 : ℝ) : ℂ)
    have hreal := Complex.norm_real (t / x ^ 2)
    have hxSquareNorm : ‖x ^ 2‖ = x ^ 2 :=
      Real.norm_of_nonneg (sq_nonneg x)
    exact hproduct.trans
      ((congrArg₂ (fun first second : ℝ => first * second)
        Complex.norm_I
        (hreal.trans
          ((norm_div t (x ^ 2)).trans
            (congrArg₂ (fun first second : ℝ => first / second)
              rfl hxSquareNorm)))).trans
        (one_mul _))
  have hsecond :
      ‖Complex.logarithmicPhaseOscillator t x *
          (Complex.I * ((t / x ^ 2 : ℝ) : ℂ))‖ =
        ‖t‖ / x ^ 2 := by
    exact
      (norm_mul _ _).trans
        ((congrArg₂ (fun first second : ℝ => first * second)
          (Complex.norm_logarithmicPhaseOscillator t x)
          hsecondFactor).trans
          (one_mul _))
  exact le_trans htriangle
    (le_of_eq (congrArg₂ (fun first second : ℝ => first + second)
      hfirst hsecond))

theorem Complex.norm_logarithmicPhaseQuantitativeAmplitudeSecondDerivative_le_density
    (t : ℝ) (a b : ℤ) {x : ℝ}
    (hx : 0 < x) :
    ‖Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b x‖ ≤
      Complex.logarithmicPhaseQuantitativeSecondDerivativeDensityMajorant
        t a b x := by
  have hexplicit :=
    Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative_eq_explicit
      t a b hx
  unfold Complex.logarithmicPhaseQuantitativeAmplitudeExplicitSecondDerivative at hexplicit
  unfold Complex.logarithmicPhaseQuantitativeSecondDerivativeDensityMajorant
  unfold Complex.logarithmicPhaseQuantitativeCutoffCurvatureDensity
  unfold Complex.logarithmicPhaseQuantitativeMixedVariationDensity
  unfold Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity
  have houter := norm_add_le
    ((Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x : ℂ) *
      Complex.logarithmicPhaseOscillator t x +
      (Real.quantitativeLogarithmicBlockCutoffDerivative a b x : ℂ) *
        Complex.logarithmicPhaseOscillatorFirstDerivative t x)
    ((Real.quantitativeLogarithmicBlockCutoffDerivative a b x : ℂ) *
        Complex.logarithmicPhaseOscillatorFirstDerivative t x +
      (Real.quantitativeLogarithmicBlockCutoff a b x : ℂ) *
        Complex.logarithmicPhaseOscillatorSecondDerivative t x)
  have hleft := norm_add_le
    ((Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x : ℂ) *
      Complex.logarithmicPhaseOscillator t x)
    ((Real.quantitativeLogarithmicBlockCutoffDerivative a b x : ℂ) *
      Complex.logarithmicPhaseOscillatorFirstDerivative t x)
  have hright := norm_add_le
    ((Real.quantitativeLogarithmicBlockCutoffDerivative a b x : ℂ) *
      Complex.logarithmicPhaseOscillatorFirstDerivative t x)
    ((Real.quantitativeLogarithmicBlockCutoff a b x : ℂ) *
      Complex.logarithmicPhaseOscillatorSecondDerivative t x)
  have htriangle := le_trans houter (add_le_add hleft hright)
  have hcutoffCurvature :
      ‖(Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x : ℂ) *
          Complex.logarithmicPhaseOscillator t x‖ =
        |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x| := by
    exact
      (norm_mul _ _).trans
        ((congrArg₂ (fun first second : ℝ => first * second)
          (Complex.norm_real _)
          (Complex.norm_logarithmicPhaseOscillator t x)).trans
          (mul_one _))
  have hmixedSingle :
      ‖(Real.quantitativeLogarithmicBlockCutoffDerivative a b x : ℂ) *
          Complex.logarithmicPhaseOscillatorFirstDerivative t x‖ =
        |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
          (‖t‖ / x) := by
    exact
      (norm_mul _ _).trans
        (congrArg₂ (fun first second : ℝ => first * second)
          (Complex.norm_real _)
          (Complex.norm_logarithmicPhaseOscillatorFirstDerivative t hx))
  have hphaseProduct :
      ‖(Real.quantitativeLogarithmicBlockCutoff a b x : ℂ) *
          Complex.logarithmicPhaseOscillatorSecondDerivative t x‖ ≤
        Real.quantitativeLogarithmicBlockCutoff a b x *
          ((‖t‖ / x) ^ 2 + ‖t‖ / x ^ 2) := by
    have hcutoffNorm :
        ‖(Real.quantitativeLogarithmicBlockCutoff a b x : ℂ)‖ =
          Real.quantitativeLogarithmicBlockCutoff a b x :=
      (Complex.norm_real _).trans
        (abs_of_nonneg
          (Real.quantitativeLogarithmicBlockCutoff_nonneg a b x))
    have hmul := mul_le_mul_of_nonneg_left
      (Complex.norm_logarithmicPhaseOscillatorSecondDerivative_le t hx)
      (Real.quantitativeLogarithmicBlockCutoff_nonneg a b x)
    exact le_trans (le_of_eq
      ((norm_mul _ _).trans
        (congrArg
          (fun value : ℝ => value *
            ‖Complex.logarithmicPhaseOscillatorSecondDerivative t x‖)
          hcutoffNorm))) hmul
  have hnormalized :
      |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x| +
          |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| * (‖t‖ / x) +
        (|Real.quantitativeLogarithmicBlockCutoffDerivative a b x| * (‖t‖ / x) +
          Real.quantitativeLogarithmicBlockCutoff a b x *
            ((‖t‖ / x) ^ 2 + ‖t‖ / x ^ 2)) =
        |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x| +
          2 * |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
            (‖t‖ / x) +
          Real.quantitativeLogarithmicBlockCutoff a b x *
            ((‖t‖ / x) ^ 2 + ‖t‖ / x ^ 2) := by
    have hdouble :
        |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| * (‖t‖ / x) +
          |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| * (‖t‖ / x) =
        2 * |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
          (‖t‖ / x) := by
      exact (two_mul
        (|Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
          (‖t‖ / x))).symm.trans
        (mul_assoc 2
          |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|
          (‖t‖ / x)).symm
    exact
      (add_assoc _ _ _).trans
        ((congrArg (fun value : ℝ =>
          |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x| + value)
          ((add_assoc _ _ _).symm.trans
            (congrArg
              (fun value : ℝ => value +
                Real.quantitativeLogarithmicBlockCutoff a b x *
                  ((‖t‖ / x) ^ 2 + ‖t‖ / x ^ 2))
              hdouble))).trans
          (add_assoc _ _ _).symm)
  have hterms := add_le_add
    (add_le_add (le_of_eq hcutoffCurvature) (le_of_eq hmixedSingle))
    (add_le_add (le_of_eq hmixedSingle) hphaseProduct)
  exact le_trans
    (Eq.subst
      (motive := fun value : ℂ => ‖value‖ ≤ _)
      hexplicit.symm htriangle)
    (le_trans hterms (le_of_eq hnormalized))

theorem Complex.continuous_logarithmicPhaseQuantitativeCutoffCurvatureDensity
    (a b : ℤ) :
    Continuous
      (Complex.logarithmicPhaseQuantitativeCutoffCurvatureDensity a b) := by
  unfold Complex.logarithmicPhaseQuantitativeCutoffCurvatureDensity
  have hsecondDerivative :=
    Real.contDiff_quantitativeLogarithmicBlockCutoffSecondDerivative a b
  exact hsecondDerivative.continuous.abs

theorem Complex.continuousOn_logarithmicPhaseQuantitativeMixedVariationDensity
    (t : ℝ) (a b : ℤ)
    (left right : ℝ)
    (hleft : 0 < left) :
    ContinuousOn
      (Complex.logarithmicPhaseQuantitativeMixedVariationDensity t a b)
      (Set.Icc left right) := by
  unfold Complex.logarithmicPhaseQuantitativeMixedVariationDensity
  have hcutoff : Continuous
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|) :=
    (Real.contDiff_quantitativeLogarithmicBlockCutoffDerivative a b).continuous.abs
  have hdenominator : ∀ x ∈ Set.Icc left right, x ≠ 0 :=
    fun x hx => ne_of_gt (lt_of_lt_of_le hleft hx.1)
  have hquotient : ContinuousOn (fun x : ℝ => ‖t‖ / x)
      (Set.Icc left right) :=
    continuousOn_const.div continuousOn_id hdenominator
  exact
    (continuousOn_const.mul hcutoff.continuousOn).mul hquotient

theorem Complex.continuousOn_logarithmicPhaseQuantitativePhaseCurvatureDensity
    (t : ℝ) (a b : ℤ)
    (left right : ℝ)
    (hleft : 0 < left) :
    ContinuousOn
      (Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity t a b)
      (Set.Icc left right) := by
  unfold Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity
  have hcutoff : Continuous
      (Real.quantitativeLogarithmicBlockCutoff a b) :=
    (Real.contDiff_quantitativeLogarithmicBlockCutoff a b).continuous
  have hdenominator : ∀ x ∈ Set.Icc left right, x ≠ 0 :=
    fun x hx => ne_of_gt (lt_of_lt_of_le hleft hx.1)
  have hdenominatorSquare : ∀ x ∈ Set.Icc left right, x ^ 2 ≠ 0 :=
    fun x hx => pow_ne_zero 2 (hdenominator x hx)
  have hquotient : ContinuousOn (fun x : ℝ => ‖t‖ / x)
      (Set.Icc left right) :=
    continuousOn_const.div continuousOn_id hdenominator
  have hquotientSquare : ContinuousOn (fun x : ℝ => (‖t‖ / x) ^ 2)
      (Set.Icc left right) :=
    hquotient.pow 2
  have hinverseSquare : ContinuousOn (fun x : ℝ => ‖t‖ / x ^ 2)
      (Set.Icc left right) :=
    continuousOn_const.div (continuousOn_id.pow 2) hdenominatorSquare
  exact hcutoff.continuousOn.mul (hquotientSquare.add hinverseSquare)

theorem Complex.intervalIntegrable_logarithmicPhaseQuantitativeCutoffCurvatureDensity
    (a b : ℤ) (left right : ℝ) :
    IntervalIntegrable
      (Complex.logarithmicPhaseQuantitativeCutoffCurvatureDensity a b)
      volume left right := by
  have hdensity : Continuous
      (Complex.logarithmicPhaseQuantitativeCutoffCurvatureDensity a b) :=
    Complex.continuous_logarithmicPhaseQuantitativeCutoffCurvatureDensity a b
  exact hdensity.intervalIntegrable left right

theorem Complex.intervalIntegrable_logarithmicPhaseQuantitativeMixedVariationDensity
    (t : ℝ) (a b : ℤ)
    (left right : ℝ)
    (hleft : 0 < left)
    (hleftRight : left ≤ right) :
    IntervalIntegrable
      (Complex.logarithmicPhaseQuantitativeMixedVariationDensity t a b)
      volume left right := by
  exact
    (Complex.continuousOn_logarithmicPhaseQuantitativeMixedVariationDensity
      t a b left right hleft).intervalIntegrable_of_Icc hleftRight

theorem Complex.intervalIntegrable_logarithmicPhaseQuantitativePhaseCurvatureDensity
    (t : ℝ) (a b : ℤ)
    (left right : ℝ)
    (hleft : 0 < left)
    (hleftRight : left ≤ right) :
    IntervalIntegrable
      (Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity t a b)
      volume left right := by
  exact
    (Complex.continuousOn_logarithmicPhaseQuantitativePhaseCurvatureDensity
      t a b left right hleft).intervalIntegrable_of_Icc hleftRight

theorem Complex.intervalIntegrable_logarithmicPhaseQuantitativeDensityMajorant
    (t : ℝ) (a b : ℤ)
    (left right : ℝ)
    (hleft : 0 < left)
    (hleftRight : left ≤ right) :
    IntervalIntegrable
      (Complex.logarithmicPhaseQuantitativeSecondDerivativeDensityMajorant
        t a b)
      volume left right := by
  unfold Complex.logarithmicPhaseQuantitativeSecondDerivativeDensityMajorant
  exact
    ((Complex.intervalIntegrable_logarithmicPhaseQuantitativeCutoffCurvatureDensity
      a b left right).add
      (Complex.intervalIntegrable_logarithmicPhaseQuantitativeMixedVariationDensity
        t a b left right hleft hleftRight)).add
      (Complex.intervalIntegrable_logarithmicPhaseQuantitativePhaseCurvatureDensity
        t a b left right hleft hleftRight)

theorem Complex.integral_logarithmicPhaseQuantitativeDensityMajorant_eq_decomposedMass
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      Complex.logarithmicPhaseQuantitativeSecondDerivativeDensityMajorant
        t a b x) =
      Complex.logarithmicPhaseQuantitativeDecomposedSecondDerivativeMass
        t a b := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hleft : 0 < left :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hleftRight : left ≤ right :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hcutoff :=
    Complex.intervalIntegrable_logarithmicPhaseQuantitativeCutoffCurvatureDensity
      a b left right
  have hmixed :=
    Complex.intervalIntegrable_logarithmicPhaseQuantitativeMixedVariationDensity
      t a b left right hleft hleftRight
  have hphase :=
    Complex.intervalIntegrable_logarithmicPhaseQuantitativePhaseCurvatureDensity
      t a b left right hleft hleftRight
  unfold Complex.logarithmicPhaseQuantitativeSecondDerivativeDensityMajorant
  unfold Complex.logarithmicPhaseQuantitativeDecomposedSecondDerivativeMass
  unfold Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass
  unfold Complex.logarithmicPhaseQuantitativeMixedVariationMass
  unfold Complex.logarithmicPhaseQuantitativePhaseCurvatureMass
  have houter :=
    intervalIntegral.integral_add (hcutoff.add hmixed) hphase
  have hinner := intervalIntegral.integral_add hcutoff hmixed
  exact houter.trans
    (congrArg
      (fun value : ℝ => value +
        ∫ x in left..right,
          Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity
            t a b x)
      hinner)

theorem Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_le_decomposed
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b ≤
      Complex.logarithmicPhaseQuantitativeDecomposedSecondDerivativeMass
        t a b := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hleft : 0 < left :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hleftRight : left ≤ right :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hactual : IntervalIntegrable
      (fun x : ℝ =>
        ‖Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b x‖)
      volume left right :=
    (Complex.intervalIntegrable_logarithmicPhaseQuantitativeAmplitudeSecondDerivative
      t a b ha left right).norm
  have hmajorant :=
    Complex.intervalIntegrable_logarithmicPhaseQuantitativeDensityMajorant
      t a b left right hleft hleftRight
  have hmono := intervalIntegral.integral_mono_on hleftRight hactual hmajorant
    (fun x hx =>
      Complex.norm_logarithmicPhaseQuantitativeAmplitudeSecondDerivative_le_density
        t a b (lt_of_lt_of_le hleft hx.1))
  unfold Complex.logarithmicPhaseQuantitativeSecondDerivativeMass
  exact le_trans hmono
    (le_of_eq
      (Complex.integral_logarithmicPhaseQuantitativeDensityMajorant_eq_decomposedMass
        t a b ha hab))

end
end LFunctions
end Boundary
