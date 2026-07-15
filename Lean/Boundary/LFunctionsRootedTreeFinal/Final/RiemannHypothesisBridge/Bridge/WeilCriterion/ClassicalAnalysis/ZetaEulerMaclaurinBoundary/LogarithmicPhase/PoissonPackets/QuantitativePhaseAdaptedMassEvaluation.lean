import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedClosedDensity

/-!
# Mass evaluation of the phase-adapted closed density

The four canonical terms are separated before integration.  Constant phase
and gap factors are pulled outside, leaving exactly the cutoff curvature mass,
cutoff variation mass, and two cutoff-mass integrals bounded by support length.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

def Complex.logarithmicPhaseAdaptedCurvatureMassDensity
    (a b : ℤ) (gap : ℝ) (x : ℝ) : ℝ :=
  |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x| / gap ^ 2

def Complex.logarithmicPhaseAdaptedVariationMassDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ) (x : ℝ) : ℝ :=
  3 * |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
    Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3

def Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ) (x : ℝ) : ℝ :=
  |Real.quantitativeLogarithmicBlockCutoff a b x| *
    Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3

def Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ) (x : ℝ) : ℝ :=
  3 * |Real.quantitativeLogarithmicBlockCutoff a b x| *
    (Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2 / gap ^ 4

theorem Complex.logarithmicPhaseAdaptedClosedDensity_eq_fourTerms
    (t : ℝ) (a b : ℤ) (gap x : ℝ) :
    Complex.logarithmicPhaseAdaptedClosedDensity t a b gap x =
      Complex.logarithmicPhaseAdaptedCurvatureMassDensity a b gap x +
      Complex.logarithmicPhaseAdaptedVariationMassDensity t a b gap x +
      Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity t a b gap x +
      Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity t a b gap x := by
  unfold Complex.logarithmicPhaseAdaptedClosedDensity
  unfold Complex.nonstationarySecondTransformMajorant
  unfold Complex.logarithmicPhaseAdaptedCurvatureMassDensity
  unfold Complex.logarithmicPhaseAdaptedVariationMassDensity
  unfold Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity
  unfold Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity
  exact rfl

theorem Complex.continuous_logarithmicPhaseAdaptedCurvatureMassDensity
    (a b : ℤ) (gap : ℝ) (hgap : gap ≠ 0) :
    Continuous (Complex.logarithmicPhaseAdaptedCurvatureMassDensity a b gap) := by
  unfold Complex.logarithmicPhaseAdaptedCurvatureMassDensity
  have hsecond : Continuous
      (Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b) :=
    (Real.contDiff_quantitativeLogarithmicBlockCutoffSecondDerivative a b).continuous
  have hnumerator : Continuous (fun x : ℝ =>
      |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x|) :=
    hsecond.abs
  have hdenominator : ∀ _ : ℝ, gap ^ 2 ≠ 0 :=
    fun _ => pow_ne_zero 2 hgap
  exact hnumerator.div continuous_const hdenominator

theorem Complex.continuous_logarithmicPhaseAdaptedVariationMassDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ) (hgap : gap ≠ 0) :
    Continuous (Complex.logarithmicPhaseAdaptedVariationMassDensity t a b gap) := by
  unfold Complex.logarithmicPhaseAdaptedVariationMassDensity
  have hfirst : Continuous
      (Real.quantitativeLogarithmicBlockCutoffDerivative a b) :=
    (Real.contDiff_quantitativeLogarithmicBlockCutoffDerivative a b).continuous
  have habs : Continuous (fun x : ℝ =>
      |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|) :=
    hfirst.abs
  have hthree : Continuous (fun _ : ℝ => (3 : ℝ)) := continuous_const
  have hcurvature : Continuous (fun _ : ℝ =>
      Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) :=
    continuous_const
  have hnumerator : Continuous (fun x : ℝ =>
      3 * |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
        Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) :=
    (hthree.mul habs).mul hcurvature
  have hdenominator : ∀ _ : ℝ, gap ^ 3 ≠ 0 :=
    fun _ => pow_ne_zero 3 hgap
  exact hnumerator.div continuous_const hdenominator

theorem Complex.continuous_logarithmicPhaseAdaptedThirdPhaseMassDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ) (hgap : gap ≠ 0) :
    Continuous (Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity t a b gap) := by
  unfold Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity
  have hcutoff : Continuous
      (Real.quantitativeLogarithmicBlockCutoff a b) :=
    (Real.contDiff_quantitativeLogarithmicBlockCutoff a b).continuous
  have habs : Continuous (fun x : ℝ =>
      |Real.quantitativeLogarithmicBlockCutoff a b x|) :=
    hcutoff.abs
  have hthird : Continuous (fun _ : ℝ =>
      Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) :=
    continuous_const
  have hnumerator : Continuous (fun x : ℝ =>
      |Real.quantitativeLogarithmicBlockCutoff a b x| *
        Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) :=
    habs.mul hthird
  have hdenominator : ∀ _ : ℝ, gap ^ 3 ≠ 0 :=
    fun _ => pow_ne_zero 3 hgap
  exact hnumerator.div continuous_const hdenominator

theorem Complex.continuous_logarithmicPhaseAdaptedCurvatureSquareMassDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ) (hgap : gap ≠ 0) :
    Continuous
      (Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity t a b gap) := by
  unfold Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity
  have hcutoff : Continuous
      (Real.quantitativeLogarithmicBlockCutoff a b) :=
    (Real.contDiff_quantitativeLogarithmicBlockCutoff a b).continuous
  have habs : Continuous (fun x : ℝ =>
      |Real.quantitativeLogarithmicBlockCutoff a b x|) :=
    hcutoff.abs
  have hthree : Continuous (fun _ : ℝ => (3 : ℝ)) := continuous_const
  have hcurvatureSquare : Continuous (fun _ : ℝ =>
      (Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) :=
    continuous_const
  have hnumerator : Continuous (fun x : ℝ =>
      3 * |Real.quantitativeLogarithmicBlockCutoff a b x| *
        (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) :=
    (hthree.mul habs).mul hcurvatureSquare
  have hdenominator : ∀ _ : ℝ, gap ^ 4 ≠ 0 :=
    fun _ => pow_ne_zero 4 hgap
  exact hnumerator.div continuous_const hdenominator

theorem Complex.intervalIntegrable_logarithmicPhaseAdaptedCurvatureMassDensity
    (a b : ℤ) (gap : ℝ) (hgap : gap ≠ 0) :
    IntervalIntegrable
      (Complex.logarithmicPhaseAdaptedCurvatureMassDensity a b gap)
      volume
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b) := by
  exact (Complex.continuous_logarithmicPhaseAdaptedCurvatureMassDensity
    a b gap hgap).intervalIntegrable _ _

theorem Complex.intervalIntegrable_logarithmicPhaseAdaptedVariationMassDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ) (hgap : gap ≠ 0) :
    IntervalIntegrable
      (Complex.logarithmicPhaseAdaptedVariationMassDensity t a b gap)
      volume
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b) := by
  exact (Complex.continuous_logarithmicPhaseAdaptedVariationMassDensity
    t a b gap hgap).intervalIntegrable _ _

theorem Complex.intervalIntegrable_logarithmicPhaseAdaptedThirdPhaseMassDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ) (hgap : gap ≠ 0) :
    IntervalIntegrable
      (Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity t a b gap)
      volume
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b) := by
  exact (Complex.continuous_logarithmicPhaseAdaptedThirdPhaseMassDensity
    t a b gap hgap).intervalIntegrable _ _

theorem Complex.intervalIntegrable_logarithmicPhaseAdaptedCurvatureSquareMassDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ) (hgap : gap ≠ 0) :
    IntervalIntegrable
      (Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity t a b gap)
      volume
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b) := by
  exact (Complex.continuous_logarithmicPhaseAdaptedCurvatureSquareMassDensity
    t a b gap hgap).intervalIntegrable _ _

theorem Complex.integral_logarithmicPhaseAdaptedClosedDensity_eq_fourTerms
    (t : ℝ) (a b : ℤ) (gap : ℝ) (hgap : gap ≠ 0) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      Complex.logarithmicPhaseAdaptedClosedDensity t a b gap x) =
      (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        Complex.logarithmicPhaseAdaptedCurvatureMassDensity a b gap x) +
      (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        Complex.logarithmicPhaseAdaptedVariationMassDensity t a b gap x) +
      (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity t a b gap x) +
      (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity
          t a b gap x) := by
  have hcurvature :=
    Complex.intervalIntegrable_logarithmicPhaseAdaptedCurvatureMassDensity
      a b gap hgap
  have hvariation :=
    Complex.intervalIntegrable_logarithmicPhaseAdaptedVariationMassDensity
      t a b gap hgap
  have hthird :=
    Complex.intervalIntegrable_logarithmicPhaseAdaptedThirdPhaseMassDensity
      t a b gap hgap
  have hfourth :=
    Complex.intervalIntegrable_logarithmicPhaseAdaptedCurvatureSquareMassDensity
      t a b gap hgap
  have hsum₁ := intervalIntegral.integral_add hcurvature hvariation
  have hsum₂ := intervalIntegral.integral_add (hcurvature.add hvariation) hthird
  have hsum₃ := intervalIntegral.integral_add
    ((hcurvature.add hvariation).add hthird) hfourth
  have hpointwise :
      (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        Complex.logarithmicPhaseAdaptedClosedDensity t a b gap x) =
      (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        Complex.logarithmicPhaseAdaptedCurvatureMassDensity a b gap x +
          Complex.logarithmicPhaseAdaptedVariationMassDensity t a b gap x +
          Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity t a b gap x +
          Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity
            t a b gap x) :=
    intervalIntegral.integral_congr (μ := volume)
      (a := Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (b := Complex.logarithmicPhaseQuantitativeSupportRight b)
      (fun x _ =>
      Complex.logarithmicPhaseAdaptedClosedDensity_eq_fourTerms
        t a b gap x)
  have hsplitThree := congrArg
    (fun z : ℝ =>
      z +
        (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
            Complex.logarithmicPhaseQuantitativeSupportRight b,
          Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity
            t a b gap x))
    hsum₂
  have hsplitTwo := congrArg
    (fun z : ℝ =>
      (z +
        (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
            Complex.logarithmicPhaseQuantitativeSupportRight b,
          Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity
            t a b gap x)) +
        (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
            Complex.logarithmicPhaseQuantitativeSupportRight b,
          Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity
            t a b gap x))
    hsum₁
  exact Eq.trans hpointwise
    (Eq.trans hsum₃ (Eq.trans hsplitThree hsplitTwo))

end
end LFunctions
end Boundary
