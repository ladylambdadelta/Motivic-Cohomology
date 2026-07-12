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
  have hnumerator :=
    (Real.contDiff_quantitativeLogarithmicBlockCutoffSecondDerivative a b)
      .continuous.abs
  exact hnumerator.div continuous_const (pow_ne_zero 2 hgap)

theorem Complex.continuous_logarithmicPhaseAdaptedVariationMassDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ) (hgap : gap ≠ 0) :
    Continuous (Complex.logarithmicPhaseAdaptedVariationMassDensity t a b gap) := by
  unfold Complex.logarithmicPhaseAdaptedVariationMassDensity
  have hnumerator :=
    (continuous_const.mul
      (Real.contDiff_quantitativeLogarithmicBlockCutoffDerivative a b)
        .continuous.abs).mul continuous_const
  exact hnumerator.div continuous_const (pow_ne_zero 3 hgap)

theorem Complex.continuous_logarithmicPhaseAdaptedThirdPhaseMassDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ) (hgap : gap ≠ 0) :
    Continuous (Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity t a b gap) := by
  unfold Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity
  have hnumerator :=
    (Real.contDiff_quantitativeLogarithmicBlockCutoff a b)
      .continuous.abs.mul continuous_const
  exact hnumerator.div continuous_const (pow_ne_zero 3 hgap)

theorem Complex.continuous_logarithmicPhaseAdaptedCurvatureSquareMassDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ) (hgap : gap ≠ 0) :
    Continuous
      (Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity t a b gap) := by
  unfold Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity
  have hnumerator :=
    (continuous_const.mul
      (Real.contDiff_quantitativeLogarithmicBlockCutoff a b)
        .continuous.abs).mul continuous_const
  exact hnumerator.div continuous_const (pow_ne_zero 4 hgap)

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
  have hpointwise := intervalIntegral.integral_congr
    (fun x hx =>
      Complex.logarithmicPhaseAdaptedClosedDensity_eq_fourTerms
        t a b gap x)
  exact Eq.trans hpointwise (Eq.trans hsum₃ rfl)

end
end LFunctions
end Boundary
