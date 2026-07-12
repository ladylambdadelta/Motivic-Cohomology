import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedMassEvaluation

/-!
# Constant factors in the phase-adapted mass integrals

Each density is normalized as a cutoff mass times one constant phase-gap
coefficient.  The interval integrals therefore reduce to the three canonical
cutoff masses without algebraic automation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

theorem Complex.logarithmicPhaseAdaptedCurvatureMassDensity_factor
    (a b : ℤ) (gap x : ℝ) :
    Complex.logarithmicPhaseAdaptedCurvatureMassDensity a b gap x =
      |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x| *
        (gap ^ 2)⁻¹ := by
  unfold Complex.logarithmicPhaseAdaptedCurvatureMassDensity
  exact div_eq_mul_inv _ _

theorem Complex.logarithmicPhaseAdaptedVariationMassDensity_factor
    (t : ℝ) (a b : ℤ) (gap x : ℝ) :
    Complex.logarithmicPhaseAdaptedVariationMassDensity t a b gap x =
      |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
        ((3 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) /
          gap ^ 3) := by
  unfold Complex.logarithmicPhaseAdaptedVariationMassDensity
  have hassoc := mul_assoc (3 : ℝ)
    |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|
    (Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a))
  have hcomm := mul_comm (3 : ℝ)
    |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|
  calc
    3 * |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
        Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3 =
      (|Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
        (3 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a))) / gap ^ 3 :=
      congrArg (fun value : ℝ => value / gap ^ 3)
        (Eq.trans hassoc
          (Eq.trans
            (congrArg (fun value : ℝ => value *
              Complex.logarithmicPhaseAdaptedCurvatureUpper t
                (Complex.logarithmicPhaseQuantitativeSupportLeft a)) hcomm)
            (mul_assoc _ _ _).symm))
    _ = |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
        ((3 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3) :=
      (mul_div_assoc _ _ _).symm

theorem Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity_factor
    (t : ℝ) (a b : ℤ) (gap x : ℝ) :
    Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity t a b gap x =
      |Real.quantitativeLogarithmicBlockCutoff a b x| *
        (Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3) := by
  unfold Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity
  exact (mul_div_assoc _ _ _).symm

theorem Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity_factor
    (t : ℝ) (a b : ℤ) (gap x : ℝ) :
    Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity t a b gap x =
      |Real.quantitativeLogarithmicBlockCutoff a b x| *
        ((3 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) /
          gap ^ 4) := by
  unfold Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity
  have hcomm := mul_comm (3 : ℝ)
    |Real.quantitativeLogarithmicBlockCutoff a b x|
  calc
    3 * |Real.quantitativeLogarithmicBlockCutoff a b x| *
        (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2 / gap ^ 4 =
      (|Real.quantitativeLogarithmicBlockCutoff a b x| *
        (3 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2)) /
          gap ^ 4 :=
      congrArg (fun value : ℝ => value / gap ^ 4)
        (Eq.trans
          (congrArg (fun value : ℝ => value *
            (Complex.logarithmicPhaseAdaptedCurvatureUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) hcomm)
          (mul_assoc _ _ _).symm)
    _ = |Real.quantitativeLogarithmicBlockCutoff a b x| *
        ((3 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) /
          gap ^ 4) := (mul_div_assoc _ _ _).symm

theorem Complex.integral_logarithmicPhaseAdaptedCurvatureMassDensity_factor
    (a b : ℤ) (gap : ℝ) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      Complex.logarithmicPhaseAdaptedCurvatureMassDensity a b gap x) =
      Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b *
        (gap ^ 2)⁻¹ := by
  have hpointwise := intervalIntegral.integral_congr
    (fun x hx =>
      Complex.logarithmicPhaseAdaptedCurvatureMassDensity_factor a b gap x)
  have hpull := intervalIntegral.integral_mul_const (gap ^ 2)⁻¹
    (fun x : ℝ =>
      |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x|)
  unfold Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass
  exact Eq.trans hpointwise hpull

theorem Complex.integral_logarithmicPhaseAdaptedVariationMassDensity_factor
    (t : ℝ) (a b : ℤ) (gap : ℝ) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      Complex.logarithmicPhaseAdaptedVariationMassDensity t a b gap x) =
      Complex.logarithmicPhaseQuantitativeCutoffVariationMass a b *
        ((3 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3) := by
  let coefficient :=
    (3 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3
  have hpointwise := intervalIntegral.integral_congr
    (fun x hx =>
      Complex.logarithmicPhaseAdaptedVariationMassDensity_factor
        t a b gap x)
  have hpull := intervalIntegral.integral_mul_const coefficient
    (fun x : ℝ =>
      |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|)
  unfold Complex.logarithmicPhaseQuantitativeCutoffVariationMass
  exact Eq.trans hpointwise hpull

theorem Complex.integral_logarithmicPhaseAdaptedThirdPhaseMassDensity_factor
    (t : ℝ) (a b : ℤ) (gap : ℝ) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity t a b gap x) =
      (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        |Real.quantitativeLogarithmicBlockCutoff a b x|) *
        (Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3) := by
  have hpointwise := intervalIntegral.integral_congr
    (fun x hx =>
      Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity_factor
        t a b gap x)
  have hpull := intervalIntegral.integral_mul_const
    (Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3)
    (fun x : ℝ => |Real.quantitativeLogarithmicBlockCutoff a b x|)
  exact Eq.trans hpointwise hpull

theorem Complex.integral_logarithmicPhaseAdaptedCurvatureSquareMassDensity_factor
    (t : ℝ) (a b : ℤ) (gap : ℝ) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity t a b gap x) =
      (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        |Real.quantitativeLogarithmicBlockCutoff a b x|) *
        ((3 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) /
          gap ^ 4) := by
  have hpointwise := intervalIntegral.integral_congr
    (fun x hx =>
      Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity_factor
        t a b gap x)
  have hpull := intervalIntegral.integral_mul_const
    ((3 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) / gap ^ 4)
    (fun x : ℝ => |Real.quantitativeLogarithmicBlockCutoff a b x|)
  exact Eq.trans hpointwise hpull

end
end LFunctions
end Boundary
