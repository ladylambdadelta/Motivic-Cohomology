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
  let cutoffDerivative : ℝ :=
    |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|
  let curvatureUpper : ℝ :=
    Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
  have hcomm : (3 : ℝ) * cutoffDerivative = cutoffDerivative * 3 :=
    mul_comm 3 cutoffDerivative
  have hnumerator :
      (3 * cutoffDerivative) * curvatureUpper =
        cutoffDerivative * (3 * curvatureUpper) :=
    Eq.trans
      (congrArg (fun value : ℝ => value * curvatureUpper) hcomm)
      (mul_assoc cutoffDerivative 3 curvatureUpper)
  calc
    (3 * cutoffDerivative * curvatureUpper) / gap ^ 3 =
        (cutoffDerivative * (3 * curvatureUpper)) / gap ^ 3 :=
      congrArg (fun value : ℝ => value / gap ^ 3) hnumerator
    _ = cutoffDerivative * ((3 * curvatureUpper) / gap ^ 3) :=
      mul_div_assoc cutoffDerivative (3 * curvatureUpper) (gap ^ 3)

theorem Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity_factor
    (t : ℝ) (a b : ℤ) (gap x : ℝ) :
    Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity t a b gap x =
      |Real.quantitativeLogarithmicBlockCutoff a b x| *
        (Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3) := by
  unfold Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity
  exact mul_div_assoc
    |Real.quantitativeLogarithmicBlockCutoff a b x|
    (Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a))
    (gap ^ 3)

theorem Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity_factor
    (t : ℝ) (a b : ℤ) (gap x : ℝ) :
    Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity t a b gap x =
      |Real.quantitativeLogarithmicBlockCutoff a b x| *
        ((3 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) /
          gap ^ 4) := by
  unfold Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity
  let cutoff : ℝ := |Real.quantitativeLogarithmicBlockCutoff a b x|
  let curvatureSquare : ℝ :=
    (Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2
  have hcomm : (3 : ℝ) * cutoff = cutoff * 3 := mul_comm 3 cutoff
  have hnumerator :
      (3 * cutoff) * curvatureSquare = cutoff * (3 * curvatureSquare) :=
    Eq.trans
      (congrArg (fun value : ℝ => value * curvatureSquare) hcomm)
      (mul_assoc cutoff 3 curvatureSquare)
  calc
    (3 * cutoff * curvatureSquare) / gap ^ 4 =
        (cutoff * (3 * curvatureSquare)) / gap ^ 4 :=
      congrArg (fun value : ℝ => value / gap ^ 4) hnumerator
    _ = cutoff * ((3 * curvatureSquare) / gap ^ 4) :=
      mul_div_assoc cutoff (3 * curvatureSquare) (gap ^ 4)

theorem Complex.integral_logarithmicPhaseAdaptedCurvatureMassDensity_factor
    (a b : ℤ) (gap : ℝ) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      Complex.logarithmicPhaseAdaptedCurvatureMassDensity a b gap x) =
      Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b *
        (gap ^ 2)⁻¹ := by
  let left : ℝ := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right : ℝ := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hpointwise :
      (∫ x in left..right,
        Complex.logarithmicPhaseAdaptedCurvatureMassDensity a b gap x) =
      (∫ x in left..right,
        |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x| *
          (gap ^ 2)⁻¹) :=
    intervalIntegral.integral_congr
      (μ := MeasureTheory.volume) (a := left) (b := right)
      (fun x (_hx : x ∈ Set.uIcc left right) =>
        Complex.logarithmicPhaseAdaptedCurvatureMassDensity_factor a b gap x)
  have hpull :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x| *
          (gap ^ 2)⁻¹) =
      (∫ x in left..right,
        |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x|) *
          (gap ^ 2)⁻¹ :=
    intervalIntegral.integral_mul_const (gap ^ 2)⁻¹
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
  let left : ℝ := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right : ℝ := Complex.logarithmicPhaseQuantitativeSupportRight b
  let coefficient : ℝ :=
    (3 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3
  have hpointwise :
      (∫ x in left..right,
        Complex.logarithmicPhaseAdaptedVariationMassDensity t a b gap x) =
      (∫ x in left..right,
        |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
          coefficient) :=
    intervalIntegral.integral_congr
      (μ := MeasureTheory.volume) (a := left) (b := right)
      (fun x (_hx : x ∈ Set.uIcc left right) =>
        Complex.logarithmicPhaseAdaptedVariationMassDensity_factor
          t a b gap x)
  have hpull :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
          coefficient) =
      (∫ x in left..right,
        |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|) *
          coefficient :=
    intervalIntegral.integral_mul_const coefficient
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
  let left : ℝ := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right : ℝ := Complex.logarithmicPhaseQuantitativeSupportRight b
  let coefficient : ℝ :=
    Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3
  have hpointwise :
      (∫ x in left..right,
        Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity t a b gap x) =
      (∫ x in left..right,
        |Real.quantitativeLogarithmicBlockCutoff a b x| * coefficient) :=
    intervalIntegral.integral_congr
      (μ := MeasureTheory.volume) (a := left) (b := right)
      (fun x (_hx : x ∈ Set.uIcc left right) =>
        Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity_factor
          t a b gap x)
  have hpull :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicBlockCutoff a b x| * coefficient) =
      (∫ x in left..right,
        |Real.quantitativeLogarithmicBlockCutoff a b x|) * coefficient :=
    intervalIntegral.integral_mul_const coefficient
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
  let left : ℝ := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right : ℝ := Complex.logarithmicPhaseQuantitativeSupportRight b
  let coefficient : ℝ :=
    (3 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) / gap ^ 4
  have hpointwise :
      (∫ x in left..right,
        Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity t a b gap x) =
      (∫ x in left..right,
        |Real.quantitativeLogarithmicBlockCutoff a b x| * coefficient) :=
    intervalIntegral.integral_congr
      (μ := MeasureTheory.volume) (a := left) (b := right)
      (fun x (_hx : x ∈ Set.uIcc left right) =>
        Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity_factor
          t a b gap x)
  have hpull :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicBlockCutoff a b x| * coefficient) =
      (∫ x in left..right,
        |Real.quantitativeLogarithmicBlockCutoff a b x|) * coefficient :=
    intervalIntegral.integral_mul_const coefficient
      (fun x : ℝ => |Real.quantitativeLogarithmicBlockCutoff a b x|)
  exact Eq.trans hpointwise hpull

end
end LFunctions
end Boundary
