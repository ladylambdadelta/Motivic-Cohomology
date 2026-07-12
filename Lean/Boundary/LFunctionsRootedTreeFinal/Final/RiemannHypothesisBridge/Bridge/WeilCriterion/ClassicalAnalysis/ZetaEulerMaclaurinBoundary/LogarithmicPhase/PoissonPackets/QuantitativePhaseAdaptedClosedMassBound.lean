import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedMassFactors

/-!
# Closed mass bound for phase-adapted packets

The cutoff has mass at most its support length, variation mass at most two,
and curvature mass at most forty-eight.  Substitution into the four factored
integrals yields the deterministic closed packet majorant.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

theorem Real.abs_quantitativeLogarithmicBlockCutoff_le_one
    (a b : ℤ) (x : ℝ) :
    |Real.quantitativeLogarithmicBlockCutoff a b x| ≤ 1 := by
  have hnonneg := Real.quantitativeLogarithmicBlockCutoff_nonneg a b x
  have hle := Real.quantitativeLogarithmicBlockCutoff_le_one a b x
  exact le_trans (le_of_eq (abs_of_nonneg hnonneg)) hle

theorem Complex.integral_abs_quantitativeLogarithmicBlockCutoff_le_length
    (a b : ℤ) (hab : a ≤ b) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      |Real.quantitativeLogarithmicBlockCutoff a b x|) ≤
      Complex.logarithmicPhaseQuantitativeSupportLength a b := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hleftRight :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hcutoff : IntervalIntegrable
      (fun x : ℝ => |Real.quantitativeLogarithmicBlockCutoff a b x|)
      volume left right :=
    ((Real.contDiff_quantitativeLogarithmicBlockCutoff a b)
      .continuous.abs).intervalIntegrable left right
  have hone : IntervalIntegrable (fun _x : ℝ => (1 : ℝ))
      volume left right := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hleftRight hcutoff hone
    (fun x hx => Real.abs_quantitativeLogarithmicBlockCutoff_le_one a b x)
  have honeIntegral : (∫ _x in left..right, (1 : ℝ)) = right - left :=
    intervalIntegral.integral_const
  unfold Complex.logarithmicPhaseQuantitativeSupportLength
  exact le_trans hmono (le_of_eq honeIntegral)

theorem Complex.logarithmicPhaseAdaptedCurvatureCoefficient_nonneg
    (gap : ℝ) (hgap : 0 ≤ gap) :
    0 ≤ (gap ^ 2)⁻¹ := by
  exact inv_nonneg.mpr (pow_nonneg hgap 2)

theorem Complex.logarithmicPhaseAdaptedVariationCoefficient_nonneg
    (t left gap : ℝ) (hleft : 0 ≤ left) (hgap : 0 ≤ gap) :
    0 ≤ (3 * Complex.logarithmicPhaseAdaptedCurvatureUpper t left) /
      gap ^ 3 := by
  have hcurvature :=
    Complex.logarithmicPhaseAdaptedCurvatureUpper_nonneg t left hleft
  exact div_nonneg (Real.mul_three_nonneg hcurvature) (pow_nonneg hgap 3)

theorem Complex.logarithmicPhaseAdaptedThirdCoefficient_nonneg
    (t left gap : ℝ) (hleft : 0 ≤ left) (hgap : 0 ≤ gap) :
    0 ≤ Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t left /
      gap ^ 3 := by
  have hthird :=
    Complex.logarithmicPhaseAdaptedThirdDerivativeUpper_nonneg t left hleft
  exact div_nonneg hthird (pow_nonneg hgap 3)

theorem Complex.logarithmicPhaseAdaptedCurvatureSquareCoefficient_nonneg
    (t left gap : ℝ) (hgap : 0 ≤ gap) :
    0 ≤ (3 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t left) ^ 2) /
      gap ^ 4 := by
  have hnumerator := Real.mul_three_nonneg
    (sq_nonneg (Complex.logarithmicPhaseAdaptedCurvatureUpper t left))
  exact div_nonneg hnumerator (pow_nonneg hgap 4)

theorem Complex.integral_logarithmicPhaseAdaptedCurvatureMassDensity_le
    (a b : ℤ) (gap : ℝ)
    (hab : a ≤ b) (hgap : 0 ≤ gap) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      Complex.logarithmicPhaseAdaptedCurvatureMassDensity a b gap x) ≤
      48 * (gap ^ 2)⁻¹ := by
  have hfactor :=
    Complex.integral_logarithmicPhaseAdaptedCurvatureMassDensity_factor
      a b gap
  have hmass :=
    Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass_le_forty_eight
      a b hab
  have hcoefficient :=
    Complex.logarithmicPhaseAdaptedCurvatureCoefficient_nonneg gap hgap
  have hmul := mul_le_mul_of_nonneg_right hmass hcoefficient
  exact le_trans (le_of_eq hfactor) hmul

theorem Complex.integral_logarithmicPhaseAdaptedVariationMassDensity_le
    (t : ℝ) (a b : ℤ) (gap : ℝ)
    (hab : a ≤ b)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a)
    (hgap : 0 ≤ gap) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      Complex.logarithmicPhaseAdaptedVariationMassDensity t a b gap x) ≤
      2 * ((3 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3) := by
  have hfactor :=
    Complex.integral_logarithmicPhaseAdaptedVariationMassDensity_factor
      t a b gap
  have hmass :=
    Complex.logarithmicPhaseQuantitativeCutoffVariationMass_le_two a b hab
  have hcoefficient :=
    Complex.logarithmicPhaseAdaptedVariationCoefficient_nonneg
      t _ gap hleft hgap
  have hmul := mul_le_mul_of_nonneg_right hmass hcoefficient
  exact le_trans (le_of_eq hfactor) hmul

theorem Complex.integral_logarithmicPhaseAdaptedThirdPhaseMassDensity_le
    (t : ℝ) (a b : ℤ) (gap : ℝ)
    (hab : a ≤ b)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a)
    (hgap : 0 ≤ gap) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      Complex.logarithmicPhaseAdaptedThirdPhaseMassDensity t a b gap x) ≤
      Complex.logarithmicPhaseQuantitativeSupportLength a b *
        (Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3) := by
  have hfactor :=
    Complex.integral_logarithmicPhaseAdaptedThirdPhaseMassDensity_factor
      t a b gap
  have hmass :=
    Complex.integral_abs_quantitativeLogarithmicBlockCutoff_le_length a b hab
  have hcoefficient :=
    Complex.logarithmicPhaseAdaptedThirdCoefficient_nonneg t _ gap hleft hgap
  have hmul := mul_le_mul_of_nonneg_right hmass hcoefficient
  exact le_trans (le_of_eq hfactor) hmul

theorem Complex.integral_logarithmicPhaseAdaptedCurvatureSquareMassDensity_le
    (t : ℝ) (a b : ℤ) (gap : ℝ)
    (hab : a ≤ b) (hgap : 0 ≤ gap) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      Complex.logarithmicPhaseAdaptedCurvatureSquareMassDensity t a b gap x) ≤
      Complex.logarithmicPhaseQuantitativeSupportLength a b *
        ((3 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) /
          gap ^ 4) := by
  have hfactor :=
    Complex.integral_logarithmicPhaseAdaptedCurvatureSquareMassDensity_factor
      t a b gap
  have hmass :=
    Complex.integral_abs_quantitativeLogarithmicBlockCutoff_le_length a b hab
  have hcoefficient :=
    Complex.logarithmicPhaseAdaptedCurvatureSquareCoefficient_nonneg
      t _ gap hgap
  have hmul := mul_le_mul_of_nonneg_right hmass hcoefficient
  exact le_trans (le_of_eq hfactor) hmul

end
end LFunctions
end Boundary
