import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeAmplitudeMass

/-!
# Parameter bounds for the decomposed amplitude mass

The transition derivatives are fixed functions.  This file removes all
dependence on the logarithmic parameters from their weighted integrals by
using the positive left support endpoint.  The remaining transition variation
and curvature masses are fixed-cutoff quantities.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

def Complex.logarithmicPhaseQuantitativeCutoffVariationMass
    (a b : ℤ) : ℝ :=
  ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
      Complex.logarithmicPhaseQuantitativeSupportRight b,
    |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|

def Complex.logarithmicPhaseQuantitativeSupportLength
    (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeSupportRight b -
    Complex.logarithmicPhaseQuantitativeSupportLeft a

def Complex.logarithmicPhaseQuantitativeMixedVariationUpper
    (t : ℝ) (a b : ℤ) : ℝ :=
  2 * (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) *
    Complex.logarithmicPhaseQuantitativeCutoffVariationMass a b

def Complex.logarithmicPhaseQuantitativePhaseCurvatureUpper
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeSupportLength a b *
    ((‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 +
      ‖t‖ /
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2)

def Complex.logarithmicPhaseQuantitativeSecondDerivativeMassUpper
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b +
    Complex.logarithmicPhaseQuantitativeMixedVariationUpper t a b +
      Complex.logarithmicPhaseQuantitativePhaseCurvatureUpper t a b

theorem Complex.logarithmicPhaseQuantitativeSupportLength_nonneg
    (a b : ℤ)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeSupportLength a b := by
  unfold Complex.logarithmicPhaseQuantitativeSupportLength
  exact sub_nonneg.mpr
    (Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab)

theorem Complex.logarithmicPhaseQuantitativeCutoffVariationMass_nonneg
    (a b : ℤ)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeCutoffVariationMass a b := by
  unfold Complex.logarithmicPhaseQuantitativeCutoffVariationMass
  exact intervalIntegral.integral_nonneg
    (Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab)
    (fun x hx => abs_nonneg _)

theorem Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass_nonneg
    (a b : ℤ)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b := by
  unfold Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass
  exact intervalIntegral.integral_nonneg
    (Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab)
    (fun x hx => abs_nonneg _)

theorem Complex.div_le_div_leftSupport
    (t : ℝ) {left x : ℝ}
    (hleft : 0 < left)
    (hx : left ≤ x) :
    ‖t‖ / x ≤ ‖t‖ / left := by
  have hxPos : 0 < x := lt_of_lt_of_le hleft hx
  exact div_le_div_of_nonneg_left
    (norm_nonneg t) hleft hx

theorem Complex.div_square_le_div_leftSupport_square
    (t : ℝ) {left x : ℝ}
    (hleft : 0 < left)
    (hx : left ≤ x) :
    ‖t‖ / x ^ 2 ≤ ‖t‖ / left ^ 2 := by
  have hleftSquare : 0 < left ^ 2 := sq_pos_of_pos hleft
  have hsquare : left ^ 2 ≤ x ^ 2 := by
    have hxNonneg : 0 ≤ x := le_trans hleft.le hx
    have hproduct : left * left ≤ x * x :=
      mul_self_le_mul_self hleft.le hx
    have hleftPow : left ^ 2 = left * left := pow_two left
    have hxPow : x ^ 2 = x * x := pow_two x
    calc
      left ^ 2 = left * left := hleftPow
      _ ≤ x * x := hproduct
      _ = x ^ 2 := hxPow.symm
  exact div_le_div_of_nonneg_left
    (norm_nonneg t) hleftSquare hsquare

theorem Complex.div_sq_le_div_leftSupport_sq
    (t : ℝ) {left x : ℝ}
    (hleft : 0 < left)
    (hx : left ≤ x) :
    (‖t‖ / x) ^ 2 ≤ (‖t‖ / left) ^ 2 := by
  have hquotient := Complex.div_le_div_leftSupport t hleft hx
  have hleftQuotient : 0 ≤ ‖t‖ / left :=
    div_nonneg (norm_nonneg t) hleft.le
  have hxQuotient : 0 ≤ ‖t‖ / x := by
    have hxNonneg : 0 ≤ x := le_trans hleft.le hx
    exact div_nonneg (norm_nonneg t) hxNonneg
  have hproduct :
      (‖t‖ / x) * (‖t‖ / x) ≤
        (‖t‖ / left) * (‖t‖ / left) :=
    mul_self_le_mul_self hxQuotient hquotient
  have hxPow : (‖t‖ / x) ^ 2 = (‖t‖ / x) * (‖t‖ / x) :=
    pow_two (‖t‖ / x)
  have hleftPow :
      (‖t‖ / left) ^ 2 = (‖t‖ / left) * (‖t‖ / left) :=
    pow_two (‖t‖ / left)
  calc
    (‖t‖ / x) ^ 2 = (‖t‖ / x) * (‖t‖ / x) := hxPow
    _ ≤ (‖t‖ / left) * (‖t‖ / left) := hproduct
    _ = (‖t‖ / left) ^ 2 := hleftPow.symm

theorem Complex.logarithmicPhaseQuantitativeMixedVariationDensity_le_leftUpper
    (t : ℝ) (a b : ℤ) {x : ℝ}
    (ha : 1 ≤ a)
    (hx : Complex.logarithmicPhaseQuantitativeSupportLeft a ≤ x) :
    Complex.logarithmicPhaseQuantitativeMixedVariationDensity t a b x ≤
      2 * |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
        (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) := by
  unfold Complex.logarithmicPhaseQuantitativeMixedVariationDensity
  have hleft :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hphase := Complex.div_le_div_leftSupport t hleft hx
  have hcoefficient :
      0 ≤ 2 * |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| :=
    mul_nonneg (Nat.cast_nonneg 2) (abs_nonneg _)
  exact mul_le_mul_of_nonneg_left hphase hcoefficient

theorem Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity_le_leftUpper
    (t : ℝ) (a b : ℤ) {x : ℝ}
    (ha : 1 ≤ a)
    (hx : Complex.logarithmicPhaseQuantitativeSupportLeft a ≤ x) :
    Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity t a b x ≤
      (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 +
        ‖t‖ /
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 := by
  unfold Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity
  have hleft :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hfirst := Complex.div_sq_le_div_leftSupport_sq t hleft hx
  have hsecond := Complex.div_square_le_div_leftSupport_square t hleft hx
  have hsum := add_le_add hfirst hsecond
  have hsumNonneg :
      0 ≤ (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 +
        ‖t‖ / (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 :=
    add_nonneg (sq_nonneg _)
      (div_nonneg (norm_nonneg t) (sq_nonneg _))
  have hcutoff := Real.quantitativeLogarithmicBlockCutoff_le_one a b x
  have hcutoffNonneg := Real.quantitativeLogarithmicBlockCutoff_nonneg a b x
  have hmul :
      Real.quantitativeLogarithmicBlockCutoff a b x *
          ((‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 +
            ‖t‖ / (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) ≤
        1 *
          ((‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 +
            ‖t‖ / (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) :=
    mul_le_mul_of_nonneg_right hcutoff hsumNonneg
  exact le_trans
    (mul_le_mul_of_nonneg_left hsum hcutoffNonneg)
    (le_trans hmul (le_of_eq (one_mul _)))

theorem Complex.logarithmicPhaseQuantitativeMixedVariationMass_le_upper
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeMixedVariationMass t a b ≤
      Complex.logarithmicPhaseQuantitativeMixedVariationUpper t a b := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hleft := Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hleftRight :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hdensity :=
    Complex.intervalIntegrable_logarithmicPhaseQuantitativeMixedVariationDensity
      t a b left right hleft hleftRight
  have hvariation : IntervalIntegrable
      (fun x : ℝ =>
        2 * |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
          (‖t‖ / left)) volume left right := by
    have hcutoffDerivativeContinuous : Continuous
        (Real.quantitativeLogarithmicBlockCutoffDerivative a b) :=
      (Real.contDiff_quantitativeLogarithmicBlockCutoffDerivative a b).continuous
    have habsContinuous : Continuous
        (fun x : ℝ =>
          |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|) :=
      hcutoffDerivativeContinuous.abs
    have hbase : IntervalIntegrable
        (fun x : ℝ =>
          |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|)
        volume left right :=
      habsContinuous.intervalIntegrable left right
    exact (hbase.const_mul 2).mul_const (‖t‖ / left)
  have hmono := intervalIntegral.integral_mono_on hleftRight hdensity hvariation
    (fun x hx =>
      Complex.logarithmicPhaseQuantitativeMixedVariationDensity_le_leftUpper
        t a b ha hx.1)
  have hpull :
      (∫ x in left..right,
        2 * |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
          (‖t‖ / left)) =
        2 * (‖t‖ / left) *
          Complex.logarithmicPhaseQuantitativeCutoffVariationMass a b := by
    unfold Complex.logarithmicPhaseQuantitativeCutoffVariationMass
    have hfirst :
        (∫ x in left..right,
          2 *
            (|Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
              (‖t‖ / left))) =
          2 *
            (∫ x in left..right,
              |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
                (‖t‖ / left)) :=
      intervalIntegral.integral_const_mul 2
        (fun x : ℝ =>
          |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
            (‖t‖ / left))
    have hsecond :
        (∫ x in left..right,
          |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
            (‖t‖ / left)) =
          (∫ x in left..right,
            |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|) *
              (‖t‖ / left) :=
      intervalIntegral.integral_mul_const (‖t‖ / left)
        (fun x : ℝ =>
          |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|)
    have hinput :
        (∫ x in left..right,
          2 * |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
            (‖t‖ / left)) =
          (∫ x in left..right,
            2 *
              (|Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
                (‖t‖ / left))) :=
      intervalIntegral.integral_congr
        (fun x hx =>
          mul_assoc 2
            |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|
            (‖t‖ / left))
    have hscaledSecond := congrArg (fun value : ℝ => 2 * value) hsecond
    have hfactorComm :
        (∫ x in left..right,
          |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|) *
            (‖t‖ / left) =
          (‖t‖ / left) *
            (∫ x in left..right,
              |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|) :=
      mul_comm _ _
    have hscaledComm := congrArg (fun value : ℝ => 2 * value) hfactorComm
    have hreassociate :
        2 *
            ((‖t‖ / left) *
              (∫ x in left..right,
                |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|)) =
          2 * (‖t‖ / left) *
            (∫ x in left..right,
              |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|) :=
      (mul_assoc 2 (‖t‖ / left) _).symm
    exact Eq.trans hinput
      (Eq.trans hfirst
        (Eq.trans hscaledSecond
          (Eq.trans hscaledComm hreassociate)))
  unfold Complex.logarithmicPhaseQuantitativeMixedVariationMass
  unfold Complex.logarithmicPhaseQuantitativeMixedVariationUpper
  exact le_trans hmono (le_of_eq hpull)

theorem Complex.logarithmicPhaseQuantitativePhaseCurvatureMass_le_upper
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativePhaseCurvatureMass t a b ≤
      Complex.logarithmicPhaseQuantitativePhaseCurvatureUpper t a b := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  let constant : ℝ :=
    (‖t‖ / left) ^ 2 + ‖t‖ / left ^ 2
  have hleft := Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hleftRight :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hdensity :=
    Complex.intervalIntegrable_logarithmicPhaseQuantitativePhaseCurvatureDensity
      t a b left right hleft hleftRight
  have hconstant : IntervalIntegrable (fun _x : ℝ => constant)
      volume left right := continuous_const.intervalIntegrable left right
  have hmono := intervalIntegral.integral_mono_on hleftRight hdensity hconstant
    (fun x hx =>
      Complex.logarithmicPhaseQuantitativePhaseCurvatureDensity_le_leftUpper
        t a b ha hx.1)
  have hintegralSmul :
      (∫ _x in left..right, constant) = (right - left) • constant :=
    intervalIntegral.integral_const constant
  have hsmulMul : (right - left) • constant = (right - left) * constant :=
    Algebra.id.smul_eq_mul (right - left) constant
  have hintegral :
      (∫ _x in left..right, constant) = (right - left) * constant :=
    Eq.trans hintegralSmul hsmulMul
  unfold Complex.logarithmicPhaseQuantitativePhaseCurvatureMass
  unfold Complex.logarithmicPhaseQuantitativePhaseCurvatureUpper
  unfold Complex.logarithmicPhaseQuantitativeSupportLength
  exact le_trans hmono (le_of_eq hintegral)

theorem Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_le_upper
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b ≤
      Complex.logarithmicPhaseQuantitativeSecondDerivativeMassUpper t a b := by
  have hdecomposed :=
    Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_le_decomposed
      t a b ha hab
  have hmixed :=
    Complex.logarithmicPhaseQuantitativeMixedVariationMass_le_upper
      t a b ha hab
  have hphase :=
    Complex.logarithmicPhaseQuantitativePhaseCurvatureMass_le_upper
      t a b ha hab
  unfold Complex.logarithmicPhaseQuantitativeDecomposedSecondDerivativeMass at hdecomposed
  unfold Complex.logarithmicPhaseQuantitativeSecondDerivativeMassUpper
  have hgrouped :
      Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b +
          (Complex.logarithmicPhaseQuantitativeMixedVariationMass t a b +
            Complex.logarithmicPhaseQuantitativePhaseCurvatureMass t a b) ≤
        Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b +
          (Complex.logarithmicPhaseQuantitativeMixedVariationUpper t a b +
            Complex.logarithmicPhaseQuantitativePhaseCurvatureUpper t a b) :=
    add_le_add_left (add_le_add hmixed hphase)
      (Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b)
  have hflat :
      Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b +
            Complex.logarithmicPhaseQuantitativeMixedVariationMass t a b +
          Complex.logarithmicPhaseQuantitativePhaseCurvatureMass t a b ≤
        Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b +
            Complex.logarithmicPhaseQuantitativeMixedVariationUpper t a b +
          Complex.logarithmicPhaseQuantitativePhaseCurvatureUpper t a b := by
    calc
      Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b +
              Complex.logarithmicPhaseQuantitativeMixedVariationMass t a b +
            Complex.logarithmicPhaseQuantitativePhaseCurvatureMass t a b =
          Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b +
            (Complex.logarithmicPhaseQuantitativeMixedVariationMass t a b +
              Complex.logarithmicPhaseQuantitativePhaseCurvatureMass t a b) :=
        add_assoc _ _ _
      _ ≤ Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b +
            (Complex.logarithmicPhaseQuantitativeMixedVariationUpper t a b +
              Complex.logarithmicPhaseQuantitativePhaseCurvatureUpper t a b) :=
        hgrouped
      _ = Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b +
              Complex.logarithmicPhaseQuantitativeMixedVariationUpper t a b +
            Complex.logarithmicPhaseQuantitativePhaseCurvatureUpper t a b :=
        (add_assoc _ _ _).symm
  exact le_trans hdecomposed hflat

end
end LFunctions
end Boundary
