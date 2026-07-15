import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedPositiveNatReindex
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedIntegratedMajorant
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedPositiveTailCore

/-!
# Shift-preserving budget for the enhanced positive tail

The four terms in the phase-adapted packet majorant are transported, without
coarsening, to the generic affine reciprocal packet series.  Consequently the
positive tail retains the support-endpoint shift in every power of its phase
gap.  Each reciprocal-power series budget keeps the `n = 0` term (positive
mode one) and then adds the integral tail.  This is the arithmetic input that
the earlier inverse-square envelope discarded.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseAdaptedSquareCoefficient : ℝ :=
  48

def Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient
    (t : ℝ) (a : ℤ) : ℝ :=
  6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
    (Complex.logarithmicPhaseQuantitativeSupportLeft a)

def Complex.logarithmicPhaseAdaptedThirdCubeCoefficient
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeSupportLength a b *
    Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)

def Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient
    (t : ℝ) (a b : ℤ) : ℝ :=
  3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
    (Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2

def Complex.logarithmicPhaseEnhancedPositiveSeriesBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Real.shiftedReciprocalPacketSeriesBudget
    (Complex.logarithmicPhaseEnhancedPositiveShift t b)
    Complex.logarithmicPhaseAngularStep
    Complex.logarithmicPhaseAdaptedSquareCoefficient
    (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a)
    (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b)
    (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b)

theorem Complex.logarithmicPhaseAdaptedSquareCoefficient_nonneg :
    0 ≤ Complex.logarithmicPhaseAdaptedSquareCoefficient := by
  unfold Complex.logarithmicPhaseAdaptedSquareCoefficient
  exact Nat.cast_nonneg 48

theorem Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient_nonneg
    (t : ℝ) (a : ℤ)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a) :
    0 ≤ Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a := by
  unfold Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient
  have hcurvature :=
    Complex.logarithmicPhaseAdaptedCurvatureUpper_nonneg t _ hleft
  have hsix : (0 : ℝ) ≤ 6 := Nat.cast_nonneg 6
  exact mul_nonneg hsix hcurvature

theorem Complex.logarithmicPhaseAdaptedThirdCubeCoefficient_nonneg
    (t : ℝ) (a b : ℤ)
    (hab : a ≤ b)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a) :
    0 ≤ Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b := by
  unfold Complex.logarithmicPhaseAdaptedThirdCubeCoefficient
  have hlength :=
    Complex.logarithmicPhaseQuantitativeSupportLength_nonneg a b hab
  have hthird :=
    Complex.logarithmicPhaseAdaptedThirdDerivativeUpper_nonneg t _ hleft
  exact mul_nonneg hlength hthird

theorem Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient_nonneg
    (t : ℝ) (a b : ℤ)
    (hab : a ≤ b)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a) :
    0 ≤ Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b := by
  unfold Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient
  have hlength :=
    Complex.logarithmicPhaseQuantitativeSupportLength_nonneg a b hab
  have hcurvature :=
    Complex.logarithmicPhaseAdaptedCurvatureUpper_nonneg t _ hleft
  have hthree : (0 : ℝ) ≤ 3 := Nat.cast_nonneg 3
  have hthreeLength : 0 ≤
      3 * Complex.logarithmicPhaseQuantitativeSupportLength a b :=
    mul_nonneg hthree hlength
  exact mul_nonneg hthreeLength (pow_nonneg hcurvature 2)

theorem Real.div_eq_mul_one_div
    (u v : ℝ) :
    u / v = u * (1 / v) := by
  exact Eq.trans (div_eq_mul_inv u v)
    (congrArg (fun factor : ℝ => u * factor) (one_div v).symm)

theorem Complex.logarithmicPhaseAdaptedClosedMajorant_eq_coefficients
    (t : ℝ) (a b : ℤ) (gap : ℝ) :
    Complex.logarithmicPhaseAdaptedClosedMajorant t a b gap =
      Complex.logarithmicPhaseAdaptedSquareCoefficient * (1 / gap ^ 2) +
      Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
        (1 / gap ^ 3) +
      Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
        (1 / gap ^ 3) +
      Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
        (1 / gap ^ 4) := by
  unfold Complex.logarithmicPhaseAdaptedClosedMajorant
  unfold Complex.logarithmicPhaseAdaptedSquareCoefficient
  unfold Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient
  unfold Complex.logarithmicPhaseAdaptedThirdCubeCoefficient
  unfold Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient
  have htwo := Real.div_eq_mul_one_div 48 (gap ^ 2)
  have hcurvature := Real.div_eq_mul_one_div
    (6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) (gap ^ 3)
  have hthird := Real.div_eq_mul_one_div
    (Complex.logarithmicPhaseQuantitativeSupportLength a b *
      Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) (gap ^ 3)
  have hfourth := Real.div_eq_mul_one_div
    (3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
      Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) (gap ^ 4)
  calc
    48 / gap ^ 2 +
          (6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
            (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3 +
        (Complex.logarithmicPhaseQuantitativeSupportLength a b *
          Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
            (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3 +
      (3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
        Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) / gap ^ 4 =
        48 * (1 / gap ^ 2) +
            (6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3 +
          (Complex.logarithmicPhaseQuantitativeSupportLength a b *
            Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3 +
        (3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
          Complex.logarithmicPhaseAdaptedCurvatureUpper t
            (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) / gap ^ 4 :=
      congrArg
        (fun first : ℝ =>
          first +
              (6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
                (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3 +
            (Complex.logarithmicPhaseQuantitativeSupportLength a b *
              Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
                (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3 +
          (3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
            Complex.logarithmicPhaseAdaptedCurvatureUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) / gap ^ 4)
        htwo
    _ = 48 * (1 / gap ^ 2) +
            (6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft a)) *
              (1 / gap ^ 3) +
          (Complex.logarithmicPhaseQuantitativeSupportLength a b *
            Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3 +
        (3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
          Complex.logarithmicPhaseAdaptedCurvatureUpper t
            (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) / gap ^ 4 :=
      congrArg
        (fun second : ℝ =>
          48 * (1 / gap ^ 2) + second +
            (Complex.logarithmicPhaseQuantitativeSupportLength a b *
              Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
                (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3 +
          (3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
            Complex.logarithmicPhaseAdaptedCurvatureUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) / gap ^ 4)
        hcurvature
    _ = 48 * (1 / gap ^ 2) +
            (6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft a)) *
              (1 / gap ^ 3) +
          (Complex.logarithmicPhaseQuantitativeSupportLength a b *
            Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft a)) *
              (1 / gap ^ 3) +
        (3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
          Complex.logarithmicPhaseAdaptedCurvatureUpper t
            (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) / gap ^ 4 :=
      congrArg
        (fun third : ℝ =>
          48 * (1 / gap ^ 2) +
              (6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
                (Complex.logarithmicPhaseQuantitativeSupportLeft a)) *
                (1 / gap ^ 3) +
            third +
          (3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
            Complex.logarithmicPhaseAdaptedCurvatureUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) / gap ^ 4)
        hthird
    _ = 48 * (1 / gap ^ 2) +
            (6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft a)) *
              (1 / gap ^ 3) +
          (Complex.logarithmicPhaseQuantitativeSupportLength a b *
            Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft a)) *
              (1 / gap ^ 3) +
        (3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
          Complex.logarithmicPhaseAdaptedCurvatureUpper t
            (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) *
          (1 / gap ^ 4) :=
      congrArg
        (fun fourth : ℝ =>
          48 * (1 / gap ^ 2) +
              (6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
                (Complex.logarithmicPhaseQuantitativeSupportLeft a)) *
                (1 / gap ^ 3) +
            (Complex.logarithmicPhaseQuantitativeSupportLength a b *
              Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
                (Complex.logarithmicPhaseQuantitativeSupportLeft a)) *
                (1 / gap ^ 3) +
          fourth)
        hfourth

theorem Complex.enhancedPositiveMajorant_reindexed_eq_packetTerm
    (t : ℝ) (a b : ℤ) (n : ℕ) :
    Complex.logarithmicPhaseAdaptedClosedMajorant t a b
        (Complex.logarithmicPhaseEnhancedPositiveModeGap t b
          ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ)) =
      Real.shiftedReciprocalPacketTerm
        (Complex.logarithmicPhaseEnhancedPositiveShift t b)
        Complex.logarithmicPhaseAngularStep
        Complex.logarithmicPhaseAdaptedSquareCoefficient
        (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a)
        (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b)
        (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b)
        n := by
  have hcoefficients :=
    Complex.logarithmicPhaseAdaptedClosedMajorant_eq_coefficients
      t a b
      (Complex.logarithmicPhaseEnhancedPositiveModeGap t b
        ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ))
  have htwo :=
    Complex.enhancedPositive_inverseSquare_eq_shiftedTerm t b n
  have hthree :=
    Complex.enhancedPositive_inverseCube_eq_shiftedTerm t b n
  have hfour :=
    Complex.enhancedPositive_inverseFourth_eq_shiftedTerm t b n
  unfold Real.shiftedReciprocalPacketTerm
  calc
    Complex.logarithmicPhaseAdaptedClosedMajorant t a b
        (Complex.logarithmicPhaseEnhancedPositiveModeGap t b
          ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ)) =
      Complex.logarithmicPhaseAdaptedSquareCoefficient *
          (1 / Complex.logarithmicPhaseEnhancedPositiveModeGap t b
            ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ) ^ 2) +
        Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
          (1 / Complex.logarithmicPhaseEnhancedPositiveModeGap t b
            ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ) ^ 3) +
        Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
          (1 / Complex.logarithmicPhaseEnhancedPositiveModeGap t b
            ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ) ^ 3) +
        Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
          (1 / Complex.logarithmicPhaseEnhancedPositiveModeGap t b
            ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ) ^ 4) :=
      hcoefficients
    _ = Complex.logarithmicPhaseAdaptedSquareCoefficient *
          Real.shiftedInverseSquareTerm
            (Complex.logarithmicPhaseEnhancedPositiveShift t b)
            Complex.logarithmicPhaseAngularStep n +
        Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
          (1 / Complex.logarithmicPhaseEnhancedPositiveModeGap t b
            ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ) ^ 3) +
        Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
          (1 / Complex.logarithmicPhaseEnhancedPositiveModeGap t b
            ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ) ^ 3) +
        Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
          (1 / Complex.logarithmicPhaseEnhancedPositiveModeGap t b
            ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ) ^ 4) :=
      congrArg
        (fun squareTerm : ℝ =>
          Complex.logarithmicPhaseAdaptedSquareCoefficient * squareTerm +
            Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
              (1 / Complex.logarithmicPhaseEnhancedPositiveModeGap t b
                ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ) ^ 3) +
            Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
              (1 / Complex.logarithmicPhaseEnhancedPositiveModeGap t b
                ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ) ^ 3) +
            Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
              (1 / Complex.logarithmicPhaseEnhancedPositiveModeGap t b
                ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ) ^ 4))
        htwo
    _ = Complex.logarithmicPhaseAdaptedSquareCoefficient *
          Real.shiftedInverseSquareTerm
            (Complex.logarithmicPhaseEnhancedPositiveShift t b)
            Complex.logarithmicPhaseAngularStep n +
        Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
          Real.shiftedInverseCubeTerm
            (Complex.logarithmicPhaseEnhancedPositiveShift t b)
            Complex.logarithmicPhaseAngularStep n +
        Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
          Real.shiftedInverseCubeTerm
            (Complex.logarithmicPhaseEnhancedPositiveShift t b)
            Complex.logarithmicPhaseAngularStep n +
        Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
          (1 / Complex.logarithmicPhaseEnhancedPositiveModeGap t b
            ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ) ^ 4) :=
      congrArg
        (fun cubeTerm : ℝ =>
          Complex.logarithmicPhaseAdaptedSquareCoefficient *
              Real.shiftedInverseSquareTerm
                (Complex.logarithmicPhaseEnhancedPositiveShift t b)
                Complex.logarithmicPhaseAngularStep n +
            Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a * cubeTerm +
            Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b * cubeTerm +
            Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
              (1 / Complex.logarithmicPhaseEnhancedPositiveModeGap t b
                ((Complex.logarithmicPhasePositiveIntegerEquivNat).symm n : ℤ) ^ 4))
        hthree
    _ = Complex.logarithmicPhaseAdaptedSquareCoefficient *
          Real.shiftedInverseSquareTerm
            (Complex.logarithmicPhaseEnhancedPositiveShift t b)
            Complex.logarithmicPhaseAngularStep n +
        Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
          Real.shiftedInverseCubeTerm
            (Complex.logarithmicPhaseEnhancedPositiveShift t b)
            Complex.logarithmicPhaseAngularStep n +
        Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
          Real.shiftedInverseCubeTerm
            (Complex.logarithmicPhaseEnhancedPositiveShift t b)
            Complex.logarithmicPhaseAngularStep n +
        Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
          Real.shiftedInverseFourthTerm
            (Complex.logarithmicPhaseEnhancedPositiveShift t b)
            Complex.logarithmicPhaseAngularStep n :=
      congrArg
        (fun fourthTerm : ℝ =>
          Complex.logarithmicPhaseAdaptedSquareCoefficient *
              Real.shiftedInverseSquareTerm
                (Complex.logarithmicPhaseEnhancedPositiveShift t b)
                Complex.logarithmicPhaseAngularStep n +
            Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
              Real.shiftedInverseCubeTerm
                (Complex.logarithmicPhaseEnhancedPositiveShift t b)
                Complex.logarithmicPhaseAngularStep n +
            Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
              Real.shiftedInverseCubeTerm
                (Complex.logarithmicPhaseEnhancedPositiveShift t b)
                Complex.logarithmicPhaseAngularStep n +
            Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b * fourthTerm)
        hfour

theorem Complex.tsum_enhancedPositiveMajorant_eq_shiftedPacketTsum
    (t : ℝ) (a b : ℤ) :
    (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b
        (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m)) =
      ∑' n : ℕ,
        Real.shiftedReciprocalPacketTerm
          (Complex.logarithmicPhaseEnhancedPositiveShift t b)
          Complex.logarithmicPhaseAngularStep
          Complex.logarithmicPhaseAdaptedSquareCoefficient
          (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a)
          (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b)
          (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b)
          n := by
  have hreindex := Complex.tsum_positiveInteger_comp_equivNat
    (fun m : Complex.logarithmicPhasePoissonPositiveTailModes =>
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b
        (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m))
  have hterms := tsum_congr
    (fun n =>
      Complex.enhancedPositiveMajorant_reindexed_eq_packetTerm t a b n)
  exact Eq.trans hreindex hterms

theorem Complex.logarithmicPhaseEnhancedPositiveTailBudget_eq_series
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b =
      ∑' n : ℕ,
        Real.shiftedReciprocalPacketTerm
          (Complex.logarithmicPhaseEnhancedPositiveShift t b)
          Complex.logarithmicPhaseAngularStep
          Complex.logarithmicPhaseAdaptedSquareCoefficient
          (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a)
          (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b)
          (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b)
          n := by
  unfold Complex.logarithmicPhaseEnhancedPositiveTailBudget
  exact Complex.tsum_enhancedPositiveMajorant_eq_shiftedPacketTsum t a b

theorem Complex.logarithmicPhaseEnhancedPositiveTailBudget_le_seriesBudget
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b ≤
      Complex.logarithmicPhaseEnhancedPositiveSeriesBudget t a b := by
  have hshift :=
    Complex.logarithmicPhaseEnhancedPositiveShift_nonneg t a b ha hab
  have hstep := Complex.logarithmicPhaseAngularStep_pos
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hsquare :=
    Complex.logarithmicPhaseAdaptedSquareCoefficient_nonneg
  have hcurvature :=
    Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient_nonneg
      t a hleft
  have hthird :=
    Complex.logarithmicPhaseAdaptedThirdCubeCoefficient_nonneg
      t a b hab hleft
  have hfourth :=
    Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient_nonneg
      t a b hab hleft
  have hseries := Real.tsum_shiftedReciprocalPacketTerm_le_seriesBudget
    (Complex.logarithmicPhaseEnhancedPositiveShift t b)
    Complex.logarithmicPhaseAngularStep
    Complex.logarithmicPhaseAdaptedSquareCoefficient
    (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a)
    (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b)
    (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b)
    hshift hstep hsquare hcurvature hthird hfourth
  have hidentify :=
    Complex.logarithmicPhaseEnhancedPositiveTailBudget_eq_series t a b
  unfold Complex.logarithmicPhaseEnhancedPositiveSeriesBudget
  exact le_trans (le_of_eq hidentify) hseries

end
end LFunctions
end Boundary
