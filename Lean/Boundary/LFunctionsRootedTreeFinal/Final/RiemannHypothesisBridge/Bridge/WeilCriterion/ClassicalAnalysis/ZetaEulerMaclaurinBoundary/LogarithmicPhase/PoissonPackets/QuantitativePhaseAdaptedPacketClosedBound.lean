import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedClosedMassBound

/-!
# Deterministic closed packet bound

The four sharp mass estimates are assembled into a single packet majorant.
The public theorem takes only support geometry and a uniform positive phase
gap; all analytic estimates are discharged by the owner chain.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

def Complex.logarithmicPhaseAdaptedFactoredMassBound
    (t : ℝ) (a b : ℤ) (gap : ℝ) : ℝ :=
  48 * (gap ^ 2)⁻¹ +
    2 * ((3 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3) +
    Complex.logarithmicPhaseQuantitativeSupportLength a b *
      (Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3) +
    Complex.logarithmicPhaseQuantitativeSupportLength a b *
      ((3 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) / gap ^ 4)

theorem Complex.integral_logarithmicPhaseAdaptedClosedDensity_le_factoredMassBound
    (t : ℝ) (a b : ℤ) (gap : ℝ)
    (hab : a ≤ b)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a)
    (hgap : 0 < gap) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      Complex.logarithmicPhaseAdaptedClosedDensity t a b gap x) ≤
      Complex.logarithmicPhaseAdaptedFactoredMassBound t a b gap := by
  have hdecompose :=
    Complex.integral_logarithmicPhaseAdaptedClosedDensity_eq_fourTerms
      t a b gap (ne_of_gt hgap)
  have hcurvature :=
    Complex.integral_logarithmicPhaseAdaptedCurvatureMassDensity_le
      a b gap hab hgap.le
  have hvariation :=
    Complex.integral_logarithmicPhaseAdaptedVariationMassDensity_le
      t a b gap hab hleft hgap.le
  have hthird :=
    Complex.integral_logarithmicPhaseAdaptedThirdPhaseMassDensity_le
      t a b gap hab hleft hgap.le
  have hfourth :=
    Complex.integral_logarithmicPhaseAdaptedCurvatureSquareMassDensity_le
      t a b gap hab hgap.le
  have hsum := add_le_add (add_le_add (add_le_add hcurvature hvariation) hthird)
    hfourth
  unfold Complex.logarithmicPhaseAdaptedFactoredMassBound
  exact le_trans (le_of_eq hdecompose) hsum

theorem Complex.logarithmicPhaseAdaptedFactoredMassBound_eq_closedMajorant
    (t : ℝ) (a b : ℤ) (gap : ℝ) :
    Complex.logarithmicPhaseAdaptedFactoredMassBound t a b gap =
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b gap := by
  unfold Complex.logarithmicPhaseAdaptedFactoredMassBound
  unfold Complex.logarithmicPhaseAdaptedClosedMajorant
  have hfirst : 48 * (gap ^ 2)⁻¹ = 48 / gap ^ 2 :=
    (div_eq_mul_inv 48 (gap ^ 2)).symm
  have hsecond :
      2 * ((3 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3) =
      6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3 := by
    have hcoefficient : (2 : ℝ) * 3 = 6 := rfl
    exact Eq.trans (mul_div_assoc 2 _ _)
      (congrArg (fun value : ℝ => value / gap ^ 3)
        (Eq.trans (mul_assoc 2 3 _)
          (congrArg (fun value : ℝ => value *
            Complex.logarithmicPhaseAdaptedCurvatureUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft a)) hcoefficient)))
  have hthird :
      Complex.logarithmicPhaseQuantitativeSupportLength a b *
        (Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3) =
      Complex.logarithmicPhaseQuantitativeSupportLength a b *
        Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3 :=
    mul_div_assoc _ _ _
  have hfourth :
      Complex.logarithmicPhaseQuantitativeSupportLength a b *
        ((3 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) / gap ^ 4) =
      3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
        (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2 / gap ^ 4 := by
    have hproduct :
        Complex.logarithmicPhaseQuantitativeSupportLength a b *
          (3 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t
            (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) =
        3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
          (Complex.logarithmicPhaseAdaptedCurvatureUpper t
            (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2 := by
      exact Eq.trans (mul_assoc _ 3 _)
        (Eq.trans
          (congrArg (fun value : ℝ => value *
            (Complex.logarithmicPhaseAdaptedCurvatureUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2)
            (mul_comm _ 3))
          (mul_assoc 3 _ _).symm)
    exact Eq.trans (mul_div_assoc _ _ _)
      (congrArg (fun value : ℝ => value / gap ^ 4) hproduct)
  exact congrArg
    (fun values : ℝ × ℝ × ℝ × ℝ =>
      values.1 + values.2.1 + values.2.2.1 + values.2.2.2)
    (Prod.ext hfirst (Prod.ext hsecond (Prod.ext hthird hfourth)))

theorem Complex.norm_logarithmicPhaseAdaptedPacket_le_closedMajorant
    (t : ℝ) (a b m : ℤ) (gap : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hgap : 0 < gap)
    (hlower : ∀ x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b gap := by
  have hpacket :=
    Complex.norm_logarithmicPhaseAdaptedPacket_le_closedDensityIntegral
      t a b m gap ha hab hgap hlower
  have hleftPos :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hmass :=
    Complex.integral_logarithmicPhaseAdaptedClosedDensity_le_factoredMassBound
      t a b gap hab hleftPos.le hgap
  have hnormalize :=
    Complex.logarithmicPhaseAdaptedFactoredMassBound_eq_closedMajorant
      t a b gap
  exact le_trans hpacket (le_trans hmass (le_of_eq hnormalize))

end
end LFunctions
end Boundary
