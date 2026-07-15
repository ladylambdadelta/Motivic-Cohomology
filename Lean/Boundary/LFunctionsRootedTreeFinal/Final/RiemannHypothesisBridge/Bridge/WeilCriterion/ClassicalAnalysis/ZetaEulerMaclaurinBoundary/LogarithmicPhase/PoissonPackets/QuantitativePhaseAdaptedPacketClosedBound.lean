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
  have hcurvatureVariation := add_le_add hcurvature hvariation
  have hcurvatureVariationThird :=
    add_le_add hcurvatureVariation hthird
  have hfourTerms := add_le_add hcurvatureVariationThird hfourth
  unfold Complex.logarithmicPhaseAdaptedFactoredMassBound
  exact le_trans (le_of_eq hdecompose) hfourTerms

theorem Complex.logarithmicPhaseAdaptedCurvatureMassTerm_eq_closed
    (gap : ℝ) :
    48 * (gap ^ 2)⁻¹ = 48 / gap ^ 2 :=
  (div_eq_mul_inv (48 : ℝ) (gap ^ 2)).symm

theorem Complex.logarithmicPhaseAdaptedVariationMassTerm_eq_closed
    (t : ℝ) (a : ℤ) (gap : ℝ) :
    2 * ((3 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3) =
    6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3 := by
  let curvature : ℝ :=
    Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
  have htwoThree : (2 : ℝ) * 3 = 6 :=
    Real.transitionSecondDerivative_natCast_mul 2 3 6 rfl
  have hnumerator :
      2 * (3 * curvature) = 6 * curvature :=
    Eq.trans
      (mul_assoc 2 3 curvature).symm
      (congrArg (fun coefficient : ℝ => coefficient * curvature) htwoThree)
  have hpull :
      2 * ((3 * curvature) / gap ^ 3) =
        (2 * (3 * curvature)) / gap ^ 3 :=
    (mul_div_assoc 2 (3 * curvature) (gap ^ 3)).symm
  exact Eq.trans hpull
    (congrArg (fun numerator : ℝ => numerator / gap ^ 3) hnumerator)

theorem Complex.logarithmicPhaseAdaptedThirdPhaseMassTerm_eq_closed
    (t : ℝ) (a b : ℤ) (gap : ℝ) :
    Complex.logarithmicPhaseQuantitativeSupportLength a b *
        (Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3) =
      Complex.logarithmicPhaseQuantitativeSupportLength a b *
        Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3 :=
  (mul_div_assoc
    (Complex.logarithmicPhaseQuantitativeSupportLength a b)
    (Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a))
    (gap ^ 3)).symm

theorem Complex.logarithmicPhaseAdaptedCurvatureSquareMassTerm_eq_closed
    (t : ℝ) (a b : ℤ) (gap : ℝ) :
    Complex.logarithmicPhaseQuantitativeSupportLength a b *
        ((3 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) /
          gap ^ 4) =
      3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
        (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2 /
          gap ^ 4 := by
  let length : ℝ := Complex.logarithmicPhaseQuantitativeSupportLength a b
  let curvatureSquare : ℝ :=
    (Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2
  have hlengthThree : length * 3 = 3 * length := mul_comm length 3
  have hnumerator :
      length * (3 * curvatureSquare) =
        3 * length * curvatureSquare :=
    Eq.trans
      (mul_assoc length 3 curvatureSquare).symm
      (congrArg
        (fun coefficient : ℝ => coefficient * curvatureSquare)
        hlengthThree)
  have hpull :
      length * ((3 * curvatureSquare) / gap ^ 4) =
        (length * (3 * curvatureSquare)) / gap ^ 4 :=
    (mul_div_assoc length (3 * curvatureSquare) (gap ^ 4)).symm
  exact Eq.trans hpull
    (congrArg (fun numerator : ℝ => numerator / gap ^ 4) hnumerator)

theorem Complex.logarithmicPhaseAdaptedFactoredMassBound_eq_closedMajorant
    (t : ℝ) (a b : ℤ) (gap : ℝ) :
    Complex.logarithmicPhaseAdaptedFactoredMassBound t a b gap =
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b gap := by
  unfold Complex.logarithmicPhaseAdaptedFactoredMassBound
  unfold Complex.logarithmicPhaseAdaptedClosedMajorant
  have hfirst : 48 * (gap ^ 2)⁻¹ = 48 / gap ^ 2 :=
    Complex.logarithmicPhaseAdaptedCurvatureMassTerm_eq_closed gap
  have hsecond :
      2 * ((3 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3) =
      6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3 :=
    Complex.logarithmicPhaseAdaptedVariationMassTerm_eq_closed t a gap
  have hthird :
      Complex.logarithmicPhaseQuantitativeSupportLength a b *
        (Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3) =
      Complex.logarithmicPhaseQuantitativeSupportLength a b *
        Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3 :=
    Complex.logarithmicPhaseAdaptedThirdPhaseMassTerm_eq_closed t a b gap
  have hfourth :
      Complex.logarithmicPhaseQuantitativeSupportLength a b *
        ((3 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) / gap ^ 4) =
      3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
        (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2 / gap ^ 4 :=
    Complex.logarithmicPhaseAdaptedCurvatureSquareMassTerm_eq_closed
      t a b gap
  have hfirstSecond :=
    congrArg₂ (fun first second : ℝ => first + second) hfirst hsecond
  have hfirstSecondThird :=
    congrArg₂ (fun firstThree third : ℝ => firstThree + third)
      hfirstSecond hthird
  exact congrArg₂ (fun firstThree fourth : ℝ => firstThree + fourth)
    hfirstSecondThird hfourth

theorem Complex.norm_logarithmicPhaseAdaptedPacket_le_closedMajorant
    (t : ℝ) (a b m : ℤ) (gap : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hgap : 0 < gap)
    (hlower : ∀ x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
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
