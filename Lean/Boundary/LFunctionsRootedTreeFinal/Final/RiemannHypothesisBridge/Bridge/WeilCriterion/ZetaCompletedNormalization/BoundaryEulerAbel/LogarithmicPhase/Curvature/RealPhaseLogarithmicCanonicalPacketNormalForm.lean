import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicCanonicalWindowAlgebra

/-!
# Normal form of the canonical stationary packet bound

The original stationary bound is intentionally close to the integration by
parts proof and therefore repeats several center-distance expressions.  At the
canonical radius these expressions collapse.  This owner exposes a compact
normal form in terms of center `x`, radius `r`, and the single factor `‖t‖/r`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseCanonicalLeftGap
    (t : ℝ) (m : ℤ) : ℝ :=
  (‖t‖ / Complex.logarithmicPhasePoissonCanonicalRadius t m) /
    (Complex.logarithmicPhaseFourierStationaryPoint t m -
      Complex.logarithmicPhasePoissonCanonicalRadius t m)

def Complex.logarithmicPhaseCanonicalRightGap
    (t : ℝ) (b m : ℤ) : ℝ :=
  (‖t‖ / Complex.logarithmicPhasePoissonCanonicalRadius t m) /
    (b : ℝ)

def Complex.logarithmicPhaseCanonicalLeftRemainder
    (t : ℝ) (a m : ℤ) : ℝ :=
  ((Complex.logarithmicPhaseFourierStationaryPoint t m -
      Complex.logarithmicPhasePoissonCanonicalRadius t m) - (a : ℝ)) *
    ((‖t‖ / (a : ℝ) ^ 2) /
      (Complex.logarithmicPhaseCanonicalLeftGap t m) ^ 2)

def Complex.logarithmicPhaseCanonicalRightRemainder
    (t : ℝ) (b m : ℤ) : ℝ :=
  ((b : ℝ) -
      (Complex.logarithmicPhaseFourierStationaryPoint t m +
        Complex.logarithmicPhasePoissonCanonicalRadius t m)) *
    ((‖t‖ /
      (Complex.logarithmicPhaseFourierStationaryPoint t m +
        Complex.logarithmicPhasePoissonCanonicalRadius t m) ^ 2) /
      (Complex.logarithmicPhaseCanonicalRightGap t b m) ^ 2)

def Complex.logarithmicPhaseCanonicalStationaryPacketNormalForm
    (t : ℝ) (a b m : ℤ) : ℝ :=
  4 / 3 +
    (2 * (Complex.logarithmicPhaseCanonicalLeftGap t m)⁻¹ +
      Complex.logarithmicPhaseCanonicalLeftRemainder t a m) +
    2 * Complex.logarithmicPhasePoissonCanonicalRadius t m +
    (2 * (Complex.logarithmicPhaseCanonicalRightGap t b m)⁻¹ +
      Complex.logarithmicPhaseCanonicalRightRemainder t b m)

theorem Complex.logarithmicPhaseCanonical_leftGap_original_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    (2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m -
          (Complex.logarithmicPhaseFourierStationaryPoint t m -
            Complex.logarithmicPhasePoissonCanonicalRadius t m)) /
        (Complex.logarithmicPhaseFourierStationaryPoint t m -
          Complex.logarithmicPhasePoissonCanonicalRadius t m) =
      Complex.logarithmicPhaseCanonicalLeftGap t m := by
  have hgap := Complex.logarithmicPhaseCanonical_leftGap_eq t ht hm
  have hcancel :=
    Complex.logarithmicPhaseCanonical_norm_mul_radius_eq_norm_div_radius
      t ht hm
  unfold Complex.logarithmicPhaseCanonicalLeftGap
  exact Eq.trans hgap
    (congrArg
      (fun numerator : ℝ => numerator /
        (Complex.logarithmicPhaseFourierStationaryPoint t m -
          Complex.logarithmicPhasePoissonCanonicalRadius t m))
      hcancel)

theorem Complex.logarithmicPhaseCanonical_rightGap_original_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) (b : ℤ) :
    (2 * Real.pi * (-(m : ℝ))) *
        ((Complex.logarithmicPhaseFourierStationaryPoint t m +
          Complex.logarithmicPhasePoissonCanonicalRadius t m) -
          Complex.logarithmicPhaseFourierStationaryPoint t m) /
        (b : ℝ) =
      Complex.logarithmicPhaseCanonicalRightGap t b m := by
  have hgap := Complex.logarithmicPhaseCanonical_rightGap_eq t ht hm b
  have hcancel :=
    Complex.logarithmicPhaseCanonical_norm_mul_radius_eq_norm_div_radius
      t ht hm
  unfold Complex.logarithmicPhaseCanonicalRightGap
  exact Eq.trans hgap
    (congrArg (fun numerator : ℝ => numerator / (b : ℝ)) hcancel)

theorem Complex.logarithmicPhaseCanonical_leftRemainder_original_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a : ℤ)
    {m : ℤ} (hm : m < 0) :
    ((Complex.logarithmicPhaseFourierStationaryPoint t m -
        Complex.logarithmicPhasePoissonCanonicalRadius t m) - (a : ℝ)) •
      ((‖t‖ / (a : ℝ) ^ 2) /
        ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m -
            (Complex.logarithmicPhaseFourierStationaryPoint t m -
              Complex.logarithmicPhasePoissonCanonicalRadius t m)) /
          (Complex.logarithmicPhaseFourierStationaryPoint t m -
            Complex.logarithmicPhasePoissonCanonicalRadius t m)) ^ 2) =
      Complex.logarithmicPhaseCanonicalLeftRemainder t a m := by
  have hgap :=
    Complex.logarithmicPhaseCanonical_leftGap_original_eq t ht hm
  unfold Complex.logarithmicPhaseCanonicalLeftRemainder
  exact congrArg₂
    (fun length density : ℝ => length * density)
    rfl
    (congrArg
      (fun denominator : ℝ =>
        (‖t‖ / (a : ℝ) ^ 2) / denominator ^ 2) hgap)

theorem Complex.logarithmicPhaseCanonical_rightRemainder_original_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) (b : ℤ)
    {m : ℤ} (hm : m < 0) :
    ((b : ℝ) -
      (Complex.logarithmicPhaseFourierStationaryPoint t m +
        Complex.logarithmicPhasePoissonCanonicalRadius t m)) •
      ((‖t‖ /
        (Complex.logarithmicPhaseFourierStationaryPoint t m +
          Complex.logarithmicPhasePoissonCanonicalRadius t m) ^ 2) /
        ((2 * Real.pi * (-(m : ℝ))) *
          ((Complex.logarithmicPhaseFourierStationaryPoint t m +
            Complex.logarithmicPhasePoissonCanonicalRadius t m) -
            Complex.logarithmicPhaseFourierStationaryPoint t m) /
          (b : ℝ)) ^ 2) =
      Complex.logarithmicPhaseCanonicalRightRemainder t b m := by
  have hgap :=
    Complex.logarithmicPhaseCanonical_rightGap_original_eq t ht hm b
  unfold Complex.logarithmicPhaseCanonicalRightRemainder
  exact congrArg₂
    (fun length density : ℝ => length * density)
    rfl
    (congrArg
      (fun denominator : ℝ =>
        (‖t‖ /
          (Complex.logarithmicPhaseFourierStationaryPoint t m +
            Complex.logarithmicPhasePoissonCanonicalRadius t m) ^ 2) /
          denominator ^ 2) hgap)

theorem Complex.logarithmicPhaseInteriorStationaryPacketBound_canonical_eq_normalForm
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b m : ℤ) (hm : m < 0) :
    Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m
        (Complex.logarithmicPhasePoissonCanonicalRadius t m) =
      Complex.logarithmicPhaseCanonicalStationaryPacketNormalForm t a b m := by
  unfold Complex.logarithmicPhaseInteriorStationaryPacketBound
  unfold Complex.logarithmicPhaseCanonicalStationaryPacketNormalForm
  have hleftGap :=
    Complex.logarithmicPhaseCanonical_leftGap_original_eq t ht hm
  have hrightGap :=
    Complex.logarithmicPhaseCanonical_rightGap_original_eq t ht hm b
  have hleftRemainder :=
    Complex.logarithmicPhaseCanonical_leftRemainder_original_eq t ht a hm
  have hrightRemainder :=
    Complex.logarithmicPhaseCanonical_rightRemainder_original_eq t ht b hm
  have hcentral :=
    Complex.logarithmicPhaseCanonical_centralLength_eq_twoRadius t m
  exact congrArg
    (fun values : ℝ × ℝ × ℝ × ℝ × ℝ =>
      4 / 3 +
        (2 * values.1⁻¹ + values.2) +
        values.3 +
        (2 * values.4⁻¹ + values.5))
    (Prod.ext hleftGap
      (Prod.ext hleftRemainder
        (Prod.ext hcentral
          (Prod.ext hrightGap hrightRemainder))))

end
end LFunctions
end Boundary
