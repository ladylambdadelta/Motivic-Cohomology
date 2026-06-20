import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.AnalyticLogBranch.RadialIdentity.Owner

/-!
# Analytic logarithm branch for zero-free Jensen disks

This owner layer was split from `ZeroFreePrimitive.AnalyticLogBranch.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Normalized exponential reconstruction from the radial FTC owner root. -/
theorem entireFunction_exp_logDerivPrimitive_model_value_eq
    (G P : ℂ → ℂ)
    {ρ : ℝ}
    (hG :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ G z)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0)
    (hP_an :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ P z)
    (hP_deriv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv P z = deriv G z * (G z)⁻¹)
    (hP_zero : P 0 = 0) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      G z = G 0 * Complex.exp (P z) := by
  exact fun z hz =>
    entireFunction_convexClosedDisk_exp_logDerivPrimitive_radialSegment_endpoint_eq
      G P hG hzero hP_an hP_deriv hP_zero hz

/-- Derivative comparison between `G` and the exponential model induced by a
normalized primitive of the logarithmic derivative.

The normalization is mathematically necessary: replacing `P` by `P + C` leaves
`P' = G'/G` unchanged but rescales the model by `exp C`. -/
theorem entireFunction_exp_logDerivPrimitive_model_deriv_eq
    (G P : ℂ → ℂ)
    {ρ : ℝ}
    (hG :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ G z)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0)
    (hP_an :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ P z)
    (hP_deriv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv P z = deriv G z * (G z)⁻¹)
    (hP_zero : P 0 = 0) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      deriv G z = deriv (fun w : ℂ => G 0 * Complex.exp (P w)) z := by
  intro z hz
  have hmodel_formula :
      deriv (fun w : ℂ => G 0 * Complex.exp (P w)) z =
        G 0 * (Complex.exp (P z) * (deriv G z * (G z)⁻¹)) :=
    entireFunction_exp_logDerivPrimitive_model_deriv_formula
      G P hP_an hP_deriv z hz
  have hreconstruct_z :
      G z = G 0 * Complex.exp (P z) := by
    exact
      entireFunction_exp_logDerivPrimitive_model_value_eq
        G P hG hzero hP_an hP_deriv hP_zero z hz
  have halgebra :
      deriv G z =
        G 0 * (Complex.exp (P z) * (deriv G z * (G z)⁻¹)) :=
    entireFunction_exp_logDerivPrimitive_model_deriv_algebra
      G P (hzero z hz) hreconstruct_z
  exact Eq.trans halgebra (Eq.symm hmodel_formula)

/-- Quotient-radial owner lemma for exponential reconstruction from a
logarithmic-derivative primitive.

On the convex Jensen disk, the quotient `G / (G 0 * exp P)` has vanishing
logarithmic derivative and is normalized to `1` at the center.  This is the
right intermediate object for the radial FTC argument: once the quotient is
constant, the desired reconstruction follows by multiplying back by the
nonzero denominator. -/
theorem entireFunction_convexClosedDisk_exp_logDerivPrimitive_quotient_deriv_zero_and_center
    (G P : ℂ → ℂ)
    {ρ : ℝ}
    (hG :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ G z)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0)
    (hP_an :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ P z)
    (hP_deriv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv P z = deriv G z * (G z)⁻¹)
    (hP_zero : P 0 = 0)
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    deriv (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z = 0 ∧
      (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) 0 = 1 := by
  exact
    entireFunction_convexClosedDisk_exp_logDerivPrimitive_quotient_deriv_zero_and_center_core
      G P hG hzero hP_an hP_deriv hP_zero hz

/-- Real-interval FTC core for radial equality propagation on a convex Jensen
disk.

For a fixed endpoint `z`, the path `t ↦ t • z` stays in the disk by convexity.
Applied to `t ↦ F (t • z) - H (t • z)`, the real interval derivative-zero
constant theorem identifies the endpoint and center values. -/
theorem entireFunction_convexClosedDisk_radialSegment_endpoint_eq_of_deriv_eq_and_center_ftc
    (F H : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hH : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ H z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    (hderiv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv F z = deriv H z)
    (hcenter : F 0 = H 0)
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    F z = H z := by
  exact
    entireFunction_convexClosedDisk_radialSegment_endpoint_eq_of_deriv_eq_and_center_ftc_core
      F H hF hH hρ hconvex hderiv hcenter hz

/-- Radial FTC owner lemma for equality propagation on a convex Jensen disk.

For a fixed endpoint `z`, apply the real interval fundamental theorem of
calculus to
`t ↦ F ((t : ℂ) • z) - H ((t : ℂ) • z)` on `[0,1]`.  Convexity keeps the
radial segment in the closed disk, the complex chain rule identifies the real
derivative with the complex derivative paired with `z`, and `hderiv` makes that
derivative zero.  The interval value is therefore constant, so the endpoint
value equals the center value. -/
theorem entireFunction_convexClosedDisk_radialSegment_endpoint_eq_of_deriv_eq_and_center
    (F H : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hH : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ H z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    (hderiv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv F z = deriv H z)
    (hcenter : F 0 = H 0)
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    F z = H z := by
  exact
    entireFunction_convexClosedDisk_radialSegment_endpoint_eq_of_deriv_eq_and_center_ftc
      F H hF hH hρ hconvex hderiv hcenter hz

/-- Radial identity principle on the Jensen disk.  This is the canonical
closed-disk propagation root: restrict to the segment `t ↦ t • z`, integrate
the derivative of `F - H`, and use convexity to keep the segment inside the
disk. -/
theorem entireFunction_convexClosedDisk_eq_on_radialSegment_of_deriv_eq_and_center
    (F H : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hH : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ H z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    (hderiv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv F z = deriv H z)
    (hcenter : F 0 = H 0) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      F z = H z := by
  exact fun z hz =>
    entireFunction_convexClosedDisk_radialSegment_endpoint_eq_of_deriv_eq_and_center
      F H hF hH hρ hconvex hderiv hcenter hz

/-- Equality propagation on a convex Jensen disk from derivative equality and a
center value. -/
theorem entireFunction_convexClosedDisk_eq_of_deriv_eq_and_center
    (F H : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hH : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ H z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    (hderiv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv F z = deriv H z)
    (hcenter : F 0 = H 0) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      F z = H z := by
  exact
    entireFunction_convexClosedDisk_eq_on_radialSegment_of_deriv_eq_and_center
      F H hF hH hρ hconvex hderiv hcenter

/-- Exponential reconstruction from a normalized primitive of the logarithmic
derivative on a Jensen disk.

The proof compares `G` with `G 0 * exp P`. Their derivatives agree on the disk
because `P' = G'/G`, and both functions take the value `G 0` at the center.
Preconnectedness of the convex disk then propagates equality across the disk.
Cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_convexClosedDisk_exp_logDerivPrimitive_reconstruct
    (G P : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hG :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ G z)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0)
    (hP_an :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ P z)
    (hP_deriv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv P z = deriv G z * (G z)⁻¹)
    (hP_zero : P 0 = 0) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      G z = G 0 * Complex.exp (P z) := by
  exact
    entireFunction_exp_logDerivPrimitive_model_value_eq
      G P hG hzero hP_an hP_deriv hP_zero

end
end LFunctions
end Boundary
