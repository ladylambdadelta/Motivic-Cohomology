import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.EndpointTube

/-!
# Zero-free primitive and harmonic mean-value transport

This file is a sequential owner sublayer split from the Jensen formula owner.
Declaration order is preserved so downstream import behavior remains routed
through `EntireJensenFormula.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

theorem complex_log_norm_exp_eq_re
    (w : ℂ) :
    Real.log ‖Complex.exp w‖ = w.re := by
  have hnorm_abs :
      ‖Complex.exp w‖ = Complex.abs (Complex.exp w) :=
    Complex.norm_eq_abs (Complex.exp w)
  have habs :
      Complex.abs (Complex.exp w) = Real.exp w.re :=
    Complex.abs_exp w
  calc
    Real.log ‖Complex.exp w‖ =
        Real.log (Complex.abs (Complex.exp w)) := by
      exact congrArg Real.log hnorm_abs
    _ = Real.log (Real.exp w.re) := by
      exact congrArg Real.log habs
    _ = w.re :=
      Real.log_exp w.re

/-- The Jensen boundary logarithm integrand is the displayed logarithmic norm. -/
theorem entireFunctionJensenBoundaryLogIntegrand_def_ownerRoot
    (F : ℂ → ℂ)
    (R θ : ℝ) :
    entireFunctionJensenBoundaryLogIntegrand F R θ =
      Real.log ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ :=
  rfl

/-- Boundary reduction from a chosen analytic logarithm to the real part of
that logarithm. -/
theorem entireFunction_zeroFreeQuotient_boundaryLog_eq_analyticLog_re
    (G L : ℂ → ℂ)
    (R θ : ℝ)
    (hlog :
      G ((R : ℂ) * Complex.exp (θ * Complex.I)) =
        Complex.exp (L ((R : ℂ) * Complex.exp (θ * Complex.I)))) :
    entireFunctionJensenBoundaryLogIntegrand G R θ =
      (L ((R : ℂ) * Complex.exp (θ * Complex.I))).re := by
  let z : ℂ := (R : ℂ) * Complex.exp (θ * Complex.I)
  have hdef :
      entireFunctionJensenBoundaryLogIntegrand G R θ =
        Real.log ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ :=
    entireFunctionJensenBoundaryLogIntegrand_def_ownerRoot G R θ
  have hboundary :
      Real.log ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ =
        (L z).re :=
    calc
      Real.log ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ =
          Real.log ‖Complex.exp (L z)‖ := by
        exact congrArg (fun w : ℂ => Real.log ‖w‖) hlog
      _ = (L z).re :=
        complex_log_norm_exp_eq_re (L z)
  exact Eq.trans hdef hboundary

/-- The Jensen closed disk is convex. -/
theorem entireFunction_jensenClosedDisk_convex
    (ρ : ℝ) :
    Convex ℝ (Metric.closedBall (0 : ℂ) ρ) :=
  convex_closedBall (0 : ℂ) ρ

/-- The Jensen closed disk is star-convex at its center once the radius is
nonnegative. -/
theorem entireFunction_jensenClosedDisk_starConvex_center
    {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ) :=
  (entireFunction_jensenClosedDisk_convex ρ).starConvex
    (Metric.mem_closedBall_self hρ)

/-- A zero-free entire function has an analytic reciprocal at each point of
the Jensen disk. -/
theorem entireFunction_zeroFreeOnClosedDisk_reciprocal_analyticAt
    (G : ℂ → ℂ)
    {ρ : ℝ}
    (hG : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ G z)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0)
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    AnalyticAt ℂ (fun w : ℂ => (G w)⁻¹) z :=
  (hG z hz).inv (hzero z hz)

/-- The scalar complex derivative of an analytic complex function is analytic.

This is the one-dimensional projection of the analytic Fréchet derivative. -/
theorem complex_deriv_analyticAt_of_analyticAt
    (G : ℂ → ℂ)
    {z : ℂ}
    (hGz : AnalyticAt ℂ G z) :
    AnalyticAt ℂ (fun w : ℂ => deriv G w) z := by
  have hfderiv :
      AnalyticAt ℂ (fun w : ℂ => fderiv ℂ G w) z :=
    hGz.fderiv
  have heval :
      AnalyticAt ℂ
        (fun L : ℂ →L[ℂ] ℂ => L (1 : ℂ))
        (fderiv ℂ G z) :=
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).analyticAt
      (fderiv ℂ G z)
  have hcomp :
      AnalyticAt ℂ
        ((fun L : ℂ →L[ℂ] ℂ => L (1 : ℂ)) ∘
          fun w : ℂ => fderiv ℂ G w)
        z :=
    heval.comp hfderiv
  exact hcomp.congr
    (Filter.Eventually.of_forall
      (fun w : ℂ => (fderiv_deriv (𝕜 := ℂ) (f := G) (x := w))))

/-- Analyticity of the logarithmic derivative on a zero-free closed ball.

This is the local holomorphic input for the primitive theorem: `G'` is
holomorphic because `G` is holomorphic, and `G⁻¹` is holomorphic by zero
freeness. -/
theorem complex_starConvexClosedBall_logDeriv_analyticAt
    (G : ℂ → ℂ)
    {ρ : ℝ}
    (hG : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ G z)
    (hrecip :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ (fun w : ℂ => (G w)⁻¹) z) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      AnalyticAt ℂ (fun w : ℂ => deriv G w * (G w)⁻¹) z := by
  intro z hz
  have hderiv :
      AnalyticAt ℂ (fun w : ℂ => deriv G w) z :=
    complex_deriv_analyticAt_of_analyticAt G (hG z hz)
  have hinv :
      AnalyticAt ℂ (fun w : ℂ => (G w)⁻¹) z :=
    hrecip z hz
  exact hderiv.mul hinv

/-- The radial segment integral used as the primitive on a star-convex closed
ball. -/
noncomputable def complex_starConvexClosedBall_radialPrimitive
    (φ : ℂ → ℂ)
    (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, z * φ ((t : ℂ) • z)

/-- The current radial primitive is the interval integral of its displayed
radial integrand. -/
theorem complex_starConvexClosedBall_radialPrimitive_unfold
    (φ : ℂ → ℂ)
    (z : ℂ) :
    complex_starConvexClosedBall_radialPrimitive φ z =
      ∫ t in (0 : ℝ)..1, z * φ ((t : ℂ) • z) :=
  rfl

/-- The closed complex ball contains the affine segment from its center to any
point of the ball. -/
theorem complex_starConvexClosedBall_lineMap_mem
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap (0 : ℂ) z t ∈ Metric.closedBall (0 : ℂ) ρ := by
  have hconvex :
      Convex ℝ (Metric.closedBall (0 : ℂ) ρ) :=
    convex_closedBall (0 : ℂ) ρ
  have hzero :
      (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ :=
    Metric.mem_closedBall_self hρ
  have hz_mem :
      z ∈ Metric.closedBall (0 : ℂ) ρ :=
    mem_closedBall_zero_iff.mpr hz
  exact hconvex.lineMap_mem hzero hz_mem ht

/-- The scalar radial point `(t : ℂ) • z` is the affine segment point from
`0` to `z`. -/
theorem complex_starConvexClosedBall_lineMap_zero_eq_radial
    (z : ℂ)
    (t : ℝ) :
    AffineMap.lineMap (0 : ℂ) z t = ((t : ℂ) • z) := by
  calc
    AffineMap.lineMap (0 : ℂ) z t =
        (1 - t) • (0 : ℂ) + t • z :=
      AffineMap.lineMap_apply_module (0 : ℂ) z t
    _ = 0 + t • z :=
      congrArg
        (fun u : ℂ => u + t • z)
        (show (1 - t : ℝ) • (0 : ℂ) = 0 from smul_zero (1 - t : ℝ))
    _ = t • z :=
      zero_add (t • z)
    _ = ((t : ℂ) • z) :=
      (algebraMap_smul ℂ t z).symm

/-- The radial segment from the center to a point of the closed ball remains
inside the closed ball. -/
theorem complex_starConvexClosedBall_radialSegment_mem
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((t : ℂ) • z) ∈ Metric.closedBall (0 : ℂ) ρ := by
  exact Eq.subst
    (motive := fun w : ℂ => w ∈ Metric.closedBall (0 : ℂ) ρ)
    (complex_starConvexClosedBall_lineMap_zero_eq_radial z t)
    (complex_starConvexClosedBall_lineMap_mem hρ hz ht)

/-- Norm form of closed-ball containment for radial segment points. -/
theorem complex_starConvexClosedBall_radialSegment_norm_le
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖((t : ℂ) • z)‖ ≤ ρ :=
  mem_closedBall_zero_iff.mp
    (complex_starConvexClosedBall_radialSegment_mem hρ hz ht)

/-- Segment integral of `φ` along the affine segment from the origin to `z`. -/
noncomputable def complex_centerSegmentIntegral
    (φ : ℂ → ℂ)
    (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    z * φ (AffineMap.lineMap (0 : ℂ) z t)

/-- The center-segment integral is the displayed interval integral. -/
theorem complex_centerSegmentIntegral_def_ownerRoot
    (φ : ℂ → ℂ)
    (z : ℂ) :
    complex_centerSegmentIntegral φ z =
      ∫ t in (0 : ℝ)..1,
        z * φ (AffineMap.lineMap (0 : ℂ) z t) :=
  rfl

/-- The affine-segment integral from `0` to `z` is the current radial
primitive expression. -/
theorem complex_centerSegmentIntegral_eq_radialPrimitive
    (φ : ℂ → ℂ)
    (z : ℂ) :
    complex_centerSegmentIntegral φ z =
      complex_starConvexClosedBall_radialPrimitive φ z := by
  have hintegrand :
      ∀ t : ℝ,
        t ∈
          Set.uIcc (0 : ℝ) 1 →
          (fun t : ℝ =>
            z * φ (AffineMap.lineMap (0 : ℂ) z t)) t =
          (fun t : ℝ =>
            z * φ ((t : ℂ) • z)) t :=
    fun t ht =>
      congrArg (fun w : ℂ => z * φ w)
        (complex_starConvexClosedBall_lineMap_zero_eq_radial z t)
  have hcenter :
      complex_centerSegmentIntegral φ z =
        ∫ t in (0 : ℝ)..1,
          z * φ (AffineMap.lineMap (0 : ℂ) z t) :=
    complex_centerSegmentIntegral_def_ownerRoot φ z
  have hintegral :
      (∫ t in (0 : ℝ)..1,
          z * φ (AffineMap.lineMap (0 : ℂ) z t)) =
        ∫ t in (0 : ℝ)..1, z * φ ((t : ℂ) • z) :=
    intervalIntegral.integral_congr hintegrand
  have hradial :
      (∫ t in (0 : ℝ)..1, z * φ ((t : ℂ) • z)) =
        complex_starConvexClosedBall_radialPrimitive φ z :=
    (complex_starConvexClosedBall_radialPrimitive_unfold φ z).symm
  exact Eq.trans hcenter (Eq.trans hintegral hradial)

/-- Star-convexity keeps every center-to-endpoint segment inside the domain. -/
theorem complex_starConvex_centerSegment_mem
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    {z : ℂ}
    (hz : z ∈ s)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap (0 : ℂ) z t ∈ s := by
  have h_image :
      AffineMap.lineMap (0 : ℂ) z t ∈
        (AffineMap.lineMap (0 : ℂ) z) '' Set.Icc (0 : ℝ) 1 :=
    Set.mem_image_of_mem (AffineMap.lineMap (0 : ℂ) z) ht
  have h_segment :
      AffineMap.lineMap (0 : ℂ) z t ∈
        segment ℝ (0 : ℂ) z :=
    Eq.subst
      (motive := fun u : Set ℂ =>
        AffineMap.lineMap (0 : ℂ) z t ∈ u)
      ((segment_eq_image_lineMap (𝕜 := ℝ) (0 : ℂ) z).symm)
      h_image
  exact hstar.segment_subset hz h_segment

/-- Holomorphicity of the integrand transported along center-to-endpoint
segments in a star-convex domain. -/
theorem complex_starConvex_centerSegment_analyticAt
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z)
    {z : ℂ}
    (hz : z ∈ s)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AnalyticAt ℂ φ (AffineMap.lineMap (0 : ℂ) z t) :=
  hφ (AffineMap.lineMap (0 : ℂ) z t)
    (complex_starConvex_centerSegment_mem hstar hz ht)

/-- The radial primitive is normalized to vanish at the center. -/
theorem complex_starConvexClosedBall_radialPrimitive_zero
    (φ : ℂ → ℂ) :
    complex_starConvexClosedBall_radialPrimitive φ 0 = 0 := by
  have hzero_integrand :
      ∀ t : ℝ,
        t ∈
          Set.uIcc (0 : ℝ) 1 →
          (fun t : ℝ => (0 : ℂ) * φ ((t : ℂ) • (0 : ℂ))) t =
          (fun _ : ℝ => (0 : ℂ)) t :=
    fun t ht => zero_mul (φ ((t : ℂ) • (0 : ℂ)))
  have hdef :
      complex_starConvexClosedBall_radialPrimitive φ 0 =
        ∫ t in (0 : ℝ)..1, (0 : ℂ) * φ ((t : ℂ) • (0 : ℂ)) :=
    complex_starConvexClosedBall_radialPrimitive_unfold φ 0
  have hintegral :
      (∫ t in (0 : ℝ)..1, (0 : ℂ) * φ ((t : ℂ) • (0 : ℂ))) =
        ∫ _t in (0 : ℝ)..1, (0 : ℂ) :=
    intervalIntegral.integral_congr hzero_integrand
  exact Eq.trans hdef (Eq.trans hintegral intervalIntegral.integral_zero)

/-- The explicit endpoint derivative integrand obtained by differentiating
`w ↦ w * φ(lineMap 0 w t)` at `z`. -/
noncomputable def complex_centerSegmentIntegral_endpointDerivativeIntegrand
    (φ : ℂ → ℂ)
    (z : ℂ)
    (t : ℝ) : ℂ :=
  φ (AffineMap.lineMap (0 : ℂ) z t) +
    z * (t : ℂ) * deriv φ (AffineMap.lineMap (0 : ℂ) z t)

/-- The scalar radial primitive whose real derivative is the endpoint
derivative integrand. -/
noncomputable def complex_centerSegmentIntegral_radialFTCPrimitive
    (φ : ℂ → ℂ)
    (z : ℂ)
    (t : ℝ) : ℂ :=
  (t : ℂ) * φ (AffineMap.lineMap (0 : ℂ) z t)

/-- Complex endpoint derivative of `w ↦ lineMap 0 w t`. -/
theorem complex_centerSegment_lineMap_hasDerivAt_endpoint
    (z : ℂ)
    (t : ℝ) :
    HasDerivAt
      (fun w : ℂ => AffineMap.lineMap (0 : ℂ) w t)
      (t : ℂ)
      z := by
  have hmul :
      HasDerivAt
        (fun w : ℂ => (t : ℂ) * w)
        ((t : ℂ) * (1 : ℂ))
        z :=
    HasDerivAt.const_mul (t : ℂ) (hasDerivAt_id' z)
  have hmul_one :
      HasDerivAt
        (fun w : ℂ => (t : ℂ) * w)
        (t : ℂ)
        z :=
    Eq.subst
      (motive := fun d : ℂ =>
        HasDerivAt
          (fun w : ℂ => (t : ℂ) * w)
          d
          z)
      (mul_one (t : ℂ))
      hmul
  have hfun :
      (fun w : ℂ => AffineMap.lineMap (0 : ℂ) w t) =
        fun w : ℂ => (t : ℂ) * w :=
    funext
      (fun w : ℂ =>
      calc
        AffineMap.lineMap (0 : ℂ) w t = t • (w - 0) + 0 :=
          AffineMap.lineMap_apply_module' (0 : ℂ) w t
        _ = (t : ℂ) * (w - 0) + 0 :=
          rfl
        _ = (t : ℂ) * w + 0 :=
          congrArg (fun a : ℂ => (t : ℂ) * a + 0) (sub_zero w)
        _ = (t : ℂ) * w :=
          add_zero ((t : ℂ) * w))
  exact
    Eq.subst
      (motive := fun f : ℂ → ℂ =>
        HasDerivAt f (t : ℂ) z)
      hfun.symm
      hmul_one

/-- Algebraic normalization for the complex endpoint derivative of
`w * φ(lineMap 0 w t)`. -/
theorem complex_centerSegmentIntegral_endpointDerivative_eq_productRule
    (φ : ℂ → ℂ)
    (z : ℂ)
    (t : ℝ) :
    (1 : ℂ) * φ (AffineMap.lineMap (0 : ℂ) z t) +
      z * ((t : ℂ) * deriv φ (AffineMap.lineMap (0 : ℂ) z t)) =
      complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t := by
  let x : ℂ := AffineMap.lineMap (0 : ℂ) z t
  let d : ℂ := deriv φ x
  have hfirst :
      (1 : ℂ) * φ x = φ x :=
    one_mul (φ x)
  have hsecond :
      z * ((t : ℂ) * d) = z * (t : ℂ) * d :=
    (mul_assoc z (t : ℂ) d).symm
  calc
    (1 : ℂ) * φ (AffineMap.lineMap (0 : ℂ) z t) +
        z * ((t : ℂ) *
          deriv φ (AffineMap.lineMap (0 : ℂ) z t)) =
        φ x + z * (t : ℂ) * d :=
      congrArg₂ (fun a b : ℂ => a + b) hfirst hsecond
    _ = complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t :=
      rfl

/-- Pointwise endpoint derivative of the center-segment integrand.

For fixed parameter `t`, differentiating
`w ↦ w * φ(lineMap 0 w t)` gives the displayed endpoint derivative
integrand. -/
theorem complex_centerSegmentIntegral_integrand_hasDerivAt_endpoint
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ) 1 →
            HasDerivAt
              (fun w : ℂ =>
                w * φ (AffineMap.lineMap (0 : ℂ) w t))
              (complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t)
              z := by
  intro z hz t ht
  let x : ℂ := AffineMap.lineMap (0 : ℂ) z t
  have hφ_at :
      HasDerivAt φ (deriv φ x) x :=
    (complex_starConvex_centerSegment_analyticAt
      φ hstar hφ hz ht).differentiableAt.hasDerivAt
  have hline :
      HasDerivAt
        (fun w : ℂ => AffineMap.lineMap (0 : ℂ) w t)
        (t : ℂ)
        z :=
    complex_centerSegment_lineMap_hasDerivAt_endpoint z t
  have hcomp_raw :
      HasDerivAt
        (fun w : ℂ => φ (AffineMap.lineMap (0 : ℂ) w t))
        (deriv φ x * (t : ℂ))
        z :=
    hφ_at.comp z hline
  have hcomp :
      HasDerivAt
        (fun w : ℂ => φ (AffineMap.lineMap (0 : ℂ) w t))
        ((t : ℂ) * deriv φ x)
        z :=
    Eq.subst
      (motive := fun d : ℂ =>
        HasDerivAt
          (fun w : ℂ => φ (AffineMap.lineMap (0 : ℂ) w t))
          d
          z)
      (mul_comm (deriv φ x) (t : ℂ))
      hcomp_raw
  have hid :
      HasDerivAt (fun w : ℂ => w) (1 : ℂ) z :=
    hasDerivAt_id' z
  have hprod :
      HasDerivAt
        (fun w : ℂ =>
          w * φ (AffineMap.lineMap (0 : ℂ) w t))
        ((1 : ℂ) * φ (AffineMap.lineMap (0 : ℂ) z t) +
          z * ((t : ℂ) * deriv φ x))
        z :=
    hid.mul hcomp
  exact
    Eq.subst
      (motive := fun d : ℂ =>
        HasDerivAt
          (fun w : ℂ =>
            w * φ (AffineMap.lineMap (0 : ℂ) w t))
          d
          z)
      (complex_centerSegmentIntegral_endpointDerivative_eq_productRule
        φ z t)
      hprod

/-- Pointwise endpoint derivative of the center-segment integrand from local
analyticity at the segment point.

This is the tube-local version of
`complex_centerSegmentIntegral_integrand_hasDerivAt_endpoint`; it does not
need the endpoint itself to lie in the star-convex set, only analyticity of
`φ` at the current segment point. -/
theorem complex_centerSegmentIntegral_integrand_hasDerivAt_endpoint_of_analyticAt
    (φ : ℂ → ℂ) :
    ∀ z : ℂ,
      ∀ t : ℝ,
        AnalyticAt ℂ φ (AffineMap.lineMap (0 : ℂ) z t) →
          HasDerivAt
            (fun w : ℂ =>
              w * φ (AffineMap.lineMap (0 : ℂ) w t))
            (complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t)
            z := by
  intro z t hφ_at_segment
  let x : ℂ := AffineMap.lineMap (0 : ℂ) z t
  have hφ_at :
      HasDerivAt φ (deriv φ x) x :=
    hφ_at_segment.differentiableAt.hasDerivAt
  have hline :
      HasDerivAt
        (fun w : ℂ => AffineMap.lineMap (0 : ℂ) w t)
        (t : ℂ)
        z :=
    complex_centerSegment_lineMap_hasDerivAt_endpoint z t
  have hcomp_raw :
      HasDerivAt
        (fun w : ℂ => φ (AffineMap.lineMap (0 : ℂ) w t))
        (deriv φ x * (t : ℂ))
        z :=
    hφ_at.comp z hline
  have hcomp :
      HasDerivAt
        (fun w : ℂ => φ (AffineMap.lineMap (0 : ℂ) w t))
        ((t : ℂ) * deriv φ x)
        z :=
    Eq.subst
      (motive := fun d : ℂ =>
        HasDerivAt
          (fun w : ℂ => φ (AffineMap.lineMap (0 : ℂ) w t))
          d
          z)
      (mul_comm (deriv φ x) (t : ℂ))
      hcomp_raw
  have hid :
      HasDerivAt (fun w : ℂ => w) (1 : ℂ) z :=
    hasDerivAt_id' z
  have hprod :
      HasDerivAt
        (fun w : ℂ =>
          w * φ (AffineMap.lineMap (0 : ℂ) w t))
        ((1 : ℂ) * φ (AffineMap.lineMap (0 : ℂ) z t) +
          z * ((t : ℂ) * deriv φ x))
        z :=
    hid.mul hcomp
  exact
    Eq.subst
      (motive := fun d : ℂ =>
        HasDerivAt
          (fun w : ℂ =>
            w * φ (AffineMap.lineMap (0 : ℂ) w t))
          d
          z)
      (complex_centerSegmentIntegral_endpointDerivative_eq_productRule
        φ z t)
      hprod

/-- Compactness of the affine center-to-endpoint segment. -/
theorem complex_centerSegment_image_Icc_isCompact
    (z : ℂ) :
    IsCompact
      ((fun t : ℝ => AffineMap.lineMap (k := ℝ) (0 : ℂ) z t) ''
        Set.Icc (0 : ℝ) 1) := by
  exact
    isCompact_Icc.image
      (AffineMap.lineMap_continuous (p := (0 : ℂ)) (v := z))

/-- Finite cover of a compact center segment by analytic-at neighborhoods of
`φ`.

The open set `{w | AnalyticAt ℂ φ w}` contains the center segment by
star-convexity and the local analyticity hypothesis, so compactness of the
segment gives a finite list of segment points whose analytic neighborhoods
cover the segment. -/
theorem complex_centerSegment_finiteAnalyticAtCover
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        IsCompact
          ((fun t : ℝ => AffineMap.lineMap (0 : ℂ) z t) ''
            Set.Icc (0 : ℝ) 1) →
          ∃ centers : Finset ℂ,
            (∀ c : ℂ, c ∈ centers → AnalyticAt ℂ φ c) ∧
            ((fun t : ℝ => AffineMap.lineMap (0 : ℂ) z t) ''
                Set.Icc (0 : ℝ) 1) ⊆
              ⋃ c ∈ centers, {w : ℂ | AnalyticAt ℂ φ w} := by
  intro z hz _hcompact
  have hcenter_analytic :
      ∀ c : ℂ, c ∈ ({z} : Finset ℂ) → AnalyticAt ℂ φ c :=
    fun c hc =>
      Eq.subst
        (motive := fun q : ℂ => AnalyticAt ℂ φ q)
        (Finset.mem_singleton.mp hc).symm
        (hφ z hz)
  have hcover :
      ((fun t : ℝ => AffineMap.lineMap (0 : ℂ) z t) ''
          Set.Icc (0 : ℝ) 1) ⊆
        ⋃ c ∈ ({z} : Finset ℂ), {w : ℂ | AnalyticAt ℂ φ w} :=
    fun w hw =>
      match hw with
      | Exists.intro t htw =>
          match htw with
          | And.intro ht hwt =>
              Set.mem_iUnion.2
                (Exists.intro z
                  (Set.mem_iUnion.2
                    (Exists.intro (Finset.mem_singleton_self z)
                        (Eq.subst
                          (motive := fun q : ℂ => AnalyticAt ℂ φ q)
                          hwt
                          (complex_starConvex_centerSegment_analyticAt
                            φ hstar hφ hz ht)))))
  exact Exists.intro ({z} : Finset ℂ) (And.intro hcenter_analytic hcover)

/-- Continuity on the parameter interval of the center-segment integrand on a
finite analytic tube. -/
theorem complex_centerSegmentIntegral_finiteTube_integrand_continuousOn
    (φ : ℂ → ℂ)
    (centers : Finset ℂ) :
    ∀ w : ℂ,
      (∀ t : ℝ,
        t ∈ Set.Icc (0 : ℝ) 1 →
          AffineMap.lineMap (0 : ℂ) w t ∈
            ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q}) →
        ContinuousOn
          (fun t : ℝ =>
            w * φ (AffineMap.lineMap (0 : ℂ) w t))
          (Set.Icc (0 : ℝ) 1) := by
  intro w htube t ht
  have hanalytic_mem :
      AffineMap.lineMap (0 : ℂ) w t ∈
        ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q} :=
    htube t ht
  have hanalytic :
      AnalyticAt ℂ φ (AffineMap.lineMap (0 : ℂ) w t) :=
    match Set.mem_iUnion.1 hanalytic_mem with
    | ⟨_c, hc_mem⟩ =>
      match Set.mem_iUnion.1 hc_mem with
      | ⟨_hc, hpoint⟩ => hpoint
  have hline_cont :
      ContinuousAt
        (fun u : ℝ => AffineMap.lineMap (0 : ℂ) w u)
        t :=
    (AffineMap.lineMap_continuous (p := (0 : ℂ)) (v := w)).continuousAt
  have hφ_cont :
      ContinuousAt
        (fun u : ℝ => φ (AffineMap.lineMap (0 : ℂ) w u))
        t :=
    hanalytic.differentiableAt.continuousAt.comp hline_cont
  exact (continuousAt_const.mul hφ_cont).continuousWithinAt

/-- Continuity on the parameter interval of the endpoint derivative integrand
on a finite analytic tube. -/
theorem complex_centerSegmentIntegral_finiteTube_endpointDerivative_continuousOn
    (φ : ℂ → ℂ)
    (centers : Finset ℂ) :
    ∀ w : ℂ,
      (∀ t : ℝ,
        t ∈ Set.Icc (0 : ℝ) 1 →
          AffineMap.lineMap (0 : ℂ) w t ∈
            ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q}) →
        ContinuousOn
          (fun t : ℝ =>
            complex_centerSegmentIntegral_endpointDerivativeIntegrand φ w t)
          (Set.Icc (0 : ℝ) 1) := by
  intro w htube
  have hφ_seg :
      ContinuousOn
        (fun t : ℝ =>
          φ (AffineMap.lineMap (0 : ℂ) w t))
        (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    have hanalytic_mem :
        AffineMap.lineMap (0 : ℂ) w t ∈
          ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q} :=
      htube t ht
    have hanalytic :
        AnalyticAt ℂ φ (AffineMap.lineMap (0 : ℂ) w t) :=
      match Set.mem_iUnion.1 hanalytic_mem with
      | ⟨_c, hc_mem⟩ =>
        match Set.mem_iUnion.1 hc_mem with
        | ⟨_hc, hpoint⟩ => hpoint
    have hline_cont :
        ContinuousAt
          (fun u : ℝ => AffineMap.lineMap (0 : ℂ) w u)
          t :=
      (AffineMap.lineMap_continuous (p := (0 : ℂ)) (v := w)).continuousAt
    exact (hanalytic.differentiableAt.continuousAt.comp hline_cont).continuousWithinAt
  have hderiv_seg :
      ContinuousOn
        (fun t : ℝ =>
          deriv φ (AffineMap.lineMap (0 : ℂ) w t))
        (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    have hanalytic_mem :
        AffineMap.lineMap (0 : ℂ) w t ∈
          ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q} :=
      htube t ht
    have hanalytic :
        AnalyticAt ℂ φ (AffineMap.lineMap (0 : ℂ) w t) :=
      match Set.mem_iUnion.1 hanalytic_mem with
      | ⟨_c, hc_mem⟩ =>
        match Set.mem_iUnion.1 hc_mem with
        | ⟨_hc, hpoint⟩ => hpoint
    have hderiv_analytic :
        AnalyticAt ℂ
          (fun q : ℂ => deriv φ q)
          (AffineMap.lineMap (0 : ℂ) w t) :=
      complex_deriv_analyticAt_of_analyticAt φ hanalytic
    have hline_cont :
        ContinuousAt
          (fun u : ℝ => AffineMap.lineMap (0 : ℂ) w u)
          t :=
      (AffineMap.lineMap_continuous (p := (0 : ℂ)) (v := w)).continuousAt
    exact
      (hderiv_analytic.differentiableAt.continuousAt.comp
        hline_cont).continuousWithinAt
  have ht_complex :
      ContinuousOn
        (fun t : ℝ => (t : ℂ))
        (Set.Icc (0 : ℝ) 1) :=
    Complex.continuous_ofReal.continuousOn
  have hw_mul_t :
      ContinuousOn
        (fun t : ℝ => w * (t : ℂ))
        (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.mul ht_complex
  have hsecond :
      ContinuousOn
        (fun t : ℝ =>
          w * (t : ℂ) *
            deriv φ (AffineMap.lineMap (0 : ℂ) w t))
        (Set.Icc (0 : ℝ) 1) :=
    hw_mul_t.mul hderiv_seg
  exact hφ_seg.add hsecond

/-- Integrability and measurability of continuous finite-tube interval
integrands. -/
theorem complex_interval_aestronglyMeasurable_of_continuousOn_Icc
    {f : ℝ → ℂ} :
    ContinuousOn f (Set.Icc (0 : ℝ) 1) →
      AEStronglyMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  intro hf
  exact
    (hf.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc

/-- Interval integrability of a complex-valued function continuous on
`[0,1]`. -/
theorem complex_interval_intervalIntegrable_of_continuousOn_Icc
    {f : ℝ → ℂ} :
    ContinuousOn f (Set.Icc (0 : ℝ) 1) →
      IntervalIntegrable f volume (0 : ℝ) 1 := by
  intro hf
  exact
    ContinuousOn.intervalIntegrable_of_Icc
      (show (0 : ℝ) ≤ 1 from zero_le_one)
      hf

theorem complex_centerSegmentIntegral_finiteTube_integrability_of_continuousOn
    (φ : ℂ → ℂ)
    (centers : Finset ℂ) :
    ∀ w : ℂ,
      (∀ᶠ x in 𝓝 w,
        ContinuousOn
          (fun t : ℝ =>
            x * φ (AffineMap.lineMap (0 : ℂ) x t))
          (Set.Icc (0 : ℝ) 1)) →
      ContinuousOn
        (fun t : ℝ =>
          w * φ (AffineMap.lineMap (0 : ℂ) w t))
        (Set.Icc (0 : ℝ) 1) →
      ContinuousOn
        (fun t : ℝ =>
          complex_centerSegmentIntegral_endpointDerivativeIntegrand φ w t)
        (Set.Icc (0 : ℝ) 1) →
        (∀ᶠ x in 𝓝 w,
          AEStronglyMeasurable
            (fun t : ℝ =>
              x * φ (AffineMap.lineMap (0 : ℂ) x t))
            (volume.restrict (Set.Ioc (0 : ℝ) 1))) ∧
        IntervalIntegrable
          (fun t : ℝ =>
            w * φ (AffineMap.lineMap (0 : ℂ) w t))
          volume
          (0 : ℝ)
          1 ∧
        AEStronglyMeasurable
          (fun t : ℝ =>
            complex_centerSegmentIntegral_endpointDerivativeIntegrand
              φ w t)
          (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  intro w hcont_eventually hcont_base hcont_deriv
  have hmeas_eventually :
      ∀ᶠ x in 𝓝 w,
        AEStronglyMeasurable
          (fun t : ℝ =>
            x * φ (AffineMap.lineMap (0 : ℂ) x t))
          (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hcont_eventually.mono
      (fun x hx =>
        complex_interval_aestronglyMeasurable_of_continuousOn_Icc hx)
  have hint :
      IntervalIntegrable
        (fun t : ℝ =>
          w * φ (AffineMap.lineMap (0 : ℂ) w t))
        volume
        (0 : ℝ)
        1 :=
    complex_interval_intervalIntegrable_of_continuousOn_Icc hcont_base
  have hderiv_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          complex_centerSegmentIntegral_endpointDerivativeIntegrand
            φ w t)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    complex_interval_aestronglyMeasurable_of_continuousOn_Icc hcont_deriv
  exact ⟨hmeas_eventually, hint, hderiv_meas⟩

/-- Measurability and interval integrability for the center-segment integrand
on endpoints lying in a finite analytic tube. -/
theorem complex_centerSegmentIntegral_finiteTube_integrability
    (φ : ℂ → ℂ)
    (centers : Finset ℂ) :
    ∀ w : ℂ,
      (∀ t : ℝ,
        t ∈ Set.Icc (0 : ℝ) 1 →
          AffineMap.lineMap (0 : ℂ) w t ∈
            ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q}) →
      (∀ᶠ x in 𝓝 w,
        ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ) 1 →
            AffineMap.lineMap (0 : ℂ) x t ∈
              ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q}) →
        (∀ᶠ x in 𝓝 w,
          AEStronglyMeasurable
            (fun t : ℝ =>
              x * φ (AffineMap.lineMap (0 : ℂ) x t))
            (volume.restrict (Set.Ioc (0 : ℝ) 1))) ∧
        IntervalIntegrable
          (fun t : ℝ =>
            w * φ (AffineMap.lineMap (0 : ℂ) w t))
          volume
          (0 : ℝ)
          1 ∧
        AEStronglyMeasurable
          (fun t : ℝ =>
            complex_centerSegmentIntegral_endpointDerivativeIntegrand
              φ w t)
          (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  intro w htube htube_eventually
  have hcont_eventually :
      ∀ᶠ x in 𝓝 w,
        ContinuousOn
          (fun t : ℝ =>
            x * φ (AffineMap.lineMap (0 : ℂ) x t))
          (Set.Icc (0 : ℝ) 1) :=
    htube_eventually.mono
      (fun x hx =>
        complex_centerSegmentIntegral_finiteTube_integrand_continuousOn
          φ centers x hx)
  exact
    complex_centerSegmentIntegral_finiteTube_integrability_of_continuousOn
      φ centers w
      hcont_eventually
      (complex_centerSegmentIntegral_finiteTube_integrand_continuousOn
        φ centers w htube)
      (complex_centerSegmentIntegral_finiteTube_endpointDerivative_continuousOn
        φ centers w htube)

/-- Compactness of the closed endpoint ball times `[0,1]`. -/
theorem complex_centerSegmentIntegral_endpointBall_Icc_isCompact
    (w : ℂ)
    (r : ℝ) :
    IsCompact
      (Metric.closedBall w r ×ˢ Set.Icc (0 : ℝ) 1) := by
  exact
    (isCompact_closedBall w r).prod isCompact_Icc

/-- Membership in the finite analytic tube gives the local analytic chart
carried by one of its pieces. -/
theorem complex_analyticAt_of_mem_finiteAnalyticTube
    (φ : ℂ → ℂ)
    (centers : Finset ℂ)
    {q : ℂ} :
    q ∈ ⋃ c ∈ centers, {p : ℂ | AnalyticAt ℂ φ p} →
      AnalyticAt ℂ φ q := by
  intro hq
  match Set.mem_iUnion.1 hq with
  | ⟨_c, hc_mem⟩ =>
    match Set.mem_iUnion.1 hc_mem with
    | ⟨_hc, hpoint⟩ => exact hpoint

/-- Continuity of the endpoint derivative integrand on a compact endpoint
ball times the parameter interval, assuming all corresponding segments lie in
the finite analytic tube. -/
theorem complex_centerSegmentIntegral_endpointDerivative_continuousOn_tube
    (φ : ℂ → ℂ)
    (centers : Finset ℂ) :
    ∀ w : ℂ,
      ∀ r : ℝ,
        (∀ x : ℂ,
          x ∈ Metric.closedBall w r →
            ∀ t : ℝ,
              t ∈ Set.Icc (0 : ℝ) 1 →
                AffineMap.lineMap (0 : ℂ) x t ∈
                  ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q}) →
          ContinuousOn
            (fun p : ℂ × ℝ =>
              complex_centerSegmentIntegral_endpointDerivativeIntegrand
                φ p.1 p.2)
            (Metric.closedBall w r ×ˢ Set.Icc (0 : ℝ) 1) := by
  intro w r htube p hp
  have hline_mem :
      AffineMap.lineMap (0 : ℂ) p.1 p.2 ∈
        ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q} :=
    htube p.1 hp.1 p.2 hp.2
  have hanalytic :
      AnalyticAt ℂ φ (AffineMap.lineMap (0 : ℂ) p.1 p.2) :=
    complex_analyticAt_of_mem_finiteAnalyticTube
      φ centers hline_mem
  have hline_cont :
      ContinuousAt
        (fun q : ℂ × ℝ =>
          AffineMap.lineMap (0 : ℂ) q.1 q.2)
        p :=
    complex_centerSegment_endpointParameter_continuous.continuousAt
  have hφ_cont :
      ContinuousAt
        (fun q : ℂ × ℝ =>
          φ (AffineMap.lineMap (0 : ℂ) q.1 q.2))
        p :=
    ContinuousAt.comp
      (f := fun q : ℂ × ℝ =>
        AffineMap.lineMap (0 : ℂ) q.1 q.2)
      (g := φ)
      hanalytic.differentiableAt.continuousAt
      hline_cont
  have hderiv_analytic :
      AnalyticAt ℂ
        (fun q : ℂ => deriv φ q)
        (AffineMap.lineMap (0 : ℂ) p.1 p.2) :=
    complex_deriv_analyticAt_of_analyticAt φ hanalytic
  have hderiv_cont :
      ContinuousAt
        (fun q : ℂ × ℝ =>
          deriv φ (AffineMap.lineMap (0 : ℂ) q.1 q.2))
        p :=
    ContinuousAt.comp
      (f := fun q : ℂ × ℝ =>
        AffineMap.lineMap (0 : ℂ) q.1 q.2)
      (g := fun q : ℂ => deriv φ q)
      hderiv_analytic.differentiableAt.continuousAt
      hline_cont
  have hendpoint_cont :
      ContinuousAt (fun q : ℂ × ℝ => q.1) p :=
    continuous_fst.continuousAt
  have hparameter_cont :
      ContinuousAt (fun q : ℂ × ℝ => (q.2 : ℂ)) p :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousAt
  have hfactor_cont :
      ContinuousAt (fun q : ℂ × ℝ => q.1 * (q.2 : ℂ)) p :=
    hendpoint_cont.mul hparameter_cont
  exact
    (hφ_cont.add (hfactor_cont.mul hderiv_cont)).continuousWithinAt

/-- Continuity of the endpoint derivative norm on a compact endpoint ball
times the parameter interval, assuming the finite analytic tube contains all
segments from that ball. -/
theorem complex_centerSegmentIntegral_endpointDerivative_norm_continuousOn_tube
    (φ : ℂ → ℂ)
    (centers : Finset ℂ) :
    ∀ w : ℂ,
      ∀ r : ℝ,
        (∀ x : ℂ,
          x ∈ Metric.closedBall w r →
            ∀ t : ℝ,
              t ∈ Set.Icc (0 : ℝ) 1 →
                AffineMap.lineMap (0 : ℂ) x t ∈
                  ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q}) →
          ContinuousOn
            (fun p : ℂ × ℝ =>
              ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
                φ p.1 p.2‖)
            (Metric.closedBall w r ×ˢ Set.Icc (0 : ℝ) 1) := by
  intro w r htube_closed
  exact
    continuous_norm.comp_continuousOn
      (complex_centerSegmentIntegral_endpointDerivative_continuousOn_tube
        φ centers w r htube_closed)

/-- Compact boundedness of the endpoint derivative norm on the endpoint-ball
parameter domain. -/
theorem complex_centerSegmentIntegral_endpointDerivative_norm_bddAbove_tube
    (φ : ℂ → ℂ)
    (centers : Finset ℂ) :
    ∀ w : ℂ,
      ∀ r : ℝ,
        (∀ x : ℂ,
          x ∈ Metric.closedBall w r →
            ∀ t : ℝ,
              t ∈ Set.Icc (0 : ℝ) 1 →
                AffineMap.lineMap (0 : ℂ) x t ∈
                  ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q}) →
          BddAbove
            ((fun p : ℂ × ℝ =>
              ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
                φ p.1 p.2‖) ''
              (Metric.closedBall w r ×ˢ Set.Icc (0 : ℝ) 1)) := by
  intro w r htube_closed
  exact
    (complex_centerSegmentIntegral_endpointBall_Icc_isCompact w r).bddAbove_image
      (complex_centerSegmentIntegral_endpointDerivative_norm_continuousOn_tube
        φ centers w r htube_closed)

/-- Compact boundedness of the endpoint derivative integrand on an endpoint
ball times the parameter interval.

This is the compact supremum step for the dominated-parameter theorem: if all
center segments from `ball w ε` lie in the finite analytic tube, then the map
`(x,t) ↦ endpointDerivativeIntegrand φ x t` is continuous on the compact
parameter set `closedBall w (ε / 2) × [0,1]`, hence admits an integrable
constant bound. -/
theorem complex_centerSegmentIntegral_finiteTube_compactBound
    (φ : ℂ → ℂ)
    (centers : Finset ℂ) :
    ∀ w : ℂ,
      ∀ ε : ℝ,
        0 < ε →
          (∀ x : ℂ,
            x ∈ Metric.closedBall w ε →
              ∀ t : ℝ,
                t ∈ Set.Icc (0 : ℝ) 1 →
                  AffineMap.lineMap (0 : ℂ) x t ∈
                    ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q}) →
            ∃ bound : ℝ → ℝ,
              (∀ᵐ t ∂volume,
                t ∈ Set.Ioc (0 : ℝ) 1 →
                  ∀ x ∈ Metric.ball w ε,
                    ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
                      φ x t‖ ≤ bound t) ∧
                IntervalIntegrable bound volume (0 : ℝ) 1 := by
  intro w ε hε_pos htube_closed
  have hbdd :
      BddAbove
        ((fun p : ℂ × ℝ =>
          ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
            φ p.1 p.2‖) ''
          (Metric.closedBall w ε ×ˢ Set.Icc (0 : ℝ) 1)) :=
    complex_centerSegmentIntegral_endpointDerivative_norm_bddAbove_tube
      φ centers w ε htube_closed
  exact
    match hbdd with
    | Exists.intro C hC_image =>
        have hC :
            ∀ y : ℂ × ℝ,
              y ∈ Metric.closedBall w ε ×ˢ Set.Icc (0 : ℝ) 1 →
                ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
                  φ y.1 y.2‖ ≤ C :=
          fun y hy =>
            hC_image
              ⟨y, hy, rfl⟩
        have hbound :
            ∀ᵐ t ∂volume,
              t ∈ Set.Ioc (0 : ℝ) 1 →
                ∀ x ∈ Metric.ball w ε,
                  ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
                    φ x t‖ ≤ (fun _t : ℝ => C) t :=
          Filter.Eventually.of_forall
            (fun t ht_interval x hx =>
              hC
                (x, t)
                ⟨Metric.ball_subset_closedBall hx, Set.Ioc_subset_Icc_self ht_interval⟩)
        Exists.intro
          (fun _t : ℝ => C)
          (And.intro hbound intervalIntegrable_const)

/-- Compact constant bound for the endpoint derivative integrand on a finite
analytic tube. -/
theorem complex_centerSegmentIntegral_finiteTube_constantBound
    (φ : ℂ → ℂ)
    (centers : Finset ℂ) :
    ∀ w : ℂ,
      ∀ ε : ℝ,
        0 < ε →
          (∀ x : ℂ,
            x ∈ Metric.closedBall w ε →
              ∀ t : ℝ,
                t ∈ Set.Icc (0 : ℝ) 1 →
                  AffineMap.lineMap (0 : ℂ) x t ∈
                    ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q}) →
            ∃ bound : ℝ → ℝ,
              (∀ᵐ t ∂volume,
                t ∈ Set.Ioc (0 : ℝ) 1 →
                  ∀ x ∈ Metric.ball w ε,
                    ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
                      φ x t‖ ≤ bound t) ∧
              IntervalIntegrable bound volume (0 : ℝ) 1 := by
  exact
    complex_centerSegmentIntegral_finiteTube_compactBound
      φ centers

/-- Pointwise endpoint derivative almost everywhere in the parameter for
endpoints whose center segments stay in a finite analytic tube. -/
theorem complex_centerSegmentIntegral_finiteTube_pointwiseDerivative_ae
    (φ : ℂ → ℂ)
    (centers : Finset ℂ) :
    ∀ w : ℂ,
      ∀ ε : ℝ,
        0 < ε →
          (∀ x : ℂ,
            x ∈ Metric.closedBall w ε →
              ∀ t : ℝ,
                t ∈ Set.Icc (0 : ℝ) 1 →
                  AffineMap.lineMap (0 : ℂ) x t ∈
                    ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q}) →
            ∀ᵐ t ∂volume,
              t ∈ Set.Ioc (0 : ℝ) 1 →
                ∀ x ∈ Metric.ball w ε,
                  HasDerivAt
                    (fun y : ℂ =>
                      y * φ (AffineMap.lineMap (0 : ℂ) y t))
                    (complex_centerSegmentIntegral_endpointDerivativeIntegrand
                      φ x t)
                    x := by
  intro w ε hε_pos htube
  exact
    Filter.Eventually.of_forall
      (fun t ht x hx =>
        let ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 :=
          And.intro ht.1.le ht.2
        let hanalytic_mem := htube x (Metric.ball_subset_closedBall hx) t ht_Icc
        let hanalytic :=
          match Set.mem_iUnion.1 hanalytic_mem with
          | ⟨_c, hc_mem⟩ =>
            match Set.mem_iUnion.1 hc_mem with
            | ⟨_hc, hpoint⟩ => hpoint
        complex_centerSegmentIntegral_integrand_hasDerivAt_endpoint_of_analyticAt
          φ x t hanalytic)

/-- Constant domination and pointwise endpoint differentiability on a finite
analytic tube. -/
theorem complex_centerSegmentIntegral_finiteTube_domination_and_derivative
    (φ : ℂ → ℂ)
    (centers : Finset ℂ) :
    ∀ w : ℂ,
      ∀ ε : ℝ,
        0 < ε →
          (∀ x : ℂ,
            x ∈ Metric.closedBall w ε →
              ∀ t : ℝ,
                t ∈ Set.Icc (0 : ℝ) 1 →
                  AffineMap.lineMap (0 : ℂ) x t ∈
                    ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q}) →
            ∃ bound : ℝ → ℝ,
              (∀ᵐ t ∂volume,
                t ∈ Set.Ioc (0 : ℝ) 1 →
                  ∀ x ∈ Metric.ball w ε,
                    ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
                      φ x t‖ ≤ bound t) ∧
              IntervalIntegrable bound volume (0 : ℝ) 1 ∧
              (∀ᵐ t ∂volume,
                t ∈ Set.Ioc (0 : ℝ) 1 →
                  ∀ x ∈ Metric.ball w ε,
                    HasDerivAt
                      (fun y : ℂ =>
                        y * φ (AffineMap.lineMap (0 : ℂ) y t))
                      (complex_centerSegmentIntegral_endpointDerivativeIntegrand
                        φ x t)
                      x) := by
    intro w ε hε_pos htube
    have hconstant :
        ∃ bound : ℝ → ℝ,
          (∀ᵐ t ∂volume,
            t ∈ Set.Ioc (0 : ℝ) 1 →
              ∀ x ∈ Metric.ball w ε,
                ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
                  φ x t‖ ≤ bound t) ∧
          IntervalIntegrable bound volume (0 : ℝ) 1 :=
      complex_centerSegmentIntegral_finiteTube_constantBound
        φ centers w ε hε_pos htube
    exact
      match hconstant with
      | Exists.intro bound hbound_data =>
          match hbound_data with
          | And.intro hbound hbound_int =>
              Exists.intro bound
                (And.intro hbound
                  (And.intro hbound_int
                    (complex_centerSegmentIntegral_finiteTube_pointwiseDerivative_ae
                      φ centers w ε hε_pos htube)))

/-- Finite analytic tube and domination package over a compact center
segment.

This is the finite-subcover step after the segment compactness lemma.  Local
analyticity at each point of the compact segment supplies finitely many
analytic charts.  A small endpoint ball keeps all nearby center segments in
that finite tube, gives continuity of both the integrand and endpoint
derivative integrand on the parameter interval, and gives a constant
dominating function for the derivative integrand. -/
theorem complex_centerSegmentIntegral_finiteAnalyticTube_dominatedPackage
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        IsCompact
          ((fun t : ℝ => AffineMap.lineMap (0 : ℂ) z t) ''
            Set.Icc (0 : ℝ) 1) →
        (∃ centers : Finset ℂ,
          (∀ c : ℂ, c ∈ centers → AnalyticAt ℂ φ c) ∧
          ((fun t : ℝ => AffineMap.lineMap (0 : ℂ) z t) ''
              Set.Icc (0 : ℝ) 1) ⊆
            ⋃ c ∈ centers, {w : ℂ | AnalyticAt ℂ φ w}) →
        ∃ u : Set ℂ,
          z ∈ u ∧
          u ∈ 𝓝 z ∧
          ∀ w : ℂ,
            w ∈ u →
              ∃ ε : ℝ,
                0 < ε ∧
                (∀ᶠ x in 𝓝 w,
                  AEStronglyMeasurable
                    (fun t : ℝ =>
                      x * φ (AffineMap.lineMap (0 : ℂ) x t))
                    (volume.restrict (Set.Ioc (0 : ℝ) 1))) ∧
                IntervalIntegrable
                  (fun t : ℝ =>
                    w * φ (AffineMap.lineMap (0 : ℂ) w t))
                  volume
                  (0 : ℝ)
                  1 ∧
                AEStronglyMeasurable
                  (fun t : ℝ =>
                    complex_centerSegmentIntegral_endpointDerivativeIntegrand
                      φ w t)
                  (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
                ∃ bound : ℝ → ℝ,
                  (∀ᵐ t ∂volume,
                    t ∈ Set.Ioc (0 : ℝ) 1 →
                      ∀ x ∈ Metric.ball w ε,
                        ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
                          φ x t‖ ≤ bound t) ∧
                  IntervalIntegrable bound volume (0 : ℝ) 1 ∧
                  (∀ᵐ t ∂volume,
                    t ∈ Set.Ioc (0 : ℝ) 1 →
                      ∀ x ∈ Metric.ball w ε,
                        HasDerivAt
                          (fun y : ℂ =>
                            y * φ (AffineMap.lineMap (0 : ℂ) y t))
                            (complex_centerSegmentIntegral_endpointDerivativeIntegrand
                              φ x t)
                            x) := by
    intro z hz _hcompact hcover
    exact
      match hcover with
      | Exists.intro centers hcover_data =>
          match hcover_data with
          | And.intro _hcenters hcover_subset =>
              match complex_centerSegment_endpointStability_finiteAnalyticTube
                  φ z centers hcover_subset with
              | Exists.intro u hu_data =>
                  match hu_data with
                  | And.intro hz_mem hu_tail =>
                      match hu_tail with
                      | And.intro hu_nhds hu_stable =>
                          have hpoint :
                              ∀ w : ℂ,
                                w ∈ u →
                                  ∃ ε : ℝ,
                                    0 < ε ∧
                                    (∀ᶠ x in 𝓝 w,
                                      AEStronglyMeasurable
                                        (fun t : ℝ =>
                                          x * φ (AffineMap.lineMap (0 : ℂ) x t))
                                        (volume.restrict (Set.Ioc (0 : ℝ) 1))) ∧
                                    IntervalIntegrable
                                      (fun t : ℝ =>
                                        w * φ (AffineMap.lineMap (0 : ℂ) w t))
                                      volume
                                      (0 : ℝ)
                                      1 ∧
                                    AEStronglyMeasurable
                                      (fun t : ℝ =>
                                        complex_centerSegmentIntegral_endpointDerivativeIntegrand
                                          φ w t)
                                      (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
                                    ∃ bound : ℝ → ℝ,
                                      (∀ᵐ t ∂volume,
                                        t ∈ Set.Ioc (0 : ℝ) 1 →
                                          ∀ x ∈ Metric.ball w (ε),
                                            ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
                                              φ x t‖ ≤ bound t) ∧
                                      IntervalIntegrable bound volume (0 : ℝ) 1 ∧
                                      (∀ᵐ t ∂volume,
                                        t ∈ Set.Ioc (0 : ℝ) 1 →
                                          ∀ x ∈ Metric.ball w (ε),
                                            HasDerivAt
                                              (fun y : ℂ =>
                                                y * φ (AffineMap.lineMap (0 : ℂ) y t))
                                              (complex_centerSegmentIntegral_endpointDerivativeIntegrand
                                                φ x t)
                                              x) :=
                            fun w hw =>
                              match hu_stable w hw with
                              | Exists.intro ε hε_data =>
                                  match hε_data with
                                  | And.intro hε_pos hε_stable =>
                                      have hδ_pos : 0 < ε / 2 :=
                                        half_pos hε_pos
                                      have hδ_lt : ε / 2 < ε :=
                                        half_lt_self hε_pos
                                      have hδ_stable_ball :
                                          ∀ x : ℂ,
                                            x ∈ Metric.ball w (ε / 2) →
                                              ∀ t : ℝ,
                                                t ∈ Set.Icc (0 : ℝ) 1 →
                                                  AffineMap.lineMap (0 : ℂ) x t ∈
                                                    ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q} :=
                                        fun x hx t ht =>
                                          hε_stable x (Metric.ball_subset_ball (le_of_lt hδ_lt) hx) t ht
                                      have hδ_stable_closed :
                                          ∀ x : ℂ,
                                            x ∈ Metric.closedBall w (ε / 2) →
                                              ∀ t : ℝ,
                                                t ∈ Set.Icc (0 : ℝ) 1 →
                                                  AffineMap.lineMap (0 : ℂ) x t ∈
                                                    ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q} :=
                                        fun x hx t ht =>
                                          hε_stable x (Metric.closedBall_subset_ball hδ_lt hx) t ht
                                      have hw_stable :
                                          ∀ t : ℝ,
                                            t ∈ Set.Icc (0 : ℝ) 1 →
                                              AffineMap.lineMap (0 : ℂ) w t ∈
                                                ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q} :=
                                        fun t ht =>
                                          hε_stable w (Metric.mem_ball_self hε_pos) t ht
                                      have hintegrability :=
                                        complex_centerSegmentIntegral_finiteTube_integrability
                                          φ centers w hw_stable
                                          (Filter.mem_of_superset
                                            (Metric.ball_mem_nhds w hδ_pos)
                                            (fun x hx t ht => hδ_stable_ball x hx t ht))
                                      have hdom :=
                                        complex_centerSegmentIntegral_finiteTube_domination_and_derivative
                                          φ centers w (ε / 2) hδ_pos hδ_stable_closed
                                      Exists.intro (ε / 2)
                                        (And.intro hδ_pos
                                          (And.intro hintegrability.1
                                            (And.intro hintegrability.2.1
                                              (And.intro hintegrability.2.2 hdom))))
                          Exists.intro u (And.intro hz_mem (And.intro hu_nhds hpoint))

/-- Compact finite-tube domination for center-segment endpoint derivatives.

This is the standard compactness step behind differentiating the segment
integral under the endpoint parameter.  The image of `[0,1]` under
`t ↦ lineMap 0 z t` is compact.  Local analyticity of `φ` at each point of
that segment gives finitely many analytic neighborhoods covering it.  After
shrinking the endpoint, every nearby segment remains in this finite tube; the
endpoint derivative integrand is continuous on the compact tube and hence is
bounded by an integrable constant on `[0,1]`. -/
theorem complex_centerSegmentIntegral_compactFiniteTube_dominatedPackage
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∃ u : Set ℂ,
          z ∈ u ∧
          u ∈ 𝓝 z ∧
          ∀ w : ℂ,
            w ∈ u →
              ∃ ε : ℝ,
                0 < ε ∧
                (∀ᶠ x in 𝓝 w,
                  AEStronglyMeasurable
                    (fun t : ℝ =>
                      x * φ (AffineMap.lineMap (0 : ℂ) x t))
                    (volume.restrict (Set.Ioc (0 : ℝ) 1))) ∧
                IntervalIntegrable
                  (fun t : ℝ =>
                    w * φ (AffineMap.lineMap (0 : ℂ) w t))
                  volume
                  (0 : ℝ)
                  1 ∧
                AEStronglyMeasurable
                  (fun t : ℝ =>
                    complex_centerSegmentIntegral_endpointDerivativeIntegrand
                      φ w t)
                  (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
                ∃ bound : ℝ → ℝ,
                  (∀ᵐ t ∂volume,
                    t ∈ Set.Ioc (0 : ℝ) 1 →
                      ∀ x ∈ Metric.ball w ε,
                        ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
                          φ x t‖ ≤ bound t) ∧
                  IntervalIntegrable bound volume (0 : ℝ) 1 ∧
                  (∀ᵐ t ∂volume,
                    t ∈ Set.Ioc (0 : ℝ) 1 →
                      ∀ x ∈ Metric.ball w ε,
                        HasDerivAt
                          (fun y : ℂ =>
                            y * φ (AffineMap.lineMap (0 : ℂ) y t))
                          (complex_centerSegmentIntegral_endpointDerivativeIntegrand
                            φ x t)
                          x) := by
  intro z hz
  exact
    complex_centerSegmentIntegral_finiteAnalyticTube_dominatedPackage
      φ hstar hφ z hz
      (complex_centerSegment_image_Icc_isCompact z)
      (complex_centerSegment_finiteAnalyticAtCover
        φ hstar hφ z hz
        (complex_centerSegment_image_Icc_isCompact z))

/-- Compact analytic tube around nearby center segments.

This is the geometric/measure-theoretic input for dominated differentiation:
local analyticity of `φ` along the compact segment from `0` to `z` gives an
endpoint neighborhood on which all nearby center segments lie in finitely many
analytic charts.  The endpoint derivative integrand is then continuous on the
compact endpoint-parameter tube, hence bounded by a constant integrable
function on `[0,1]`, and the pointwise endpoint derivative follows from the
already-proved product/chain rule. -/
theorem complex_centerSegmentIntegral_compactAnalyticTube_dominatedPackage
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∃ u : Set ℂ,
          z ∈ u ∧
          u ∈ 𝓝 z ∧
          ∀ w : ℂ,
            w ∈ u →
              ∃ ε : ℝ,
                0 < ε ∧
                (∀ᶠ x in 𝓝 w,
                  AEStronglyMeasurable
                    (fun t : ℝ =>
                      x * φ (AffineMap.lineMap (0 : ℂ) x t))
                    (volume.restrict (Set.Ioc (0 : ℝ) 1))) ∧
                IntervalIntegrable
                  (fun t : ℝ =>
                    w * φ (AffineMap.lineMap (0 : ℂ) w t))
                  volume
                  (0 : ℝ)
                  1 ∧
                AEStronglyMeasurable
                  (fun t : ℝ =>
                    complex_centerSegmentIntegral_endpointDerivativeIntegrand
                      φ w t)
                  (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
                ∃ bound : ℝ → ℝ,
                  (∀ᵐ t ∂volume,
                    t ∈ Set.Ioc (0 : ℝ) 1 →
                      ∀ x ∈ Metric.ball w ε,
                        ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
                          φ x t‖ ≤ bound t) ∧
                  IntervalIntegrable bound volume (0 : ℝ) 1 ∧
                  (∀ᵐ t ∂volume,
                    t ∈ Set.Ioc (0 : ℝ) 1 →
                      ∀ x ∈ Metric.ball w ε,
                        HasDerivAt
                          (fun y : ℂ =>
                            y * φ (AffineMap.lineMap (0 : ℂ) y t))
                          (complex_centerSegmentIntegral_endpointDerivativeIntegrand
                            φ x t)
                          x) := by
  exact
    complex_centerSegmentIntegral_compactFiniteTube_dominatedPackage
      φ hstar hφ

/-- Compact-neighborhood hypotheses for applying mathlib's dominated
parameter-integral derivative theorem to the center-segment integrand.

For each endpoint `z`, one can shrink to an endpoint neighborhood `u` so that
for every `w ∈ u` there is a ball centered at `w` on which the endpoint
derivative integrand is pointwise dominated by an interval-integrable bound,
and the current integrand and derivative integrand have the measurability and
integrability hypotheses required by
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`. -/
theorem complex_centerSegmentIntegral_compact_dominatedHypotheses_on_nhd
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∃ u : Set ℂ,
          z ∈ u ∧
          u ∈ 𝓝 z ∧
          ∀ w : ℂ,
            w ∈ u →
              ∃ ε : ℝ,
                0 < ε ∧
                (∀ᶠ x in 𝓝 w,
                  AEStronglyMeasurable
                    (fun t : ℝ =>
                      x * φ (AffineMap.lineMap (0 : ℂ) x t))
                    (volume.restrict (Set.Ioc (0 : ℝ) 1))) ∧
                IntervalIntegrable
                  (fun t : ℝ =>
                    w * φ (AffineMap.lineMap (0 : ℂ) w t))
                  volume
                  (0 : ℝ)
                  1 ∧
                AEStronglyMeasurable
                  (fun t : ℝ =>
                    complex_centerSegmentIntegral_endpointDerivativeIntegrand
                      φ w t)
                  (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
                ∃ bound : ℝ → ℝ,
                  (∀ᵐ t ∂volume,
                    t ∈ Set.Ioc (0 : ℝ) 1 →
                      ∀ x ∈ Metric.ball w ε,
                        ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
                          φ x t‖ ≤ bound t) ∧
                  IntervalIntegrable bound volume (0 : ℝ) 1 ∧
                  (∀ᵐ t ∂volume,
                    t ∈ Set.Ioc (0 : ℝ) 1 →
                      ∀ x ∈ Metric.ball w ε,
                        HasDerivAt
                          (fun y : ℂ =>
                            y * φ (AffineMap.lineMap (0 : ℂ) y t))
                          (complex_centerSegmentIntegral_endpointDerivativeIntegrand
                            φ x t)
                          x) := by
  exact
    complex_centerSegmentIntegral_compactAnalyticTube_dominatedPackage
      φ hstar hφ

/-- Local dominated differentiation for the exact center-segment integrand.

This is the standard parameter-integral theorem specialized to
`F w t = w * φ(lineMap 0 w t)` and
`F' w t = endpointDerivativeIntegrand φ w t`.  It owns the compact-family
analyticity, measurability, integrability, and domination hypotheses needed to
apply `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
near every endpoint in the star-convex domain. -/
theorem complex_centerSegmentIntegral_dominatedParametricIntegral_hypotheses
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∃ u : Set ℂ,
          z ∈ u ∧
          u ∈ 𝓝 z ∧
          ∀ w : ℂ,
            w ∈ u →
              HasDerivAt
                (fun x : ℂ =>
                  ∫ t in (0 : ℝ)..1,
                    x * φ (AffineMap.lineMap (0 : ℂ) x t))
                (∫ t in (0 : ℝ)..1,
                  complex_centerSegmentIntegral_endpointDerivativeIntegrand
                    φ w t)
                  w := by
    intro z hz
    exact
      match complex_centerSegmentIntegral_compact_dominatedHypotheses_on_nhd
          φ hstar hφ z hz with
      | Exists.intro u hu_data =>
          match hu_data with
          | And.intro hz_mem hu_tail =>
              match hu_tail with
              | And.intro hu_nhds hu_hyp =>
                  have hu_deriv :
                      ∀ w : ℂ,
                        w ∈ u →
                          HasDerivAt
                            (fun x : ℂ =>
                              ∫ t in (0 : ℝ)..1,
                                x * φ (AffineMap.lineMap (0 : ℂ) x t))
                            (∫ t in (0 : ℝ)..1,
                              complex_centerSegmentIntegral_endpointDerivativeIntegrand
                                φ w t)
                            w :=
                    fun w hw =>
                      match hu_hyp w hw with
                      | Exists.intro ε hε_data =>
                          match hε_data with
                          | And.intro hε_pos hF_tail =>
                              match hF_tail with
                              | And.intro hF_meas hF_tail_two =>
                                  match hF_tail_two with
                                  | And.intro hF_int hF_tail_three =>
                                      match hF_tail_three with
                                      | And.intro hF'_meas hbound_exists =>
                                          match hbound_exists with
                                          | Exists.intro bound hbound_data =>
                                              match hbound_data with
                                              | And.intro h_bound hbound_tail =>
                                                  match hbound_tail with
                                                  | And.intro hbound_int h_diff =>
                                                      have h_uIoc_eq :
                                                          Ι (0 : ℝ) 1 =
                                                            Set.Ioc (0 : ℝ) 1 :=
                                                        Set.uIoc_of_le
                                                          (show (0 : ℝ) ≤ 1 from zero_le_one)
                                                      have hF_meas_interval :
                                                          ∀ᶠ x in 𝓝 w,
                                                            AEStronglyMeasurable
                                                              (fun t : ℝ =>
                                                                x * φ (AffineMap.lineMap (0 : ℂ) x t))
                                                              (volume.restrict (Ι (0 : ℝ) 1)) :=
                                                        hF_meas.mono
                                                          (fun x hx =>
                                                            Eq.subst
                                                              (motive := fun interval : Set ℝ =>
                                                                AEStronglyMeasurable
                                                                  (fun t : ℝ =>
                                                                    x * φ (AffineMap.lineMap (0 : ℂ) x t))
                                                                  (volume.restrict interval))
                                                              (Eq.symm h_uIoc_eq)
                                                              hx)
                                                      have hF'_meas_interval :
                                                          AEStronglyMeasurable
                                                            (fun t : ℝ =>
                                                              complex_centerSegmentIntegral_endpointDerivativeIntegrand
                                                                φ w t)
                                                            (volume.restrict (Ι (0 : ℝ) 1)) :=
                                                        Eq.subst
                                                          (motive := fun interval : Set ℝ =>
                                                            AEStronglyMeasurable
                                                              (fun t : ℝ =>
                                                                complex_centerSegmentIntegral_endpointDerivativeIntegrand
                                                                  φ w t)
                                                              (volume.restrict interval))
                                                          (Eq.symm h_uIoc_eq)
                                                          hF'_meas
                                                      have h_bound_interval :
                                                          ∀ᵐ t ∂volume,
                                                            t ∈ Ι (0 : ℝ) 1 →
                                                              ∀ x ∈ Metric.ball w ε,
                                                                ‖complex_centerSegmentIntegral_endpointDerivativeIntegrand
                                                                  φ x t‖ ≤ bound t :=
                                                        h_bound.mono
                                                          (fun t ht ht_interval =>
                                                            ht
                                                              (Eq.subst
                                                                (motive := fun interval : Set ℝ =>
                                                                  t ∈ interval)
                                                                h_uIoc_eq
                                                                ht_interval))
                                                      have h_diff_interval :
                                                          ∀ᵐ t ∂volume,
                                                            t ∈ Ι (0 : ℝ) 1 →
                                                              ∀ x ∈ Metric.ball w ε,
                                                                HasDerivAt
                                                                  (fun y : ℂ =>
                                                                    y * φ (AffineMap.lineMap (0 : ℂ) y t))
                                                                  (complex_centerSegmentIntegral_endpointDerivativeIntegrand
                                                                    φ x t)
                                                                  x :=
                                                        h_diff.mono
                                                          (fun t ht ht_interval =>
                                                            ht
                                                              (Eq.subst
                                                                (motive := fun interval : Set ℝ =>
                                                                  t ∈ interval)
                                                                h_uIoc_eq
                                                                ht_interval))
                                                      have hparam :=
                                                        intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
                                                          (μ := volume)
                                                          (a := (0 : ℝ))
                                                          (b := 1)
                                                          (ε_pos := hε_pos)
                                                          (F := fun x : ℂ => fun t : ℝ =>
                                                            x * φ (AffineMap.lineMap (0 : ℂ) x t))
                                                          (F' := fun x : ℂ => fun t : ℝ =>
                                                            complex_centerSegmentIntegral_endpointDerivativeIntegrand φ x t)
                                                          (x₀ := w)
                                                          hF_meas_interval
                                                          hF_int
                                                          hF'_meas_interval
                                                          h_bound_interval
                                                          hbound_int
                                                          h_diff_interval
                                                      hparam.2
                  Exists.intro u (And.intro hz_mem (And.intro hu_nhds hu_deriv))

/-- Local dominated differentiation under the endpoint-parametrized segment
integral.

This is the exact parametric interval-integral theorem needed for the
star-convex primitive construction.  For endpoints near `z`, the compact
family of center segments stays in analytic neighborhoods of `φ`; the
endpoint derivative integrand is the derivative of
`w ↦ w * φ(lineMap 0 w t)`, and the compactness gives the uniform integrable
bound needed by `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`. -/
theorem complex_centerSegmentIntegral_hasDerivAt_on_nhd_dominatedParametricIntegral
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∃ u : Set ℂ,
          z ∈ u ∧
          u ∈ 𝓝 z ∧
          ∀ w : ℂ,
            w ∈ u →
                HasDerivAt
                  (complex_centerSegmentIntegral φ)
                  (∫ t in (0 : ℝ)..1,
                    complex_centerSegmentIntegral_endpointDerivativeIntegrand φ w t)
                  w := by
    intro z hz
    exact
      match complex_centerSegmentIntegral_dominatedParametricIntegral_hypotheses
          φ hstar hφ z hz with
      | Exists.intro u hu_data =>
          match hu_data with
          | And.intro hz_mem hu_tail =>
              match hu_tail with
              | And.intro hu_nhds hu_deriv_integral =>
                  have hu_deriv :
                      ∀ w : ℂ,
                        w ∈ u →
                          HasDerivAt
                            (complex_centerSegmentIntegral φ)
                            (∫ t in (0 : ℝ)..1,
                              complex_centerSegmentIntegral_endpointDerivativeIntegrand φ w t)
                            w :=
                    fun w hw =>
                      hu_deriv_integral w hw
                  Exists.intro u (And.intro hz_mem (And.intro hu_nhds hu_deriv))

/-- Local endpoint differentiability supplied by the parametric interval
integral theorem near a fixed segment endpoint. -/
theorem complex_centerSegmentIntegral_hasDerivAt_on_nhd_parametricIntegral
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∃ u : Set ℂ,
          z ∈ u ∧
          u ∈ 𝓝 z ∧
          ∀ w : ℂ,
            w ∈ u →
              HasDerivAt
                (complex_centerSegmentIntegral φ)
                (∫ t in (0 : ℝ)..1,
                  complex_centerSegmentIntegral_endpointDerivativeIntegrand φ w t)
                w := by
  exact
    complex_centerSegmentIntegral_hasDerivAt_on_nhd_dominatedParametricIntegral
      φ hstar hφ

/-- Derivative under the endpoint parameter for the center-segment integral.

This is the parametric interval-integral theorem specialized to
`w ↦ ∫ t in 0..1, w * φ(lineMap 0 w t)`.  The compact segment is covered by
analytic neighborhoods of `φ`, giving the uniform differentiability and
integrable bounds required by mathlib's parametric-integral API. -/
theorem complex_centerSegmentIntegral_hasDerivAt_integral_endpointDerivative
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        HasDerivAt
          (complex_centerSegmentIntegral φ)
          (∫ t in (0 : ℝ)..1,
            complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t)
            z := by
    intro z hz
    exact
      match complex_centerSegmentIntegral_hasDerivAt_on_nhd_parametricIntegral
          φ hstar hφ z hz with
      | Exists.intro u hu_data =>
          match hu_data with
          | And.intro hz_mem hu_tail =>
              match hu_tail with
              | And.intro _hu_nhds hu_deriv =>
                  hu_deriv z hz_mem

/-- Continuity of `φ` at every point of a center-to-endpoint segment. -/
theorem complex_starConvex_centerSegment_phi_continuousAt
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ) 1 →
            ContinuousAt φ (AffineMap.lineMap (0 : ℂ) z t) := by
  intro z hz t ht
  exact
    (complex_starConvex_centerSegment_analyticAt
      φ hstar hφ hz ht).differentiableAt.continuousAt

/-- Analyticity of `deriv φ` at every point of a center-to-endpoint segment. -/
theorem complex_starConvex_centerSegment_deriv_phi_analyticAt
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ) 1 →
            AnalyticAt ℂ
              (fun w : ℂ => deriv φ w)
              (AffineMap.lineMap (0 : ℂ) z t) := by
  intro z hz t ht
  exact
    complex_deriv_analyticAt_of_analyticAt φ
      (complex_starConvex_centerSegment_analyticAt φ hstar hφ hz ht)

/-- Continuity of `deriv φ` at every point of a center-to-endpoint segment. -/
theorem complex_starConvex_centerSegment_deriv_phi_continuousAt
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ) 1 →
            ContinuousAt
              (fun w : ℂ => deriv φ w)
              (AffineMap.lineMap (0 : ℂ) z t) := by
  intro z hz t ht
  exact
    (complex_starConvex_centerSegment_deriv_phi_analyticAt
      φ hstar hφ z hz t ht).differentiableAt.continuousAt

/-- Continuity of `φ` restricted to a center-to-endpoint segment. -/
theorem complex_starConvex_centerSegment_phi_continuousOn
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ContinuousOn
          (fun t : ℝ =>
            φ (AffineMap.lineMap (0 : ℂ) z t))
          (Set.Icc (0 : ℝ) 1) := by
  intro z hz t ht
  have hline_cont :
      ContinuousAt
        (fun u : ℝ => AffineMap.lineMap (0 : ℂ) z u)
        t :=
    (AffineMap.lineMap_continuous (p := (0 : ℂ)) (v := z)).continuousAt
  exact
    ((complex_starConvex_centerSegment_phi_continuousAt
      φ hstar hφ z hz t ht).comp hline_cont).continuousWithinAt

/-- Continuity of `deriv φ` restricted to a center-to-endpoint segment. -/
theorem complex_starConvex_centerSegment_deriv_phi_continuousOn
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ContinuousOn
          (fun t : ℝ =>
            deriv φ (AffineMap.lineMap (0 : ℂ) z t))
          (Set.Icc (0 : ℝ) 1) := by
  intro z hz t ht
  have hline_cont :
      ContinuousAt
        (fun u : ℝ => AffineMap.lineMap (0 : ℂ) z u)
        t :=
    (AffineMap.lineMap_continuous (p := (0 : ℂ)) (v := z)).continuousAt
  exact
    ((complex_starConvex_centerSegment_deriv_phi_continuousAt
      φ hstar hφ z hz t ht).comp hline_cont).continuousWithinAt

/-- Real derivative of the affine segment map from `0` to `z`. -/
theorem complex_centerSegment_lineMap_hasDerivAt_real
    (z : ℂ)
    (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => AffineMap.lineMap (0 : ℂ) z u)
      z
      t := by
  have hraw :
      HasDerivAt
        (fun u : ℝ => AffineMap.lineMap (0 : ℂ) z u)
        (z - 0)
        t :=
    AffineMap.hasDerivAt_lineMap (a := (0 : ℂ)) (b := z) (x := t)
  exact
    Eq.subst
      (motive := fun v : ℂ =>
        HasDerivAt
          (fun u : ℝ => AffineMap.lineMap (0 : ℂ) z u)
          v
          t)
      (sub_zero z)
      hraw

/-- Real chain rule for a holomorphic function composed with the affine
center-to-endpoint segment. -/
theorem complex_starConvex_centerSegment_phi_hasDerivAt_real_chainRule
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ) 1 →
            HasDerivAt
              (fun u : ℝ =>
                φ (AffineMap.lineMap (0 : ℂ) z u))
              (z * deriv φ (AffineMap.lineMap (0 : ℂ) z t))
              t := by
  intro z hz t ht
  let x : ℂ := AffineMap.lineMap (0 : ℂ) z t
  have hφ_at :
      HasDerivAt φ (deriv φ x) x :=
    (complex_starConvex_centerSegment_analyticAt
      φ hstar hφ hz ht).differentiableAt.hasDerivAt
  have hline_at :
      HasDerivAt
        (fun u : ℝ => AffineMap.lineMap (0 : ℂ) z u)
        z
        t :=
    complex_centerSegment_lineMap_hasDerivAt_real z t
  have hcomp_deriv :
      HasDerivAt
        (φ ∘ fun u : ℝ => AffineMap.lineMap (0 : ℂ) z u)
        ((deriv φ x) * z)
        t :=
    hφ_at.comp t hline_at
  exact
    Eq.subst
      (motive := fun v : ℂ =>
        HasDerivAt
          (fun u : ℝ => φ (AffineMap.lineMap (0 : ℂ) z u))
          v
          t)
      (mul_comm (deriv φ x) z)
      hcomp_deriv

/-- Real chain rule for `φ` along a center-to-endpoint segment. -/
theorem complex_starConvex_centerSegment_phi_hasDerivAt_real
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ) 1 →
            HasDerivAt
              (fun u : ℝ =>
                φ (AffineMap.lineMap (0 : ℂ) z u))
              (z * deriv φ (AffineMap.lineMap (0 : ℂ) z t))
              t := by
  exact
    complex_starConvex_centerSegment_phi_hasDerivAt_real_chainRule
      φ hstar hφ

/-- Algebraic normalization of the product-rule derivative for the radial FTC
primitive. -/
theorem complex_centerSegmentIntegral_radialFTCProduct_derivative_eq_endpointDerivative
    (φ : ℂ → ℂ)
    (z : ℂ)
    (t : ℝ) :
    (1 : ℂ) * φ (AffineMap.lineMap (0 : ℂ) z t) +
      (t : ℂ) *
        (z * deriv φ (AffineMap.lineMap (0 : ℂ) z t)) =
      complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t := by
  let w : ℂ := AffineMap.lineMap (0 : ℂ) z t
  let d : ℂ := deriv φ w
  have hfirst :
      (1 : ℂ) * φ w = φ w :=
    one_mul (φ w)
  have hsecond :
      (t : ℂ) * (z * d) = z * (t : ℂ) * d := by
    calc
      (t : ℂ) * (z * d) = ((t : ℂ) * z) * d :=
        (mul_assoc (t : ℂ) z d).symm
      _ = (z * (t : ℂ)) * d :=
        congrArg (fun a : ℂ => a * d) (mul_comm (t : ℂ) z)
      _ = z * (t : ℂ) * d :=
        rfl
  calc
    (1 : ℂ) * φ (AffineMap.lineMap (0 : ℂ) z t) +
        (t : ℂ) *
          (z * deriv φ (AffineMap.lineMap (0 : ℂ) z t)) =
        φ w + z * (t : ℂ) * d :=
      congrArg₂ (fun a b : ℂ => a + b) hfirst hsecond
    _ = complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t :=
      rfl

/-- Product rule for the radial FTC primitive after the segment pullback
derivative has been computed. -/
theorem complex_centerSegmentIntegral_radialFTCPrimitive_hasDerivAt_productRule_core
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ) 1 →
            HasDerivAt
              (fun u : ℝ =>
                complex_centerSegmentIntegral_radialFTCPrimitive φ z u)
              (complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t)
              t := by
  intro z hz t ht
  have hleft :
      HasDerivAt
        (fun u : ℝ => (u : ℂ))
        (1 : ℂ)
        t :=
    Complex.ofRealCLM.hasDerivAt
  have hright :
      HasDerivAt
        (fun u : ℝ =>
          φ (AffineMap.lineMap (0 : ℂ) z u))
        (z * deriv φ (AffineMap.lineMap (0 : ℂ) z t))
        t :=
    complex_starConvex_centerSegment_phi_hasDerivAt_real
      φ hstar hφ z hz t ht
  have hprod :
      HasDerivAt
        (fun u : ℝ =>
          (u : ℂ) * φ (AffineMap.lineMap (0 : ℂ) z u))
        ((1 : ℂ) * φ (AffineMap.lineMap (0 : ℂ) z t) +
          (t : ℂ) *
            (z * deriv φ (AffineMap.lineMap (0 : ℂ) z t)))
        t :=
    hleft.mul hright
  exact
    Eq.subst
      (motive := fun v : ℂ =>
        HasDerivAt
          (fun u : ℝ =>
            complex_centerSegmentIntegral_radialFTCPrimitive φ z u)
          v
          t)
      (complex_centerSegmentIntegral_radialFTCProduct_derivative_eq_endpointDerivative
        φ z t)
      hprod

/-- Product-rule form of the radial FTC derivative. -/
theorem complex_centerSegmentIntegral_radialFTCPrimitive_hasDerivAt_productRule
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ) 1 →
            HasDerivAt
              (fun u : ℝ =>
                complex_centerSegmentIntegral_radialFTCPrimitive φ z u)
              (complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t)
              t := by
  exact
    complex_centerSegmentIntegral_radialFTCPrimitive_hasDerivAt_productRule_core
      φ hstar hφ

/-- Real derivative of the radial FTC primitive.

This is the chain-rule computation
`d/dt (t * φ(tz)) = φ(tz) + z * t * φ'(tz)`, written using the affine segment
map from `0` to `z`. -/
theorem complex_centerSegmentIntegral_radialFTCPrimitive_hasDerivAt
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ) 1 →
            HasDerivAt
              (fun u : ℝ =>
                complex_centerSegmentIntegral_radialFTCPrimitive φ z u)
              (complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t)
              t := by
  exact
    complex_centerSegmentIntegral_radialFTCPrimitive_hasDerivAt_productRule
      φ hstar hφ

/-- Continuity of the endpoint derivative integrand on the radial segment. -/
theorem complex_centerSegmentIntegral_endpointDerivativeIntegrand_continuousOn
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ContinuousOn
          (fun t : ℝ =>
            complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t)
          (Set.Icc (0 : ℝ) 1) := by
  intro z hz
  have hφ_seg :
      ContinuousOn
        (fun t : ℝ =>
          φ (AffineMap.lineMap (0 : ℂ) z t))
        (Set.Icc (0 : ℝ) 1) :=
    complex_starConvex_centerSegment_phi_continuousOn φ hstar hφ z hz
  have hderiv_seg :
      ContinuousOn
        (fun t : ℝ =>
          deriv φ (AffineMap.lineMap (0 : ℂ) z t))
        (Set.Icc (0 : ℝ) 1) :=
    complex_starConvex_centerSegment_deriv_phi_continuousOn φ hstar hφ z hz
  have ht_complex :
      ContinuousOn
        (fun t : ℝ => (t : ℂ))
        (Set.Icc (0 : ℝ) 1) :=
    Complex.continuous_ofReal.continuousOn
  have hz_mul_t :
      ContinuousOn
        (fun t : ℝ => z * (t : ℂ))
        (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.mul ht_complex
  have hsecond :
      ContinuousOn
        (fun t : ℝ =>
          z * (t : ℂ) *
            deriv φ (AffineMap.lineMap (0 : ℂ) z t))
        (Set.Icc (0 : ℝ) 1) :=
    hz_mul_t.mul hderiv_seg
  exact hφ_seg.add hsecond

/-- Interval integrability of the endpoint derivative integrand on the radial
segment. -/
theorem complex_centerSegmentIntegral_endpointDerivativeIntegrand_intervalIntegrable
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        IntervalIntegrable
          (fun t : ℝ =>
            complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t)
          volume
          (0 : ℝ)
          1 := by
  intro z hz
  exact
    ContinuousOn.intervalIntegrable_of_Icc
      (show (0 : ℝ) ≤ 1 from zero_le_one)
      (complex_centerSegmentIntegral_endpointDerivativeIntegrand_continuousOn
        φ hstar hφ z hz)

/-- Interval FTC for the radial primitive along a center-to-endpoint segment. -/
theorem complex_centerSegmentIntegral_radialFTC_integral_eq_endpoint_sub_base
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        (∫ t in (0 : ℝ)..1,
          complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t) =
          complex_centerSegmentIntegral_radialFTCPrimitive φ z 1 -
            complex_centerSegmentIntegral_radialFTCPrimitive φ z 0 := by
  intro z hz
  have hderiv :
      ∀ t : ℝ,
        t ∈ Set.uIcc (0 : ℝ) 1 →
          HasDerivAt
            (fun u : ℝ =>
              complex_centerSegmentIntegral_radialFTCPrimitive φ z u)
            (complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t)
            t := by
    intro t ht
    have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 :=
      Eq.subst
        (motive := fun u : Set ℝ => t ∈ u)
        (Set.uIcc_of_le (show (0 : ℝ) ≤ 1 from zero_le_one))
        ht
    exact
      complex_centerSegmentIntegral_radialFTCPrimitive_hasDerivAt
        φ hstar hφ z hz t ht_Icc
  have hint :
      IntervalIntegrable
        (fun t : ℝ =>
          complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t)
        volume
        (0 : ℝ)
        1 :=
    complex_centerSegmentIntegral_endpointDerivativeIntegrand_intervalIntegrable
      φ hstar hφ z hz
  exact
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Endpoint calculation for the radial FTC primitive. -/
theorem complex_centerSegmentIntegral_radialFTC_endpoint_sub_base
    (φ : ℂ → ℂ)
    (z : ℂ) :
    complex_centerSegmentIntegral_radialFTCPrimitive φ z 1 -
      complex_centerSegmentIntegral_radialFTCPrimitive φ z 0 =
      φ z := by
  have hline_one :
      AffineMap.lineMap (0 : ℂ) z (1 : ℝ) = z :=
    Eq.trans
      (complex_starConvexClosedBall_lineMap_zero_eq_radial z 1)
      (one_smul ℂ z)
  have hline_zero :
      AffineMap.lineMap (0 : ℂ) z (0 : ℝ) = 0 :=
    Eq.trans
      (complex_starConvexClosedBall_lineMap_zero_eq_radial z 0)
      (zero_smul ℂ z)
  have hleft :
      ((1 : ℂ) *
        φ (AffineMap.lineMap (0 : ℂ) z (1 : ℝ))) =
        φ z :=
    Eq.trans
      (congrArg
        (fun w : ℂ => (1 : ℂ) * φ w)
        hline_one)
      (one_mul (φ z))
  have hright :
      ((0 : ℂ) *
        φ (AffineMap.lineMap (0 : ℂ) z (0 : ℝ))) =
        0 :=
    zero_mul (φ (AffineMap.lineMap (0 : ℂ) z (0 : ℝ)))
  calc
    complex_centerSegmentIntegral_radialFTCPrimitive φ z 1 -
        complex_centerSegmentIntegral_radialFTCPrimitive φ z 0 =
        ((1 : ℂ) *
          φ (AffineMap.lineMap (0 : ℂ) z (1 : ℝ))) -
          ((0 : ℂ) *
            φ (AffineMap.lineMap (0 : ℂ) z (0 : ℝ))) :=
      rfl
    _ = φ z - 0 :=
      congrArg₂ (fun a b : ℂ => a - b) hleft hright
    _ = φ z :=
      sub_zero (φ z)

/-- Radial FTC identity for the differentiated center-segment integrand.

For holomorphic `φ`, the derivative of the endpoint-parametrized segment
integral reduces to the one-dimensional identity
`∫₀¹ d/dt (t * φ(tz)) dt = φ z`. -/
theorem complex_centerSegmentIntegral_endpointDerivativeIntegral_eq
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        (∫ t in (0 : ℝ)..1,
          complex_centerSegmentIntegral_endpointDerivativeIntegrand φ z t) =
          φ z := by
  intro z hz
  exact Eq.trans
    (complex_centerSegmentIntegral_radialFTC_integral_eq_endpoint_sub_base
      φ hstar hφ z hz)
    (complex_centerSegmentIntegral_radialFTC_endpoint_sub_base φ z)

/-- Local endpoint differentiability supplied by the same parametric integral
argument near a fixed segment endpoint. -/
theorem complex_centerSegmentIntegral_hasDerivAt_on_nhd
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        ∃ u : Set ℂ,
          u ∈ 𝓝 z ∧
          ∀ w : ℂ,
            w ∈ u →
              HasDerivAt
                (complex_centerSegmentIntegral φ)
                (∫ t in (0 : ℝ)..1,
                  complex_centerSegmentIntegral_endpointDerivativeIntegrand φ w t)
                  w := by
    intro z hz
    exact
      match complex_centerSegmentIntegral_hasDerivAt_on_nhd_parametricIntegral
          φ hstar hφ z hz with
      | Exists.intro u hu_data =>
          match hu_data with
          | And.intro _hz_mem hu_tail =>
              match hu_tail with
              | And.intro hu_nhds hu_deriv =>
                  Exists.intro u (And.intro hu_nhds hu_deriv)

/-- Cauchy--FTC endpoint derivative for the center-segment primitive.

This is the concrete differential core of primitive existence on a
star-convex complex domain.  Its proof is the standard triangular Cauchy
argument, equivalently differentiating the endpoint-parametrized interval
integral and using the one-dimensional FTC along the radial segment. -/
theorem complex_starConvex_centerSegmentIntegral_hasDerivAt_cauchyFTC
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        HasDerivAt
          (complex_centerSegmentIntegral φ)
          (φ z)
          z := by
  intro z hz
  exact
    (complex_centerSegmentIntegral_endpointDerivativeIntegral_eq
      φ hstar hφ z hz) ▸
      (complex_centerSegmentIntegral_hasDerivAt_integral_endpointDerivative
        φ hstar hφ z hz)

/-- Local differentiability of the center-segment primitive near each endpoint.

This is the neighborhood form needed to turn complex differentiability into
analyticity.  It follows from the same compact-segment parameter-integral
argument as the endpoint derivative theorem, applied uniformly on a small
endpoint neighborhood. -/
theorem complex_starConvex_centerSegmentIntegral_differentiableOn_nhd
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
          ∃ u : Set ℂ,
            u ∈ 𝓝 z ∧
            DifferentiableOn ℂ (complex_centerSegmentIntegral φ) u := by
    intro z hz
    exact
      match complex_centerSegmentIntegral_hasDerivAt_on_nhd
          φ hstar hφ z hz with
      | Exists.intro u hu_data =>
          match hu_data with
          | And.intro hu_nhds hu_deriv =>
              have hdiff :
                  DifferentiableOn ℂ (complex_centerSegmentIntegral φ) u :=
                fun w hw =>
                  (hu_deriv w hw).differentiableAt.differentiableWithinAt
              Exists.intro u (And.intro hu_nhds hdiff)

/-- Holomorphic parameter-integral regularity for the center-segment
primitive.

This is the analytic regularity core accompanying the Cauchy--FTC derivative:
local analyticity of the integrand along the compact center segment gives
analyticity of the endpoint-parametrized segment integral. -/
theorem complex_starConvex_centerSegmentIntegral_analyticAt_parameterIntegral
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
      ∀ z : ℂ,
        z ∈ s →
          AnalyticAt ℂ (complex_centerSegmentIntegral φ) z := by
    intro z hz
    exact
      match complex_starConvex_centerSegmentIntegral_differentiableOn_nhd
          φ hstar hφ z hz with
      | Exists.intro u hu_data =>
          match hu_data with
          | And.intro hu_nhds hu_diff =>
              hu_diff.analyticAt hu_nhds

/-- Standard star-convex primitive theorem for the center-segment integral.

This is the canonical owner API corresponding to the classical proof of
primitive existence on a star-convex domain: integrate `φ` along the affine
segment from the center to the endpoint, then use Cauchy's theorem on the
small triangle swept out by moving the endpoint to identify the endpoint
derivative with `φ`. -/
theorem complex_starConvex_centerSegmentIntegral_isPrimitive
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        AnalyticAt ℂ (complex_centerSegmentIntegral φ) z ∧
        HasDerivAt
          (complex_centerSegmentIntegral φ)
          (φ z)
          z := by
  intro z hz
  exact
    And.intro
      (complex_starConvex_centerSegmentIntegral_analyticAt_parameterIntegral
        φ hstar hφ z hz)
      (complex_starConvex_centerSegmentIntegral_hasDerivAt_cauchyFTC
        φ hstar hφ z hz)

/-- The standard Cauchy--FTC theorem for the endpoint-parametrized segment
integral on a star-convex complex domain.

This wrapper gives the parameter-integral name used by the Jensen primitive
lane while delegating the mathematics to the owner theorem
`complex_starConvex_centerSegmentIntegral_isPrimitive`. -/
theorem complex_centerSegmentIntegral_parametricPrimitive_of_holomorphicOn_starConvex
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
        AnalyticAt ℂ (complex_centerSegmentIntegral φ) z ∧
        HasDerivAt
          (complex_centerSegmentIntegral φ)
          (φ z)
          z := by
  exact
    complex_starConvex_centerSegmentIntegral_isPrimitive
      φ hstar hφ

/-- Parametric interval-integral derivative theorem for the center-segment
primitive.

This packages the derivative-under-the-integral-sign argument for
`z ↦ ∫ t in 0..1, z * φ(lineMap 0 z t)`, together with the one-dimensional
FTC computation along the radial segment. -/
theorem complex_centerSegmentIntegral_hasDerivAt_parametricIntegral
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
      HasDerivAt
        (complex_centerSegmentIntegral φ)
        (φ z)
        z := by
  intro z hz
  exact
    (complex_centerSegmentIntegral_parametricPrimitive_of_holomorphicOn_starConvex
      φ hstar hφ z hz).2

/-- Holomorphic parameter-integral theorem for the center-segment primitive.

This is the analytic counterpart of the derivative-under-integral theorem: a
holomorphic integrand depending analytically on the endpoint has a holomorphic
segment integral. -/
theorem complex_centerSegmentIntegral_analyticAt_parameterIntegral
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
      AnalyticAt ℂ (complex_centerSegmentIntegral φ) z := by
  intro z hz
  exact
    (complex_centerSegmentIntegral_parametricPrimitive_of_holomorphicOn_starConvex
      φ hstar hφ z hz).1

/-- Differentiation under the endpoint parameter for the center segment
integral. -/
theorem complex_centerSegmentIntegral_hasDerivAt_of_holomorphicOn_starConvex
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
      HasDerivAt
        (complex_centerSegmentIntegral φ)
        (φ z)
        z := by
  exact
    complex_centerSegmentIntegral_hasDerivAt_parametricIntegral
      φ hstar hφ

/-- Analyticity of the center segment integral from the endpoint derivative
theorem. -/
theorem complex_centerSegmentIntegral_analyticAt_of_holomorphicOn_starConvex
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      z ∈ s →
      AnalyticAt ℂ (complex_centerSegmentIntegral φ) z := by
  exact
    complex_centerSegmentIntegral_analyticAt_parameterIntegral
      φ hstar hφ

/-- Fundamental theorem for holomorphic segment integrals on star-convex
domains.

This is the standard path-integral result: for a holomorphic function on a
star-convex domain, the segment integral from the star center is analytic and
has derivative equal to the endpoint integrand. -/
theorem complex_segmentIntegral_primitive_hasDerivAt_of_holomorphicOn_starConvex
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    (∀ z : ℂ,
      z ∈ s →
      AnalyticAt ℂ (complex_centerSegmentIntegral φ) z) ∧
    (∀ z : ℂ,
      z ∈ s →
      deriv (complex_centerSegmentIntegral φ) z = φ z) := by
  exact
    ⟨complex_centerSegmentIntegral_analyticAt_of_holomorphicOn_starConvex
        φ hstar hφ,
      fun z hz =>
        (complex_centerSegmentIntegral_hasDerivAt_of_holomorphicOn_starConvex
          φ hstar hφ z hz).deriv⟩

/-- Standard segment-integral primitive theorem for holomorphic functions on a
star-convex complex domain, specialized to the radial primitive from the
center.

This is the reusable complex-analysis API: differentiating the segment
integral from the star center gives back the holomorphic integrand, and the
resulting primitive is analytic at every point of the domain. -/
theorem complex_segmentIntegral_primitive_isPrimitive_of_holomorphicOn_starConvex
    (φ : ℂ → ℂ)
    {s : Set ℂ}
    (hstar : StarConvex ℝ (0 : ℂ) s)
    (hφ : ∀ z : ℂ, z ∈ s → AnalyticAt ℂ φ z) :
    (∀ z : ℂ,
      z ∈ s →
      AnalyticAt ℂ (complex_starConvexClosedBall_radialPrimitive φ) z) ∧
    (∀ z : ℂ,
      z ∈ s →
      deriv (complex_starConvexClosedBall_radialPrimitive φ) z = φ z) := by
  have hseg :
      (∀ z : ℂ,
        z ∈ s →
        AnalyticAt ℂ (complex_centerSegmentIntegral φ) z) ∧
      (∀ z : ℂ,
        z ∈ s →
        deriv (complex_centerSegmentIntegral φ) z = φ z) :=
    complex_segmentIntegral_primitive_hasDerivAt_of_holomorphicOn_starConvex
      φ hstar hφ
  have heq :
      ∀ z : ℂ,
        complex_centerSegmentIntegral φ z =
          complex_starConvexClosedBall_radialPrimitive φ z :=
    fun z => complex_centerSegmentIntegral_eq_radialPrimitive φ z
  exact
    ⟨fun z hz =>
      (hseg.1 z hz).congr
        (Filter.Eventually.of_forall
          (fun w : ℂ => heq w)),
      fun z hz =>
        Eq.trans
          (Filter.EventuallyEq.deriv_eq
            (Filter.Eventually.of_forall
              (fun w : ℂ => (heq w).symm)))
          (hseg.2 z hz)⟩

/-- Canonical star-convex radial primitive theorem on a closed complex ball.

For an analytic function on a star-convex closed ball, radial integration from
the star center gives a primitive on the ball.  The proof is the standard
Cauchy-Goursat/path-independence argument for star-shaped domains together
with differentiation of the segment integral. -/
theorem complex_starConvexClosedBall_radialPrimitive_isPrimitive_on_starConvex
    (φ : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ))
    (hφ : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ φ z) :
    (∀ z : ℂ,
      ‖z‖ ≤ ρ →
      AnalyticAt ℂ (complex_starConvexClosedBall_radialPrimitive φ) z) ∧
    (∀ z : ℂ,
      ‖z‖ ≤ ρ →
      deriv (complex_starConvexClosedBall_radialPrimitive φ) z = φ z) := by
  have hclosed :
      (∀ z : ℂ,
        z ∈ Metric.closedBall (0 : ℂ) ρ →
        AnalyticAt ℂ (complex_starConvexClosedBall_radialPrimitive φ) z) ∧
      (∀ z : ℂ,
        z ∈ Metric.closedBall (0 : ℂ) ρ →
        deriv (complex_starConvexClosedBall_radialPrimitive φ) z = φ z) :=
    complex_segmentIntegral_primitive_isPrimitive_of_holomorphicOn_starConvex
      φ
      hstar
      (fun z hz => hφ z (mem_closedBall_zero_iff.mp hz))
  exact
    ⟨fun z hz => hclosed.1 z (mem_closedBall_zero_iff.mpr hz),
      fun z hz => hclosed.2 z (mem_closedBall_zero_iff.mpr hz)⟩

/-- Closed-ball specialization of the canonical star-convex radial primitive
theorem. -/
theorem complex_starConvexClosedBall_radialPrimitive_isPrimitive
    (φ : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ))
    (hφ : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ φ z) :
    (∀ z : ℂ,
      ‖z‖ ≤ ρ →
      AnalyticAt ℂ (complex_starConvexClosedBall_radialPrimitive φ) z) ∧
    (∀ z : ℂ,
      ‖z‖ ≤ ρ →
      deriv (complex_starConvexClosedBall_radialPrimitive φ) z = φ z) :=
  complex_starConvexClosedBall_radialPrimitive_isPrimitive_on_starConvex
    φ hρ hstar hφ

/-- Local endpoint-variation theorem for the radial primitive.

This is the parametric/path-integral differentiability theorem needed for the
segment integral, with the segment kept inside the closed ball. -/
theorem complex_starConvexClosedBall_radialPrimitive_localEndpoint
    (φ : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ))
    (hφ : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      AnalyticAt ℂ (complex_starConvexClosedBall_radialPrimitive φ) z := by
  intro z hz
  exact
    (complex_starConvexClosedBall_radialPrimitive_isPrimitive_on_starConvex
      φ hρ hstar hφ).1 z hz

/-- Derivative computation for the radial segment primitive.

Classically this is the fundamental theorem for the one-form `φ(w) dw` on a
star-convex domain: the derivative of the segment integral with respect to its
endpoint is the integrand at the endpoint. -/
theorem complex_starConvexClosedBall_radialPrimitive_derivativeFromFTC
    (φ : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ))
    (hφ : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      deriv (complex_starConvexClosedBall_radialPrimitive φ) z = φ z := by
  intro z hz
  exact
    (complex_starConvexClosedBall_radialPrimitive_isPrimitive_on_starConvex
      φ hρ hstar hφ).2 z hz

/-- Analyticity of the radial segment primitive as a function of its endpoint. -/
theorem complex_starConvexClosedBall_radialPrimitive_analyticAt
    (φ : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ))
    (hφ : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      AnalyticAt ℂ (complex_starConvexClosedBall_radialPrimitive φ) z := by
  exact
    complex_starConvexClosedBall_radialPrimitive_localEndpoint
      φ hρ hstar hφ

/-- Cauchy/FTC path-integral step for the radial primitive derivative. -/
theorem complex_starConvexClosedBall_radialPrimitive_deriv_eq_cauchy
    (φ : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ))
    (hφ : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      deriv (complex_starConvexClosedBall_radialPrimitive φ) z = φ z := by
  exact
    complex_starConvexClosedBall_radialPrimitive_derivativeFromFTC
      φ hρ hstar hφ

/-- Derivative formula for the radial segment primitive. -/
theorem complex_starConvexClosedBall_radialPrimitive_deriv_eq
    (φ : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ))
    (hφ : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ φ z) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      deriv (complex_starConvexClosedBall_radialPrimitive φ) z = φ z :=
  complex_starConvexClosedBall_radialPrimitive_deriv_eq_cauchy
    φ hρ hstar hφ

/-- Path-integral primitive theorem over radial segments in a star-convex
closed ball.

The primitive is the line integral of `φ` over the segment from `0` to `z`.
Star-convexity keeps the segment inside the closed ball; Cauchy's theorem on
star-shaped domains identifies its complex derivative with `φ`. -/
theorem holomorphicOn_starConvexClosedBall_radialPrimitive
    (φ : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ))
    (hφ : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ φ z) :
    (∀ z : ℂ,
      ‖z‖ ≤ ρ →
      AnalyticAt ℂ (complex_starConvexClosedBall_radialPrimitive φ) z) ∧
    (∀ z : ℂ,
      ‖z‖ ≤ ρ →
      deriv (complex_starConvexClosedBall_radialPrimitive φ) z = φ z) ∧
    complex_starConvexClosedBall_radialPrimitive φ 0 = 0 := by
  exact
    ⟨complex_starConvexClosedBall_radialPrimitive_analyticAt
        φ hρ hstar hφ,
      complex_starConvexClosedBall_radialPrimitive_deriv_eq
        φ hρ hstar hφ,
      complex_starConvexClosedBall_radialPrimitive_zero φ⟩

/-- Canonical primitive theorem for analytic functions on a star-convex closed
ball.

The primitive is obtained by integrating the analytic integrand over radial
segments from the center.  Star-convexity supplies the admissible paths, and
Cauchy's theorem gives the derivative of the segment integral. -/
theorem holomorphicOn_starConvexClosedBall_hasPrimitive
    (φ : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ))
    (hφ : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ φ z) :
    ∃ P : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ P z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → deriv P z = φ z) ∧
      P 0 = 0 := by
  exact
    ⟨complex_starConvexClosedBall_radialPrimitive φ,
      holomorphicOn_starConvexClosedBall_radialPrimitive
        φ hρ hstar hφ⟩

/-- Canonical closed-ball logarithmic-derivative primitive theorem.

For a holomorphic zero-free function on a star-convex closed ball, the
logarithmic derivative has a normalized primitive on the ball.  The classical
construction is the path integral of `G' / G` along line segments, with
path-independence supplied by Cauchy's theorem on star-convex domains; cf.
Conway, *Functions of One Complex Variable I*, Ch. V, and Rudin, *Real and
Complex Analysis*, Ch. 10. -/
theorem complex_starConvexClosedBall_exists_logDerivPrimitive
    (G : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hG : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ G z)
    (hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ))
    (hrecip :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ (fun w : ℂ => (G w)⁻¹) z) :
    ∃ P : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ P z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → deriv P z = deriv G z * (G z)⁻¹) ∧
      P 0 = 0 := by
  have hlog_an :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ (fun w : ℂ => deriv G w * (G w)⁻¹) z :=
    complex_starConvexClosedBall_logDeriv_analyticAt G hG hrecip
  exact
    holomorphicOn_starConvexClosedBall_hasPrimitive
      (fun w : ℂ => deriv G w * (G w)⁻¹)
      hρ
      hstar
      hlog_an

/-- Primitive theorem for the logarithmic derivative on Jensen's convex disk.

The mathematical construction is the path integral
`P z = ∫_[0,z] G'(w) / G(w) dw` over the radial segment in the disk. Convexity
keeps every segment in the disk, analyticity of `G⁻¹` makes the logarithmic
derivative holomorphic there, and Cauchy's theorem on the convex domain gives
path independence. The normalization is the empty path at the center. Cf.
Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_convexClosedDisk_exists_logDerivPrimitive
    (G : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hG : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ G z)
    (hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ))
    (hrecip :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ (fun w : ℂ => (G w)⁻¹) z) :
    ∃ P : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ P z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → deriv P z = deriv G z * (G z)⁻¹) ∧
      P 0 = 0 := by
  exact
    complex_starConvexClosedBall_exists_logDerivPrimitive
      G hρ hG hstar hrecip

/-- Center-value comparison for the exponential reconstruction model. -/
theorem entireFunction_exp_logDerivPrimitive_reconstruct_center
    (G P : ℂ → ℂ)
    (hP_zero : P 0 = 0) :
    G 0 = G 0 * Complex.exp (P 0) := by
  calc
    G 0 = G 0 * 1 :=
      (mul_one (G 0)).symm
    _ = G 0 * Complex.exp 0 :=
      congrArg (fun w : ℂ => G 0 * w) (Complex.exp_zero.symm)
    _ = G 0 * Complex.exp (P 0) :=
      congrArg (fun w : ℂ => G 0 * Complex.exp w) hP_zero.symm

/-- Derivative of the exponential model attached to a primitive. -/
theorem entireFunction_exp_logDerivPrimitive_model_deriv_formula
    (G P : ℂ → ℂ)
    {ρ : ℝ}
    (hP_an :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ P z)
    (hP_deriv :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        deriv P z = deriv G z * (G z)⁻¹) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      deriv (fun w : ℂ => G 0 * Complex.exp (P w)) z =
        G 0 * (Complex.exp (P z) * (deriv G z * (G z)⁻¹)) := by
  intro z hz
  have hP_diff : DifferentiableAt ℂ P z :=
    (hP_an z hz).differentiableAt
  have hP_deriv_at :
      HasDerivAt P (deriv P z) z :=
    hP_diff.hasDerivAt
  have hexp_deriv_at :
      HasDerivAt
        (fun w : ℂ => Complex.exp (P w))
        (Complex.exp (P z) * deriv P z)
        z :=
    hP_deriv_at.cexp
  have hmodel_deriv_at :
      HasDerivAt
        (fun w : ℂ => G 0 * Complex.exp (P w))
        (G 0 * (Complex.exp (P z) * deriv P z))
        z :=
    hexp_deriv_at.const_mul (G 0)
  have hmodel_deriv :
      deriv (fun w : ℂ => G 0 * Complex.exp (P w)) z =
        G 0 * (Complex.exp (P z) * deriv P z) :=
    hmodel_deriv_at.deriv
  have hprimitive_deriv :
      deriv P z = deriv G z * (G z)⁻¹ :=
    hP_deriv z hz
  exact
    Eq.trans hmodel_deriv
      (congrArg
        (fun u : ℂ => G 0 * (Complex.exp (P z) * u))
        hprimitive_deriv)

/-- Pointwise algebra turning the logarithmic-derivative equation into equality
with the exponential model, once reconstruction of the value is known. -/
theorem entireFunction_exp_logDerivPrimitive_model_deriv_algebra
    (G P : ℂ → ℂ)
    {z : ℂ}
    (hzero_z : G z ≠ 0)
    (hreconstruct_z : G z = G 0 * Complex.exp (P z)) :
    deriv G z =
      G 0 * (Complex.exp (P z) * (deriv G z * (G z)⁻¹)) := by
  calc
    deriv G z = deriv G z * 1 :=
      (mul_one (deriv G z)).symm
    _ = deriv G z * (G z * (G z)⁻¹) :=
      congrArg (fun u : ℂ => deriv G z * u)
        (Eq.symm (mul_inv_cancel₀ hzero_z))
    _ = deriv G z * (G 0 * Complex.exp (P z) * (G z)⁻¹) :=
      congrArg
        (fun u : ℂ => deriv G z * (u * (G z)⁻¹))
        hreconstruct_z
    _ = deriv G z * (G 0 * (Complex.exp (P z) * (G z)⁻¹)) :=
      congrArg
        (fun u : ℂ => deriv G z * u)
        (mul_assoc (G 0) (Complex.exp (P z)) (G z)⁻¹)
    _ = (deriv G z * G 0) * (Complex.exp (P z) * (G z)⁻¹) :=
      (mul_assoc (deriv G z) (G 0) (Complex.exp (P z) * (G z)⁻¹)).symm
    _ = (G 0 * deriv G z) * (Complex.exp (P z) * (G z)⁻¹) :=
      congrArg
        (fun u : ℂ => u * (Complex.exp (P z) * (G z)⁻¹))
        (mul_comm (deriv G z) (G 0))
    _ = G 0 * (deriv G z * (Complex.exp (P z) * (G z)⁻¹)) :=
      mul_assoc (G 0) (deriv G z) (Complex.exp (P z) * (G z)⁻¹)
    _ = G 0 * ((deriv G z * Complex.exp (P z)) * (G z)⁻¹) :=
      congrArg
        (fun u : ℂ => G 0 * u)
        (mul_assoc (deriv G z) (Complex.exp (P z)) (G z)⁻¹).symm
    _ = G 0 * ((Complex.exp (P z) * deriv G z) * (G z)⁻¹) :=
      congrArg
        (fun u : ℂ => G 0 * (u * (G z)⁻¹))
        (mul_comm (deriv G z) (Complex.exp (P z)))
    _ = G 0 * (Complex.exp (P z) * (deriv G z * (G z)⁻¹)) :=
      congrArg
        (fun u : ℂ => G 0 * u)
        (mul_assoc (Complex.exp (P z)) (deriv G z) (G z)⁻¹)

/-- Core quotient derivative-zero calculation for exponential reconstruction
from a logarithmic-derivative primitive.

The quotient `G / (G 0 * exp P)` has zero derivative wherever the primitive
identity `P' = G'/G` holds and `G` is zero-free on the disk.  This is the
radial FTC input before any endpoint reconstruction is used. -/
theorem entireFunction_convexClosedDisk_exp_logDerivPrimitive_quotient_deriv_zero_and_center_core
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
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans (norm_nonneg z) hz
  have hzero_mem : ‖(0 : ℂ)‖ ≤ ρ := by
    calc
      ‖(0 : ℂ)‖ = 0 := norm_zero
      _ ≤ ρ := hρ_nonneg
  have hG0_ne : G 0 ≠ 0 :=
    hzero 0 hzero_mem
  have hGz_ne : G z ≠ 0 :=
    hzero z hz
  have hden_ne : G 0 * Complex.exp (P z) ≠ 0 := by
    exact mul_ne_zero hG0_ne (Complex.exp_ne_zero (P z))
  have hdiffG : DifferentiableAt ℂ G z :=
    (hG z hz).differentiableAt
  have hdiffP : DifferentiableAt ℂ P z :=
    (hP_an z hz).differentiableAt
  have hdiffExp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (P w)) z :=
    hdiffP.cexp
  have hdiffModel : DifferentiableAt ℂ (fun w : ℂ => G 0 * Complex.exp (P w)) z :=
    hdiffExp.const_mul (G 0)
  have hlogExp : logDeriv (fun w : ℂ => Complex.exp (P w)) z = deriv P z := by
    calc
      logDeriv (fun w : ℂ => Complex.exp (P w)) z =
          logDeriv (Complex.exp) (P z) * deriv P z := by
            exact
              logDeriv_comp (f := Complex.exp) (g := P) (x := z)
                Complex.differentiableAt_exp hdiffP
      _ = 1 * deriv P z := by
            exact congrArg (fun t : ℂ => t * deriv P z)
              (congrArg (fun f : ℂ → ℂ => f (P z)) Complex.LogDeriv_exp)
      _ = deriv P z := by
            exact one_mul (deriv P z)
  have hlogModel : logDeriv (fun w : ℂ => G 0 * Complex.exp (P w)) z =
      deriv G z * (G z)⁻¹ := by
    calc
      logDeriv (fun w : ℂ => G 0 * Complex.exp (P w)) z =
          logDeriv (fun w : ℂ => Complex.exp (P w)) z := by
            exact logDeriv_const_mul (f := fun w : ℂ => Complex.exp (P w)) z (G 0) hG0_ne
      _ = deriv P z := hlogExp
      _ = deriv G z * (G z)⁻¹ := hP_deriv z hz
  have hlogG : logDeriv G z = deriv G z * (G z)⁻¹ := by
    calc
      logDeriv G z = deriv G z / G z := rfl
      _ = deriv G z * (G z)⁻¹ := by
            exact (div_eq_mul_inv _ _).symm
  have hsame :
      logDeriv G z = logDeriv (fun w : ℂ => G 0 * Complex.exp (P w)) z := by
    calc
      logDeriv G z = deriv G z * (G z)⁻¹ := hlogG
      _ = logDeriv (fun w : ℂ => G 0 * Complex.exp (P w)) z := hlogModel.symm
  have hlogQ :
      logDeriv (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z = 0 := by
    calc
      logDeriv (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z =
          logDeriv G z -
            logDeriv (fun w : ℂ => G 0 * Complex.exp (P w)) z := by
              exact
                logDeriv_div z hGz_ne hden_ne hdiffG hdiffModel
      _ = 0 := by
            exact sub_eq_zero.mpr hsame
  have hderiv_zero :
      deriv (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z = 0 := by
    have hquot_ne :
        G z / (G 0 * Complex.exp (P z)) ≠ 0 := by
      exact div_ne_zero hGz_ne hden_ne
    have hdiv_zero :
        deriv (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z /
          (G z / (G 0 * Complex.exp (P z))) = 0 := by
      calc
        deriv (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z /
            (G z / (G 0 * Complex.exp (P z))) =
          logDeriv (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z := by
            rfl
        _ = 0 := hlogQ
    exact
      match div_eq_zero_iff.mp hdiv_zero with
      | Or.inl hnum_zero => hnum_zero
      | Or.inr hden_zero => False.elim (hquot_ne hden_zero)
  have hcenter :
      (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) 0 = 1 := by
    have hden0 : G 0 * Complex.exp (P 0) = G 0 := by
      calc
        G 0 * Complex.exp (P 0) = G 0 * Complex.exp 0 := by
          exact congrArg (fun t : ℂ => G 0 * Complex.exp t) hP_zero
        _ = G 0 * 1 := by
          exact congrArg (fun t : ℂ => G 0 * t) Complex.exp_zero
        _ = G 0 := by
          exact mul_one (G 0)
    calc
      (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) 0 =
          G 0 / (G 0 * Complex.exp (P 0)) := rfl
      _ = G 0 / G 0 := by
          exact congrArg (fun t : ℂ => G 0 / t) hden0
      _ = 1 := by
          exact div_self hG0_ne
  exact ⟨hderiv_zero, hcenter⟩

/-- Analyticity of the exponential reconstruction quotient on the zero-free
closed disk. -/
theorem entireFunction_convexClosedDisk_exp_logDerivPrimitive_quotient_analyticAt
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
    (hρ : 0 ≤ ρ) :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      AnalyticAt ℂ (fun w : ℂ => G w / (G 0 * Complex.exp (P w))) z := by
  intro z hz
  have hzero_mem : ‖(0 : ℂ)‖ ≤ ρ := by
    calc
      ‖(0 : ℂ)‖ = 0 := norm_zero
      _ ≤ ρ := hρ
  have hG0_ne : G 0 ≠ 0 :=
    hzero 0 hzero_mem
  have hden_ne : G 0 * Complex.exp (P z) ≠ 0 := by
    exact mul_ne_zero hG0_ne (Complex.exp_ne_zero (P z))
  have hden_an : AnalyticAt ℂ (fun w : ℂ => G 0 * Complex.exp (P w)) z :=
    let hden_const_an : AnalyticAt ℂ (fun _w : ℂ => G 0) z :=
      analyticAt_const
    let hden_exp_an : AnalyticAt ℂ (fun w : ℂ => Complex.exp (P w)) z :=
      (hP_an z hz).cexp
    hden_const_an.mul hden_exp_an
  exact (hG z hz).div hden_an hden_ne

/-- Real interval derivative-zero constant theorem on `[0,1]`, in endpoint
form.

This is the one-dimensional FTC input used by the radial segment argument:
continuity on the closed interval plus right-derivative zero on `Ico 0 1`
forces the endpoint values to agree. -/
theorem complex_interval_endpoint_eq_of_hasDerivWithinAt_zero
    (φ : ℝ → ℂ)
    (hcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1))
    (hderiv :
      ∀ t : ℝ,
        t ∈ Set.Ico (0 : ℝ) 1 →
        HasDerivWithinAt φ 0 (Set.Ici t) t) :
    φ 1 = φ 0 :=
  constant_of_has_deriv_right_zero hcont hderiv 1
    (Set.right_mem_Icc.mpr zero_le_one)

/-- The radial closed-disk difference function attached to two analytic
functions. -/
def entireFunction_convexClosedDisk_radialDifference
    (F H : ℂ → ℂ)
    (z : ℂ) :
    ℝ → ℂ :=
  fun t : ℝ => F ((t : ℂ) • z) - H ((t : ℂ) • z)

/-- The real affine segment from `0` to `z` is the same parametrization as
complex scalar multiplication by the real parameter. -/
theorem complex_lineMap_zero_eq_ofReal_smul
    (z : ℂ)
    (t : ℝ) :
    AffineMap.lineMap (0 : ℂ) z t = ((t : ℂ) • z) := by
  calc
    AffineMap.lineMap (0 : ℂ) z t =
        (1 - t) • (0 : ℂ) + t • z :=
      AffineMap.lineMap_apply_module (0 : ℂ) z t
    _ = 0 + t • z :=
      congrArg
        (fun u : ℂ => u + t • z)
        (show (1 - t : ℝ) • (0 : ℂ) = 0 from smul_zero (1 - t : ℝ))
    _ = t • z :=
      zero_add (t • z)
    _ = ((t : ℂ) • z) :=
      (algebraMap_smul ℂ t z).symm

/-- Convexity keeps the radial segment from the center to `z` inside the
closed disk. -/
theorem entireFunction_convexClosedDisk_radialSegment_mem
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((t : ℂ) • z) ∈ Metric.closedBall (0 : ℂ) ρ := by
  have hzero_mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ :=
    Metric.mem_closedBall_self hρ
  have hz_mem : z ∈ Metric.closedBall (0 : ℂ) ρ :=
    mem_closedBall_zero_iff.mpr hz
  have hline :
      AffineMap.lineMap (0 : ℂ) z t ∈ Metric.closedBall (0 : ℂ) ρ :=
    hconvex.mapsTo_lineMap hzero_mem hz_mem ht
  exact
    Eq.subst
      (motive := fun w : ℂ => w ∈ Metric.closedBall (0 : ℂ) ρ)
      (complex_lineMap_zero_eq_ofReal_smul z t)
      hline

/-- The radial parametrization is continuous on `[0,1]`. -/
theorem complex_radialSegment_continuousOn
    (z : ℂ) :
    ContinuousOn (fun t : ℝ => ((t : ℂ) • z)) (Set.Icc (0 : ℝ) 1) :=
  (Complex.continuous_ofReal.smul continuous_const).continuousOn

/-- Analyticity on the closed disk gives continuity of a function along a
radial segment in that disk. -/
theorem entireFunction_convexClosedDisk_radial_comp_continuousOn
    (F : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    ContinuousOn (fun t : ℝ => F ((t : ℂ) • z)) (Set.Icc (0 : ℝ) 1) := by
  have hF_cont :
      ContinuousOn F (Metric.closedBall (0 : ℂ) ρ) := by
    intro w hw
    exact (hF w (mem_closedBall_zero_iff.mp hw)).continuousAt.continuousWithinAt
  have hpath_cont :
      ContinuousOn (fun t : ℝ => ((t : ℂ) • z)) (Set.Icc (0 : ℝ) 1) :=
    complex_radialSegment_continuousOn z
  have hpath_mem :
      Set.MapsTo
        (fun t : ℝ => ((t : ℂ) • z))
        (Set.Icc (0 : ℝ) 1)
        (Metric.closedBall (0 : ℂ) ρ) := by
    intro t ht
    exact
      entireFunction_convexClosedDisk_radialSegment_mem hρ hconvex hz ht
  exact hF_cont.comp' hpath_cont hpath_mem

/-- The radial difference is continuous on `[0,1]`. -/
theorem entireFunction_convexClosedDisk_radialDifference_continuousOn
    (F H : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hH : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ H z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    ContinuousOn
      (entireFunction_convexClosedDisk_radialDifference F H z)
      (Set.Icc (0 : ℝ) 1) := by
  have hF_cont :
      ContinuousOn (fun t : ℝ => F ((t : ℂ) • z)) (Set.Icc (0 : ℝ) 1) :=
    entireFunction_convexClosedDisk_radial_comp_continuousOn
      F hF hρ hconvex hz
  have hH_cont :
      ContinuousOn (fun t : ℝ => H ((t : ℂ) • z)) (Set.Icc (0 : ℝ) 1) :=
    entireFunction_convexClosedDisk_radial_comp_continuousOn
      H hH hρ hconvex hz
  exact hF_cont.sub hH_cont

/-- The radial path `t ↦ (t : ℂ) • z` has real derivative `z`. -/
theorem complex_radialSegment_hasDerivWithinAt
    (z : ℂ)
    (t : ℝ) :
    HasDerivWithinAt
      (fun s : ℝ => ((s : ℂ) • z))
      z
      (Set.Ici t)
      t := by
  have hmul_complex :
      HasDerivAt (fun w : ℂ => w * z) z (t : ℂ) :=
    hasDerivAt_mul_const z
  have hmul_real :
      HasDerivAt (fun s : ℝ => (s : ℂ) * z) z t :=
    hmul_complex.comp_ofReal
  have hradial_real :
      HasDerivAt (fun s : ℝ => ((s : ℂ) • z)) z t := by
    exact hmul_real
  exact hradial_real.hasDerivWithinAt

/-- Complex differentiability of `F` at a radial point, viewed as a real
Fréchet derivative. -/
theorem entireFunction_convexClosedDisk_radialPoint_hasFDerivAt_real
    (F : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ)
    {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    HasFDerivAt
      F
      ((deriv F ((t : ℂ) • z)) • (1 : ℂ →L[ℝ] ℂ))
      ((t : ℂ) • z) := by
  have hpoint_mem :
      ((t : ℂ) • z) ∈ Metric.closedBall (0 : ℂ) ρ :=
    entireFunction_convexClosedDisk_radialSegment_mem
      hρ hconvex hz (Set.Ico_subset_Icc_self ht)
  have hpoint_norm : ‖((t : ℂ) • z)‖ ≤ ρ :=
    mem_closedBall_zero_iff.mp hpoint_mem
  have hcomplex :
      HasDerivAt F (deriv F ((t : ℂ) • z)) ((t : ℂ) • z) :=
    (hF ((t : ℂ) • z) hpoint_norm).differentiableAt.hasDerivAt
  exact hcomplex.complexToReal_fderiv

/-- Chain rule for one analytic function restricted to a radial segment.

The derivative is the complex derivative paired with the radial tangent `z`.
This is the ordinary calculus bridge from complex differentiability at the
radial point to a right-derivative in the real parameter. -/
theorem entireFunction_convexClosedDisk_radial_comp_hasDerivWithinAt
    (F : ℂ → ℂ)
    {ρ : ℝ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ F z)
    (hρ : 0 ≤ ρ)
    (hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ))
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ)
    {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun s : ℝ => F ((s : ℂ) • z))
      (deriv F ((t : ℂ) • z) * z)
      (Set.Ici t)
      t := by
  have hF_real :
      HasFDerivAt
        F
        ((deriv F ((t : ℂ) • z)) • (1 : ℂ →L[ℝ] ℂ))
        ((t : ℂ) • z) :=
    entireFunction_convexClosedDisk_radialPoint_hasFDerivAt_real
      F hF hρ hconvex hz ht
  have hpath :
      HasDerivWithinAt
        (fun s : ℝ => ((s : ℂ) • z))
        z
        (Set.Ici t)
        t :=
    complex_radialSegment_hasDerivWithinAt z t
  have hcomp :
      HasDerivWithinAt
        (fun s : ℝ => F ((s : ℂ) • z))
        (((deriv F ((t : ℂ) • z)) • (1 : ℂ →L[ℝ] ℂ)) z)
        (Set.Ici t)
        t :=
    hF_real.comp_hasDerivWithinAt t hpath
  have htangent :
      ((deriv F ((t : ℂ) • z)) • (1 : ℂ →L[ℝ] ℂ)) z =
        deriv F ((t : ℂ) • z) * z := by
    exact rfl
  exact
    Eq.subst
      (motive := fun u : ℂ =>
        HasDerivWithinAt
          (fun s : ℝ => F ((s : ℂ) • z))
          u
          (Set.Ici t)
          t)
      htangent
      hcomp

/-- Chain-rule derivative calculation for the radial difference.

This is the only remaining ordinary-calculus sink in the radial FTC branch:
differentiate `t ↦ F ((t : ℂ) • z) - H ((t : ℂ) • z)` from the right and use
`deriv F = deriv H` at the radial point. -/
theorem entireFunction_convexClosedDisk_radialDifference_hasDerivWithinAt_zero
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
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ)
    {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    HasDerivWithinAt
      (entireFunction_convexClosedDisk_radialDifference F H z)
      0
      (Set.Ici t)
      t := by
  have hF_radial :
      HasDerivWithinAt
        (fun s : ℝ => F ((s : ℂ) • z))
        (deriv F ((t : ℂ) • z) * z)
        (Set.Ici t)
        t :=
    entireFunction_convexClosedDisk_radial_comp_hasDerivWithinAt
      F hF hρ hconvex hz ht
  have hH_radial :
      HasDerivWithinAt
        (fun s : ℝ => H ((s : ℂ) • z))
        (deriv H ((t : ℂ) • z) * z)
        (Set.Ici t)
        t :=
    entireFunction_convexClosedDisk_radial_comp_hasDerivWithinAt
      H hH hρ hconvex hz ht
  have hsub :
      HasDerivWithinAt
        (entireFunction_convexClosedDisk_radialDifference F H z)
        (deriv F ((t : ℂ) • z) * z - deriv H ((t : ℂ) • z) * z)
        (Set.Ici t)
        t :=
    hF_radial.sub hH_radial
  have hpoint_mem :
      ((t : ℂ) • z) ∈ Metric.closedBall (0 : ℂ) ρ :=
    entireFunction_convexClosedDisk_radialSegment_mem
      hρ hconvex hz (Set.Ico_subset_Icc_self ht)
  have hpoint_norm : ‖((t : ℂ) • z)‖ ≤ ρ :=
    mem_closedBall_zero_iff.mp hpoint_mem
  have hderiv_eq :
      deriv F ((t : ℂ) • z) = deriv H ((t : ℂ) • z) :=
    hderiv ((t : ℂ) • z) hpoint_norm
  have hradial_deriv_zero :
      deriv F ((t : ℂ) • z) * z - deriv H ((t : ℂ) • z) * z = 0 :=
    sub_eq_zero.mpr (congrArg (fun u : ℂ => u * z) hderiv_eq)
  exact
    Eq.subst
      (motive := fun u : ℂ =>
        HasDerivWithinAt
          (entireFunction_convexClosedDisk_radialDifference F H z)
          u
          (Set.Ici t)
          t)
      hradial_deriv_zero
      hsub

/-- Center value of the radial difference. -/
theorem entireFunction_convexClosedDisk_radialDifference_zero
    (F H : ℂ → ℂ)
    (hcenter : F 0 = H 0)
    (z : ℂ) :
    entireFunction_convexClosedDisk_radialDifference F H z 0 = 0 := by
  calc
    entireFunction_convexClosedDisk_radialDifference F H z 0 =
        F ((0 : ℂ) • z) - H ((0 : ℂ) • z) := rfl
    _ = F 0 - H 0 :=
      congrArg₂ (fun u v : ℂ => F u - H v) (zero_smul ℂ z) (zero_smul ℂ z)
    _ = H 0 - H 0 :=
      congrArg (fun u : ℂ => u - H 0) hcenter
    _ = 0 :=
      sub_self (H 0)

/-- Endpoint value of the radial difference. -/
theorem entireFunction_convexClosedDisk_radialDifference_one
    (F H : ℂ → ℂ)
    (z : ℂ) :
    entireFunction_convexClosedDisk_radialDifference F H z 1 = F z - H z := by
  calc
    entireFunction_convexClosedDisk_radialDifference F H z 1 =
        F ((1 : ℂ) • z) - H ((1 : ℂ) • z) := rfl
    _ = F z - H z :=
      congrArg₂ (fun u v : ℂ => F u - H v) (one_smul ℂ z) (one_smul ℂ z)

/-- Turning constancy of the radial difference into endpoint equality. -/
theorem entireFunction_convexClosedDisk_endpoint_eq_of_radialDifference_endpoint_eq
    (F H : ℂ → ℂ)
    (hcenter : F 0 = H 0)
    {z : ℂ}
    (hdiff_endpoint :
      entireFunction_convexClosedDisk_radialDifference F H z 1 =
        entireFunction_convexClosedDisk_radialDifference F H z 0) :
    F z = H z := by
  have hleft :
      entireFunction_convexClosedDisk_radialDifference F H z 1 = F z - H z :=
    entireFunction_convexClosedDisk_radialDifference_one F H z
  have hright :
      entireFunction_convexClosedDisk_radialDifference F H z 0 = 0 :=
    entireFunction_convexClosedDisk_radialDifference_zero F H hcenter z
  have hsub_zero : F z - H z = 0 := by
    exact Eq.trans (Eq.symm hleft) (Eq.trans hdiff_endpoint hright)
  exact sub_eq_zero.mp hsub_zero

/-- Real-interval calculus package for a radial segment difference.

The missing analytic work in the FTC branch is exactly to show that the radial
difference is continuous on `[0,1]` and has right-derivative zero on `Ico 0 1`.
That proof is the complex chain rule along `t ↦ t • z`, plus convexity of the
disk segment and the hypothesis `deriv F = deriv H`. -/
theorem entireFunction_convexClosedDisk_radialDifference_intervalCalculus
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
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    ContinuousOn
        (entireFunction_convexClosedDisk_radialDifference F H z)
        (Set.Icc (0 : ℝ) 1) ∧
      (∀ t : ℝ,
        t ∈ Set.Ico (0 : ℝ) 1 →
        HasDerivWithinAt
          (entireFunction_convexClosedDisk_radialDifference F H z)
          0
          (Set.Ici t)
          t) := by
  have hcont :
      ContinuousOn
        (entireFunction_convexClosedDisk_radialDifference F H z)
        (Set.Icc (0 : ℝ) 1) :=
    entireFunction_convexClosedDisk_radialDifference_continuousOn
      F H hF hH hρ hconvex hz
  have hderiv_zero :
      ∀ t : ℝ,
        t ∈ Set.Ico (0 : ℝ) 1 →
        HasDerivWithinAt
          (entireFunction_convexClosedDisk_radialDifference F H z)
          0
          (Set.Ici t)
          t := by
    intro t ht
    exact
      entireFunction_convexClosedDisk_radialDifference_hasDerivWithinAt_zero
        F H hF hH hρ hconvex hderiv hz ht
  exact ⟨hcont, hderiv_zero⟩

/-- Constancy of the radial difference on `[0,1]` from the interval calculus
package. -/
theorem entireFunction_convexClosedDisk_radialDifference_endpoint_eq
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
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    entireFunction_convexClosedDisk_radialDifference F H z 1 =
      entireFunction_convexClosedDisk_radialDifference F H z 0 := by
  have hcalc :
      ContinuousOn
          (entireFunction_convexClosedDisk_radialDifference F H z)
          (Set.Icc (0 : ℝ) 1) ∧
        (∀ t : ℝ,
          t ∈ Set.Ico (0 : ℝ) 1 →
          HasDerivWithinAt
            (entireFunction_convexClosedDisk_radialDifference F H z)
            0
            (Set.Ici t)
            t) :=
    entireFunction_convexClosedDisk_radialDifference_intervalCalculus
      F H hF hH hρ hconvex hderiv hz
  exact
    complex_interval_endpoint_eq_of_hasDerivWithinAt_zero
      (entireFunction_convexClosedDisk_radialDifference F H z)
      hcalc.1
      hcalc.2

/-- Deep real-interval FTC core for radial equality propagation on a convex
Jensen disk.

This is the reusable radial theorem underneath both generic derivative-equality
propagation and quotient reconstruction: restrict to `t ↦ t • z`, use convexity
to stay in the disk, and apply the real derivative-zero constant theorem on
`[0,1]`. -/
theorem entireFunction_convexClosedDisk_radialSegment_endpoint_eq_of_deriv_eq_and_center_ftc_core
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
  have hdiff_endpoint :
      entireFunction_convexClosedDisk_radialDifference F H z 1 =
        entireFunction_convexClosedDisk_radialDifference F H z 0 :=
    entireFunction_convexClosedDisk_radialDifference_endpoint_eq
      F H hF hH hρ hconvex hderiv hz
  exact
    entireFunction_convexClosedDisk_endpoint_eq_of_radialDifference_endpoint_eq
      F H hcenter hdiff_endpoint

/-- Radial FTC owner root for exponential reconstruction from a logarithmic
derivative primitive.

For a fixed endpoint `z`, restrict to the segment `t ↦ t • z` and apply the
real interval derivative-zero constant theorem to
`t ↦ G (t • z) / (G 0 * exp (P (t • z)))`.  Convexity keeps the segment in the
closed disk, the chain rule and `P' = G'/G` make the real derivative vanish,
and the normalization `P 0 = 0` fixes the center value. -/
theorem entireFunction_convexClosedDisk_exp_logDerivPrimitive_radialSegment_endpoint_eq
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
    G z = G 0 * Complex.exp (P z) := by
  have hρ : 0 ≤ ρ :=
    le_trans (norm_nonneg z) hz
  have hquot_an :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        AnalyticAt ℂ (fun u : ℂ => G u / (G 0 * Complex.exp (P u))) w :=
    entireFunction_convexClosedDisk_exp_logDerivPrimitive_quotient_analyticAt
      G P hG hzero hP_an hρ
  have hquot_deriv :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        deriv (fun u : ℂ => G u / (G 0 * Complex.exp (P u))) w =
          deriv (fun _ : ℂ => (1 : ℂ)) w := by
    intro w hw
    have hcore :
        deriv (fun u : ℂ => G u / (G 0 * Complex.exp (P u))) w = 0 ∧
          (fun u : ℂ => G u / (G 0 * Complex.exp (P u))) 0 = 1 :=
      entireFunction_convexClosedDisk_exp_logDerivPrimitive_quotient_deriv_zero_and_center_core
        G P hG hzero hP_an hP_deriv hP_zero hw
    have hconst_deriv_fun :
        deriv (fun _ : ℂ => (1 : ℂ)) = fun _ : ℂ => 0 :=
      deriv_const' (𝕜 := ℂ) (c := (1 : ℂ))
    have hconst_deriv_at :
        deriv (fun _ : ℂ => (1 : ℂ)) w = 0 :=
      congrArg (fun f : ℂ → ℂ => f w) hconst_deriv_fun
    exact Eq.trans hcore.1 (Eq.symm hconst_deriv_at)
  have hquot_center :
      (fun u : ℂ => G u / (G 0 * Complex.exp (P u))) 0 =
        (fun _ : ℂ => (1 : ℂ)) 0 :=
    (entireFunction_convexClosedDisk_exp_logDerivPrimitive_quotient_deriv_zero_and_center_core
      G P hG hzero hP_an hP_deriv hP_zero hz).2
  have hquot_endpoint :
      (fun u : ℂ => G u / (G 0 * Complex.exp (P u))) z =
        (fun _ : ℂ => (1 : ℂ)) z :=
    entireFunction_convexClosedDisk_radialSegment_endpoint_eq_of_deriv_eq_and_center_ftc_core
      (fun u : ℂ => G u / (G 0 * Complex.exp (P u)))
      (fun _ : ℂ => (1 : ℂ))
      hquot_an
      (fun _ _ => analyticAt_const)
      hρ
      (entireFunction_jensenClosedDisk_convex ρ)
      hquot_deriv
      hquot_center
      hz
  have hzero_mem : ‖(0 : ℂ)‖ ≤ ρ := by
    calc
      ‖(0 : ℂ)‖ = 0 := norm_zero
      _ ≤ ρ := hρ
  have hden_ne : G 0 * Complex.exp (P z) ≠ 0 := by
    exact mul_ne_zero (hzero 0 hzero_mem) (Complex.exp_ne_zero (P z))
  exact (div_eq_one_iff_eq hden_ne).mp hquot_endpoint

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

/-- The logarithmic derivative of a zero-free holomorphic function on a Jensen
closed disk has a primitive on that disk, normalized at the disk center.

This is the analytic integration step in the simply-connected disk proof:
on the convex disk, the closed holomorphic one-form `(G' / G) dz` has a
single-valued primitive.  Cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_zeroFreeOnClosedDisk_exists_logDerivPrimitive
    (G : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hG : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ G z)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0) :
    ∃ P : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ P z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → deriv P z = deriv G z * (G z)⁻¹) ∧
      P 0 = 0 := by
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans zero_le_one hρ
  have hstar :
      StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ) :=
    entireFunction_jensenClosedDisk_starConvex_center hρ_nonneg
  have hrecip :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ (fun w : ℂ => (G w)⁻¹) z :=
    fun z hz =>
      entireFunction_zeroFreeOnClosedDisk_reciprocal_analyticAt
        G hG hzero hz
  exact
    entireFunction_convexClosedDisk_exists_logDerivPrimitive
      G hρ_nonneg hG hstar hrecip

/-- A normalized primitive of `G' / G` reconstructs the zero-free holomorphic
function by exponentiating and multiplying by the center value. -/
theorem entireFunction_zeroFreeOnClosedDisk_exp_logDerivPrimitive_reconstruct
    (G P : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hG : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ G z)
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
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans zero_le_one hρ
  have hconvex : Convex ℝ (Metric.closedBall (0 : ℂ) ρ) :=
    entireFunction_jensenClosedDisk_convex ρ
  exact
    entireFunction_convexClosedDisk_exp_logDerivPrimitive_reconstruct
      G P hρ_nonneg hG hconvex hzero hP_an hP_deriv hP_zero

/-- A normalized primitive of the logarithmic derivative gives an analytic
logarithm branch after adding one logarithm of the nonzero center value. -/
theorem entireFunction_zeroFreeOnClosedDisk_exists_analyticLogBranch_of_logDerivPrimitive
    (G P : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0)
    (hP_an :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ P z)
    (hP_reconstruct :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z = G 0 * Complex.exp (P z)) :
    ∃ L : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ L z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → G z = Complex.exp (L z)) := by
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans zero_le_one hρ
  have hzero_mem : ‖(0 : ℂ)‖ ≤ ρ :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ρ)
      (norm_zero : ‖(0 : ℂ)‖ = 0).symm
      hρ_nonneg
  have hG_zero_ne : G 0 ≠ 0 :=
    hzero 0 hzero_mem
  let L : ℂ → ℂ := fun z => Complex.log (G 0) + P z
  have hL_an :
      ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ L z :=
    fun z hz =>
      analyticAt_const.add (hP_an z hz)
  have hL_log :
      ∀ z : ℂ, ‖z‖ ≤ ρ → G z = Complex.exp (L z) := by
    intro z hz
    have hrec : G z = G 0 * Complex.exp (P z) :=
      hP_reconstruct z hz
    have hcenter_exp : Complex.exp (Complex.log (G 0)) = G 0 :=
      Complex.exp_log hG_zero_ne
    calc
      G z = G 0 * Complex.exp (P z) :=
        hrec
      _ = Complex.exp (Complex.log (G 0)) * Complex.exp (P z) :=
        congrArg (fun w : ℂ => w * Complex.exp (P z)) hcenter_exp.symm
      _ = Complex.exp (Complex.log (G 0) + P z) :=
        (Complex.exp_add (Complex.log (G 0)) (P z)).symm
      _ = Complex.exp (L z) :=
        congrArg Complex.exp rfl
  exact ⟨L, hL_an, hL_log⟩

/-- Holomorphic logarithm existence on a zero-free simply connected Jensen disk.

This is the canonical analytic-log construction used by Jensen's formula: a
holomorphic zero-free map from the disk to `ℂˣ` lifts through
`Complex.exp : ℂ → ℂˣ`.  Cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_zeroFreeOnClosedDisk_exists_analyticLogBranch_from_simplyConnectedDisk
    (G : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hG : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ G z)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0) :
    ∃ L : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ L z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → G z = Complex.exp (L z)) := by
  exact
    match entireFunction_zeroFreeOnClosedDisk_exists_logDerivPrimitive
        G hρ hG hzero with
    | Exists.intro P hP_data =>
        match hP_data with
        | And.intro hP_an hP_tail =>
            match hP_tail with
            | And.intro hP_deriv hP_zero =>
                have hP_reconstruct :
                    ∀ z : ℂ,
                      ‖z‖ ≤ ρ →
                        G z = G 0 * Complex.exp (P z) :=
                  entireFunction_zeroFreeOnClosedDisk_exp_logDerivPrimitive_reconstruct
                    G P hρ hG hzero hP_an hP_deriv hP_zero
                entireFunction_zeroFreeOnClosedDisk_exists_analyticLogBranch_of_logDerivPrimitive
                  G P hρ hzero hP_an hP_reconstruct

/-- The real part of any chosen analytic logarithm is the logarithm of the
norm of the original zero-free function. -/
theorem entireFunction_analyticLogBranch_re_eq_log_norm
    (G L : ℂ → ℂ)
    {ρ : ℝ}
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ)
    (hlog :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        G w = Complex.exp (L w)) :
    (L z).re = Real.log ‖G z‖ := by
  have hzlog : G z = Complex.exp (L z) :=
    hlog z hz
  have hnorm_log :
      Real.log ‖G z‖ = Real.log ‖Complex.exp (L z)‖ := by
    exact congrArg (fun w : ℂ => Real.log ‖w‖) hzlog
  have hexp_log :
      Real.log ‖Complex.exp (L z)‖ = (L z).re :=
    complex_log_norm_exp_eq_re (L z)
  exact (Eq.trans hnorm_log hexp_log).symm

/-- The analytic logarithm branch supplied on a Jensen disk is automatically
normalized in real part at the center. -/
theorem entireFunction_analyticLogBranch_center_re_eq_log_norm
    (G L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hlog :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        G w = Complex.exp (L w)) :
    (L 0).re = Real.log ‖G 0‖ := by
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans zero_le_one hρ
  have hzero_mem : ‖(0 : ℂ)‖ ≤ ρ :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ρ)
      (norm_zero : ‖(0 : ℂ)‖ = 0).symm
      hρ_nonneg
  exact
    entireFunction_analyticLogBranch_re_eq_log_norm
      G L hzero_mem hlog

/-- Analytic-log existence on a simply connected Jensen disk.

This is the exact topological/complex-analytic owner root needed by Jensen's
formula: a holomorphic zero-free function on a neighborhood of the closed disk
has a holomorphic logarithm on that disk, with the real part normalized at the
center.  The intended proof is the classical lifting of `G : D → ℂˣ` through
`Complex.exp : ℂ → ℂˣ` on the simply connected disk, followed by the identity
`Real.log ‖Complex.exp w‖ = w.re`.  Cf. Titchmarsh, *The Theory of
Functions*, §5. -/
theorem entireFunction_zeroFreeOnClosedDisk_exists_analyticLog_from_simplyConnectedDisk
    (G : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hG : ∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ G z)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0) :
    ∃ L : ℂ → ℂ,
    (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ L z) ∧
    (∀ z : ℂ, ‖z‖ ≤ ρ → G z = Complex.exp (L z)) ∧
    (L 0).re = Real.log ‖G 0‖ := by
  exact
    match entireFunction_zeroFreeOnClosedDisk_exists_analyticLogBranch_from_simplyConnectedDisk
        G hρ hG hzero with
    | Exists.intro L hL_data =>
        match hL_data with
        | And.intro hL_an hL_log =>
            have hcenter :
                (L 0).re = Real.log ‖G 0‖ :=
              entireFunction_analyticLogBranch_center_re_eq_log_norm
                G L hρ hL_log
            Exists.intro L (And.intro hL_an (And.intro hL_log hcenter))

/-- A zero-free holomorphic function on a closed disk admits a holomorphic
logarithm on a neighborhood of that disk, normalized at the center.

This is the analytic-log existence step in Jensen's proof.  It follows by
applying the holomorphic logarithm construction to the zero-free image of the
simply connected disk; cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_zeroFreeOnClosedDisk_exists_analyticLog
    (G : ℂ → ℂ)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0) :
    ∃ L : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ L z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → G z = Complex.exp (L z)) ∧
      (L 0).re = Real.log ‖G 0‖ := by
  exact
    entireFunction_zeroFreeOnClosedDisk_exists_analyticLog_from_simplyConnectedDisk
      G hρ (fun z _hz => hG z) hzero

/-- Pointwise analyticity on Jensen's closed disk gives the `DiffContOnCl`
package needed by Cauchy's integral formula on the corresponding open disk. -/
theorem entireFunction_analyticOnClosedDisk_diffContOnCl
  (L : ℂ → ℂ)
  {ρ : ℝ}
  (hL :
    ∀ z : ℂ,
      ‖z‖ ≤ ρ →
      AnalyticAt ℂ L z) :
  DiffContOnCl ℂ L (Metric.ball (0 : ℂ) ρ) := by
  have hdiff :
      DifferentiableOn ℂ L (Metric.ball (0 : ℂ) ρ) :=
    fun z hz =>
      have hz_norm_lt : ‖z‖ < ρ :=
        mem_ball_zero_iff.mp hz
      have hz_norm_le : ‖z‖ ≤ ρ :=
        le_of_lt hz_norm_lt
      (hL z hz_norm_le).differentiableAt.differentiableWithinAt
  have hcont :
      ContinuousOn L (Metric.closedBall (0 : ℂ) ρ) :=
    fun z hz =>
      have hz_norm_le : ‖z‖ ≤ ρ :=
        mem_closedBall_zero_iff.mp hz
      (hL z hz_norm_le).continuousAt.continuousWithinAt
  exact DiffContOnCl.mk_ball hdiff hcont

/-- Cauchy's integral formula at the center of the Jensen disk, in the
`circleIntegral` normalization. -/
theorem entireFunction_analyticLog_cauchy_center_circleIntegral
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hL :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ L z) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C((0 : ℂ), ρ), (z - 0)⁻¹ • L z) =
      L 0 := by
  have hρ_pos : 0 < ρ :=
    lt_of_lt_of_le zero_lt_one hρ
  have hdiff : DiffContOnCl ℂ L (Metric.ball (0 : ℂ) ρ) :=
    entireFunction_analyticOnClosedDisk_diffContOnCl L hL
  have hzero_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ :=
    Metric.mem_ball_self hρ_pos
  exact hdiff.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hzero_mem

/-- Parametrization of the Cauchy kernel on Jensen's boundary circle.

This is the exact boundary cancellation used to pass from Cauchy's
`circleIntegral` normalization to the ordinary angular integral.  The proof is
the direct expansion of `circleIntegral`, `circleMap 0 ρ θ`, and
`deriv_circleMap`, followed by cancellation of the nonzero boundary point. -/
theorem entireFunction_cauchyKernel_circleMap_boundaryCancellation
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (θ : ℝ) :
    deriv (circleMap (0 : ℂ) ρ) θ •
        (((circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ) =
      Complex.I := by
  have hρ_pos : 0 < ρ :=
    lt_of_lt_of_le zero_lt_one hρ
  have hρ_ne : ρ ≠ 0 :=
    hρ_pos.ne'
  have hcircle_ne :
      circleMap (0 : ℂ) ρ θ ≠ 0 :=
    circleMap_ne_center hρ_ne
  have hsub :
      circleMap (0 : ℂ) ρ θ - 0 =
        circleMap (0 : ℂ) ρ θ :=
    circleMap_sub_center (0 : ℂ) ρ θ
  have hderiv :
      deriv (circleMap (0 : ℂ) ρ) θ =
        circleMap (0 : ℂ) ρ θ * Complex.I :=
    deriv_circleMap (0 : ℂ) ρ θ
  have hcancel :
      (circleMap (0 : ℂ) ρ θ * Complex.I) *
          (circleMap (0 : ℂ) ρ θ)⁻¹ =
        Complex.I := by
    calc
      (circleMap (0 : ℂ) ρ θ * Complex.I) *
          (circleMap (0 : ℂ) ρ θ)⁻¹ =
          (Complex.I * circleMap (0 : ℂ) ρ θ) *
            (circleMap (0 : ℂ) ρ θ)⁻¹ := by
        exact congrArg
          (fun z : ℂ => z * (circleMap (0 : ℂ) ρ θ)⁻¹)
          (mul_comm (circleMap (0 : ℂ) ρ θ) Complex.I)
      _ = Complex.I := by
        exact mul_inv_cancel_right₀ hcircle_ne Complex.I
  calc
    deriv (circleMap (0 : ℂ) ρ) θ •
        (((circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ) =
        deriv (circleMap (0 : ℂ) ρ) θ *
          (((circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ) := by
      rfl
    _ =
        (circleMap (0 : ℂ) ρ θ * Complex.I) *
          (((circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ) := by
      exact congrArg
        (fun z : ℂ => z * (((circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ))
        hderiv
    _ =
        (circleMap (0 : ℂ) ρ θ * Complex.I) *
          (circleMap (0 : ℂ) ρ θ)⁻¹ := by
      exact congrArg
        (fun z : ℂ => (circleMap (0 : ℂ) ρ θ * Complex.I) * z)
        (congrArg Inv.inv hsub)
    _ = Complex.I :=
      hcancel

/-- The zero-centered circle parametrization is the Jensen exponential boundary
sample. -/
theorem entireFunction_circleMap_zero_eq_boundarySample
    (ρ : ℝ)
    (θ : ℝ) :
    circleMap (0 : ℂ) ρ θ =
      (ρ : ℂ) * Complex.exp (θ * Complex.I) := by
  exact circleMap_zero ρ θ

/-- The circle-integral Cauchy-kernel integrand cancels to `I` times the
boundary value after passing to the Jensen exponential parametrization. -/
theorem entireFunction_cauchyCircleIntegral_integrand_eq_I_smul_boundarySample
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (θ : ℝ) :
    deriv (circleMap (0 : ℂ) ρ) θ •
        (((circleMap (0 : ℂ) ρ θ - 0)⁻¹) •
          L (circleMap (0 : ℂ) ρ θ)) =
      Complex.I • L ((ρ : ℂ) * Complex.exp (θ * Complex.I)) := by
  have hcancel :
      deriv (circleMap (0 : ℂ) ρ) θ •
          (((circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ) =
        Complex.I :=
    entireFunction_cauchyKernel_circleMap_boundaryCancellation hρ θ
  have hsample :
      circleMap (0 : ℂ) ρ θ =
        (ρ : ℂ) * Complex.exp (θ * Complex.I) :=
    entireFunction_circleMap_zero_eq_boundarySample ρ θ
  calc
    deriv (circleMap (0 : ℂ) ρ) θ •
        (((circleMap (0 : ℂ) ρ θ - 0)⁻¹) •
          L (circleMap (0 : ℂ) ρ θ)) =
        (deriv (circleMap (0 : ℂ) ρ) θ •
          (((circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ)) •
          L (circleMap (0 : ℂ) ρ θ) := by
      exact (smul_smul
        (deriv (circleMap (0 : ℂ) ρ) θ)
        (((circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ)
        (L (circleMap (0 : ℂ) ρ θ)))
    _ = Complex.I • L (circleMap (0 : ℂ) ρ θ) := by
      exact congrArg
        (fun z : ℂ => z • L (circleMap (0 : ℂ) ρ θ))
        hcancel
    _ = Complex.I • L ((ρ : ℂ) * Complex.exp (θ * Complex.I)) := by
      exact congrArg (fun z : ℂ => Complex.I • L z) hsample

/-- Circle-integral transport for the holomorphic mean value formula on the
Jensen boundary.

This lemma isolates the only parametrization work in the complex mean-value
step: after the Cauchy-kernel cancellation, the circle integral is exactly
`Complex.I` times the angular boundary integral. -/
theorem entireFunction_cauchyCircleIntegral_eq_I_smul_boundaryIntervalIntegral
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ) :
    (∮ z in C((0 : ℂ), ρ), (z - 0)⁻¹ • L z) =
      Complex.I •
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          L ((ρ : ℂ) * Complex.exp (θ * Complex.I))) := by
  -- Expand `circleIntegral`, identify `circleMap 0 ρ θ` with
  -- `(ρ : ℂ) * exp (θ * I)`, and use
  -- `entireFunction_cauchyKernel_circleMap_boundaryCancellation` pointwise.
  calc
    (∮ z in C((0 : ℂ), ρ), (z - 0)⁻¹ • L z) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          deriv (circleMap (0 : ℂ) ρ) θ •
            (((circleMap (0 : ℂ) ρ θ - 0)⁻¹) •
              L (circleMap (0 : ℂ) ρ θ)) := by
      rfl
    _ =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.I • L ((ρ : ℂ) * Complex.exp (θ * Complex.I)) := by
      exact intervalIntegral.integral_congr fun θ _hθ =>
        entireFunction_cauchyCircleIntegral_integrand_eq_I_smul_boundarySample
          L hρ θ
    _ =
        Complex.I •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I))) := by
      exact intervalIntegral.integral_smul
        Complex.I
        (fun θ : ℝ => L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))

/-- Scalar normalization after the Cauchy boundary parametrization. -/
theorem entireFunction_two_pi_I_inv_smul_I_smul_eq_two_pi_inv_smul
    (w : ℂ) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • (Complex.I • w)) =
      ((2 * Real.pi : ℂ)⁻¹ • w) := by
  have hcoeff :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I) =
        ((2 * Real.pi : ℂ)⁻¹) := by
    calc
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I) =
          ((Complex.I⁻¹ * (2 * Real.pi : ℂ)⁻¹) * Complex.I) := by
        exact congrArg (fun z : ℂ => z * Complex.I)
          (mul_inv_rev (2 * Real.pi : ℂ) Complex.I)
      _ =
          (((2 * Real.pi : ℂ)⁻¹ * Complex.I⁻¹) * Complex.I) := by
        exact congrArg
          (fun z : ℂ => z * Complex.I)
          (mul_comm Complex.I⁻¹ ((2 * Real.pi : ℂ)⁻¹))
      _ = ((2 * Real.pi : ℂ)⁻¹ * (Complex.I⁻¹ * Complex.I)) := by
        exact mul_assoc ((2 * Real.pi : ℂ)⁻¹) Complex.I⁻¹ Complex.I
      _ = ((2 * Real.pi : ℂ)⁻¹ * 1) := by
        exact congrArg (fun z : ℂ => ((2 * Real.pi : ℂ)⁻¹ * z))
          (inv_mul_cancel₀ Complex.I_ne_zero)
      _ = ((2 * Real.pi : ℂ)⁻¹) := by
        exact mul_one ((2 * Real.pi : ℂ)⁻¹)
  calc
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • (Complex.I • w)) =
        (((2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I) • w) := by
      exact smul_smul (2 * Real.pi * Complex.I : ℂ)⁻¹ Complex.I w
    _ = ((2 * Real.pi : ℂ)⁻¹ • w) := by
      exact congrArg (fun z : ℂ => z • w) hcoeff

/-- The Cauchy center formula after circle parametrization and scalar
normalization. -/
theorem entireFunction_analyticLog_complex_holomorphicMeanValue_circle_from_cauchyKernel
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hL :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ L z) :
    ((2 * Real.pi : ℂ)⁻¹ •
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) =
      L 0 := by
  have hcauchy :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ z in C((0 : ℂ), ρ), (z - 0)⁻¹ • L z) =
        L 0 :=
    entireFunction_analyticLog_cauchy_center_circleIntegral L hρ hL
  have hcircle :
      (∮ z in C((0 : ℂ), ρ), (z - 0)⁻¹ • L z) =
        Complex.I •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I))) :=
    entireFunction_cauchyCircleIntegral_eq_I_smul_boundaryIntervalIntegral
      L hρ
  have hnormalized :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (Complex.I •
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              L ((ρ : ℂ) * Complex.exp (θ * Complex.I))))) =
        ((2 * Real.pi : ℂ)⁻¹ •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) :=
    entireFunction_two_pi_I_inv_smul_I_smul_eq_two_pi_inv_smul
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
  exact Eq.trans hnormalized.symm (Eq.trans (congrArg (fun w : ℂ =>
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • w)) hcircle.symm) hcauchy)

/-- The Cauchy center formula rewritten as the normalized complex boundary mean
of the holomorphic function. -/
theorem entireFunction_analyticLog_complex_holomorphicMeanValue_circle
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hL :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ L z) :
    ((2 * Real.pi : ℂ)⁻¹ •
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) =
      L 0 := by
  exact
    entireFunction_analyticLog_complex_holomorphicMeanValue_circle_from_cauchyKernel
      L hρ hL

/-- Real-part transport across an interval integral, in the mathematically
correct form with interval integrability of the complex integrand. -/
theorem entireFunction_boundaryIntervalIntegral_re_of_intervalIntegrable
    (L : ℂ → ℂ)
    (ρ : ℝ)
    (hL_int :
      IntervalIntegrable
        (fun θ : ℝ => L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi)) :
    ((∫ θ in (0 : ℝ)..(2 * Real.pi),
        L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re := by
  have hmap :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.reCLM
            (L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) =
        Complex.reCLM
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I))) := by
    exact ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hL_int
  exact hmap.symm

/-- The real part of the Jensen angular interval integral is the interval
integral of the real part, under the necessary integrability hypothesis.

This is the canonical `intervalIntegral`/`Complex.re` transport needed after
the complex mean-value formula. -/
theorem entireFunction_boundaryIntervalIntegral_re
    (L : ℂ → ℂ)
    (ρ : ℝ)
    (hL_int :
      IntervalIntegrable
        (fun θ : ℝ => L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi)) :
    ((∫ θ in (0 : ℝ)..(2 * Real.pi),
        L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re := by
  exact entireFunction_boundaryIntervalIntegral_re_of_intervalIntegrable L ρ hL_int

/-- Analyticity on Jensen's closed disk makes the angular boundary
parametrization interval-integrable. -/
theorem entireFunction_boundaryIntervalIntegrable_of_analyticOnClosedDisk
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hL :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ L z) :
    IntervalIntegrable
      (fun θ : ℝ => L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  -- The boundary path is continuous and lies in the closed disk by
  -- `circleMap_mem_closedBall`; analytic functions are continuous on that
  -- image, hence the compact interval parametrization is interval-integrable.
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans zero_le_one hρ
  have hsample_cont :
      Continuous (fun θ : ℝ =>
        (ρ : ℂ) * Complex.exp (θ * Complex.I)) := by
    have hcircle_cont :
        Continuous (circleMap (0 : ℂ) ρ) :=
      continuous_circleMap (0 : ℂ) ρ
    have hsample_eq :
        (fun θ : ℝ => (ρ : ℂ) * Complex.exp (θ * Complex.I)) =
          circleMap (0 : ℂ) ρ := by
      exact
        funext
          (fun θ =>
            (entireFunction_circleMap_zero_eq_boundarySample ρ θ).symm)
    exact Eq.subst
      (motive := fun f : ℝ → ℂ => Continuous f)
      hsample_eq.symm
      hcircle_cont
  have hboundary_norm :
      ∀ θ : ℝ, ‖(ρ : ℂ) * Complex.exp (θ * Complex.I)‖ ≤ ρ := by
    intro θ
    have hcircle :
        circleMap (0 : ℂ) ρ θ =
          (ρ : ℂ) * Complex.exp (θ * Complex.I) :=
      entireFunction_circleMap_zero_eq_boundarySample ρ θ
    have hclosed :
        circleMap (0 : ℂ) ρ θ ∈
          Metric.closedBall (0 : ℂ) ρ :=
      circleMap_mem_closedBall (0 : ℂ) hρ_nonneg θ
    have hnorm_circle : ‖circleMap (0 : ℂ) ρ θ‖ ≤ ρ :=
      mem_closedBall_zero_iff.mp hclosed
    exact Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ ρ)
      hcircle
      hnorm_circle
  have hcomp :
      Continuous (fun θ : ℝ =>
        L ((ρ : ℂ) * Complex.exp (θ * Complex.I))) := by
    exact continuous_iff_continuousAt.mpr
      (fun θ =>
        have hL_at :
            ContinuousAt L ((ρ : ℂ) * Complex.exp (θ * Complex.I)) :=
          (hL
            ((ρ : ℂ) * Complex.exp (θ * Complex.I))
            (hboundary_norm θ)).continuousAt
        ContinuousAt.comp hL_at hsample_cont.continuousAt)
  exact hcomp.intervalIntegrable (0 : ℝ) (2 * Real.pi)

/-- Real scalar multiplication in `ℂ`, viewed by real parts. -/
theorem entireFunction_complexMean_realScalar_re_mul
    (c : ℝ)
    (w : ℂ) :
    (((c : ℂ) * w).re) = c * w.re := by
  exact Complex.re_ofReal_mul c w

/-- Real part of a complex mean with a real scalar coefficient. -/
theorem entireFunction_complexMean_realScalar_re
    (c : ℝ)
    (w : ℂ) :
    (((c : ℂ) • w).re) = c * w.re := by
  have hsmul : ((c : ℂ) • w) = (c : ℂ) * w :=
    rfl
  exact Eq.trans
    (congrArg Complex.re hsmul)
    (entireFunction_complexMean_realScalar_re_mul c w)

/-- The complex inverse of the real Jensen normalizing scalar is the coercion
of the real inverse. -/
theorem entireFunction_complex_twoPi_inv_eq_real_twoPi_inv :
    ((2 * Real.pi : ℂ)⁻¹) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by
  have htwo_pi :
      (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
    exact (Complex.ofReal_mul 2 Real.pi).symm
  exact Eq.trans
    (congrArg Inv.inv htwo_pi)
    (Complex.ofReal_inv (2 * Real.pi)).symm

/-- Real-part transport for the normalized complex boundary mean, isolated from
the analytic Cauchy input. -/
theorem entireFunction_complexMeanValue_re_part_transport_from_integral_re
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hL_int :
      IntervalIntegrable
        (fun θ : ℝ => L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi))
    (hcomplex :
      ((2 * Real.pi : ℂ)⁻¹ •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) =
        L 0) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) =
      (L 0).re := by
  have hreal_scalar :
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))).re =
        (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re :=
    entireFunction_complexMean_realScalar_re
      ((2 * Real.pi)⁻¹)
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
  have hintegral_re :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re :=
    entireFunction_boundaryIntervalIntegral_re L ρ hL_int
  have hleft :
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))).re =
        (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) :=
    Eq.trans hreal_scalar
      (congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) hintegral_re)
  have hcomplex_re :
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))).re =
        (L 0).re :=
    congrArg Complex.re
      (Eq.trans
        (congrArg
          (fun c : ℂ =>
            c •
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                L ((ρ : ℂ) * Complex.exp (θ * Complex.I))))
          entireFunction_complex_twoPi_inv_eq_real_twoPi_inv.symm)
        hcomplex)
  exact Eq.trans hleft.symm hcomplex_re

/-- Real-part transport for the normalized complex boundary mean. -/
theorem entireFunction_complexMeanValue_re_part_transport
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hL_int :
      IntervalIntegrable
        (fun θ : ℝ => L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi))
    (hcomplex :
      ((2 * Real.pi : ℂ)⁻¹ •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) =
        L 0) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) =
      (L 0).re := by
  exact
    entireFunction_complexMeanValue_re_part_transport_from_integral_re
      L hL_int hcomplex

/-- Cauchy mean-value theorem for the real part of a holomorphic function on a
Jensen circle.

This is the analytic mean-value owner root in the exact interval-integral
normalization used in this file.  The intended proof applies Cauchy's integral
formula to `L` at `0` on `C(0, ρ)`, rewrites the circle integral through
`circleMap 0 ρ θ = (ρ : ℂ) * Complex.exp (θ * Complex.I)`, cancels the
nonzero boundary factor, and then applies `MeasureTheory.integral_re`.
Cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_analyticLog_re_holomorphicMeanValue_circle_from_cauchyIntegral
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hL :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ L z) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) =
      (L 0).re := by
  have hcomplex :
      ((2 * Real.pi : ℂ)⁻¹ •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) =
        L 0 :=
    entireFunction_analyticLog_complex_holomorphicMeanValue_circle L hρ hL
  have hL_int :
      IntervalIntegrable
        (fun θ : ℝ => L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) :=
    entireFunction_boundaryIntervalIntegrable_of_analyticOnClosedDisk L hρ hL
  exact entireFunction_complexMeanValue_re_part_transport L hL_int hcomplex

/-- Mean-value theorem for the real part of a holomorphic function on a disk,
with Jensen's boundary parametrization and normalization. -/
theorem entireFunction_analyticLog_re_holomorphicMeanValue_circle
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hL :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ L z) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) =
      (L 0).re := by
  exact
    entireFunction_analyticLog_re_holomorphicMeanValue_circle_from_cauchyIntegral
      L hρ hL

/-- Boundary factorization for a single nonzero Jensen zero inside the circle. -/
theorem entireFunction_singleZeroFactor_boundary_point_ne_zero
    {ρ : ℝ}
    (hρ_pos : 0 < ρ)
    (θ : ℝ) :
    ((ρ : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 := by
  have hρ_ne : (ρ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hρ_pos.ne'
  have hexp_ne : Complex.exp (θ * Complex.I) ≠ 0 :=
    Complex.exp_ne_zero (θ * Complex.I)
  exact mul_ne_zero hρ_ne hexp_ne

/-- The inner single-zero boundary factor is nonzero when the zero is strictly
inside the Jensen circle. -/
theorem entireFunction_singleZeroFactor_inner_ne_zero
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ)
    (θ : ℝ) :
    1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))) ≠ 0 := by
  have hρ_pos : 0 < ρ :=
    lt_of_le_of_lt (norm_nonneg a) haρ
  have hz_ne :
      ((ρ : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 :=
    entireFunction_singleZeroFactor_boundary_point_ne_zero hρ_pos θ
  intro hzero
  have hdiv_eq_one : a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)) = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnorm_div_eq_one :
      ‖a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ = 1 :=
    Eq.trans (congrArg norm hdiv_eq_one) norm_one
  have hnorm_exp :
      ‖Complex.exp (θ * Complex.I)‖ = 1 := by
    calc
      ‖Complex.exp (θ * Complex.I)‖ =
          Complex.abs (Complex.exp (θ * Complex.I)) := by
        exact Complex.norm_eq_abs (Complex.exp (θ * Complex.I))
      _ = 1 := by
        exact Complex.abs_exp_ofReal_mul_I θ
  have hnorm_z :
      ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ = ρ := by
    calc
      ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ =
          ‖(ρ : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := by
        exact norm_mul (ρ : ℂ) (Complex.exp (θ * Complex.I))
      _ = |ρ| * 1 := by
        exact congrArg₂
          (fun x y : ℝ => x * y)
          (Complex.norm_real ρ)
          hnorm_exp
      _ = ρ := by
        exact Eq.trans (mul_one |ρ|) (abs_of_pos hρ_pos)
  have hnorm_a_div :
      ‖a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ = ‖a‖ / ρ := by
    calc
      ‖a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ =
          ‖a‖ / ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ := by
        exact norm_div a ((ρ : ℂ) * Complex.exp (θ * Complex.I))
      _ = ‖a‖ / ρ := by
        exact congrArg (fun x : ℝ => ‖a‖ / x) hnorm_z
  have hratio_lt_one : ‖a‖ / ρ < 1 :=
    (div_lt_one hρ_pos).mpr haρ
  have hratio_eq_one : ‖a‖ / ρ = 1 :=
    Eq.trans hnorm_a_div.symm hnorm_div_eq_one
  exact (ne_of_lt hratio_lt_one) hratio_eq_one

/-- Boundary factorization for a single nonzero Jensen zero on a nonzero
circle. -/
theorem entireFunction_singleZeroFactor_boundary_factorization
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (hρ_pos : 0 < ρ)
    (θ : ℝ) :
    1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) =
      -(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) *
        (1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) := by
  let z : ℂ := (ρ : ℂ) * Complex.exp (θ * Complex.I)
  have hz0 : z ≠ 0 :=
    entireFunction_singleZeroFactor_boundary_point_ne_zero hρ_pos θ
  have ha_inv : a * a⁻¹ = 1 :=
    mul_inv_cancel₀ ha0
  have hz_inv : z * z⁻¹ = 1 :=
    mul_inv_cancel₀ hz0
  have hinner :
      (z * a⁻¹) * (a * z⁻¹) = 1 := by
    calc
      (z * a⁻¹) * (a * z⁻¹) = ((z * a⁻¹) * a) * z⁻¹ := by
        exact (mul_assoc (z * a⁻¹) a z⁻¹).symm
      _ = (z * (a⁻¹ * a)) * z⁻¹ := by
        exact congrArg (fun x : ℂ => x * z⁻¹) (mul_assoc z a⁻¹ a)
      _ = z * ((a⁻¹ * a) * z⁻¹) := by
        exact mul_assoc z (a⁻¹ * a) z⁻¹
      _ = z * (1 * z⁻¹) := by
        exact congrArg (fun x : ℂ => z * (x * z⁻¹)) (inv_mul_cancel₀ ha0)
      _ = z * z⁻¹ := by
        exact congrArg (fun x : ℂ => z * x) (one_mul z⁻¹)
      _ = 1 := hz_inv
  calc
    1 - (z / a) = 1 - (z * a⁻¹) := by
      exact congrArg (fun x : ℂ => 1 - x) (div_eq_mul_inv z a)
    _ = -(z * a⁻¹) * (1 - a * z⁻¹) := by
      calc
        1 - (z * a⁻¹) = 1 - (z * a⁻¹) * 1 := by
          exact congrArg (fun x : ℂ => 1 - x) (mul_one (z * a⁻¹)).symm
        _ =
            (z * a⁻¹) * (a * z⁻¹) - (z * a⁻¹) * 1 := by
          exact congrArg (fun x : ℂ => x - (z * a⁻¹) * 1) hinner.symm
        _ = (z * a⁻¹) * ((a * z⁻¹) - 1) := by
          exact (mul_sub (z * a⁻¹) (a * z⁻¹) 1).symm
        _ = -(z * a⁻¹) * (1 - a * z⁻¹) := by
          let u : ℂ := z * a⁻¹
          let v : ℂ := 1 - a * z⁻¹
          have hsub : (a * z⁻¹) - 1 = -v :=
            (neg_sub 1 (a * z⁻¹)).symm
          have hmul_neg : u * (-v) = -(u * v) :=
            mul_neg u v
          have hneg_mul : -(u * v) = (-u) * v :=
            (neg_mul u v).symm
          exact Eq.trans
            (congrArg (fun y : ℂ => u * y) hsub)
            (Eq.trans hmul_neg hneg_mul)
    _ = -(z / a) * (1 - (a / z)) := by
      exact congrArg₂ (fun x y : ℂ => -x * (1 - y))
        (div_eq_mul_inv z a).symm
        (div_eq_mul_inv a z).symm

/-- The boundary factor has norm `ρ / ‖a‖`. -/
theorem entireFunction_singleZeroFactor_outer_norm
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (hρ_pos : 0 < ρ)
    (θ : ℝ) :
    ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ =
      ρ / ‖a‖ := by
  have hnorm_exp :
      ‖Complex.exp (θ * Complex.I)‖ = 1 := by
    calc
      ‖Complex.exp (θ * Complex.I)‖ =
          Complex.abs (Complex.exp (θ * Complex.I)) := by
        exact Complex.norm_eq_abs (Complex.exp (θ * Complex.I))
      _ = 1 := by
        exact Complex.abs_exp_ofReal_mul_I θ
  have hnorm_rho :
      ‖(ρ : ℂ)‖ = ρ := by
    calc
      ‖(ρ : ℂ)‖ = |ρ| := by
        exact Complex.norm_real ρ
      _ = ρ :=
        abs_of_pos hρ_pos
  calc
    ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ =
        ‖(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ := by
      exact norm_neg (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)
    _ = ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ / ‖a‖ := by
      exact norm_div ((ρ : ℂ) * Complex.exp (θ * Complex.I)) a
    _ = (‖(ρ : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖) / ‖a‖ := by
      exact congrArg (fun x : ℝ => x / ‖a‖)
        (norm_mul (ρ : ℂ) (Complex.exp (θ * Complex.I)))
    _ = (ρ * 1) / ‖a‖ := by
      exact congrArg (fun x : ℝ => x / ‖a‖)
        (congrArg₂ (fun x y : ℝ => x * y) hnorm_rho hnorm_exp)
    _ = ρ / ‖a‖ := by
      exact congrArg (fun x : ℝ => x / ‖a‖) (mul_one ρ)

/-- Splitting the logarithm of one boundary factor into the constant outer
radial term and the inner disk logarithmic term. -/
theorem entireFunction_singleZeroFactor_boundary_log_split
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (haρ : ‖a‖ < ρ)
    (hρ_pos : 0 < ρ)
    (θ : ℝ) :
    Real.log
        ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ =
      Real.log (ρ / ‖a‖) +
        Real.log ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖ := by
  have hfactor :=
    entireFunction_singleZeroFactor_boundary_factorization ha0 hρ_pos θ
  have houter_norm :=
    entireFunction_singleZeroFactor_outer_norm ha0 hρ_pos θ
  have hinner_ne :
      1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))) ≠ 0 :=
    entireFunction_singleZeroFactor_inner_ne_zero haρ θ
  have houter_ne :
      -(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) ≠ 0 := by
    have hz_ne :
        ((ρ : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 :=
      entireFunction_singleZeroFactor_boundary_point_ne_zero hρ_pos θ
    exact neg_ne_zero.mpr (div_ne_zero hz_ne ha0)
  have houter_norm_ne :
      ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr houter_ne
  have hinner_norm_ne :
      ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hinner_ne
  calc
    Real.log
        ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ =
      Real.log
        ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) *
          (1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))))‖ := by
      exact congrArg (fun x : ℂ => Real.log ‖x‖) hfactor
    _ =
      Real.log
        (‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ *
          ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖) := by
      exact congrArg Real.log
        (norm_mul
          (-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a))
          (1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))))
    _ =
      Real.log ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ +
        Real.log ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖ := by
      exact Real.log_mul houter_norm_ne hinner_norm_ne
    _ =
      Real.log (ρ / ‖a‖) +
        Real.log ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖ := by
      exact congrArg
        (fun x : ℝ =>
          Real.log x +
            Real.log ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖)
        houter_norm

/-- The affine disk factor `z ↦ 1 - c z` is entire. -/
theorem complex_one_sub_mul_id_analyticAt
    (c z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => 1 - c * w) z := by
  exact analyticAt_const.sub (analyticAt_const.mul analyticAt_id)

/-- The affine disk factor `1 - c z` has no zeros on the closed unit disk when
`c` is contracting. -/
theorem complex_one_sub_mul_id_ne_zero_on_closed_unitDisk
    {c z : ℂ}
    (hc : ‖c‖ < 1)
    (hz : ‖z‖ ≤ 1) :
    1 - c * z ≠ 0 := by
  intro hzero
  have hmul_eq_one : c * z = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnorm_mul_eq_one : ‖c * z‖ = 1 :=
    Eq.trans (congrArg norm hmul_eq_one) norm_one
  have hnorm_mul_le : ‖c * z‖ ≤ ‖c‖ := by
    have hmul_norm : ‖c * z‖ = ‖c‖ * ‖z‖ :=
      norm_mul c z
    have hc_nonneg : 0 ≤ ‖c‖ :=
      norm_nonneg c
    have hmul_le : ‖c‖ * ‖z‖ ≤ ‖c‖ * 1 :=
      mul_le_mul_of_nonneg_left hz hc_nonneg
    have hmul_one : ‖c‖ * 1 = ‖c‖ :=
      mul_one ‖c‖
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ ‖c‖)
      hmul_norm.symm
      (le_trans hmul_le (le_of_eq hmul_one))
  have hone_le_c : 1 ≤ ‖c‖ :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖c‖)
      hnorm_mul_eq_one
      hnorm_mul_le
  exact (not_le_of_gt hc) hone_le_c

/-- Contractivity is preserved by complex conjugation. -/
theorem complex_norm_conj_lt_one
    {q : ℂ}
    (hq : ‖q‖ < 1) :
    ‖(starRingEnd ℂ) q‖ < 1 := by
  exact Eq.subst
    (motive := fun x : ℝ => x < 1)
    (RCLike.norm_conj q).symm
    hq

/-- The negative-orientation boundary factor has the same norm as the
positive-orientation factor with conjugated coefficient. -/
theorem complex_one_sub_contracting_negativeMode_norm_eq_conj_positiveMode_norm
    (q : ℂ)
    (θ : ℝ) :
    ‖1 - q * Complex.exp (-(θ * Complex.I))‖ =
      ‖1 - (starRingEnd ℂ) q * Complex.exp (θ * Complex.I)‖ := by
  have hconj_exp :
      (starRingEnd ℂ) (Complex.exp (-(θ * Complex.I))) =
        Complex.exp (θ * Complex.I) := by
    calc
      (starRingEnd ℂ) (Complex.exp (-(θ * Complex.I))) =
          Complex.exp ((starRingEnd ℂ) (-(θ * Complex.I))) := by
        exact (Complex.exp_conj (-(θ * Complex.I))).symm
      _ = Complex.exp (θ * Complex.I) := by
        have harg :
            (starRingEnd ℂ) (-(θ * Complex.I)) = θ * Complex.I := by
          calc
            (starRingEnd ℂ) (-(θ * Complex.I)) =
                -((starRingEnd ℂ) (θ * Complex.I)) := by
              exact map_neg (starRingEnd ℂ) (θ * Complex.I)
            _ = -(((starRingEnd ℂ) (θ : ℂ)) *
                ((starRingEnd ℂ) Complex.I)) := by
              exact congrArg Neg.neg
                (map_mul (starRingEnd ℂ) (θ : ℂ) Complex.I)
            _ = -((θ : ℂ) * (-Complex.I)) := by
              have htheta :
                  (starRingEnd ℂ) (θ : ℂ) = (θ : ℂ) :=
                Complex.conj_ofReal θ
              have hI :
                  (starRingEnd ℂ) Complex.I = -Complex.I :=
                Complex.conj_I
              exact Eq.trans
                (congrArg
                  (fun z : ℂ =>
                    -(z * ((starRingEnd ℂ) Complex.I)))
                  htheta)
                (congrArg (fun z : ℂ => -((θ : ℂ) * z)) hI)
            _ = (θ : ℂ) * Complex.I := by
              exact Eq.trans
                (neg_mul_eq_mul_neg (θ : ℂ) (-Complex.I))
                (congrArg
                  (fun z : ℂ => (θ : ℂ) * z)
                  (neg_neg Complex.I))
        exact congrArg Complex.exp harg
  have hconj_factor :
      (starRingEnd ℂ) (1 - q * Complex.exp (-(θ * Complex.I))) =
        1 - (starRingEnd ℂ) q * Complex.exp (θ * Complex.I) := by
    calc
      (starRingEnd ℂ) (1 - q * Complex.exp (-(θ * Complex.I))) =
          (starRingEnd ℂ) 1 -
            (starRingEnd ℂ) (q * Complex.exp (-(θ * Complex.I))) := by
        exact map_sub (starRingEnd ℂ) 1
          (q * Complex.exp (-(θ * Complex.I)))
      _ = 1 -
            (starRingEnd ℂ) (q * Complex.exp (-(θ * Complex.I))) := by
        exact congrArg
          (fun x : ℂ =>
            x - (starRingEnd ℂ) (q * Complex.exp (-(θ * Complex.I))))
          (map_one (starRingEnd ℂ))
      _ =
          1 - (starRingEnd ℂ) q *
            (starRingEnd ℂ) (Complex.exp (-(θ * Complex.I))) := by
        exact congrArg (fun x : ℂ => 1 - x)
          (map_mul (starRingEnd ℂ) q (Complex.exp (-(θ * Complex.I))))
      _ = 1 - (starRingEnd ℂ) q * Complex.exp (θ * Complex.I) := by
        exact congrArg (fun x : ℂ => 1 - (starRingEnd ℂ) q * x) hconj_exp
  calc
    ‖1 - q * Complex.exp (-(θ * Complex.I))‖ =
        ‖(starRingEnd ℂ)
          (1 - q * Complex.exp (-(θ * Complex.I)))‖ := by
      exact (RCLike.norm_conj
        (1 - q * Complex.exp (-(θ * Complex.I)))).symm
    _ = ‖1 - (starRingEnd ℂ) q * Complex.exp (θ * Complex.I)‖ := by
      exact congrArg norm hconj_factor

/-- The center value of the affine disk factor has zero logarithmic norm. -/
theorem complex_one_sub_mul_id_center_log_norm_eq_zero
    (c : ℂ) :
    Real.log ‖(fun z : ℂ => 1 - c * z) 0‖ = 0 := by
  have hmul_zero : c * (0 : ℂ) = 0 :=
    mul_zero c
  have hvalue : (fun z : ℂ => 1 - c * z) 0 = 1 := by
    calc
      (fun z : ℂ => 1 - c * z) 0 = 1 - c * 0 := rfl
      _ = 1 - 0 := by
        exact congrArg (fun x : ℂ => 1 - x) hmul_zero
      _ = 1 := by
        exact sub_zero 1
  have hnorm : ‖(fun z : ℂ => 1 - c * z) 0‖ = 1 := by
    calc
      ‖(fun z : ℂ => 1 - c * z) 0‖ = ‖(1 : ℂ)‖ := by
        exact congrArg norm hvalue
      _ = 1 :=
        norm_one
  calc
    Real.log ‖(fun z : ℂ => 1 - c * z) 0‖ =
        Real.log 1 := by
      exact congrArg Real.log hnorm
    _ = 0 :=
      Real.log_one

/-- Analytic-log mean theorem for the positive Fourier orientation of the
contracting affine disk factor. -/
theorem complex_log_one_sub_contracting_positive_fourier_mean_zero
    {c : ℂ}
    (hc : ‖c‖ < 1) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - c * Complex.exp (θ * Complex.I)‖) =
        0 := by
    let G : ℂ → ℂ := fun z => 1 - c * z
    have hG : ∀ z : ℂ, AnalyticAt ℂ G z := by
      intro z
      exact complex_one_sub_mul_id_analyticAt c z
    have hzero :
        ∀ z : ℂ, ‖z‖ ≤ (1 : ℝ) → G z ≠ 0 := by
      intro z hz
      exact complex_one_sub_mul_id_ne_zero_on_closed_unitDisk hc hz
    exact
      match entireFunction_zeroFreeOnClosedDisk_exists_analyticLog
          G hG (le_refl (1 : ℝ)) hzero with
      | Exists.intro L hL_data =>
          match hL_data with
          | And.intro hL_an hL_tail =>
              match hL_tail with
              | And.intro hL_log hL_center =>
                  have hmean :
                      (2 * Real.pi)⁻¹ *
                          (∫ θ in (0 : ℝ)..(2 * Real.pi),
                            (L (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))).re) =
                        (L 0).re :=
                    entireFunction_analyticLog_re_holomorphicMeanValue_circle
                      L (le_refl (1 : ℝ)) hL_an
                  have hboundary :
                      (∫ θ in (0 : ℝ)..(2 * Real.pi),
                          Real.log ‖1 - c * Complex.exp (θ * Complex.I)‖) =
                        ∫ θ in (0 : ℝ)..(2 * Real.pi),
                          (L (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))).re := by
                    exact intervalIntegral.integral_congr fun θ _hθ =>
                      by
                        have hpoint :
                            ‖(((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))‖ ≤
                              (1 : ℝ) := by
                          calc
                            ‖(((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))‖ =
                                ‖((1 : ℝ) : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := by
                              exact norm_mul (((1 : ℝ) : ℂ)) (Complex.exp (θ * Complex.I))
                            _ = 1 * ‖Complex.exp (θ * Complex.I)‖ := by
                              exact congrArg
                                (fun x : ℝ => x * ‖Complex.exp (θ * Complex.I)‖)
                                norm_one
                            _ = 1 * 1 := by
                              exact congrArg (fun x : ℝ => 1 * x)
                                (Complex.norm_exp_ofReal_mul_I θ)
                            _ = 1 := by
                              exact one_mul 1
                            _ ≤ (1 : ℝ) := by
                              exact le_refl 1
                        have hlog_re :
                            (L (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))).re =
                              Real.log ‖G (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))‖ :=
                          entireFunction_analyticLogBranch_re_eq_log_norm
                            G L hpoint hL_log
                        have hG_eval :
                            G (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) =
                              1 - c * Complex.exp (θ * Complex.I) := by
                          calc
                            G (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) =
                                1 - c * (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) := rfl
                            _ = 1 - (c * (((1 : ℝ) : ℂ)) * Complex.exp (θ * Complex.I)) := by
                              exact congrArg (fun x : ℂ => 1 - x)
                                (mul_assoc c (((1 : ℝ) : ℂ)) (Complex.exp (θ * Complex.I))).symm
                            _ = 1 - (c * 1 * Complex.exp (θ * Complex.I)) := by
                              exact congrArg
                                (fun x : ℂ => 1 - (c * x * Complex.exp (θ * Complex.I)))
                                rfl
                            _ = 1 - c * Complex.exp (θ * Complex.I) := by
                              exact congrArg (fun x : ℂ => 1 - x)
                                (congrArg (fun x : ℂ => x * Complex.exp (θ * Complex.I))
                                  (mul_one c))
                        calc
                          Real.log ‖1 - c * Complex.exp (θ * Complex.I)‖ =
                              Real.log ‖G (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))‖ := by
                            exact congrArg (fun x : ℂ => Real.log ‖x‖) hG_eval.symm
                          _ = (L (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))).re :=
                            hlog_re.symm
                  have hcenter_zero :
                      (L 0).re = 0 := by
                    exact Eq.trans hL_center (complex_one_sub_mul_id_center_log_norm_eq_zero c)
                  Eq.trans
                    (congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) hboundary)
                    (Eq.trans hmean hcenter_zero)

/-- The Fourier-mode logarithmic mean for a contracting inner disk factor.

For `‖q‖ < 1`, the branch
`log (1 - q * exp (-θ I)) = -∑ n≥1 q^n exp (-n θ I) / n` is uniformly
convergent on the Jensen circle.  Every nonzero Fourier mode has zero angular
mean, hence the real logarithmic norm has zero normalized mean.  Cf.
Titchmarsh, *The Theory of Functions*, §5. -/
theorem complex_log_one_sub_contracting_fourier_mean_zero
    {q : ℂ}
    (hq : ‖q‖ < 1) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - q * Complex.exp (-(θ * Complex.I))‖) =
      0 := by
  have hconj_contract : ‖(starRingEnd ℂ) q‖ < 1 :=
    complex_norm_conj_lt_one hq
  have hpositive :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log ‖1 - (starRingEnd ℂ) q *
              Complex.exp (θ * Complex.I)‖) =
        0 :=
    complex_log_one_sub_contracting_positive_fourier_mean_zero hconj_contract
  have hboundary :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - q * Complex.exp (-(θ * Complex.I))‖) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - (starRingEnd ℂ) q *
            Complex.exp (θ * Complex.I)‖ := by
    exact intervalIntegral.integral_congr fun θ _hθ =>
      congrArg Real.log
        (complex_one_sub_contracting_negativeMode_norm_eq_conj_positiveMode_norm
          q θ)
  exact Eq.trans
    (congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) hboundary)
    hpositive

/-- The normalized zero location `a / ρ` is strictly inside the unit disk. -/
theorem entireFunction_singleZeroFactor_normalized_zero_norm_lt_one
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ) :
    ‖a / (ρ : ℂ)‖ < 1 := by
  have hρ_pos : 0 < ρ :=
    lt_of_le_of_lt (norm_nonneg a) haρ
  have hnorm_div :
      ‖a / (ρ : ℂ)‖ = ‖a‖ / ρ := by
    calc
      ‖a / (ρ : ℂ)‖ = ‖a‖ / ‖(ρ : ℂ)‖ := by
        exact norm_div a (ρ : ℂ)
      _ = ‖a‖ / |ρ| := by
        exact congrArg (fun x : ℝ => ‖a‖ / x) (Complex.norm_real ρ)
      _ = ‖a‖ / ρ := by
        exact congrArg (fun x : ℝ => ‖a‖ / x) (abs_of_pos hρ_pos)
  have hratio_lt : ‖a‖ / ρ < 1 :=
    (div_lt_one hρ_pos).mpr haρ
  exact Eq.subst
    (motive := fun x : ℝ => x < 1)
    hnorm_div.symm
    hratio_lt

/-- Algebraic transport from the Jensen inner factor to the normalized
contracting Fourier factor. -/
theorem entireFunction_singleZeroFactor_inner_eq_contracting_fourier_factor
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ)
    (θ : ℝ) :
    1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))) =
      1 - (a / (ρ : ℂ)) * Complex.exp (-(θ * Complex.I)) := by
  have hρ_pos : 0 < ρ :=
    lt_of_le_of_lt (norm_nonneg a) haρ
  have hdiv :
      a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)) =
        (a / (ρ : ℂ)) * Complex.exp (-(θ * Complex.I)) := by
    calc
      a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)) =
          a * (((ρ : ℂ) * Complex.exp (θ * Complex.I))⁻¹) := by
        exact div_eq_mul_inv a ((ρ : ℂ) * Complex.exp (θ * Complex.I))
      _ = a * ((Complex.exp (θ * Complex.I))⁻¹ * (ρ : ℂ)⁻¹) := by
        exact congrArg (fun x : ℂ => a * x)
          (mul_inv_rev (ρ : ℂ) (Complex.exp (θ * Complex.I)))
      _ = a * ((ρ : ℂ)⁻¹ * (Complex.exp (θ * Complex.I))⁻¹) := by
        exact congrArg (fun x : ℂ => a * x)
          (mul_comm (Complex.exp (θ * Complex.I))⁻¹ (ρ : ℂ)⁻¹)
      _ = (a * (ρ : ℂ)⁻¹) * (Complex.exp (θ * Complex.I))⁻¹ := by
        exact (mul_assoc a (ρ : ℂ)⁻¹ (Complex.exp (θ * Complex.I))⁻¹).symm
      _ = (a / (ρ : ℂ)) * (Complex.exp (θ * Complex.I))⁻¹ := by
        exact congrArg
          (fun x : ℂ => x * (Complex.exp (θ * Complex.I))⁻¹)
          (div_eq_mul_inv a (ρ : ℂ)).symm
      _ = (a / (ρ : ℂ)) * Complex.exp (-(θ * Complex.I)) := by
        exact congrArg (fun x : ℂ => (a / (ρ : ℂ)) * x)
          (Complex.exp_neg (θ * Complex.I)).symm
  exact congrArg (fun x : ℂ => 1 - x) hdiv

/-- The logarithmic power-series mean for an inside-disk linear factor
vanishes on the Jensen boundary. -/
theorem entireFunction_singleZeroFactor_inner_log_mean_zero_from_powerSeries
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log
            ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖) =
      0 := by
  have hq : ‖a / (ρ : ℂ)‖ < 1 :=
    entireFunction_singleZeroFactor_normalized_zero_norm_lt_one haρ
  have hmean :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log ‖1 - (a / (ρ : ℂ)) *
              Complex.exp (-(θ * Complex.I))‖) =
        0 :=
    complex_log_one_sub_contracting_fourier_mean_zero hq
  have hintegrand :
      (fun θ : ℝ =>
        Real.log
          ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖) =
      (fun θ : ℝ =>
        Real.log ‖1 - (a / (ρ : ℂ)) *
          Complex.exp (-(θ * Complex.I))‖) := by
    funext θ
    exact congrArg (fun z : ℂ => Real.log ‖z‖)
      (entireFunction_singleZeroFactor_inner_eq_contracting_fourier_factor
        haρ θ)
  exact Eq.subst
    (motive := fun f : ℝ → ℝ =>
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ) =
        0)
    hintegrand.symm
    hmean

/-- The inner single-zero logarithmic boundary factor is continuous on the
Jensen parameter interval. -/
theorem entireFunction_singleZeroFactor_inner_log_continuous
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ) :
    Continuous
      (fun θ : ℝ =>
        Real.log
          ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖) := by
  have hρ_pos : 0 < ρ :=
    lt_of_le_of_lt (norm_nonneg a) haρ
  have hden_ne :
      ∀ θ : ℝ, ((ρ : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 :=
    fun θ : ℝ =>
      entireFunction_singleZeroFactor_boundary_point_ne_zero hρ_pos θ
  have hinner_ne :
      ∀ θ : ℝ,
        1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))) ≠ 0 :=
    fun θ : ℝ =>
      entireFunction_singleZeroFactor_inner_ne_zero haρ θ
  let q : ℝ → ℂ :=
    fun θ : ℝ => 1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
  have hq_cont : Continuous q :=
    continuous_const.sub
      (continuous_const.div
        ((continuous_const.mul
          (Complex.continuous_exp.comp
            ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const))))
        hden_ne)
  have hnorm_cont : Continuous (fun θ : ℝ => ‖q θ‖) :=
    hq_cont.norm
  exact continuous_iff_continuousAt.mpr
    (fun θ : ℝ =>
      ContinuousAt.comp
        (x := θ)
        (f := fun t : ℝ => ‖q t‖)
        (g := Real.log)
        (Real.continuousAt_log (norm_ne_zero_iff.mpr (hinner_ne θ)))
        hnorm_cont.continuousAt)

/-- The inner single-zero logarithmic boundary factor is interval-integrable on
the Jensen parameter interval. -/
theorem entireFunction_singleZeroFactor_inner_log_intervalIntegrable
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        Real.log
          ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖)
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact
    (entireFunction_singleZeroFactor_inner_log_continuous haρ).intervalIntegrable
      (0 : ℝ)
      (2 * Real.pi)

/-- Normalized constant-plus Jensen interval integral when the normalized
remainder mean vanishes. -/
theorem entireFunction_normalized_const_add_integral_eq_const_of_mean_zero
    (v : ℝ → ℝ)
    (c : ℝ)
    (hv :
      IntervalIntegrable v MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi))
    (hmean :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), v θ) =
        0) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ) =
      c := by
  have hintegral :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ) =
        (2 * Real.pi - 0) • c +
          ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ := by
    have hconst_int :
        IntervalIntegrable
          (fun _θ : ℝ => c)
          MeasureTheory.volume
          (0 : ℝ)
          (2 * Real.pi) :=
      continuous_const.intervalIntegrable (0 : ℝ) (2 * Real.pi)
    have hadd :
        (∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ) =
          (∫ θ in (0 : ℝ)..(2 * Real.pi), c) +
            ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ :=
      intervalIntegral.integral_add hconst_int hv
    have hconst :
        (∫ _θ in (0 : ℝ)..(2 * Real.pi), c) =
          (2 * Real.pi - 0) • c :=
      intervalIntegral.integral_const c
    exact Eq.trans hadd
      (congrArg
        (fun x : ℝ =>
          x + ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ)
        hconst)
  have htwo_ne : 2 * Real.pi ≠ 0 :=
    ne_of_gt Real.two_pi_pos
  have hconst :
      (2 * Real.pi)⁻¹ * ((2 * Real.pi - 0) • c) = c := by
    calc
      (2 * Real.pi)⁻¹ * ((2 * Real.pi - 0) • c) =
          (2 * Real.pi)⁻¹ * ((2 * Real.pi) * c) := by
        exact congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * (x • c)) (sub_zero (2 * Real.pi))
      _ = ((2 * Real.pi)⁻¹ * (2 * Real.pi)) * c := by
        exact (mul_assoc (2 * Real.pi)⁻¹ (2 * Real.pi) c).symm
      _ = 1 * c := by
        exact congrArg (fun x : ℝ => x * c) (inv_mul_cancel₀ htwo_ne)
      _ = c :=
        one_mul c
  calc
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ) =
      (2 * Real.pi)⁻¹ *
        ((2 * Real.pi - 0) • c +
          ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ) := by
      exact congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) hintegral
    _ =
      (2 * Real.pi)⁻¹ * ((2 * Real.pi - 0) • c) +
        (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), v θ) := by
      exact left_distrib
        (2 * Real.pi)⁻¹
        ((2 * Real.pi - 0) • c)
        (∫ θ in (0 : ℝ)..(2 * Real.pi), v θ)
    _ = c + 0 := by
      exact congrArg₂ (fun x y : ℝ => x + y) hconst hmean
    _ = c :=
      add_zero c

/-- Integrating the split single-factor boundary logarithm leaves only the
outer Jensen radial term. -/
theorem entireFunction_singleZeroFactor_boundaryAverage_from_log_split
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (haρ : ‖a‖ < ρ) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖) =
      Real.log (ρ / ‖a‖) := by
  have hρ_pos : 0 < ρ :=
    lt_of_le_of_lt (norm_nonneg a) haρ
  have hsplit :
      ∀ θ : ℝ,
        Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ =
          Real.log (ρ / ‖a‖) +
            Real.log ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖ :=
    fun θ : ℝ =>
      entireFunction_singleZeroFactor_boundary_log_split ha0 haρ hρ_pos θ
  have hinner :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖) =
        0 :=
    entireFunction_singleZeroFactor_inner_log_mean_zero_from_powerSeries haρ
  let u : ℝ → ℝ :=
    fun θ : ℝ =>
      Real.log
        ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖
  let v : ℝ → ℝ :=
    fun θ : ℝ =>
      Real.log
        ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖
  let c : ℝ := Real.log (ρ / ‖a‖)
  have hv :
      IntervalIntegrable v MeasureTheory.volume
        (0 : ℝ) (2 * Real.pi) :=
    entireFunction_singleZeroFactor_inner_log_intervalIntegrable haρ
  have htransport :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ := by
    exact intervalIntegral.integral_congr
      (fun θ _hθ => hsplit θ)
  have hmean_v :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), v θ) =
        0 :=
    hinner
  calc
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ) := by
      exact congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) htransport
    _ = c :=
      entireFunction_normalized_const_add_integral_eq_const_of_mean_zero
        v c hv hmean_v

/-- The single-factor Poisson-Jensen circle integral.

For `0 < ‖a‖ < ρ`, the normalized boundary average of
`θ ↦ log ‖1 - ρ e^{iθ}/a‖` is `log (ρ / ‖a‖)`.  Equivalently, after factoring
`ρ/a`, this is the vanishing mean of
`log ‖1 - (a/ρ)e^{-iθ}‖` for `‖a/ρ‖ < 1`, obtained from the real part of the
convergent logarithmic power series.  Cf. Titchmarsh, *The Theory of
Functions*, §5. -/
theorem entireFunction_singleZeroFactor_boundaryAverage_identity_from_logPowerSeries
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (haρ : ‖a‖ < ρ) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖) =
      Real.log (ρ / ‖a‖) := by
  exact
    entireFunction_singleZeroFactor_boundaryAverage_from_log_split ha0 haρ

/-- The normalized boundary average of one extracted nonzero linear zero factor
is its Jensen radial logarithm. -/
theorem entireFunction_singleZeroFactor_boundaryAverage_identity
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (haρ : ‖a‖ < ρ) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖) =
      Real.log (ρ / ‖a‖) := by
  exact
    entireFunction_singleZeroFactor_boundaryAverage_identity_from_logPowerSeries
      ha0 haρ

/-- The finite product radial-gap sum is the finite sum of normalized
single-factor boundary averages, for any divisor whose members are nonzero and
strictly inside the Jensen circle. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum_eq_singleFactorBoundaryAverageSum_of_mem_zeroInside
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (s : Finset (EntireFunctionZero F))
    (hs0 : ∀ z : EntireFunctionZero F, z ∈ s → (z : ℂ) ≠ 0)
    (hsρ : ∀ z : EntireFunctionZero F, z ∈ s → ‖(z : ℂ)‖ < ρ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ s =
      ∑ z in s,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) := by
  let f : EntireFunctionZero F → ℝ :=
    fun z : EntireFunctionZero F =>
      entireFunctionJensenRadialGapSummand F hF ρ z
  let g : EntireFunctionZero F → ℝ :=
    fun z : EntireFunctionZero F =>
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))
  have hsum_def :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ s =
        ∑ z in s, f z :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum_def_ownerRoot
      F hF ρ s
  have hpoint : ∀ z : EntireFunctionZero F, z ∈ s → f z = g z :=
    fun z hz =>
      have hz0 : (z : ℂ) ≠ 0 := hs0 z hz
      have hzρ : ‖(z : ℂ)‖ < ρ := hsρ z hz
      have hradial :
          f z =
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log (ρ / ‖(z : ℂ)‖) :=
        entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFactor_radialContribution_identity
          F hF ρ z hz0 hzρ
      have havg :
          (2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖) =
            Real.log (ρ / ‖(z : ℂ)‖) :=
        entireFunction_singleZeroFactor_boundaryAverage_identity
          (a := (z : ℂ)) (ρ := ρ) hz0 hzρ
      Eq.trans hradial
        (congrArg
          (fun x : ℝ =>
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) * x)
          havg.symm)
  have hsum_eq : (∑ z in s, f z) = ∑ z in s, g z :=
    Finset.sum_congr rfl hpoint
  exact Eq.trans hsum_def hsum_eq

/-- The support finite product radial-gap sum is exactly the finite sum of
single-factor Poisson-Jensen boundary averages. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProductRadialGapSum_eq_singleFactorBoundaryAverageSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) =
      ∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum_eq_singleFactorBoundaryAverageSum_of_mem_zeroInside
      F hF ρ
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ)
      (fun z hz =>
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_ne_zero
          F hF hF0 ρ z hz)
      (fun z hz =>
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_norm_lt
          F hF hF0 ρ z hz)

end
end LFunctions
end Boundary
