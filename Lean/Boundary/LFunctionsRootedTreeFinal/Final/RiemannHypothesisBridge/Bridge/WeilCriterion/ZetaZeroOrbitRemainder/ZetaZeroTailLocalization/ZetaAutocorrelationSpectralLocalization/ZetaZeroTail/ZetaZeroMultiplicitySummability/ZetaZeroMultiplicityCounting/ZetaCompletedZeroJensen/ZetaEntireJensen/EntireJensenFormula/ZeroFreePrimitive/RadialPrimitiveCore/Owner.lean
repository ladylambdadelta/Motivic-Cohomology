import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.EndpointTube

/-!
# Zero-free primitive and Jensen boundary average

This owner layer was split from `ZeroFreePrimitive.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

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


end
end LFunctions
end Boundary
