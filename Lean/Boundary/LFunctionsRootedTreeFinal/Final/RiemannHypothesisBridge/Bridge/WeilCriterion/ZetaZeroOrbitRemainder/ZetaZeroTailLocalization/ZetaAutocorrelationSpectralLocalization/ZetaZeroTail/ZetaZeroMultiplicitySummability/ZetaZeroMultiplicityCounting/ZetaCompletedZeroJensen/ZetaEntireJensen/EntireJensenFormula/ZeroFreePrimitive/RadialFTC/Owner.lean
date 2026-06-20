import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.DominatedTube.Owner

/-!
# Zero-free primitive and Jensen boundary average

This owner layer was split from `ZeroFreePrimitive.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

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

end
end LFunctions
end Boundary
