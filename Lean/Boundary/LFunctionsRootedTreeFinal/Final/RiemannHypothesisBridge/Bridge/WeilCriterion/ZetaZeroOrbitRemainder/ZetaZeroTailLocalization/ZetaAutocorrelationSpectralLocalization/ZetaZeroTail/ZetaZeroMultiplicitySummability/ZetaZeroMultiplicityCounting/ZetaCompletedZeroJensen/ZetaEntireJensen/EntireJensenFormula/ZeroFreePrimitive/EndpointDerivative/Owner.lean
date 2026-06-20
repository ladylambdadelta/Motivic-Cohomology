import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.RadialPrimitiveCore.Owner

/-!
# Zero-free primitive and Jensen boundary average

This owner layer was split from `ZeroFreePrimitive.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

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


end
end LFunctions
end Boundary
