import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.EndpointDerivative.Owner

/-!
# Zero-free primitive and Jensen boundary average

This owner layer was split from `ZeroFreePrimitive.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

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


end
end LFunctions
end Boundary
