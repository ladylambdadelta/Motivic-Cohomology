import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleEndpointBounds

/-!
# Endpoint-defect layer for right-semicircle staircase approximation

This file owns the finite endpoint-defect algebra and the resulting convergence
of exterior-safe horizontal samples to exact graph-coordinate samples.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- Summation-by-parts form of the safe-coordinate horizontal sample error.

The exterior safe-coordinate increment error is not estimated termwise.  The
endpoint defects telescope, leaving adjacent differences of the graph probe
weighted by the safe endpoint defects. -/
theorem Complex.rightSemicircleStaircaseHorizontalSampleSum_sub_graphHorizontalSampleSum_eq_endpointDefectSum
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
      Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m =
        ∑ k in Finset.range (m + 1),
          (Complex.rightSemicircleGraphProbeGrid f c ρ m k -
            Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)) *
            ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ) := by
  let g : ℕ → ℂ := fun k =>
    Complex.rightSemicircleGraphProbeGrid f c ρ m k
  let r : ℕ → ℝ := fun k =>
    Complex.rightSemicircleGraphRe ρ
      (Complex.rightSemicircleStaircaseY ρ m k)
  let s : ℕ → ℝ := fun k =>
    Complex.rightSemicircleStaircaseSafeRe ρ m k
  let e : ℕ → ℝ := fun k =>
    Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k
  have hprev :
      ∀ k : ℕ,
        Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
            r k =
          if k = 0 then
            0
          else
            e (k - 1) := by
    intro k
    show
      Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
          Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k) =
        if k = 0 then
          0
        else
          Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m (k - 1)
    exact
      Complex.rightSemicircleStaircasePrevSafeRe_sub_graphRe_eq_zero_or_endpointDefect
        ρ m k
  have hcell :
      ∀ k ∈ Finset.range (m + 1),
        g k *
            (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
                Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ)) -
          g k *
            (((r (k + 1) - r k : ℝ) : ℂ)) =
          g k * ((e k : ℝ) : ℂ) -
          g k *
            (((Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
                r k : ℝ) : ℂ)) := by
    intro k _hk
    show
      g k *
          (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
              Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ)) -
        g k *
          (((r (k + 1) - r k : ℝ) : ℂ)) =
      g k *
          (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
              r (k + 1) : ℝ) : ℂ)) -
        g k *
          (((Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
              r k : ℝ) : ℂ))
    exact
      safe_endpoint_cell_error_algebra
        (g k)
        (Complex.rightSemicircleStaircaseSafeRe ρ m k)
        (Complex.rightSemicircleStaircasePrevSafeRe ρ m k)
        (r (k + 1))
        (r k)
  have hsum_shift :
      (∑ k in Finset.range (m + 1),
        g k *
          (((Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
              r k : ℝ) : ℂ))) =
      ∑ k in Finset.range m,
        g (k + 1) * ((e k : ℝ) : ℂ) := by
    have hterm :
        ∀ k : ℕ,
          (((Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
              r k : ℝ) : ℂ)) =
            if k = 0 then 0 else ((e (k - 1) : ℝ) : ℂ) := by
      intro k
      exact
        Eq.trans
          (congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) (hprev k))
          (Complex.ofReal_if_nat_zero e k)
    have hsum_if :
        (∑ k in Finset.range (m + 1),
          g k *
            (if k = 0 then 0 else ((e (k - 1) : ℝ) : ℂ))) =
        ∑ k in Finset.range m,
          g (k + 1) * ((e k : ℝ) : ℂ) :=
      finset_sum_succ_shift_of_zero_or_prev
        m g (fun k => ((e k : ℝ) : ℂ))
    exact
      Eq.trans
        (Finset.sum_congr rfl
          (fun k _hk =>
            congrArg (fun z : ℂ => g k * z) (hterm k)))
        hsum_if
  have htop :
      Complex.rightSemicircleGraphProbeGrid f c ρ m (m + 1) *
          (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ)) =
        -g (m + 1) * ((e m : ℝ) : ℂ) := by
    have hrtop : r (m + 1) = 0 := by
      show
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (m + 1)) = 0
      exact
        Eq.trans
          (congrArg
            (fun y : ℝ => Complex.rightSemicircleGraphRe ρ y)
            (Complex.rightSemicircleStaircaseY_last ρ m))
          (Complex.rightSemicircleGraphRe_top (ρ := ρ))
    show
      f (Complex.rightSemicircleGraphPoint c ρ
          (Complex.rightSemicircleStaircaseY ρ m (m + 1))) *
          (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ)) =
        -f (Complex.rightSemicircleGraphPoint c ρ
          (Complex.rightSemicircleStaircaseY ρ m (m + 1))) *
          (((Complex.rightSemicircleStaircaseSafeRe ρ m m -
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m (m + 1)) : ℝ) : ℂ))
    exact
      Eq.trans
        (top_connector_scalar_eq_neg_endpoint_defect_scalar
          (f (Complex.rightSemicircleGraphPoint c ρ
            (Complex.rightSemicircleStaircaseY ρ m (m + 1))))
          (Complex.rightSemicircleStaircaseSafeRe ρ m m))
        (congrArg
          (fun z : ℂ =>
            -f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m (m + 1))) * z)
          (Eq.symm
            (congrArg
              (fun x : ℝ =>
                ((Complex.rightSemicircleStaircaseSafeRe ρ m m - x : ℝ) : ℂ))
              hrtop)))
  show
    ((∑ k in Finset.range (m + 1),
        f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) *
          (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
              Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ))) +
        f (Complex.rightSemicircleGraphPoint c ρ ρ) *
          (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ))) -
      ∑ k in Finset.range (m + 1),
        f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) *
          (((Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m (k + 1)) -
              Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m k) : ℝ) : ℂ))
      =
        ∑ k in Finset.range (m + 1),
          (f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) -
            f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m (k + 1)))) *
            ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ)
  calc
    (∑ k in Finset.range (m + 1),
        f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) *
          (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
              Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ)) +
        f (Complex.rightSemicircleGraphPoint c ρ ρ) *
          (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ))) -
      ∑ k in Finset.range (m + 1),
        f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) *
          (((Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m (k + 1)) -
              Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m k) : ℝ) : ℂ))
        =
      (∑ k in Finset.range (m + 1),
        (f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) *
          (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
              Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ)) -
        f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) *
          (((Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m (k + 1)) -
              Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m k) : ℝ) : ℂ)))) +
        f (Complex.rightSemicircleGraphPoint c ρ ρ) *
          (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ)) := by
          exact
            finset_sum_add_tail_sub_sum_eq_sum_sub_add_tail
              (Finset.range (m + 1))
              (fun k =>
                f (Complex.rightSemicircleGraphPoint c ρ
                    (Complex.rightSemicircleStaircaseY ρ m k)) *
                  (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
                      Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ)))
              (fun k =>
                f (Complex.rightSemicircleGraphPoint c ρ
                    (Complex.rightSemicircleStaircaseY ρ m k)) *
                  (((Complex.rightSemicircleGraphRe ρ
                        (Complex.rightSemicircleStaircaseY ρ m (k + 1)) -
                      Complex.rightSemicircleGraphRe ρ
                        (Complex.rightSemicircleStaircaseY ρ m k) : ℝ) : ℂ)))
              (f (Complex.rightSemicircleGraphPoint c ρ ρ) *
                (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ)))
      _ =
        ∑ k in Finset.range (m + 1),
          (f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) -
            f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m (k + 1)))) *
            ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ) := by
          let G : ℕ → ℂ := fun k =>
            f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k))
          let E : ℕ → ℂ := fun k =>
            ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ)
          let P : ℕ → ℂ := fun k =>
            (((Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
                Complex.rightSemicircleGraphRe ρ
                  (Complex.rightSemicircleStaircaseY ρ m k) : ℝ) : ℂ))
          let tail : ℂ :=
            f (Complex.rightSemicircleGraphPoint c ρ ρ) *
              (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ))
          have hsum_cell :
              (∑ k in Finset.range (m + 1),
                (f (Complex.rightSemicircleGraphPoint c ρ
                      (Complex.rightSemicircleStaircaseY ρ m k)) *
                    (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
                        Complex.rightSemicircleStaircasePrevSafeRe ρ m k :
                          ℝ) : ℂ)) -
                  f (Complex.rightSemicircleGraphPoint c ρ
                      (Complex.rightSemicircleStaircaseY ρ m k)) *
                    (((Complex.rightSemicircleGraphRe ρ
                          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) -
                        Complex.rightSemicircleGraphRe ρ
                          (Complex.rightSemicircleStaircaseY ρ m k) :
                            ℝ) : ℂ)))) =
              ∑ k in Finset.range (m + 1),
                (G k * E k - G k * P k) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hcell k hk
          have htail_neg_left :
              tail = -G (m + 1) * E m := by
            have hpoint :
              f (Complex.rightSemicircleGraphPoint c ρ ρ) =
                f (Complex.rightSemicircleGraphPoint c ρ
                    (Complex.rightSemicircleStaircaseY ρ m (m + 1))) := by
                exact
                  Eq.symm
                    (congrArg
                      (fun y : ℝ =>
                        f (Complex.rightSemicircleGraphPoint c ρ y))
                      (Complex.rightSemicircleStaircaseY_last ρ m))
            exact
              Eq.trans
                (congrArg
                  (fun z : ℂ =>
                    z *
                    (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m :
                        ℝ) : ℂ)))
                  hpoint)
                htop
          have htail :
              tail = -(G (m + 1) * E m) :=
            Eq.trans htail_neg_left (neg_mul (G (m + 1)) (E m))
          have hshift :
              (∑ k in Finset.range (m + 1),
                G k * P k) =
                ∑ k in Finset.range m, G (k + 1) * E k :=
            hsum_shift
          exact
            Eq.trans
              (congrArg₂ HAdd.hAdd hsum_cell rfl)
              (endpoint_defect_summation_by_parts_with_tail
                m G E P tail hshift htail)

/-- The total safe endpoint defect is uniformly bounded by twice the radius.

The lower-half cells have zero defect, the upper-half cells telescope against
the decreasing circular graph, and the single crossing cell is bounded by the
radius. -/
theorem Complex.sum_abs_rightSemicircleStaircaseSafeEndpointDefect_le_two_radius
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ) :
    (∑ k in Finset.range (m + 1),
      |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k|)
        ≤ 2 * ρ := by
  let j : ℕ := (m + 1) / 2
  let e : ℕ → ℝ := fun k =>
    |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k|
  have hjm : j ≤ m := by
    show (m + 1) / 2 ≤ m
    exact nat_staircase_midpoint_le m
  have hsplit :
      (∑ k in Finset.range (m + 1), e k) =
        (∑ k in Finset.range j, e k) + e j +
          ∑ t in Finset.range (m - j), e (j + 1 + t) := by
    exact finset_sum_range_split_at_index e m j hjm
  have hlower :
      (∑ k in Finset.range j, e k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk_lt : k < j := by
      exact Finset.mem_range.mp hk
    have hzero :
        Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k = 0 :=
      Complex.rightSemicircleStaircaseSafeEndpointDefect_eq_zero_of_lt_midpoint
        hρ.le (m := m) (k := k) hk_lt
    show |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k| = 0
    exact Eq.trans (congrArg abs hzero) abs_zero
  have hj_range : j ∈ Finset.range (m + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hjm)
  have hcross : e j ≤ ρ := by
    show |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m j| ≤ ρ
    exact
      Complex.abs_rightSemicircleStaircaseSafeEndpointDefect_le_radius
        hρ.le m j hj_range
  have hsuffix :
      (∑ t in Finset.range (m - j), e (j + 1 + t)) ≤ ρ := by
    show
      (∑ t in Finset.range (m - (m + 1) / 2),
        |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m
          (((m + 1) / 2) + 1 + t)|) ≤ ρ
    exact
      Complex.sum_abs_rightSemicircleStaircaseSafeEndpointDefect_suffix_le_radius
        hρ.le m
  calc
    (∑ k in Finset.range (m + 1),
      |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k|)
        =
      ∑ k in Finset.range (m + 1), e k := by
        rfl
    _ =
      (∑ k in Finset.range j, e k) + e j +
        ∑ t in Finset.range (m - j), e (j + 1 + t) := hsplit
    _ ≤ 2 * ρ := by
      have hcollapse :
          (∑ k in Finset.range j, e k) + e j +
              ∑ t in Finset.range (m - j), e (j + 1 + t) =
            e j + ∑ t in Finset.range (m - j), e (j + 1 + t) :=
        Eq.trans
          (add_assoc
            (∑ k in Finset.range j, e k)
            (e j)
            (∑ t in Finset.range (m - j), e (j + 1 + t)))
          (Eq.trans
            (congrArg
              (fun x : ℝ => x + (e j + ∑ t in Finset.range (m - j), e (j + 1 + t)))
              hlower)
            (zero_add (e j + ∑ t in Finset.range (m - j), e (j + 1 + t))))
      exact
        Eq.subst
          (motive := fun x : ℝ => x ≤ 2 * ρ)
          (Eq.symm hcollapse)
          (add_le_two_mul_of_each_le hcross hsuffix)

/-- Adjacent graph probes on the staircase height grid become uniformly
close. -/
theorem Complex.rightSemicircleGraphProbeGrid_adjacent_uniform_tendsto_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        Finset.sup' (Finset.range (m + 1)) ⟨0, zero_mem_range_nat_succ m⟩
          (fun k =>
            ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
              Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖))
      atTop
      (𝓝 0) := by
  exact Metric.tendsto_atTop.mpr (fun ε hε => by
    have hprobe_cont :
        ContinuousOn
          (fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y))
          (Set.Icc (-ρ) ρ) :=
      Complex.continuousOn_rightSemicircleGraphVerticalIntegrand
        f c hρ hcont
    have hprobe_uniform :
        UniformContinuousOn
          (fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y))
          (Set.Icc (-ρ) ρ) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hprobe_cont
    let ⟨δ, hδ, hδ_modulus⟩ :=
      Metric.uniformContinuousOn_iff.mp hprobe_uniform ε hε
    have hmesh :
        ∀ᶠ m : ℕ in atTop,
          ∀ k ∈ Finset.range (m + 1),
            |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
              Complex.rightSemicircleStaircaseY ρ m k| < δ :=
      Complex.eventually_rightSemicircleStaircase_cell_length_lt hρ hδ
    match eventually_atTop.mp hmesh with
    | ⟨N, hN⟩ =>
      exact ⟨N, fun m hmN => by
        have hm : ∀ k ∈ Finset.range (m + 1),
            |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
              Complex.rightSemicircleStaircaseY ρ m k| < δ :=
          hN m hmN
        have hsup_lt :
            Finset.sup' (Finset.range (m + 1)) ⟨0, zero_mem_range_nat_succ m⟩
                (fun k =>
                  ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                    Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖) < ε :=
          (Finset.sup'_lt_iff ⟨0, zero_mem_range_nat_succ m⟩).mpr
          (by
            intro k hk
            have hk0 : k ∈ Finset.range (m + 2) := by
              exact Complex.staircase_lower_sample_mem_range hk
            have hk1 : k + 1 ∈ Finset.range (m + 2) := by
              exact Complex.staircase_upper_sample_mem_range hk
            have hy0 :
                Complex.rightSemicircleStaircaseY ρ m k ∈ Set.Icc (-ρ) ρ := by
              exact Complex.mem_semicircle_height_Icc_of_mem_uIcc hρ.le
                (Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k hk0)
            have hy1 :
                Complex.rightSemicircleStaircaseY ρ m (k + 1) ∈ Set.Icc (-ρ) ρ := by
              exact Complex.mem_semicircle_height_Icc_of_mem_uIcc hρ.le
                (Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m (k + 1) hk1)
            have hdist :
                dist
                  (Complex.rightSemicircleStaircaseY ρ m k)
                  (Complex.rightSemicircleStaircaseY ρ m (k + 1)) < δ := by
              exact
                Eq.subst
                  (motive := fun x : ℝ => x < δ)
                  (Eq.symm
                    (Eq.trans
                      (Real.dist_eq
                        (Complex.rightSemicircleStaircaseY ρ m k)
                        (Complex.rightSemicircleStaircaseY ρ m (k + 1)))
                      (abs_sub_comm
                        (Complex.rightSemicircleStaircaseY ρ m k)
                        (Complex.rightSemicircleStaircaseY ρ m (k + 1)))))
                  (hm k hk)
            have hclose :
                dist
                  (f (Complex.rightSemicircleGraphPoint c ρ
                    (Complex.rightSemicircleStaircaseY ρ m k)))
                  (f (Complex.rightSemicircleGraphPoint c ρ
                    (Complex.rightSemicircleStaircaseY ρ m (k + 1)))) < ε :=
              hδ_modulus
                (Complex.rightSemicircleStaircaseY ρ m k) hy0
                (Complex.rightSemicircleStaircaseY ρ m (k + 1)) hy1
                hdist
            show
              ‖f (Complex.rightSemicircleGraphPoint c ρ
                    (Complex.rightSemicircleStaircaseY ρ m k)) -
                f (Complex.rightSemicircleGraphPoint c ρ
                    (Complex.rightSemicircleStaircaseY ρ m (k + 1)))‖ < ε
            let z₀ : ℂ :=
              f (Complex.rightSemicircleGraphPoint c ρ
                (Complex.rightSemicircleStaircaseY ρ m k))
            let z₁ : ℂ :=
              f (Complex.rightSemicircleGraphPoint c ρ
                (Complex.rightSemicircleStaircaseY ρ m (k + 1)))
            have hdist_norm : dist z₀ z₁ = ‖z₀ - z₁‖ :=
              dist_eq_norm z₀ z₁
            exact
              Eq.subst
                (motive := fun x : ℝ => x < ε)
                hdist_norm
                hclose)
        have hsup_nonneg :
            0 ≤
              Finset.sup' (Finset.range (m + 1)) ⟨0, zero_mem_range_nat_succ m⟩
                (fun k =>
                  ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                    Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖) := by
          have hterm_nonneg :
              0 ≤
                ‖Complex.rightSemicircleGraphProbeGrid f c ρ m 0 -
                  Complex.rightSemicircleGraphProbeGrid f c ρ m (0 + 1)‖ :=
            norm_nonneg _
          have hterm_le_sup :
              ‖Complex.rightSemicircleGraphProbeGrid f c ρ m 0 -
                  Complex.rightSemicircleGraphProbeGrid f c ρ m (0 + 1)‖ ≤
                Finset.sup' (Finset.range (m + 1)) ⟨0, zero_mem_range_nat_succ m⟩
                  (fun k =>
                    ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                      Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖) :=
            Finset.le_sup'
              (fun k =>
                ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                  Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖)
              (zero_mem_range_nat_succ m)
          exact le_trans hterm_nonneg hterm_le_sup
        have hdist :
            dist
              (Finset.sup' (Finset.range (m + 1)) ⟨0, zero_mem_range_nat_succ m⟩
                (fun k =>
                  ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                    Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖))
              0 =
            Finset.sup' (Finset.range (m + 1)) ⟨0, zero_mem_range_nat_succ m⟩
              (fun k =>
                ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                  Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖) :=
          Eq.trans
            (dist_zero_right _)
            (Real.norm_of_nonneg hsup_nonneg)
        exact
          Eq.subst
            (motive := fun x : ℝ => x < ε)
            (Eq.symm hdist)
            hsup_lt⟩)

/-- Endpoint-defect summation-by-parts estimate for the safe-coordinate
horizontal sample error. -/
theorem Complex.norm_rightSemicircleStaircaseHorizontalSampleSum_sub_graphHorizontalSampleSum_le_endpointDefect
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (_hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (m : ℕ) :
    ‖Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
      Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m‖
      ≤
        (Finset.sup' (Finset.range (m + 1)) ⟨0, zero_mem_range_nat_succ m⟩
          (fun k =>
            ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
              Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖)) *
        (2 * ρ) := by
  let M : ℝ :=
    Finset.sup' (Finset.range (m + 1)) ⟨0, zero_mem_range_nat_succ m⟩
      (fun k =>
        ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
          Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖)
  have hM_nonneg : 0 ≤ M := by
    have hterm_nonneg :
        0 ≤
          ‖Complex.rightSemicircleGraphProbeGrid f c ρ m 0 -
            Complex.rightSemicircleGraphProbeGrid f c ρ m (0 + 1)‖ :=
      norm_nonneg _
    have hterm_le_sup :
        ‖Complex.rightSemicircleGraphProbeGrid f c ρ m 0 -
            Complex.rightSemicircleGraphProbeGrid f c ρ m (0 + 1)‖ ≤ M :=
      Finset.le_sup'
        (fun k =>
          ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
            Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖)
        (zero_mem_range_nat_succ m)
    exact le_trans hterm_nonneg hterm_le_sup
  have hrepresentation :
      Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
        Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m =
        ∑ k in Finset.range (m + 1),
          (Complex.rightSemicircleGraphProbeGrid f c ρ m k -
            Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)) *
            ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ) :=
    Complex.rightSemicircleStaircaseHorizontalSampleSum_sub_graphHorizontalSampleSum_eq_endpointDefectSum
      f c ρ m
  have hsum_bound :
      ‖∑ k in Finset.range (m + 1),
          (Complex.rightSemicircleGraphProbeGrid f c ρ m k -
            Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)) *
            ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ)‖
        ≤ M * (2 * ρ) := by
    calc
      ‖∑ k in Finset.range (m + 1),
          (Complex.rightSemicircleGraphProbeGrid f c ρ m k -
            Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)) *
            ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ)‖
          ≤
        ∑ k in Finset.range (m + 1),
          ‖(Complex.rightSemicircleGraphProbeGrid f c ρ m k -
            Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)) *
            ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ)‖ :=
            norm_sum_le _ _
      _ ≤
        ∑ k in Finset.range (m + 1),
          M *
            |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k| := by
          apply Finset.sum_le_sum
          intro k hk
          have hfactor :
              ‖(Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                  Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)) *
                  ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ)‖ =
                ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                  Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖ *
                  |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k| := by
            have hnorm_mul :
                ‖(Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                    Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)) *
                    ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ)‖ =
                  ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                    Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖ *
                    ‖((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ)‖ :=
              norm_mul
                (Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                  Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1))
                ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ)
            have hnorm_real :
                ‖((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ)‖ =
                  |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k| :=
              Eq.trans
                (RCLike.norm_ofReal
                  (Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k))
                (Real.norm_eq_abs
                  (Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k))
            exact
              Eq.trans hnorm_mul
                (congrArg
                  (fun x : ℝ =>
                    ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                      Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖ * x)
                  hnorm_real)
          exact
            Eq.subst
              (motive := fun x : ℝ => x ≤
                M * |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k|)
              (Eq.symm hfactor)
              (mul_le_mul_of_nonneg_right
                (Finset.le_sup'
                  (fun k =>
                    ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                      Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖)
                  hk)
                (abs_nonneg _))
      _ =
        M *
          ∑ k in Finset.range (m + 1),
            |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k| := by
          exact
            finset_sum_const_mul_eq_mul_sum
              (Finset.range (m + 1))
              M
              (fun k =>
                |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k|)
      _ ≤
        M * (2 * ρ) := by
          exact mul_le_mul_of_nonneg_left
            (Complex.sum_abs_rightSemicircleStaircaseSafeEndpointDefect_le_two_radius
              hρ m)
            hM_nonneg
  exact
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ M * (2 * ρ))
      (Eq.symm hrepresentation)
      hsum_bound

/-- The safe-staircase horizontal finite-difference samples and the exact
graph-coordinate finite-difference samples have the same limit.

This is the exterior-safe coordinate half of the horizontal quadrature
argument: uniform convergence of the safe and previous-safe real coordinates
to the graph coordinate, together with a compact bound for the graph probe,
makes the weighted coordinate-increment error tend to zero. -/
theorem Complex.rightSemicircleStaircaseHorizontalSampleSum_sub_graphHorizontalSampleSum_tendsto_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
          Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m)
      atTop
      (𝓝 0) := by
  have hsup :
      Tendsto
        (fun m : ℕ =>
          Finset.sup' (Finset.range (m + 1)) ⟨0, zero_mem_range_nat_succ m⟩
            (fun k =>
              ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖))
        atTop
        (𝓝 0) :=
    Complex.rightSemicircleGraphProbeGrid_adjacent_uniform_tendsto_zero
      f c hρ hcont
  have hprod :
      Tendsto
        (fun m : ℕ =>
          (Finset.sup' (Finset.range (m + 1)) ⟨0, zero_mem_range_nat_succ m⟩
            (fun k =>
              ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖)) *
            (2 * ρ))
        atTop
        (𝓝 (0 * (2 * ρ))) :=
    hsup.mul tendsto_const_nhds
  have hprod_zero :
      Tendsto
        (fun m : ℕ =>
          (Finset.sup' (Finset.range (m + 1)) ⟨0, zero_mem_range_nat_succ m⟩
            (fun k =>
              ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖)) *
            (2 * ρ))
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun m : ℕ =>
            (Finset.sup' (Finset.range (m + 1)) ⟨0, zero_mem_range_nat_succ m⟩
              (fun k =>
                ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                  Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖)) *
              (2 * ρ))
          atTop
          (𝓝 x))
      (zero_mul (2 * ρ))
      hprod
  have hnorm_tendsto :
      Tendsto
        (fun m : ℕ =>
          ‖Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
            Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m‖)
        atTop
        (𝓝 0) := by
    exact
      squeeze_zero
        (fun m =>
          norm_nonneg
            (Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
              Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m))
        (fun m =>
          Complex.norm_rightSemicircleStaircaseHorizontalSampleSum_sub_graphHorizontalSampleSum_le_endpointDefect
            f c hρ hcont m)
        hprod_zero
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_tendsto

end
end LFunctions
end Boundary
