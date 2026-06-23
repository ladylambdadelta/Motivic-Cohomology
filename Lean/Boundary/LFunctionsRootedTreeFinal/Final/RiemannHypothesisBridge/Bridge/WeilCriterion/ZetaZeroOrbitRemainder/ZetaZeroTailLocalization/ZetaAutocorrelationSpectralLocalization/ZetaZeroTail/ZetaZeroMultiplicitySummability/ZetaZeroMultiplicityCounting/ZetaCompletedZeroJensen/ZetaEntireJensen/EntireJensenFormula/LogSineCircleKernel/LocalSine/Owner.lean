import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.LogSineCircleKernel.ChordGeometry.Owner

/-!
# Log-sine and unit-circle boundary kernel

This owner layer was split from `LogSineCircleKernel.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Half-angle linear substitution before removing the absolute value. -/
theorem unitCircleLogKernel_halfSineLog_integral_eq_twice_absSineLog :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.log |Real.sin (θ / 2)|) =
      2 * (∫ u in (0 : ℝ)..Real.pi, Real.log |Real.sin u|) := by
  let f : ℝ → ℝ := fun u : ℝ => Real.log |Real.sin u|
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.log |Real.sin (θ / 2)|) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), f (θ / 2) := by
      rfl
    _ = 2 * (∫ u in ((0 : ℝ) / 2)..((2 * Real.pi) / 2), f u) := by
      exact intervalIntegral.integral_comp_div (f := f) (a := (0 : ℝ))
        (b := 2 * Real.pi) (c := 2) two_ne_zero
    _ = 2 * (∫ u in (0 : ℝ)..Real.pi, Real.log |Real.sin u|) := by
      have h0 : (0 : ℝ) / 2 = 0 := by
        exact zero_div 2
      have hpi : (2 * Real.pi) / 2 = Real.pi := by
        calc
          (2 * Real.pi) / 2 = (Real.pi * 2) / 2 := by
            exact congrArg (fun x : ℝ => x / 2) (mul_comm 2 Real.pi)
          _ = Real.pi * (2 / 2 : ℝ) := by
            exact mul_div_assoc Real.pi 2 2
          _ = Real.pi * 1 := by
            exact congrArg (fun x : ℝ => Real.pi * x) (div_self two_ne_zero)
          _ = Real.pi := by
            exact mul_one Real.pi
      have hinterval :
          (∫ u in ((0 : ℝ) / 2)..((2 * Real.pi) / 2), f u) =
            ∫ u in (0 : ℝ)..Real.pi, f u := by
        calc
          (∫ u in ((0 : ℝ) / 2)..((2 * Real.pi) / 2), f u) =
              ∫ u in (0 : ℝ)..((2 * Real.pi) / 2), f u := by
            exact congrArg
              (fun a : ℝ => ∫ u in a..((2 * Real.pi) / 2), f u)
              h0
          _ = ∫ u in (0 : ℝ)..Real.pi, f u := by
            exact congrArg
              (fun b : ℝ => ∫ u in (0 : ℝ)..b, f u)
              hpi
      calc
        2 * (∫ u in ((0 : ℝ) / 2)..((2 * Real.pi) / 2), f u)
            = 2 * (∫ u in (0 : ℝ)..Real.pi, f u) := by
              exact congrArg (fun t : ℝ => 2 * t) hinterval
        _ = 2 * (∫ u in (0 : ℝ)..Real.pi, Real.log |Real.sin u|) := by
              rfl

/-- The sine is a.e. positive on the open Jensen sine interval. -/
theorem real_sin_pos_ae_zero_pi :
    ∀ᵐ u ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) Real.pi),
      0 < Real.sin u := by
  have hne_pi :
      ∀ᵐ u ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) Real.pi),
        u ≠ Real.pi :=
    MeasureTheory.ae_restrict_of_ae
      ((Set.countable_singleton Real.pi).ae_not_mem MeasureTheory.volume)
  have hinterval :
      ∀ᵐ u ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) Real.pi),
        u ∈ Ι (0 : ℝ) Real.pi :=
    MeasureTheory.ae_restrict_mem measurableSet_uIoc
  exact
    (hne_pi.and hinterval).mono
      (fun u hu =>
        have hu_ne_pi : u ≠ Real.pi := hu.1
        have hu_interval : u ∈ Ι (0 : ℝ) Real.pi := hu.2
        have hu_cases :
            0 < u ∧ u ≤ Real.pi ∨ Real.pi < u ∧ u ≤ 0 :=
          Set.mem_uIoc.1 hu_interval
        match hu_cases with
        | Or.inl hmain =>
            Real.sin_pos_of_pos_of_lt_pi
              hmain.1
              (lt_of_le_of_ne hmain.2 hu_ne_pi)
        | Or.inr hrev =>
            have hpi_le_zero : Real.pi ≤ 0 :=
              hrev.1.le.trans hrev.2
            False.elim ((not_lt_of_ge hpi_le_zero) Real.pi_pos))

/-- A.e. removal of the absolute value in the sine-log integral on `[0,π]`. -/
theorem real_log_abs_sin_ae_eq_log_sin_zero_pi :
    (fun u : ℝ => Real.log |Real.sin u|) =ᵐ[
        MeasureTheory.volume.restrict (Ι (0 : ℝ) Real.pi)]
      (fun u : ℝ => Real.log (Real.sin u)) := by
  exact
    real_sin_pos_ae_zero_pi.mono
      (fun u hu =>
        congrArg Real.log (abs_of_pos hu))

/-- On `[0,π]`, replacing `log |sin u|` by `log (sin u)` changes only the
finite endpoint singularities. -/
theorem real_integral_log_abs_sin_zero_pi_eq_log_sin :
    (∫ u in (0 : ℝ)..Real.pi, Real.log |Real.sin u|) =
      ∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u) := by
  exact
    intervalIntegral.integral_congr_ae
      ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).1
        real_log_abs_sin_ae_eq_log_sin_zero_pi)

/-- Away from the endpoint zeros, the logarithmic sine kernel is continuous on
the Jensen sine interval. -/
theorem real_log_abs_sin_continuousOn_Icc_compl_endpoints :
    ContinuousOn
      (fun u : ℝ => Real.log |Real.sin u|)
      ({u : ℝ | u ∈ Set.Icc (0 : ℝ) Real.pi ∧
        u ∉ ({0, Real.pi} : Set ℝ)}) := by
  have hsin_ne :
      ∀ u : ℝ,
        u ∈ {u : ℝ | u ∈ Set.Icc (0 : ℝ) Real.pi ∧
          u ∉ ({0, Real.pi} : Set ℝ)} →
          |Real.sin u| ≠ 0 := by
    intro u hu
    have huIcc : u ∈ Set.Icc (0 : ℝ) Real.pi :=
      hu.1
    have hu_not_end : u ∉ ({0, Real.pi} : Set ℝ) :=
      hu.2
    have hu0_ne : u ≠ 0 := by
      intro hu0
      exact hu_not_end (Or.inl hu0)
    have hupi_ne : u ≠ Real.pi := by
      intro hupi
      exact hu_not_end (Or.inr hupi)
    have h0_lt_u : 0 < u :=
      lt_of_le_of_ne huIcc.1 (Ne.symm hu0_ne)
    have hu_lt_pi : u < Real.pi :=
      lt_of_le_of_ne huIcc.2 hupi_ne
    have hsin_pos : 0 < Real.sin u :=
      Real.sin_pos_of_pos_of_lt_pi h0_lt_u hu_lt_pi
    exact abs_ne_zero.mpr hsin_pos.ne'
  have habs_cont :
      ContinuousOn
        (fun u : ℝ => |Real.sin u|)
        ({u : ℝ | u ∈ Set.Icc (0 : ℝ) Real.pi ∧
          u ∉ ({0, Real.pi} : Set ℝ)}) :=
    (Real.continuous_sin.continuousOn).abs
  exact
    ContinuousOn.log habs_cont hsin_ne

/-- The sine quotient filled by value `1` at the origin is continuous at `0`.

This is the derivative-slope form of `sin θ / θ → 1`. -/
theorem real_filled_sin_div_self_continuousAt_zero :
    [DecidableEq ℝ] →
    ContinuousAt
      (Function.update (fun x : ℝ => Real.sin x / x) 0 1)
      0 := by
  intro _hdec
  have hslope :
      ContinuousAt
        (Function.update
          (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0))
          0
          (Real.cos 0))
        0 :=
    (Real.hasDerivAt_sin 0).continuousAt_div
  have hfun :
      Function.update
          (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0))
          0
          (Real.cos 0) =
        Function.update (fun x : ℝ => Real.sin x / x) 0 1 := by
    exact
      funext
        (fun x =>
          match (inferInstance : Decidable (x = 0)) with
          | isTrue hx =>
              have hleft :
                  Function.update
                      (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0))
                      0
                      (Real.cos 0) x =
                    Real.cos 0 :=
                Eq.subst
                  (motive := fun y : ℝ =>
                    Function.update
                        (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0))
                        0
                        (Real.cos 0) y =
                      Real.cos 0)
                  hx.symm
                  (Function.update_same 0 (Real.cos 0)
                    (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0)))
              have hright :
                  Function.update (fun x : ℝ => Real.sin x / x) 0 1 x =
                    1 :=
                Eq.subst
                  (motive := fun y : ℝ =>
                    Function.update (fun x : ℝ => Real.sin x / x) 0 1 y =
                      1)
                  hx.symm
                  (Function.update_same 0 1 (fun x : ℝ => Real.sin x / x))
              calc
                Function.update
                    (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0))
                    0
                    (Real.cos 0) x =
                  Real.cos 0 := hleft
                _ = 1 := Real.cos_zero
                _ = Function.update (fun x : ℝ => Real.sin x / x) 0 1 x :=
                  hright.symm
          | isFalse hx =>
              have hleft :
                Function.update
                    (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0))
                    0
                    (Real.cos 0) x =
                  (Real.sin x - Real.sin 0) / (x - 0) :=
              Function.update_noteq hx (Real.cos 0)
                (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0))
              have hright :
                Function.update (fun x : ℝ => Real.sin x / x) 0 1 x =
                  Real.sin x / x :=
                Function.update_noteq hx 1 (fun x : ℝ => Real.sin x / x)
              calc
                Function.update
                    (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0))
                    0
                    (Real.cos 0) x =
                    (Real.sin x - Real.sin 0) / (x - 0) := hleft
                _ = Real.sin x / x := by
                  exact congrArg₂ HDiv.hDiv
                    (sub_eq_self.2 Real.sin_zero)
                    (sub_zero x)
                _ = Function.update (fun x : ℝ => Real.sin x / x) 0 1 x :=
                  hright.symm)
  exact
    Eq.subst
      (motive := fun f : ℝ → ℝ => ContinuousAt f 0)
      hfun
      hslope

/-- A continuous real-valued function that is nonzero at `c` has locally
interval-integrable logarithmic absolute value near `c`. -/
theorem real_log_abs_local_intervalIntegrable_of_continuous_nonzero
    (f : ℝ → ℝ)
    (c : ℝ)
    (hf : Continuous f)
    (hfc : f c ≠ 0) :
    ∃ u v : ℝ,
      u < c ∧ c < v ∧
      IntervalIntegrable
        (fun x : ℝ => Real.log |f x|)
        MeasureTheory.volume
        u
        v := by
  have hne_event :
      ∀ᶠ x in 𝓝 c, f x ≠ 0 :=
    hf.continuousAt.eventually_ne hfc
  match Metric.mem_nhds_iff.1 hne_event with
  | ⟨ε, hε_pos, hball⟩ =>
    let δ : ℝ := ε / 2
    let u : ℝ := c - δ
    let v : ℝ := c + δ
    have hδ_pos : 0 < δ :=
      half_pos hε_pos
    have hδ_nonneg : 0 ≤ δ :=
      hδ_pos.le
    have hδ_lt : δ < ε :=
      half_lt_self hε_pos
    have hu_lt_c : u < c := by
      exact sub_lt_self c hδ_pos
    have hc_lt_v : c < v := by
      exact lt_add_of_pos_right c hδ_pos
    have huv_le : u ≤ v :=
      hu_lt_c.le.trans hc_lt_v.le
    have huIcc_eq_closed :
        Set.uIcc u v = Metric.closedBall c δ := by
      calc
        Set.uIcc u v = Set.Icc u v := by
          exact Set.uIcc_of_le huv_le
        _ = Set.Icc (c - δ) (c + δ) := by
          exact rfl
        _ = Metric.closedBall c δ := by
          exact (Real.closedBall_eq_Icc (x := c) (r := δ)).symm
    have hcont_abs :
        ContinuousOn
          (fun x : ℝ => |f x|)
          (Set.uIcc u v) :=
      hf.continuousOn.abs
    have hnonzero_abs :
        ∀ x : ℝ, x ∈ Set.uIcc u v → |f x| ≠ 0 := by
      intro x hx
      have hx_closed : x ∈ Metric.closedBall c δ :=
        huIcc_eq_closed ▸ hx
      have hx_ball : x ∈ Metric.ball c ε :=
        Metric.closedBall_subset_ball hδ_lt hx_closed
      exact abs_ne_zero.mpr (hball hx_ball)
    exact
      ⟨u, v, hu_lt_c, hc_lt_v,
        (ContinuousOn.log hcont_abs hnonzero_abs).intervalIntegrable⟩

/-- The sine quotient filled by value `1` at the origin is continuous. -/
theorem real_filled_sin_div_self_continuous :
    [DecidableEq ℝ] →
    Continuous
      (Function.update (fun x : ℝ => Real.sin x / x) 0 1) := by
  intro _hdec
  exact
    continuous_iff_continuousAt.2
      (fun x : ℝ =>
        match (inferInstance : Decidable (x = 0)) with
        | isTrue hx =>
            Eq.subst
              (motive := fun y : ℝ =>
                ContinuousAt
                  (Function.update (fun x : ℝ => Real.sin x / x) 0 1)
                  y)
              hx.symm
              real_filled_sin_div_self_continuousAt_zero
        | isFalse hx =>
            (continuousAt_update_of_ne hx).2
              (Real.continuous_sin.continuousAt.div continuousAt_id hx))

/-- The filled sine-ratio logarithm is locally interval-integrable near `0`.

The filled ratio is continuous at `0` by applying
`HasDerivAt.continuousAt_div` to `Real.hasDerivAt_sin 0`; the value at `0` is
`1`, so the logarithm is locally continuous and hence locally
interval-integrable. -/
theorem real_log_abs_filled_sin_div_self_local_intervalIntegrable_zero :
    [DecidableEq ℝ] →
    ∃ u v : ℝ,
      u < (0 : ℝ) ∧ (0 : ℝ) < v ∧
      IntervalIntegrable
        (fun θ : ℝ =>
          Real.log |Function.update (fun x : ℝ => Real.sin x / x) 0 1 θ|)
        MeasureTheory.volume
        u
        v := by
  intro _hdec
  have hvalue :
      Function.update (fun x : ℝ => Real.sin x / x) 0 1 0 = 1 :=
    Function.update_same 0 1 (fun x : ℝ => Real.sin x / x)
  have hnonzero :
      Function.update (fun x : ℝ => Real.sin x / x) 0 1 0 ≠ 0 := by
    exact Eq.subst
      (motive := fun y : ℝ => y ≠ 0)
      hvalue.symm
      one_ne_zero
  exact
    real_log_abs_local_intervalIntegrable_of_continuous_nonzero
      (Function.update (fun x : ℝ => Real.sin x / x) 0 1)
      0
      real_filled_sin_div_self_continuous
      hnonzero

/-- The derivative-slope quotient for `sin` filled at `π` is continuous. -/
theorem real_filled_sin_sub_pi_div_sub_pi_continuous :
    [DecidableEq ℝ] →
    Continuous
      (Function.update
        (fun x : ℝ => (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
        Real.pi
        (Real.cos Real.pi)) := by
  intro _hdec
  have hcont_at_pi :
      ContinuousAt
        (Function.update
          (fun x : ℝ => (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
          Real.pi
          (Real.cos Real.pi))
        Real.pi :=
    (Real.hasDerivAt_sin Real.pi).continuousAt_div
  exact
    continuous_iff_continuousAt.2
      (fun x : ℝ =>
        match (inferInstance : Decidable (x = Real.pi)) with
        | isTrue hx =>
            Eq.subst
              (motive := fun y : ℝ =>
                ContinuousAt
                  (Function.update
                    (fun x : ℝ =>
                      (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
                    Real.pi
                    (Real.cos Real.pi))
                  y)
              hx.symm
              hcont_at_pi
        | isFalse hx =>
            (continuousAt_update_of_ne hx).2
              ((Real.continuous_sin.continuousAt.sub continuousAt_const).div
                (continuousAt_id.sub continuousAt_const)
                (sub_ne_zero.mpr hx)))

/-- The filled derivative-slope logarithm for `sin` is locally
interval-integrable near `π`. -/
theorem real_log_abs_filled_sin_sub_pi_div_sub_pi_local_intervalIntegrable_pi :
    [DecidableEq ℝ] →
    ∃ u v : ℝ,
      u < Real.pi ∧ Real.pi < v ∧
      IntervalIntegrable
        (fun θ : ℝ =>
          Real.log |(
            Function.update
              (fun x : ℝ =>
                (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
              Real.pi
              (Real.cos Real.pi)
              θ)|)
        MeasureTheory.volume
        u
        v := by
  intro _hdec
  have hvalue :
      Function.update
          (fun x : ℝ => (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
          Real.pi
          (Real.cos Real.pi)
          Real.pi =
        Real.cos Real.pi :=
    Function.update_same Real.pi (Real.cos Real.pi)
      (fun x : ℝ => (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
  have hcos_nonzero : Real.cos Real.pi ≠ 0 := by
    exact Real.cos_pi ▸ neg_ne_zero.mpr one_ne_zero
  have hnonzero :
      Function.update
          (fun x : ℝ => (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
          Real.pi
          (Real.cos Real.pi)
          Real.pi ≠ 0 := by
    intro hzero
    exact hcos_nonzero (Eq.trans hvalue.symm hzero)
  exact
    real_log_abs_local_intervalIntegrable_of_continuous_nonzero
      (Function.update
        (fun x : ℝ => (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
        Real.pi
        (Real.cos Real.pi))
      Real.pi
      real_filled_sin_sub_pi_div_sub_pi_continuous
      hnonzero

/-- Local logarithmic model for `log |sin u|` at `0`.

The remainder is `log |sin u / u|`, extended at `0`; its continuity follows
from the standard sine-ratio limit. -/
theorem real_log_abs_sin_localModel_zero :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      (∃ u v : ℝ,
        u < (0 : ℝ) ∧ (0 : ℝ) < v ∧
        IntervalIntegrable g MeasureTheory.volume u v) ∧
      ∀ᶠ θ in 𝓝[≠] (0 : ℝ),
        Real.log |Real.sin θ| =
          (n : ℝ) * Real.log |θ - 0| + g θ := by
  let g : ℝ → ℝ :=
    fun θ : ℝ =>
      Real.log |Function.update (fun x : ℝ => Real.sin x / x) 0 1 θ|
  have hlocal :
      ∃ u v : ℝ,
        u < (0 : ℝ) ∧ (0 : ℝ) < v ∧
        IntervalIntegrable g MeasureTheory.volume u v :=
    real_log_abs_filled_sin_div_self_local_intervalIntegrable_zero
  have hevent :
      ∀ᶠ θ in 𝓝[≠] (0 : ℝ),
        Real.log |Real.sin θ| =
          ((1 : ℕ) : ℝ) * Real.log |θ - 0| + g θ := by
    have hsmall :
        ∀ᶠ θ in 𝓝[≠] (0 : ℝ), θ ∈ Set.Ioo (-Real.pi) Real.pi :=
      Filter.mem_of_superset
        (nhdsWithin_le_nhds (s := {0}ᶜ)
          (Ioo_mem_nhds (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos))
        (fun θ hθ => hθ)
    have hself :
        ∀ᶠ θ in 𝓝[≠] (0 : ℝ), θ ∈ ({0} : Set ℝ)ᶜ :=
      self_mem_nhdsWithin
    exact
      (hself.and hsmall).mono
        (fun θ hθ =>
          have hθ_ne : θ ≠ 0 := hθ.1
          have hθ_small : θ ∈ Set.Ioo (-Real.pi) Real.pi := hθ.2
          have hsin_ne : Real.sin θ ≠ 0 := by
            have hzero_iff : Real.sin θ = 0 ↔ θ = 0 :=
              Real.sin_eq_zero_iff_of_lt_of_lt hθ_small.1 hθ_small.2
            intro hsin_zero
            exact hθ_ne (hzero_iff.1 hsin_zero)
          have hupdate :
              Function.update (fun x : ℝ => Real.sin x / x) 0 1 θ =
                Real.sin θ / θ := by
            exact Function.update_noteq hθ_ne 1 (fun x : ℝ => Real.sin x / x)
          have hsin_factor :
              Real.sin θ = θ * (Real.sin θ / θ) := by
            exact (mul_div_cancel₀ (Real.sin θ) hθ_ne).symm
          have habs_factor :
              |Real.sin θ| = |θ| * |Real.sin θ / θ| := by
            calc
              |Real.sin θ| = |θ * (Real.sin θ / θ)| := by
                exact congrArg abs hsin_factor
              _ = |θ| * |Real.sin θ / θ| := by
                exact abs_mul θ (Real.sin θ / θ)
          have hθ_abs_ne : |θ| ≠ 0 :=
            abs_ne_zero.mpr hθ_ne
          have hratio_ne : |Real.sin θ / θ| ≠ 0 := by
            exact abs_ne_zero.mpr (div_ne_zero hsin_ne hθ_ne)
          calc
            Real.log |Real.sin θ| =
                Real.log (|θ| * |Real.sin θ / θ|) := by
              exact congrArg Real.log habs_factor
            _ = Real.log |θ| + Real.log |Real.sin θ / θ| := by
              exact Real.log_mul hθ_abs_ne hratio_ne
            _ = ((1 : ℕ) : ℝ) * Real.log |θ - 0| + g θ := by
              have htheta_sub : |θ - 0| = |θ| :=
                congrArg abs (sub_zero θ)
              have hgθ : g θ = Real.log |Real.sin θ / θ| := by
                exact congrArg (fun x : ℝ => Real.log |x|) hupdate
              calc
                Real.log |θ| + Real.log |Real.sin θ / θ| =
                    Real.log |θ - 0| + Real.log |Real.sin θ / θ| := by
                  exact congrArg
                    (fun x : ℝ => Real.log x + Real.log |Real.sin θ / θ|)
                    htheta_sub.symm
                _ = ((1 : ℕ) : ℝ) * Real.log |θ - 0| +
                    Real.log |Real.sin θ / θ| := by
                  have hone_mul :
                      ((1 : ℕ) : ℝ) * Real.log |θ - 0| =
                        Real.log |θ - 0| := by
                    calc
                      ((1 : ℕ) : ℝ) * Real.log |θ - 0| =
                          (1 : ℝ) * Real.log |θ - 0| := by
                        exact congrArg
                          (fun x : ℝ => x * Real.log |θ - 0|)
                          Nat.cast_one
                      _ = Real.log |θ - 0| :=
                        one_mul (Real.log |θ - 0|)
                  exact congrArg
                    (fun x : ℝ => x + Real.log |Real.sin θ / θ|)
                    hone_mul.symm
                _ = ((1 : ℕ) : ℝ) * Real.log |θ - 0| + g θ := by
                  exact congrArg
                    (fun x : ℝ => ((1 : ℕ) : ℝ) * Real.log |θ - 0| + x)
                    hgθ.symm)
  exact ⟨1, g, hlocal, hevent⟩

/-- Local logarithmic model for `log |sin u|` at `π`.

This is transported from the model at `0` using
`sin u = sin (π - u)` and `|π - u| = |u - π|`. -/
theorem real_log_abs_sin_localModel_pi :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      (∃ u v : ℝ,
        u < Real.pi ∧ Real.pi < v ∧
        IntervalIntegrable g MeasureTheory.volume u v) ∧
      ∀ᶠ θ in 𝓝[≠] Real.pi,
        Real.log |Real.sin θ| =
          (n : ℝ) * Real.log |θ - Real.pi| + g θ := by
  let g : ℝ → ℝ :=
    fun θ : ℝ =>
      Real.log |(
        Function.update
          (fun x : ℝ =>
            (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
          Real.pi
          (Real.cos Real.pi)
          θ)|
  have hlocal :
      ∃ u v : ℝ,
        u < Real.pi ∧ Real.pi < v ∧
        IntervalIntegrable g MeasureTheory.volume u v :=
    real_log_abs_filled_sin_sub_pi_div_sub_pi_local_intervalIntegrable_pi
  have hevent :
      ∀ᶠ θ in 𝓝[≠] Real.pi,
        Real.log |Real.sin θ| =
          ((1 : ℕ) : ℝ) * Real.log |θ - Real.pi| + g θ := by
    have hsmall :
        ∀ᶠ θ in 𝓝[≠] Real.pi, θ ∈ Set.Ioo 0 (2 * Real.pi) :=
      Filter.mem_of_superset
        (nhdsWithin_le_nhds (s := {Real.pi}ᶜ)
          (Ioo_mem_nhds Real.pi_pos
            (lt_of_eq_of_lt
              (Eq.symm (one_mul Real.pi))
              (mul_lt_mul_of_pos_right one_lt_two Real.pi_pos))))
        (fun θ hθ => hθ)
    have hself :
        ∀ᶠ θ in 𝓝[≠] Real.pi, θ ∈ ({Real.pi} : Set ℝ)ᶜ :=
      self_mem_nhdsWithin
    exact
      (hself.and hsmall).mono
        (fun θ hθ =>
          have hθ_ne : θ ≠ Real.pi := hθ.1
          have hθ_small : θ ∈ Set.Ioo 0 (2 * Real.pi) := hθ.2
          have hsin_ne : Real.sin θ ≠ 0 := by
            have hsub_small : θ - Real.pi ∈ Set.Ioo (-Real.pi) Real.pi := by
              constructor
              · have hzero_lt_theta : 0 < θ := hθ_small.1
                exact neg_lt_sub_iff_lt_add.2
                  (lt_add_of_pos_right Real.pi hzero_lt_theta)
              · exact sub_lt_iff_lt_add.2
                  (Eq.subst
                    (motive := fun x : ℝ => θ < x)
                    (two_mul Real.pi)
                    hθ_small.2)
            have hsub_ne : θ - Real.pi ≠ 0 :=
              sub_ne_zero.mpr hθ_ne
            have hzero_iff :
                Real.sin (θ - Real.pi) = 0 ↔ θ - Real.pi = 0 :=
              Real.sin_eq_zero_iff_of_lt_of_lt hsub_small.1 hsub_small.2
            intro hsin_zero
            have hsin_sub_zero : Real.sin (θ - Real.pi) = 0 := by
              exact Eq.trans (Real.sin_sub_pi θ) (neg_eq_zero.mpr hsin_zero)
            exact hsub_ne (hzero_iff.1 hsin_sub_zero)
          have hupdate :
              Function.update
                  (fun x : ℝ => (Real.sin x - Real.sin Real.pi) /
                    (x - Real.pi))
                  Real.pi
                  (Real.cos Real.pi)
                  θ =
                (Real.sin θ - Real.sin Real.pi) / (θ - Real.pi) := by
            exact
              Function.update_noteq hθ_ne (Real.cos Real.pi)
                (fun x : ℝ =>
                  (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
          have hsin_factor :
              Real.sin θ = (θ - Real.pi) *
                ((Real.sin θ - Real.sin Real.pi) / (θ - Real.pi)) := by
            calc
              Real.sin θ = Real.sin θ - Real.sin Real.pi := by
                exact (sub_eq_self.2 Real.sin_pi).symm
              _ = (θ - Real.pi) *
                  ((Real.sin θ - Real.sin Real.pi) / (θ - Real.pi)) := by
                exact (mul_div_cancel₀ (Real.sin θ - Real.sin Real.pi)
                  (sub_ne_zero.mpr hθ_ne)).symm
          have habs_factor :
              |Real.sin θ| =
                |θ - Real.pi| *
                  |(Real.sin θ - Real.sin Real.pi) / (θ - Real.pi)| := by
            calc
              |Real.sin θ| =
                  |(θ - Real.pi) *
                    ((Real.sin θ - Real.sin Real.pi) / (θ - Real.pi))| := by
                exact congrArg abs hsin_factor
              _ = |θ - Real.pi| *
                  |(Real.sin θ - Real.sin Real.pi) / (θ - Real.pi)| := by
                exact abs_mul (θ - Real.pi)
                  ((Real.sin θ - Real.sin Real.pi) / (θ - Real.pi))
          have hθ_abs_ne : |θ - Real.pi| ≠ 0 :=
            abs_ne_zero.mpr (sub_ne_zero.mpr hθ_ne)
          have hratio_ne :
              |(Real.sin θ - Real.sin Real.pi) / (θ - Real.pi)| ≠ 0 := by
            have hnum_ne : Real.sin θ - Real.sin Real.pi ≠ 0 := by
              intro hdiff_zero
              have hsin_eq_pi : Real.sin θ = Real.sin Real.pi :=
                sub_eq_zero.1 hdiff_zero
              exact hsin_ne (Eq.trans hsin_eq_pi Real.sin_pi)
            exact abs_ne_zero.mpr (div_ne_zero hnum_ne (sub_ne_zero.mpr hθ_ne))
          calc
            Real.log |Real.sin θ| =
                Real.log
                  (|θ - Real.pi| *
                    |(Real.sin θ - Real.sin Real.pi) / (θ - Real.pi)|) := by
              exact congrArg Real.log habs_factor
            _ = Real.log |θ - Real.pi| +
                Real.log |(Real.sin θ - Real.sin Real.pi) /
                  (θ - Real.pi)| := by
              exact Real.log_mul hθ_abs_ne hratio_ne
            _ = ((1 : ℕ) : ℝ) * Real.log |θ - Real.pi| + g θ := by
              have hgθ :
                  g θ =
                    Real.log
                      |(Real.sin θ - Real.sin Real.pi) /
                        (θ - Real.pi)| := by
                exact congrArg (fun x : ℝ => Real.log |x|) hupdate
              calc
                Real.log |θ - Real.pi| +
                    Real.log |(Real.sin θ - Real.sin Real.pi) /
                      (θ - Real.pi)| =
                    ((1 : ℕ) : ℝ) * Real.log |θ - Real.pi| +
                      Real.log |(Real.sin θ - Real.sin Real.pi) /
                        (θ - Real.pi)| := by
                  have hone_mul :
                      ((1 : ℕ) : ℝ) * Real.log |θ - Real.pi| =
                        Real.log |θ - Real.pi| := by
                    calc
                      ((1 : ℕ) : ℝ) * Real.log |θ - Real.pi| =
                          (1 : ℝ) * Real.log |θ - Real.pi| := by
                        exact congrArg
                          (fun x : ℝ => x * Real.log |θ - Real.pi|)
                          Nat.cast_one
                      _ = Real.log |θ - Real.pi| :=
                        one_mul (Real.log |θ - Real.pi|)
                  exact congrArg
                    (fun x : ℝ =>
                      x + Real.log
                        |(Real.sin θ - Real.sin Real.pi) / (θ - Real.pi)|)
                    hone_mul.symm
                _ = ((1 : ℕ) : ℝ) * Real.log |θ - Real.pi| + g θ := by
                  exact congrArg
                    (fun x : ℝ => ((1 : ℕ) : ℝ) * Real.log |θ - Real.pi| + x)
                    hgθ.symm)
  exact ⟨1, g, hlocal, hevent⟩

/-- Endpoint local logarithmic models for the finite singular set
`{0, π}` of `log |sin|` on `[0,π]`. -/
theorem real_log_abs_sin_endpoint_localModel
    (θ₀ : ℝ)
    (hθ₀ : θ₀ ∈ ({0, Real.pi} : Set ℝ)) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      (∃ u v : ℝ,
        u < θ₀ ∧ θ₀ < v ∧
        IntervalIntegrable g MeasureTheory.volume u v) ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        Real.log |Real.sin θ| =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  have hcases : θ₀ = 0 ∨ θ₀ = Real.pi :=
    Set.mem_insert_iff.1 hθ₀
  match hcases with
  | Or.inl hzero =>
      exact
        Eq.subst
          (motive := fun x : ℝ =>
            ∃ n : ℕ, ∃ g : ℝ → ℝ,
              (∃ u v : ℝ,
                u < x ∧ x < v ∧
                IntervalIntegrable g MeasureTheory.volume u v) ∧
              ∀ᶠ θ in 𝓝[≠] x,
                Real.log |Real.sin θ| =
                  (n : ℝ) * Real.log |θ - x| + g θ)
          hzero.symm
          real_log_abs_sin_localModel_zero
  | Or.inr hpi =>
      exact
        Eq.subst
          (motive := fun x : ℝ =>
            ∃ n : ℕ, ∃ g : ℝ → ℝ,
              (∃ u v : ℝ,
                u < x ∧ x < v ∧
                IntervalIntegrable g MeasureTheory.volume u v) ∧
              ∀ᶠ θ in 𝓝[≠] x,
                Real.log |Real.sin θ| =
                  (n : ℝ) * Real.log |θ - x| + g θ)
          hpi.symm
          real_log_abs_sin_localModel_pi

/-- Standard interval-integrability of the logarithmic sine kernel on
`[0,π]`.

This is the integrability companion to the classical log-sine integral
`real_integral_log_sin_zero_pi`. -/
theorem real_log_abs_sin_intervalIntegrable_zero_pi :
    IntervalIntegrable
      (fun u : ℝ => Real.log |Real.sin u|)
      MeasureTheory.volume
      0
      Real.pi := by
  exact
    intervalIntegrable_of_finite_log_singularities_on_compact
      (fun u : ℝ => Real.log |Real.sin u|)
      0
      Real.pi
      ({0, Real.pi} : Set ℝ)
      (le_of_lt Real.pi_pos)
      ((Set.finite_singleton Real.pi).insert 0)
      real_log_abs_sin_endpoint_localModel
      real_log_abs_sin_continuousOn_Icc_compl_endpoints

end
end LFunctions
end Boundary
