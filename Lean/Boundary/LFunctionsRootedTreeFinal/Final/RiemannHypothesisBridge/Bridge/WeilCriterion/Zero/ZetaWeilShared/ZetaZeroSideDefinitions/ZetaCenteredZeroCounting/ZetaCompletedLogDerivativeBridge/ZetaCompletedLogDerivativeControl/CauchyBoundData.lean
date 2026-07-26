import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.ConcreteStripBounds

/-!
# Cauchy construction of completed-log-derivative bound data

This file converts explicit Cauchy circle estimates and lower value bounds into
the concrete bound-data packages consumed by the completed-log-derivative owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A continuous nonvanishing factor on a nonempty compact carrier has a
positive uniform norm lower bound. -/
theorem exists_positive_norm_lower_bound_of_isCompact_of_continuousOn
    {s : Set ℂ} {g : ℂ → ℂ}
    (hs : IsCompact s)
    (hs_nonempty : s.Nonempty)
    (hg : ContinuousOn g s)
    (hg_ne : ∀ z : ℂ, z ∈ s → g z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, z ∈ s → δ ≤ ‖g z‖ := by
  obtain ⟨z₀, hz₀, hz₀_min⟩ :=
    hs.exists_isMinOn hs_nonempty hg.norm
  have hz₀_pos : 0 < ‖g z₀‖ :=
    norm_pos_iff.mpr (hg_ne z₀ hz₀)
  refine ⟨‖g z₀‖, hz₀_pos, ?_⟩
  intro z hz
  exact hz₀_min hz

/- A compact sphere supplies the magnitude part of a Cauchy estimate from
continuity alone.  Keeping this construction here makes the later factor
owners independent of ad hoc supremum witnesses. -/
theorem exists_norm_upper_bound_of_isCompact_of_continuousOn
    {s : Set ℂ} {g : ℂ → ℂ}
    (hs : IsCompact s)
    (hg : ContinuousOn g s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℂ, z ∈ s → ‖g z‖ ≤ A := by
  obtain ⟨rawBound, hrawBound⟩ :=
    hs.bddAbove_image hg.norm
  let A : ℝ := max rawBound 0
  refine ⟨A, le_max_right rawBound 0, ?_⟩
  intro z hz
  have himage : ‖g z‖ ∈ (fun w : ℂ => ‖g w‖) '' s :=
    Exists.intro z (And.intro hz rfl)
  have hraw : ‖g z‖ ≤ rawBound := hrawBound himage
  exact le_trans hraw (le_max_left rawBound 0)

theorem exists_inverseGamma_norm_upper_bound_of_isCompact_of_continuousOn
    {s : Set ℂ}
    (hs : IsCompact s)
    (hg : ContinuousOn (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) s) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ z : ℂ, z ∈ s → ‖(Complex.Gammaℝ z)⁻¹‖ ≤ A :=
  exists_norm_upper_bound_of_isCompact_of_continuousOn hs hg

theorem exists_inverseGamma_positive_norm_lower_bound_of_isCompact_of_continuousOn
    {s : Set ℂ}
    (hs : IsCompact s)
    (hs_nonempty : s.Nonempty)
    (hg : ContinuousOn (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) s)
    (hg_ne : ∀ z : ℂ, z ∈ s → (Complex.Gammaℝ z)⁻¹ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, z ∈ s → δ ≤ ‖(Complex.Gammaℝ z)⁻¹‖ :=
  exists_positive_norm_lower_bound_of_isCompact_of_continuousOn
    hs hs_nonempty hg hg_ne

/-- The zero-excised strip owner supplies the nonvanishing premise needed to
turn compactness and continuity into the Cauchy value lower bound. -/
theorem exists_zetaSideFactor_positive_lower_bound_of_compact_carrier
    {a b : ℝ}
    (E : CompletedZetaZeroExcisedStrip a b)
    (hcompact : IsCompact E.carrier)
    (hcarrier_nonempty : E.carrier.Nonempty)
    (hcontinuous : ContinuousOn zetaSideFactor E.carrier) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, z ∈ E.carrier → δ ≤ ‖zetaSideFactor z‖ :=
  exists_positive_norm_lower_bound_of_isCompact_of_continuousOn
    hcompact
    hcarrier_nonempty
    hcontinuous
    E.zeta_ne_zero

theorem zetaSideNegLogDeriv_norm_eq_deriv_quotient_norm_owner
    (z : ℂ) :
    ‖zetaSideNegLogDeriv z‖ =
      ‖deriv zetaSideFactor z / zetaSideFactor z‖ := by
  have hdef :
      ‖zetaSideNegLogDeriv z‖ =
        ‖-deriv zetaSideFactor z / zetaSideFactor z‖ :=
    congrArg (fun u : ℂ => ‖u‖) (zetaSideNegLogDeriv_eq_def z)
  have hneg :
      ‖-deriv zetaSideFactor z / zetaSideFactor z‖ =
        ‖deriv zetaSideFactor z / zetaSideFactor z‖ :=
    norm_neg_div_eq_norm_div
      (deriv zetaSideFactor z)
      (zetaSideFactor z)
  exact Eq.trans hdef hneg

theorem zetaSideFactor_cauchy_log_derivative_bound_owner
    (z : ℂ) (N : ℕ) (radius amplitude valueLower : ℝ)
    (radius_pos : 0 < radius)
    (diffCont :
      DiffContOnCl ℂ zetaSideFactor (Metric.ball z radius))
    (sphere_bound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z radius →
        ‖zetaSideFactor w‖ ≤ amplitude * (1 + ‖z.im‖) ^ N)
    (valueLower_pos : 0 < valueLower)
    (value_lower : valueLower ≤ ‖zetaSideFactor z‖) :
    ‖deriv zetaSideFactor z / zetaSideFactor z‖ ≤
      ((amplitude / radius) / valueLower) * (1 + ‖z.im‖) ^ N :=
  cauchy_logDeriv_polynomial_norm_le_of_sphere_bound
    (f := zetaSideFactor)
    (z := z)
    (R := radius)
    (A := amplitude)
    (δ := valueLower)
    (q := (1 + ‖z.im‖) ^ N)
    radius_pos
    diffCont
    sphere_bound
    valueLower_pos
    value_lower

theorem cauchy_log_derivative_bound_of_compact_sphere_owner
    {z : ℂ} (radius : ℝ) (valueLower : ℝ)
    (radius_pos : 0 < radius)
    (diffCont :
      DiffContOnCl ℂ zetaSideFactor (Metric.ball z radius))
    (sphere_continuous :
      ContinuousOn zetaSideFactor (Metric.sphere z radius))
    (valueLower_pos : 0 < valueLower)
    (value_lower : valueLower ≤ ‖zetaSideFactor z‖) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv zetaSideFactor z / zetaSideFactor z‖ ≤ B := by
  obtain ⟨rawBound, rawBound_nonneg, rawBound_spec⟩ :=
    exists_norm_upper_bound_of_isCompact_of_continuousOn
      isCompact_sphere sphere_continuous
  let amplitude : ℝ := rawBound + 1
  have amplitude_pos : 0 < amplitude :=
    add_pos_of_nonneg_of_pos rawBound_nonneg zero_lt_one
  have sphere_bound :
      ∀ w : ℂ, w ∈ Metric.sphere z radius →
        ‖zetaSideFactor w‖ ≤ amplitude * (1 + ‖z.im‖) ^ (0 : ℕ) := by
    intro w hw
    have hraw : ‖zetaSideFactor w‖ ≤ rawBound :=
      rawBound_spec w hw
    have hinc : rawBound ≤ amplitude :=
      le_add_of_nonneg_right zero_le_one
    have hbase : ‖zetaSideFactor w‖ ≤ amplitude :=
      le_trans hraw hinc
    have hpow : (1 + ‖z.im‖) ^ (0 : ℕ) = 1 :=
      pow_zero (1 + ‖z.im‖)
    have hshape : amplitude * (1 + ‖z.im‖) ^ (0 : ℕ) = amplitude :=
      Eq.trans
        (congrArg (fun q : ℝ => amplitude * q) hpow)
        (mul_one amplitude)
    hbase.trans_eq hshape
  have hbound :=
    zetaSideFactor_cauchy_log_derivative_bound_owner
      z 0 radius amplitude valueLower radius_pos diffCont sphere_bound
      valueLower_pos value_lower
  let B : ℝ := (amplitude / radius) / valueLower
  have B_pos : 0 < B :=
    div_pos (div_pos amplitude_pos radius_pos) valueLower_pos
  refine ⟨B, B_pos, ?_⟩
  exact hbound

theorem cauchy_log_derivative_bound_of_diffContOnCl_owner
    {z : ℂ} (radius : ℝ) (valueLower : ℝ)
    (radius_pos : 0 < radius)
    (diffCont :
      DiffContOnCl ℂ zetaSideFactor (Metric.ball z radius))
    (valueLower_pos : 0 < valueLower)
    (value_lower : valueLower ≤ ‖zetaSideFactor z‖) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv zetaSideFactor z / zetaSideFactor z‖ ≤ B := by
  have hcontinuous_closure :
      ContinuousOn zetaSideFactor (closure (Metric.ball z radius)) :=
    diffCont.continuousOn
  have hsphere_subset :
      Metric.sphere z radius ⊆ closure (Metric.ball z radius) := by
    intro w hw
    have hclosed : w ∈ Metric.closedBall z radius :=
      Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hw))
    exact Eq.subst
      (motive := fun s : Set ℂ => w ∈ s)
      (closure_ball z radius_pos.ne').symm
      hclosed
  have hsphere_continuous :
      ContinuousOn zetaSideFactor (Metric.sphere z radius) :=
    hcontinuous_closure.mono hsphere_subset
  exact cauchy_log_derivative_bound_of_compact_sphere_owner
    radius valueLower radius_pos diffCont hsphere_continuous
    valueLower_pos value_lower

theorem zetaSideFactor_cauchy_log_derivative_bound_of_diffContOnCl_of_ne_zero_on_closure
    {z : ℂ} (radius : ℝ)
    (radius_pos : 0 < radius)
    (diffCont :
      DiffContOnCl ℂ zetaSideFactor (Metric.ball z radius))
    (ne_zero_on_closure :
      ∀ w : ℂ, w ∈ closure (Metric.ball z radius) → zetaSideFactor w ≠ 0) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv zetaSideFactor z / zetaSideFactor z‖ ≤ B := by
  have hcompact : IsCompact (closure (Metric.ball z radius)) := by
    exact Eq.subst
      (motive := fun s : Set ℂ => IsCompact s)
      (closure_ball z radius_pos.ne').symm
      Metric.isCompact_closedBall
  have hnonempty : (closure (Metric.ball z radius)).Nonempty := by
    exact ⟨z, subset_closure (Metric.mem_ball_self radius_pos)⟩
  have hcontinuous_closure :
      ContinuousOn zetaSideFactor (closure (Metric.ball z radius)) :=
    diffCont.continuousOn
  obtain ⟨valueLower, valueLower_pos, valueLower_bound⟩ :=
    exists_positive_norm_lower_bound_of_isCompact_of_continuousOn
      hcompact hnonempty hcontinuous_closure ne_zero_on_closure
  have hsphere_continuous :
      ContinuousOn zetaSideFactor (Metric.sphere z radius) := by
    apply hcontinuous_closure.mono
    intro w hw
    have hclosed : w ∈ Metric.closedBall z radius :=
      Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hw))
    exact Eq.subst
      (motive := fun s : Set ℂ => w ∈ s)
      (closure_ball z radius_pos.ne').symm hclosed
  obtain ⟨rawAmplitude, rawAmplitude_nonneg, rawAmplitude_bound⟩ :=
    exists_norm_upper_bound_of_isCompact_of_continuousOn
      Metric.isCompact_sphere hsphere_continuous
  let amplitude : ℝ := rawAmplitude + 1
  have amplitude_pos : 0 < amplitude := by
    exact lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_left rawAmplitude_nonneg)
  have sphere_bound :
      ∀ w : ℂ, w ∈ Metric.sphere z radius →
        ‖zetaSideFactor w‖ ≤ amplitude := by
    intro w hw
    exact (rawAmplitude_bound w hw).trans
      (le_add_of_nonneg_right zero_le_one)
  exact zetaSideFactor_cauchy_log_derivative_bound_owner
    z 0 radius amplitude valueLower radius_pos diffCont sphere_bound
    valueLower_pos
    (valueLower_bound z (subset_closure (Metric.mem_ball_self radius_pos)))

theorem zetaSideFactor_cauchy_log_derivative_bound_of_closedBall_nonzero
    {z : ℂ} (radius : ℝ)
    (radius_pos : 0 < radius)
    (diffCont :
      DiffContOnCl ℂ zetaSideFactor (Metric.ball z radius))
    (ne_zero_on_closedBall :
      ∀ w : ℂ, w ∈ Metric.closedBall z radius → zetaSideFactor w ≠ 0) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv zetaSideFactor z / zetaSideFactor z‖ ≤ B := by
  apply zetaSideFactor_cauchy_log_derivative_bound_of_diffContOnCl_of_ne_zero_on_closure
    radius radius_pos diffCont
  intro w hw
  exact ne_zero_on_closedBall w (Eq.subst
    (motive := fun s : Set ℂ => w ∈ s)
    (closure_ball z radius_pos.ne').symm hw)

def CompletedZetaZeroExcisedStrip.ZetaSideBoundData.ofCauchyLogDerivative
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b)
    (separated : E.HasPositiveSingularSeparation)
    (radius amplitude valueLower : ℕ → ℝ)
    (radius_pos : ∀ N : ℕ, 0 < radius N)
    (amplitude_pos : ∀ N : ℕ, 0 < amplitude N)
    (valueLower_pos : ∀ N : ℕ, 0 < valueLower N)
    (diffCont :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        DiffContOnCl ℂ zetaSideFactor (Metric.ball z (radius N)))
    (sphere_bound :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (radius N) →
          ‖zetaSideFactor w‖ ≤
            amplitude N * (1 + ‖z.im‖) ^ N)
    (value_lower :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        valueLower N ≤ ‖zetaSideFactor z‖) :
    CompletedZetaZeroExcisedStrip.ZetaSideBoundData E :=
  { separated := separated
    constant := fun N : ℕ => (amplitude N / radius N) / valueLower N
    constant_pos :=
      fun N : ℕ =>
        div_pos
          (div_pos (amplitude_pos N) (radius_pos N))
          (valueLower_pos N)
    bound :=
      fun N z hz =>
        let q : ℝ := (1 + ‖z.im‖) ^ N
        let hnorm :
            ‖zetaSideNegLogDeriv z‖ =
              ‖deriv zetaSideFactor z / zetaSideFactor z‖ :=
          zetaSideNegLogDeriv_norm_eq_deriv_quotient_norm_owner z
        Eq.subst
          (motive := fun u : ℝ =>
            u ≤ ((amplitude N / radius N) / valueLower N) * q)
          hnorm.symm
          (zetaSideFactor_cauchy_log_derivative_bound_owner
            z N (radius N) (amplitude N) (valueLower N)
            (radius_pos N)
            (diffCont N z hz)
            (sphere_bound N z hz)
            (valueLower_pos N)
            (value_lower N z hz)) }

theorem inverseGamma_cauchy_log_derivative_bound_owner
    (z : ℂ) (N : ℕ) (radius amplitude valueLower : ℝ)
    (radius_pos : 0 < radius)
    (diffCont :
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball z radius))
    (sphere_bound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z radius →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ amplitude * (1 + ‖z.im‖) ^ N)
    (valueLower_pos : 0 < valueLower)
    (value_lower : valueLower ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
        (Complex.Gammaℝ z)⁻¹‖ ≤
      ((amplitude / radius) / valueLower) * (1 + ‖z.im‖) ^ N :=
  cauchy_logDeriv_polynomial_norm_le_of_sphere_bound
    (f := fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
    (z := z)
    (R := radius)
    (A := amplitude)
    (δ := valueLower)
    (q := (1 + ‖z.im‖) ^ N)
    radius_pos
    diffCont
    sphere_bound
    valueLower_pos
    value_lower

theorem inverseGamma_cauchy_log_derivative_bound_of_diffContOnCl_owner
    {z : ℂ} (radius valueLower : ℝ)
    (radius_pos : 0 < radius)
    (diffCont :
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball z radius))
    (valueLower_pos : 0 < valueLower)
    (value_lower : valueLower ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤ B := by
  have hcontinuous_closure :
      ContinuousOn (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (closure (Metric.ball z radius)) :=
    diffCont.continuousOn
  have hsphere_subset :
      Metric.sphere z radius ⊆ closure (Metric.ball z radius) := by
    intro w hw
    have hclosed : w ∈ Metric.closedBall z radius :=
      Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hw))
    exact Eq.subst
      (motive := fun s : Set ℂ => w ∈ s)
      (closure_ball z radius_pos.ne').symm
      hclosed
  have hsphere_continuous :
      ContinuousOn (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.sphere z radius) :=
    hcontinuous_closure.mono hsphere_subset
  obtain ⟨rawBound, rawBound_nonneg, rawBound_spec⟩ :=
    exists_inverseGamma_norm_upper_bound_of_isCompact_of_continuousOn
      isCompact_sphere hsphere_continuous
  let amplitude : ℝ := rawBound + 1
  have amplitude_pos : 0 < amplitude :=
    add_pos_of_nonneg_of_pos rawBound_nonneg zero_lt_one
  have sphere_bound :
      ∀ w : ℂ, w ∈ Metric.sphere z radius →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          amplitude * (1 + ‖z.im‖) ^ (0 : ℕ) := by
    intro w hw
    have hraw : ‖(Complex.Gammaℝ w)⁻¹‖ ≤ rawBound :=
      rawBound_spec w hw
    have hbase : ‖(Complex.Gammaℝ w)⁻¹‖ ≤ amplitude :=
      le_trans hraw (le_add_of_nonneg_right zero_le_one)
    have hpow : (1 + ‖z.im‖) ^ (0 : ℕ) = 1 :=
      pow_zero (1 + ‖z.im‖)
    have hshape : amplitude * (1 + ‖z.im‖) ^ (0 : ℕ) = amplitude :=
      Eq.trans
        (congrArg (fun q : ℝ => amplitude * q) hpow)
        (mul_one amplitude)
    hbase.trans_eq hshape
  have hbound :=
    inverseGamma_cauchy_log_derivative_bound_owner
      z 0 radius amplitude valueLower radius_pos diffCont sphere_bound
      valueLower_pos value_lower
  let B : ℝ := (amplitude / radius) / valueLower
  have B_pos : 0 < B :=
    div_pos (div_pos amplitude_pos radius_pos) valueLower_pos
  refine ⟨B, B_pos, ?_⟩
  exact hbound

theorem inverseGamma_cauchy_log_derivative_bound_of_diffContOnCl_of_ne_zero_on_closure
    {z : ℂ} (radius : ℝ)
    (radius_pos : 0 < radius)
    (diffCont :
      DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball z radius))
    (ne_zero_on_closure :
      ∀ w : ℂ, w ∈ closure (Metric.ball z radius) →
        (Complex.Gammaℝ w)⁻¹ ≠ 0) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤ B := by
  have hcompact : IsCompact (closure (Metric.ball z radius)) := by
    exact Eq.subst
      (motive := fun s : Set ℂ => IsCompact s)
      (closure_ball z radius_pos.ne').symm
      Metric.isCompact_closedBall
  have hnonempty : (closure (Metric.ball z radius)).Nonempty := by
    exact ⟨z, subset_closure (Metric.mem_ball_self radius_pos)⟩
  have hcontinuous_closure :
      ContinuousOn (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (closure (Metric.ball z radius)) :=
    diffCont.continuousOn
  obtain ⟨valueLower, valueLower_pos, valueLower_bound⟩ :=
    exists_positive_norm_lower_bound_of_isCompact_of_continuousOn
      hcompact hnonempty hcontinuous_closure ne_zero_on_closure
  have hsphere_continuous :
      ContinuousOn (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.sphere z radius) := by
    apply hcontinuous_closure.mono
    intro w hw
    have hclosed : w ∈ Metric.closedBall z radius :=
      Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hw))
    exact Eq.subst
      (motive := fun s : Set ℂ => w ∈ s)
      (closure_ball z radius_pos.ne').symm hclosed
  obtain ⟨rawAmplitude, rawAmplitude_nonneg, rawAmplitude_bound⟩ :=
    exists_inverseGamma_norm_upper_bound_of_isCompact_of_continuousOn
      Metric.isCompact_sphere hsphere_continuous
  let amplitude : ℝ := rawAmplitude + 1
  have amplitude_pos : 0 < amplitude := by
    exact lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_left rawAmplitude_nonneg)
  have sphere_bound :
      ∀ w : ℂ, w ∈ Metric.sphere z radius →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ amplitude := by
    intro w hw
    exact (rawAmplitude_bound w hw).trans
      (le_add_of_nonneg_right zero_le_one)
  exact inverseGamma_cauchy_log_derivative_bound_owner
    z 0 radius amplitude valueLower radius_pos diffCont sphere_bound
    valueLower_pos
    (valueLower_bound z (subset_closure (Metric.mem_ball_self radius_pos)))

theorem inverseGamma_cauchy_log_derivative_bound_of_closedBall_nonzero
    {z : ℂ} (radius : ℝ)
    (radius_pos : 0 < radius)
    (diffCont :
      DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball z radius))
    (ne_zero_on_closedBall :
      ∀ w : ℂ, w ∈ Metric.closedBall z radius →
        (Complex.Gammaℝ w)⁻¹ ≠ 0) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤ B := by
  apply inverseGamma_cauchy_log_derivative_bound_of_diffContOnCl_of_ne_zero_on_closure
    radius radius_pos diffCont
  intro w hw
  exact ne_zero_on_closedBall w (Eq.subst
    (motive := fun s : Set ℂ => w ∈ s)
    (closure_ball z radius_pos.ne').symm hw)

theorem inverseGamma_ne_zero_on_closedBall_of_center_re_gt_radius
    {z : ℂ} (radius : ℝ)
    (center_re_gt_radius : radius < z.re) :
    ∀ w : ℂ, w ∈ Metric.closedBall z radius →
      (Complex.Gammaℝ w)⁻¹ ≠ 0 := by
  intro w hw
  have hdist : ‖w - z‖ ≤ radius := by
    calc
      ‖w - z‖ = dist w z := (dist_eq_norm w z).symm
      _ = dist z w := dist_comm w z
      _ ≤ radius := Metric.mem_closedBall.mp hw
  have hreal_norm : ‖(w - z).re‖ ≤ radius :=
    (RCLike.norm_re_le_norm (w - z)).trans hdist
  have hreal_lower : -radius ≤ (w - z).re :=
    neg_le_of_abs_le hreal_norm
  have hw_re_pos : 0 < w.re := by
    have hcenter : z.re - radius ≤ w.re := by
      calc
        z.re - radius = z.re + (-radius) := sub_eq_add_neg z.re radius
        _ ≤ z.re + (w - z).re := add_le_add_left hreal_lower z.re
        _ = w.re := by
          exact add_sub_cancel_left w.re z.re
    exact lt_of_lt_of_le (sub_pos.mpr center_re_gt_radius) hcenter
  exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos w hw_re_pos)

theorem inverseGamma_cauchy_log_derivative_bound_of_center_re_gt_radius
    {z : ℂ} (radius : ℝ)
    (radius_pos : 0 < radius)
    (center_re_gt_radius : radius < z.re) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤ B := by
  apply inverseGamma_cauchy_log_derivative_bound_of_closedBall_nonzero
    radius radius_pos
    (Differentiable.diffContOnCl Complex.differentiable_Gammaℝ_inv)
  exact inverseGamma_ne_zero_on_closedBall_of_center_re_gt_radius
    center_re_gt_radius

theorem inverseGamma_cauchy_log_derivative_bound_of_re_pos
    {z : ℂ} (hz : 0 < z.re) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤ B := by
  let radius : ℝ := z.re / 2
  have hradius_pos : 0 < radius := by
    exact div_pos hz zero_lt_two
  have hradius_lt : radius < z.re := by
    apply (div_lt_iff₀ zero_lt_two).2
    calc
      z.re = z.re * 1 := (mul_one z.re).symm
      _ < z.re * 2 := mul_lt_mul_of_pos_left one_lt_two hz
  exact inverseGamma_cauchy_log_derivative_bound_of_center_re_gt_radius
    radius hradius_pos hradius_lt

theorem inverseGamma_cauchy_log_derivative_bound_of_fixedRealPartLine
    {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (σ + t * Complex.I) /
          (Complex.Gammaℝ (σ + t * Complex.I))⁻¹‖ ≤ B := by
  have hz : 0 < (σ + t * Complex.I).re :=
    Complex.fixedRealPartLine_re_pos hσ
  exact inverseGamma_cauchy_log_derivative_bound_of_re_pos
    (z := σ + t * Complex.I) hz

def CompletedZetaZeroExcisedStrip.InverseGammaBoundData.ofCauchyLogDerivative
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b)
    (separated : E.HasPositiveSingularSeparation)
    (radius amplitude valueLower : ℕ → ℝ)
    (radius_pos : ∀ N : ℕ, 0 < radius N)
    (amplitude_pos : ∀ N : ℕ, 0 < amplitude N)
    (valueLower_pos : ∀ N : ℕ, 0 < valueLower N)
    (diffCont :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (radius N)))
    (sphere_bound :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (radius N) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            amplitude N * (1 + ‖z.im‖) ^ N)
    (value_lower :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        valueLower N ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    CompletedZetaZeroExcisedStrip.InverseGammaBoundData E :=
  { separated := separated
    constant := fun N : ℕ => (amplitude N / radius N) / valueLower N
    constant_pos :=
      fun N : ℕ =>
        div_pos
          (div_pos (amplitude_pos N) (radius_pos N))
          (valueLower_pos N)
    bound :=
      fun N z hz =>
        inverseGamma_cauchy_log_derivative_bound_owner
          z N (radius N) (amplitude N) (valueLower N)
          (radius_pos N)
          (diffCont N z hz)
          (sphere_bound N z hz)
          (valueLower_pos N)
          (value_lower N z hz) }

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
