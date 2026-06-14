import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Binet

/-!
# Sectorial estimates from Binet

This file owns the sectorial remainder estimate extracted from the
Binet-kernel majorant package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Trivial real nonnegativity of `2`, named to keep arithmetic side
conditions out of the Binet estimates. -/
theorem Real.zero_le_two_real : (0 : ℝ) ≤ 2 :=
  zero_le_two

/-- Trivial real positivity of `8`, named to keep arithmetic side conditions
out of the Binet estimates. -/
theorem Real.zero_lt_eight_real : (0 : ℝ) < 8 := by
  linarith [zero_lt_one]

/-- Rewriting the lower split kernel majorant into constant-times-majorant
form. -/
theorem Real.two_mul_div_norm_div_exp_sub_one_eq
    (t : ℝ)
    (r : ℝ) :
    (2 * (t / r)) /
        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
      (2 / r) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  ring

/-- Doubling a constant-times-integral expression gives the Binet split
constant. -/
theorem Real.two_mul_two_div_mul_eq_four_mul_div
    (J r : ℝ) :
    2 * ((2 / r) * J) = 4 * J / r := by
  ring

/-- The triangle-assembled split constant is `8`. -/
theorem Real.four_div_add_four_div_eq_eight_div
    (J r : ℝ) :
    4 * J / r + 4 * J / r = 8 * J / r := by
  ring

/-- The cutoff conversion arithmetic for turning a bounded tail estimate into
a linear estimate. -/
theorem Real.two_mul_div_mul_half_eq
    {B r : ℝ}
    (hr : r ≠ 0) :
    (2 * B / r) * (r / 2) = B := by
  field_simp [hr]

/-- Distributing the leading Binet factor over a split complex integral. -/
theorem Complex.two_mul_add_eq_add_two_mul
    (a b : ℂ) :
    2 * (a + b) = 2 * a + 2 * b := by
  ring

/-- Algebraic normalization of the first arctangent branch denominator. -/
theorem Complex.one_sub_real_div_mul_I_eq
    (w : ℂ)
    (t : ℝ) :
    1 - ((t : ℂ) / w) * Complex.I =
      (w - (t : ℂ) * Complex.I) / w := by
  by_cases hw : w = 0
  · subst w
    simp
  · field_simp [hw]
    ring

/-- Algebraic normalization of the second arctangent branch denominator. -/
theorem Complex.one_add_real_div_mul_I_eq
    (w : ℂ)
    (t : ℝ) :
    1 + ((t : ℂ) / w) * Complex.I =
      (w + (t : ℂ) * Complex.I) / w := by
  by_cases hw : w = 0
  · subst w
    simp
  · field_simp [hw]
    ring

/-- The first normalized branch denominator is bounded below by the real part
of the fixed open-half-plane point. -/
theorem Complex.one_sub_real_div_mul_I_norm_lower
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    w.re / ‖w‖ ≤ ‖1 - ((t : ℂ) / w) * Complex.I‖ := by
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have hre_nonneg : 0 ≤ (w - (t : ℂ) * Complex.I).re := by
    simpa using le_of_lt hw_re_pos
  have hre_abs_eq :
      |(w - (t : ℂ) * Complex.I).re| = w.re := by
    simp [Complex.sub_re, Complex.mul_re, hre_nonneg]
  have hre_le_norm :
      w.re ≤ ‖w - (t : ℂ) * Complex.I‖ := by
    calc
      w.re = |(w - (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
      _ ≤ ‖w - (t : ℂ) * Complex.I‖ := by
        simpa [Complex.normSq, norm_eq_abs] using
          Complex.abs_re_le_abs (w - (t : ℂ) * Complex.I)
  calc
    w.re / ‖w‖ ≤ ‖w - (t : ℂ) * Complex.I‖ / ‖w‖ :=
      div_le_div_of_nonneg_right hre_le_norm (le_of_lt hw_norm_pos)
    _ = ‖(w - (t : ℂ) * Complex.I) / w‖ := by
      rw [norm_div]
    _ = ‖1 - ((t : ℂ) / w) * Complex.I‖ := by
      rw [Complex.one_sub_real_div_mul_I_eq]

/-- The second normalized branch denominator is bounded below by the real part
of the fixed open-half-plane point. -/
theorem Complex.one_add_real_div_mul_I_norm_lower
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    w.re / ‖w‖ ≤ ‖1 + ((t : ℂ) / w) * Complex.I‖ := by
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have hre_nonneg : 0 ≤ (w + (t : ℂ) * Complex.I).re := by
    simpa using le_of_lt hw_re_pos
  have hre_abs_eq :
      |(w + (t : ℂ) * Complex.I).re| = w.re := by
    simp [Complex.add_re, Complex.mul_re, hre_nonneg]
  have hre_le_norm :
      w.re ≤ ‖w + (t : ℂ) * Complex.I‖ := by
    calc
      w.re = |(w + (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
      _ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
        simpa [Complex.normSq, norm_eq_abs] using
          Complex.abs_re_le_abs (w + (t : ℂ) * Complex.I)
  calc
    w.re / ‖w‖ ≤ ‖w + (t : ℂ) * Complex.I‖ / ‖w‖ :=
      div_le_div_of_nonneg_right hre_le_norm (le_of_lt hw_norm_pos)
    _ = ‖(w + (t : ℂ) * Complex.I) / w‖ := by
      rw [norm_div]
    _ = ‖1 + ((t : ℂ) / w) * Complex.I‖ := by
      rw [Complex.one_add_real_div_mul_I_eq]

/-- Along the fixed open-half-plane ray `t / w`, the principal arctangent is
uniformly separated from the arctangent branch singularities on the upper split
interval. -/
theorem Complex.binetSecondFormula_arctan_tail_branch_separation
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          δ ≤ ‖1 - ((t : ℂ) / w) * Complex.I‖ ∧
          δ ≤ ‖1 + ((t : ℂ) / w) * Complex.I‖ := by
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  refine ⟨w.re / ‖w‖, div_pos hw_re_pos hw_norm_pos, ?_⟩
  intro t ht
  exact
    ⟨Complex.one_sub_real_div_mul_I_norm_lower hw_re_pos t,
      Complex.one_add_real_div_mul_I_norm_lower hw_re_pos t⟩

/-- The principal logarithm is bounded by the absolute logarithm of the norm
plus the universal argument bound. -/
theorem Complex.log_norm_le_abs_log_norm_add_pi
    (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  calc
    ‖Complex.log z‖ = Complex.abs (Complex.log z) := norm_eq_abs _
    _ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
      Complex.abs_le_abs_re_add_abs_im (Complex.log z)
    _ = |Real.log ‖z‖| + |Complex.arg z| := by
      rw [Complex.log_re, Complex.log_im, norm_eq_abs]
    _ ≤ |Real.log ‖z‖| + Real.pi :=
      add_le_add_left (Complex.abs_arg_le_pi z) _

/-- A positive two-sided bound for a real argument gives a finite bound for
the absolute value of its logarithm. -/
theorem Real.abs_log_le_max_abs_log_of_bounds
    {m M x : ℝ}
    (hm_pos : 0 < m)
    (hmM : m ≤ M)
    (hmx : m ≤ x)
    (hxM : x ≤ M) :
    |Real.log x| ≤
      max |Real.log m| |Real.log M| := by
  have hx_pos : 0 < x := lt_of_lt_of_le hm_pos hmx
  have hM_pos : 0 < M := lt_of_lt_of_le hm_pos hmM
  have hlog_lower : Real.log m ≤ Real.log x :=
    Real.log_le_log hm_pos hmx
  have hlog_upper : Real.log x ≤ Real.log M :=
    Real.log_le_log hx_pos hxM
  have hleft :
      -(max |Real.log m| |Real.log M|) ≤ Real.log x := by
    have hneg_abs_m : -|Real.log m| ≤ Real.log m :=
      neg_abs_le (Real.log m)
    have hmax_left : |Real.log m| ≤ max |Real.log m| |Real.log M| :=
      le_max_left _ _
    exact
      le_trans (neg_le_neg hmax_left)
        (le_trans hneg_abs_m hlog_lower)
  have hright :
      Real.log x ≤ max |Real.log m| |Real.log M| := by
    have hlogM_le_abs : Real.log M ≤ |Real.log M| :=
      le_abs_self (Real.log M)
    have hmax_right : |Real.log M| ≤ max |Real.log m| |Real.log M| :=
      le_max_right _ _
    exact le_trans hlog_upper (le_trans hlogM_le_abs hmax_right)
  exact abs_le.mpr ⟨hleft, hright⟩

/-- A nonzero complex number whose norm has positive two-sided real bounds
has bounded principal logarithm. -/
theorem Complex.log_norm_le_of_norm_bounds
    {m M : ℝ}
    (hm_pos : 0 < m)
    (hmM : m ≤ M)
    {z : ℂ}
    (hmz : m ≤ ‖z‖)
    (hzM : ‖z‖ ≤ M) :
    ‖Complex.log z‖ ≤
      max |Real.log m| |Real.log M| + Real.pi := by
  have hlog :
      |Real.log ‖z‖| ≤ max |Real.log m| |Real.log M| :=
    Real.abs_log_le_max_abs_log_of_bounds
      hm_pos hmM hmz hzM
  calc
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi :=
      Complex.log_norm_le_abs_log_norm_add_pi z
    _ ≤ max |Real.log m| |Real.log M| + Real.pi :=
      add_le_add_right hlog _

/-- On the fixed upper split interval the Möbius ratio entering the arctangent
has norm bounded above and below by positive constants depending only on `w`.

This is the real-variable tail root: after rewriting the ratio as
`(w + tI) / (w - tI)`, it is a two-sided bound for a rational expression in
`t` on `t > ‖w‖ / 2`. -/
theorem Complex.binetSecondFormula_arctan_tail_ratio_norm_bounds
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ m M : ℝ,
      0 < m ∧
      m ≤ M ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          m ≤
            ‖(1 + ((t : ℂ) / w) * Complex.I) /
              (1 - ((t : ℂ) / w) * Complex.I)‖ ∧
          ‖(1 + ((t : ℂ) / w) * Complex.I) /
              (1 - ((t : ℂ) / w) * Complex.I)‖ ≤ M := by
  sorry

/-- Fixed-ray branch separation gives a uniform bound for the principal
arctangent on the upper split interval. -/
theorem Complex.binetSecondFormula_arctan_tail_log_ratio_bounded
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ L : ℝ,
      0 ≤ L ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.log
            ((1 + ((t : ℂ) / w) * Complex.I) /
              (1 - ((t : ℂ) / w) * Complex.I))‖ ≤ L := by
  rcases
      Complex.binetSecondFormula_arctan_tail_ratio_norm_bounds
        hw_re_pos with
    ⟨m, M, hm_pos, hmM, hbounds⟩
  refine ⟨max |Real.log m| |Real.log M| + Real.pi, ?_, ?_⟩
  · exact add_nonneg (le_max_of_le_left (abs_nonneg _)) Real.pi_pos.le
  · intro t ht_tail
    rcases hbounds t ht_tail with ⟨hlower, hupper⟩
    exact
      Complex.log_norm_le_of_norm_bounds
        hm_pos hmM hlower hupper

/-- A uniform logarithm bound for the separated arctangent ratio bounds the
principal arctangent itself. -/
theorem Complex.binetSecondFormula_arctan_tail_bounded_of_log_ratio_bound
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hlog :
      ∃ L : ℝ,
        0 ≤ L ∧
        ∀ t : ℝ,
          t ∈ Set.Ioi (‖w‖ / 2) →
            ‖Complex.log
              ((1 + ((t : ℂ) / w) * Complex.I) /
                (1 - ((t : ℂ) / w) * Complex.I))‖ ≤ L) :
    ∃ B : ℝ,
      0 ≤ B ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤ B := by
  rcases hlog with ⟨L, hL_nonneg, hL⟩
  refine ⟨L, hL_nonneg, ?_⟩
  intro t ht_tail
  let z : ℂ := (t : ℂ) / w
  have hfactor_norm_le_one : ‖(-Complex.I / 2 : ℂ)‖ ≤ (1 : ℝ) := by
    have hfactor_norm : ‖(-Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
      simp [norm_div, Complex.normSq]
    calc
      ‖(-Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := hfactor_norm
      _ ≤ 1 := by norm_num
  have hmul :
      ‖(-Complex.I / 2 : ℂ) *
          Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ ≤
        ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := by
    calc
      ‖(-Complex.I / 2 : ℂ) *
          Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ ≤
          ‖(-Complex.I / 2 : ℂ)‖ *
            ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ :=
        norm_mul_le _ _
      _ ≤ 1 *
            ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ :=
        mul_le_mul_of_nonneg_right hfactor_norm_le_one (norm_nonneg _)
      _ = ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := by
        rw [one_mul]
  calc
    ‖Complex.arctan ((t : ℂ) / w)‖ =
        ‖(-Complex.I / 2 : ℂ) *
          Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := by
      simp [Complex.arctan, z]
    _ ≤ ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := hmul
    _ ≤ L := hL t ht_tail

/-- Fixed-ray branch separation gives a uniform bound for the principal
arctangent on the upper split interval. -/
theorem Complex.binetSecondFormula_arctan_tail_bounded_of_branch_separation
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ B : ℝ,
      0 ≤ B ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤ B := by
  exact
    Complex.binetSecondFormula_arctan_tail_bounded_of_log_ratio_bound
      hw_re_pos
      (Complex.binetSecondFormula_arctan_tail_log_ratio_bounded
        hw_re_pos)

/-- A uniform arctangent bound on the upper split interval becomes a linear
bound because the split cutoff is strictly positive in the open right
half-plane. -/
theorem Complex.binetSecondFormula_arctan_tail_linear_bound_of_bounded
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbounded :
      ∃ B : ℝ,
        0 ≤ B ∧
        ∀ t : ℝ,
          t ∈ Set.Ioi (‖w‖ / 2) →
            ‖Complex.arctan ((t : ℂ) / w)‖ ≤ B) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C * t := by
  rcases hbounded with ⟨B, hB_nonneg, hB⟩
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  let C : ℝ := 2 * B / ‖w‖
  have hC_nonneg : 0 ≤ C :=
    div_nonneg (mul_nonneg Real.zero_le_two_real hB_nonneg)
      (le_of_lt hw_norm_pos)
  refine ⟨C, hC_nonneg, ?_⟩
  intro t ht_tail
  have ht_lower : ‖w‖ / 2 ≤ t :=
    le_of_lt ht_tail
  have hC_mul_lower : B ≤ C * t := by
    have hmul :
        B ≤ C * (‖w‖ / 2) := by
      calc
        B = (2 * B / ‖w‖) * (‖w‖ / 2) :=
          (Real.two_mul_div_mul_half_eq
            (B := B) (r := ‖w‖) hw_norm_pos.ne').symm
        _ = C * (‖w‖ / 2) := rfl
    have hC_mul_mono :
        C * (‖w‖ / 2) ≤ C * t :=
      mul_le_mul_of_nonneg_left ht_lower hC_nonneg
    exact le_trans hmul hC_mul_mono
  exact le_trans (hB t ht_tail) hC_mul_lower

/-- Along the fixed open-half-plane ray `t / w`, the principal arctangent is
linearly bounded on the upper split interval. -/
theorem Complex.binetSecondFormula_arctan_tail_linear_bound
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C * t := by
  exact
    Complex.binetSecondFormula_arctan_tail_linear_bound_of_bounded
      hw_re_pos
      (Complex.binetSecondFormula_arctan_tail_bounded_of_branch_separation
        hw_re_pos)

/-- The Binet kernel is integrable on the lower split interval. -/
theorem Complex.binetSecondFormula_kernel_integrableOn_small_interval
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Set.Ioc (0 : ℝ) (‖w‖ / 2)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let c : ℝ := 2 / ‖w‖
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcM_integrable :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set Ioc_subset_Ioi_self).const_mul c
  have hK_meas :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2))) := by
    have hmeas : Measurable K := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2)),
        ‖K t‖ ≤ c * M t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht => by
        have hkernel :
            ‖K t‖ ≤
              (2 * (t / ‖w‖)) /
                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
          Complex.binetSecondFormula_kernel_norm_le_on_small_interval
            hw_re_pos ht
        have hrewrite :
            (2 * (t / ‖w‖)) /
                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
              c * M t := by
          dsimp [c, M]
          exact Real.two_mul_div_norm_div_exp_sub_one_eq t ‖w‖
        exact hrewrite ▸ hkernel)
  exact
    hcM_integrable.mono' hK_meas hpointwise

/-- Tail pointwise domination for the Binet kernel on the open right
half-plane after the split at `‖w‖ / 2`, with a constant depending on the
fixed open-half-plane point `w`.

The uniform constant `(2 / ‖w‖)` is false pointwise near the principal
arctangent singularity on rays approaching the imaginary axis. -/
theorem Complex.binetSecondFormula_kernel_tail_norm_le_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
            C *
              (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  rcases
      Complex.binetSecondFormula_arctan_tail_linear_bound
        hw_re_pos with
    ⟨C, hC_nonneg, harctan_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro t ht_tail
  have ht_pos : 0 < t :=
    lt_of_le_of_lt
      (div_nonneg (norm_nonneg w) Real.zero_le_two_real)
      ht_tail
  have hden_norm :
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
        Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
    calc
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
          ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ :=
        Complex.binetSecondFormula_exp_denominator_norm_eq t
      _ = Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
        Real.binetSecondFormula_exp_denominator_norm_eq ht_pos
  have hden_nonneg :
      0 ≤ Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
    le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht_pos)
  have harctan :
      ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C * t :=
    harctan_bound t ht_tail
  calc
    ‖Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
      exact norm_div _ _
    _ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
      rw [hden_norm]
    _ ≤ (C * t) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
      div_le_div_of_nonneg_right harctan hden_nonneg
    _ =
        C * (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
      rw [mul_div_assoc]

/-- The Binet kernel is integrable on the upper split interval. -/
theorem Complex.binetSecondFormula_kernel_integrableOn_tail_interval
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Set.Ioi (‖w‖ / 2)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  rcases
      Complex.binetSecondFormula_kernel_tail_norm_le_majorant
        hw_re_pos with
    ⟨c, hc_nonneg, htail_bound⟩
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) Real.zero_le_two_real
  have hcM_integrable :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioi (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set (Ioi_subset_Ioi hcut_nonneg)).const_mul c
  have hK_meas :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioi (‖w‖ / 2))) := by
    have hmeas : Measurable K := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
        ‖K t‖ ≤ c * M t :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => htail_bound t ht)
  exact
    hcM_integrable.mono' hK_meas hpointwise

/-- The complex Binet kernel is integrable on the positive half-line in the
open right half-plane. -/
theorem Complex.binetSecondFormula_kernel_integrableOn_Ioi_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Set.Ioi (0 : ℝ)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) Real.zero_le_two_real
  have hsmall : IntegrableOn K (Set.Ioc (0 : ℝ) (‖w‖ / 2)) :=
    Complex.binetSecondFormula_kernel_integrableOn_small_interval
      hw_re_pos
  have htail : IntegrableOn K (Set.Ioi (‖w‖ / 2)) :=
    Complex.binetSecondFormula_kernel_integrableOn_tail_interval
      hw_re_pos
  have hunion :
      Set.Ioc (0 : ℝ) (‖w‖ / 2) ∪ Set.Ioi (‖w‖ / 2) =
        Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi hcut_nonneg
  exact
    hunion ▸ hsmall.union htail

/-- The Binet remainder integral splits at `‖w‖ / 2` into its small-argument
and tail pieces. -/
theorem Complex.binetSecondFormulaRemainder_eq_small_add_tail
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Complex.binetSecondFormulaRemainder w =
      2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) +
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hK_integrable_Ioi : IntegrableOn K (Set.Ioi (0 : ℝ)) :=
    Complex.binetSecondFormula_kernel_integrableOn_Ioi_openRightHalfPlane
      hw_re_pos
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) Real.zero_le_two_real
  have hsmall_integrable :
      IntegrableOn K (Set.Ioc (0 : ℝ) (‖w‖ / 2)) :=
    hK_integrable_Ioi.mono_set Ioc_subset_Ioi_self
  have htail_integrable :
      IntegrableOn K (Set.Ioi (‖w‖ / 2)) :=
    hK_integrable_Ioi.mono_set (Ioi_subset_Ioi hcut_nonneg)
  have hsplit :
      ∫ t : ℝ in Set.Ioi (0 : ℝ), K t =
        ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t +
          ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t := by
    have hunion :
        Set.Ioc (0 : ℝ) (‖w‖ / 2) ∪ Set.Ioi (‖w‖ / 2) =
          Set.Ioi (0 : ℝ) :=
      Set.Ioc_union_Ioi_eq_Ioi hcut_nonneg
    have hdisjoint :
        Disjoint (Set.Ioc (0 : ℝ) (‖w‖ / 2))
          (Set.Ioi (‖w‖ / 2)) :=
      Ioc_disjoint_Ioi le_rfl
    calc
      ∫ t : ℝ in Set.Ioi (0 : ℝ), K t =
          ∫ t : ℝ in
            Set.Ioc (0 : ℝ) (‖w‖ / 2) ∪ Set.Ioi (‖w‖ / 2), K t := by
        rw [hunion]
      _ =
          ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t +
            ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t := by
        exact
          setIntegral_union hdisjoint measurableSet_Ioi
            hsmall_integrable htail_integrable
  calc
    Complex.binetSecondFormulaRemainder w =
        2 * ∫ t : ℝ in Set.Ioi (0 : ℝ), K t := by
      rfl
    _ =
        2 *
            (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t +
              ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t) := by
      rw [hsplit]
    _ =
        2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t +
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t := by
      exact
        Complex.two_mul_add_eq_add_two_mul
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t)
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t)

/-- Small-argument part of the Binet remainder integral, where the principal
arctangent is controlled by its power-series disk estimate. -/
theorem Complex.binetSecondFormulaRemainder_small_norm_le_integral_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
      4 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let c : ℝ := 2 / ‖w‖
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have hc_nonneg : 0 ≤ c :=
    div_nonneg Real.zero_le_two_real (le_of_lt hw_norm_pos)
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcM_integrable_Ioc :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set Ioc_subset_Ioi_self).const_mul c
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2)),
        ‖K t‖ ≤ c * M t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht => by
        have hkernel :
            ‖K t‖ ≤
              (2 * (t / ‖w‖)) /
                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
          Complex.binetSecondFormula_kernel_norm_le_on_small_interval
            hw_re_pos ht
        have hrewrite :
            (2 * (t / ‖w‖)) /
                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
              c * M t := by
          dsimp [c, M]
          exact Real.two_mul_div_norm_div_exp_sub_one_eq t ‖w‖
        exact hrewrite ▸ hkernel)
  have hnorm_integral :
      ‖∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t‖ ≤
        ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), c * M t :=
    norm_integral_le_of_norm_le hcM_integrable_Ioc hpointwise
  have hmono :
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), M t ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
    setIntegral_mono_set hM_integrable_Ioi
      ((ae_restrict_mem measurableSet_Ioi).mono
        (fun t ht => Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t ht))
      (Eventually.of_forall (fun t ht => ht.1))
  have hscaled_mono :
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), c * M t ≤
        c * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t := by
    calc
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), c * M t =
          c * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), M t := by
        exact integral_const_mul c M
      _ ≤ c * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
        mul_le_mul_of_nonneg_left hmono hc_nonneg
  calc
    ‖2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t‖ =
        2 * ‖∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t‖ := by
      simp [norm_mul]
    _ ≤ 2 * (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), c * M t) :=
      mul_le_mul_of_nonneg_left hnorm_integral Real.zero_le_two_real
    _ ≤ 2 * (c * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t) :=
      mul_le_mul_of_nonneg_left hscaled_mono Real.zero_le_two_real
    _ =
        4 *
          (∫ t : ℝ in Set.Ioi (0 : ℝ), M t) / ‖w‖ := by
      dsimp [c]
      exact
        Real.two_mul_two_div_mul_eq_four_mul_div
          (∫ t : ℝ in Set.Ioi (0 : ℝ), M t) ‖w‖

/-- Tail part of the Binet remainder integral.  This is where one uses the
principal-branch arctangent bound away from the branch singularities together
with the exponential denominator. -/
theorem Complex.binetSecondFormulaRemainder_tail_norm_le_fixed_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
        2 * C *
          (∫ t : ℝ in Set.Ioi (0 : ℝ),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  rcases
      Complex.binetSecondFormula_kernel_tail_norm_le_majorant
        hw_re_pos with
    ⟨C, hC_nonneg, htail_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) Real.zero_le_two_real
  have hCM_integrable_tail :
      Integrable (fun t : ℝ => C * M t)
        (volume.restrict (Set.Ioi (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set (Ioi_subset_Ioi hcut_nonneg)).const_mul C
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
        ‖K t‖ ≤ C * M t :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => htail_bound t ht)
  have hnorm_integral :
      ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ ≤
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t :=
    norm_integral_le_of_norm_le hCM_integrable_tail hpointwise
  have hmono :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
    setIntegral_mono_set hM_integrable_Ioi
      ((ae_restrict_mem measurableSet_Ioi).mono
        (fun t ht => Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t ht))
      (Eventually.of_forall (fun t ht => lt_of_le_of_lt hcut_nonneg ht))
  have hscaled_mono :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t ≤
        C * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t := by
    calc
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t =
          C * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t := by
        exact integral_const_mul C M
      _ ≤ C * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
        mul_le_mul_of_nonneg_left hmono hC_nonneg
  calc
    ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ =
        2 * ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ := by
      simp [norm_mul]
    _ ≤ 2 * (∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t) :=
      mul_le_mul_of_nonneg_left hnorm_integral Real.zero_le_two_real
    _ ≤ 2 * (C * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t) :=
      mul_le_mul_of_nonneg_left hscaled_mono Real.zero_le_two_real
    _ = 2 * C * (∫ t : ℝ in Set.Ioi (0 : ℝ), M t) := by
      rw [mul_assoc]

/-- Uniform tail part of the Binet remainder integral.  This requires an
additional cancellation estimate beyond the fixed-`w` tail majorant. -/
theorem Complex.binetSecondFormulaRemainder_tail_norm_le_integral_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
      4 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ := by
  sorry

/-- Splitting the Binet integral at `‖w‖ / 2` gives the global open-half-plane
remainder bound. -/
theorem Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_from_split
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖Complex.binetSecondFormulaRemainder w‖ ≤
      8 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ := by
  let J : ℝ :=
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let S : ℂ :=
    2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let T : ℂ :=
    2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
      Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hsplit : Complex.binetSecondFormulaRemainder w = S + T := by
    exact Complex.binetSecondFormulaRemainder_eq_small_add_tail hw_re_pos
  have hS : ‖S‖ ≤ 4 * J / ‖w‖ :=
    Complex.binetSecondFormulaRemainder_small_norm_le_integral_majorant
      hw_re_pos
  have hT : ‖T‖ ≤ 4 * J / ‖w‖ :=
    Complex.binetSecondFormulaRemainder_tail_norm_le_integral_majorant
      hw_re_pos
  have hsum : ‖S + T‖ ≤ 8 * J / ‖w‖ := by
    calc
      ‖S + T‖ ≤ ‖S‖ + ‖T‖ := norm_add_le S T
      _ ≤ 4 * J / ‖w‖ + 4 * J / ‖w‖ := add_le_add hS hT
      _ = 8 * J / ‖w‖ :=
        Real.four_div_add_four_div_eq_eight_div J ‖w‖
  exact
    Eq.subst
      (motive := fun x : ℂ => ‖x‖ ≤ 8 * J / ‖w‖)
      hsplit.symm
      hsum

/-- The pointwise Binet-kernel majorant integrates to a norm bound for the
Binet remainder in the open right half-plane. -/
theorem Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_from_kernel_bound
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖Complex.binetSecondFormulaRemainder w‖ ≤
      8 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ := by
  exact
    Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_from_split
      hw_re_pos

/-- Integration of the pointwise Binet-kernel majorant on the open right
half-plane. -/
theorem Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖Complex.binetSecondFormulaRemainder w‖ ≤
      8 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ := by
  exact
    Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_from_kernel_bound
      hw_re_pos

/-- A positive integrable function on an open real interval has positive
integral. -/
theorem Real.setIntegral_pos_of_integrableOn_of_pos_on_Ioo
    {f : ℝ → ℝ}
    {a b : ℝ}
    (hab : a < b)
    (h_integrable : IntegrableOn f (Set.Ioo a b))
    (hpos : ∀ t : ℝ, t ∈ Set.Ioo a b → 0 < f t) :
    0 < ∫ t : ℝ in Set.Ioo a b, f t := by
  have hnonneg_ae :
      0 ≤ᵐ[volume.restrict (Set.Ioo a b)] f :=
    (ae_restrict_mem measurableSet_Ioo).mono
      (fun t ht => le_of_lt (hpos t ht))
  have hsupport_pos :
      0 < volume (Function.support f ∩ Set.Ioo a b) := by
    have hIoo_pos : 0 < volume (Set.Ioo a b) :=
      (Measure.measure_Ioo_pos volume).mpr hab
    have hsubset :
        Set.Ioo a b ⊆ Function.support f ∩ Set.Ioo a b := by
      intro t ht
      exact ⟨fun hzero => (ne_of_gt (hpos t ht)) hzero, ht⟩
    exact lt_of_lt_of_le hIoo_pos (measure_mono hsubset)
  exact
    (setIntegral_pos_iff_support_of_nonneg_ae
      hnonneg_ae h_integrable).mpr hsupport_pos

/-- The Binet majorant is integrable on `(0,1)`. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_Ioo_zero_one :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioo (0 : ℝ) 1) := by
  exact
    IntegrableOn.mono_set
      Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one
      Set.Ioo_subset_Ioc_self

/-- The Binet majorant has strictly positive integral on `(0,1)`. -/
theorem Real.binetSecondFormula_kernel_majorant_integral_pos_on_zero_one :
    0 <
      ∫ t : ℝ in Set.Ioo (0 : ℝ) 1,
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    Real.setIntegral_pos_of_integrableOn_of_pos_on_Ioo
      zero_lt_one
      Real.binetSecondFormula_kernel_majorant_integrableOn_Ioo_zero_one
      (fun t ht =>
        Real.binetSecondFormula_kernel_majorant_pos ht.1)

/-- Positivity of an integral on a subinterval propagates to the larger
positive half-line for a nonnegative integrable function. -/
theorem Real.integral_pos_on_Ioi_zero_of_integral_pos_on_Ioo_zero_one_of_nonneg
    {f : ℝ → ℝ}
    (h_integrable : IntegrableOn f (Set.Ioi (0 : ℝ)))
    (hpos_subinterval :
      0 <
        ∫ t : ℝ in Set.Ioo (0 : ℝ) 1, f t)
    (hnonneg :
      ∀ t : ℝ,
        t ∈ Set.Ioi (0 : ℝ) →
          0 ≤ f t) :
    0 <
      ∫ t : ℝ in Set.Ioi (0 : ℝ), f t := by
  have hnonneg_ae :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] f :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => hnonneg t ht)
  have hsubset_ae :
      Set.Ioo (0 : ℝ) 1 ≤ᵐ[volume] Set.Ioi (0 : ℝ) :=
    Eventually.of_forall (fun t ht => ht.1)
  have hmono :
      ∫ t : ℝ in Set.Ioo (0 : ℝ) 1, f t ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ), f t :=
    setIntegral_mono_set h_integrable hnonneg_ae hsubset_ae
  exact lt_of_lt_of_le hpos_subinterval hmono

/-- Positivity on `(0,1)` propagates to positivity of the half-line integral
for the nonnegative Binet majorant. -/
theorem Real.binetSecondFormula_kernel_majorant_integral_pos_of_zero_one
    (hpos_subinterval :
      0 <
        ∫ t : ℝ in Set.Ioo (0 : ℝ) 1,
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
    (hnonneg :
      ∀ t : ℝ,
        t ∈ Set.Ioi (0 : ℝ) →
          0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :
    0 <
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    Real.integral_pos_on_Ioi_zero_of_integral_pos_on_Ioo_zero_one_of_nonneg
      Real.binetSecondFormula_kernel_majorant_integrableOn
      hpos_subinterval hnonneg

/-- The Binet majorant integral is a positive finite constant. -/
theorem Real.binetSecondFormula_kernel_majorant_integral_pos :
    0 <
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  have hpos_subinterval :
      0 <
        ∫ t : ℝ in Set.Ioo (0 : ℝ) 1,
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    Real.binetSecondFormula_kernel_majorant_integral_pos_on_zero_one
  have hnonneg :
      ∀ t : ℝ,
        t ∈ Set.Ioi (0 : ℝ) →
          0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi
  exact
    Real.binetSecondFormula_kernel_majorant_integral_pos_of_zero_one
      hpos_subinterval hnonneg

/-- The Binet second-formula remainder is bounded by a constant divided by
`‖w‖` in the open right half-plane. -/
theorem Complex.binetSecondFormulaRemainder_norm_le_openRightHalfPlane :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
          ‖Complex.binetSecondFormulaRemainder w‖ ≤ C / ‖w‖ := by
  let J : ℝ :=
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let C : ℝ := 8 * J
  have hJ_pos : 0 < J :=
    Real.binetSecondFormula_kernel_majorant_integral_pos
  have hC_pos : 0 < C :=
    mul_pos Real.zero_lt_eight_real hJ_pos
  refine ⟨C, hC_pos, ?_⟩
  intro w hw_re_pos
  exact
    Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_openRightHalfPlane
      hw_re_pos

end

end LFunctions
end Boundary
