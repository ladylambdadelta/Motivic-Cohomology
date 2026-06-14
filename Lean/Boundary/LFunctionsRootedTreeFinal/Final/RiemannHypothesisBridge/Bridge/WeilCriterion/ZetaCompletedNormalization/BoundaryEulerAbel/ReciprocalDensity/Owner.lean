import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Owner

/-!
# Reciprocal-density variation estimates

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.BoundaryEulerAbel.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem reciprocalDerivative_norm_eq_on_positive_interval
    {a b x : ℝ}
    (ha : 0 < a)
    (hx : x ∈ Set.Icc a b) :
    ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
      (1 : ℝ) / x ^ 2 := by
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha hx.1
  exact complexReciprocalOfReal_deriv_norm_eq hx_pos

/-- Concrete reciprocal variation bound on a finite post-cutoff interval.

This is the non-oscillatory real-variable input used by partial summation:
the total variation density of `u ↦ 1 / u` is `1/u^2` on the positive interval
starting at the canonical cutoff. -/
theorem concreteReciprocalVariation_density_bound_on_cutoff_interval
    (t : ℝ)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
      ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
        (1 : ℝ) / x ^ 2 := by
  intro x hx
  have hcutoff_pos : 0 < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (boundaryLineOnePointRealParam_cutoff_pos t)
  exact reciprocalDerivative_norm_eq_on_positive_interval hcutoff_pos hx

/-- Pointwise scalar majorization of the reciprocal-density integrand on the
post-cutoff interval. -/
theorem reciprocalDensityIntegral_pointwise_norm_le_scalar_majorant
    (t : ℝ)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
      ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
  intro x hx
  have hx_Icc :
      x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ) :=
    ⟨le_of_lt hx.1, hx.2⟩
  have hleft :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ x :=
    le_of_lt hx.1
  have hdensity :
      ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
        (1 : ℝ) / x ^ 2 :=
    hreciprocal_density x hx_Icc
  have hpartial_x :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) :=
    hpartial hleft
  have hnorm_mul :
      ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ =
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ *
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ :=
    norm_mul
      (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
      (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊)
  have hdensity_nonneg :
      0 ≤ (1 : ℝ) / x ^ 2 := by
    exact Eq.subst
      (motive := fun u : ℝ => 0 ≤ u)
      hdensity
      (norm_nonneg (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x))
  have hmul :
      ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ *
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) :=
    Eq.subst
      (motive := fun u : ℝ =>
        u * ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
          ((1 : ℝ) / x ^ 2) *
            (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)))
      hdensity.symm
      (mul_le_mul_of_nonneg_left hpartial_x hdensity_nonneg)
  exact Eq.subst
    (motive := fun u : ℝ =>
      u ≤ ((1 : ℝ) / x ^ 2) *
        (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)))
    hnorm_mul.symm
    hmul

/-- Measure-theoretic norm domination for the reciprocal-density integral from
the pointwise scalar majorant. -/
theorem reciprocalDensityIntegral_norm_le_scalar_majorant_of_pointwise
    (t : ℝ)
    {M : ℕ}
    (hpointwise :
      ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
          ((1 : ℝ) / x ^ 2) *
            (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
  let s : Set ℝ :=
    Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)
  let f : ℝ → ℂ := fun x =>
    deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊
  let g : ℝ → ℝ := fun x =>
    ((1 : ℝ) / x ^ 2) *
      (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
  have hg : Integrable g (volume.restrict s) := by
    fun_prop
  have hbound : ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx => hpointwise x hx)
  exact norm_integral_le_of_norm_le hg hbound

/-- Bochner norm domination for the reciprocal-density logarithmic-phase
integral. -/
theorem reciprocalDensityIntegral_norm_le_scalar_majorant
    (t : ℝ)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
  exact
    reciprocalDensityIntegral_norm_le_scalar_majorant_of_pointwise
      t
      (reciprocalDensityIntegral_pointwise_norm_le_scalar_majorant
        t hpartial hNM hreciprocal_density)

/-- The canonical Abel/Euler-Maclaurin cutoff is positive as a real endpoint. -/
theorem scalarReciprocalDensity_cutoff_real_pos
    (t : ℝ) :
    0 < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) := by
  exact Nat.cast_pos.mpr (boundaryLineOnePointRealParam_cutoff_pos t)

/-- The canonical Abel/Euler-Maclaurin cutoff is at least two as a real
endpoint. -/
theorem scalarReciprocalDensity_two_le_cutoff_real
    (t : ℝ) :
    (2 : ℝ) ≤ (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) := by
  exact Nat.cast_le.mpr (boundaryLineOnePointRealParam_two_le_cutoff t)

/-- Points in the post-cutoff interval are positive. -/
theorem scalarReciprocalDensity_Ioc_point_pos
    (t : ℝ)
    {M : ℕ}
    {x : ℝ}
    (hx :
      x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)) :
    0 < x := by
  exact lt_trans (scalarReciprocalDensity_cutoff_real_pos t) hx.1

/-- Points in the closed post-cutoff interval are positive. -/
theorem scalarReciprocalDensity_Icc_point_pos
    (t : ℝ)
    {M : ℕ}
    {x : ℝ}
    (hx :
      x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)) :
    0 < x := by
  exact lt_of_lt_of_le (scalarReciprocalDensity_cutoff_real_pos t) hx.1

/-- Positivity of the shifted logarithm on the scalar-calculus range. -/
theorem real_log_two_add_nonneg_of_two_le
    {x : ℝ}
    (hx : (2 : ℝ) ≤ x) :
    0 ≤ Real.log (2 + x) := by
  have hone_le_two : (1 : ℝ) ≤ 2 := by
    calc
      (1 : ℝ) ≤ 1 + 1 := le_add_of_nonneg_right zero_le_one
      _ = 2 := by
        rfl
  have htwo_le_two_add : (2 : ℝ) ≤ 2 + x :=
    le_trans hx (le_add_of_nonneg_left (show (0 : ℝ) ≤ 2 by
      calc
        (0 : ℝ) ≤ 1 := zero_le_one
        _ ≤ 2 := hone_le_two))
  exact Real.log_nonneg (le_trans hone_le_two htwo_le_two_add)

/-- On `2 ≤ x`, `log(2+x)/x` is bounded by the derivative density of
`(log(2+x))²`. -/
theorem real_log_two_add_div_self_le_log_sq_derivative_density
    {x : ℝ}
    (hx : (2 : ℝ) ≤ x) :
    Real.log (2 + x) / x ≤
      2 * Real.log (2 + x) / (2 + x) := by
  have hx_pos : 0 < x :=
    lt_of_lt_of_le zero_lt_two hx
  have hshift_pos : 0 < 2 + x :=
    add_pos_of_pos_of_nonneg zero_lt_two (le_trans (show (0 : ℝ) ≤ 2 by
      exact le_of_lt zero_lt_two) hx)
  have hlog_nonneg : 0 ≤ Real.log (2 + x) :=
    real_log_two_add_nonneg_of_two_le hx
  have hreciprocal :
      (1 : ℝ) / x ≤ 2 / (2 + x) := by
    have hmul :
        (2 + x) ≤ 2 * x := by
      calc
        2 + x ≤ x + x :=
          add_le_add_right hx x
        _ = 2 * x := by
          exact (two_mul x).symm
    exact (div_le_div_iff₀ hx_pos hshift_pos).mpr hmul
  have hscaled :
      Real.log (2 + x) * ((1 : ℝ) / x) ≤
        Real.log (2 + x) * (2 / (2 + x)) :=
    mul_le_mul_of_nonneg_left hreciprocal hlog_nonneg
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ 2 * Real.log (2 + x) / (2 + x))
    (div_eq_mul_one_div (Real.log (2 + x)) x).symm
    (Eq.subst
      (motive := fun y : ℝ =>
        Real.log (2 + x) * (2 / (2 + x)) ≤ y)
      (by
        calc
          2 * Real.log (2 + x) / (2 + x) =
              (2 * Real.log (2 + x)) * ((1 : ℝ) / (2 + x)) := by
            exact div_eq_mul_one_div (2 * Real.log (2 + x)) (2 + x)
          _ = Real.log (2 + x) * (2 * ((1 : ℝ) / (2 + x))) := by
            ac_rfl
          _ = Real.log (2 + x) * (2 / (2 + x)) := by
            exact congrArg
              (fun y : ℝ => Real.log (2 + x) * y)
              (div_eq_mul_one_div 2 (2 + x)).symm)
      hscaled)

/-- Derivative of the square of the shifted logarithm. -/
theorem real_hasDerivAt_log_two_add_sq
    {x : ℝ}
    (hx : (0 : ℝ) < 2 + x) :
    HasDerivAt
      (fun y : ℝ => (Real.log (2 + y)) ^ 2)
      (2 * Real.log (2 + x) / (2 + x))
      x := by
  have hshift_ne : 2 + x ≠ 0 :=
    ne_of_gt hx
  have hshift :
      HasDerivAt (fun y : ℝ => 2 + y) 1 x :=
    (hasDerivAt_id x).const_add 2
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (2 + y)) ((2 + x)⁻¹) x :=
    (hasDerivAt_log hshift_ne).comp x hshift
  have hpow :
      HasDerivAt
        (fun y : ℝ => (Real.log (2 + y)) ^ 2)
        (((2 : ℝ) * (Real.log (2 + x)) ^ (2 - 1)) * ((2 + x)⁻¹))
        x :=
    (hasDerivAt_pow 2 (Real.log (2 + x))).comp x hlog
  have hcoeff :
      ((2 : ℝ) * (Real.log (2 + x)) ^ (2 - 1)) * ((2 + x)⁻¹) =
        2 * Real.log (2 + x) / (2 + x) := by
    calc
      ((2 : ℝ) * (Real.log (2 + x)) ^ (2 - 1)) * ((2 + x)⁻¹) =
          (2 * Real.log (2 + x)) * ((2 + x)⁻¹) := by
        rfl
      _ = 2 * Real.log (2 + x) / (2 + x) := by
        exact (div_eq_mul_inv (2 * Real.log (2 + x)) (2 + x)).symm
  exact hcoeff ▸ hpow

/-- Integral evaluation for the shifted-log square derivative density. -/
theorem real_intervalIntegral_log_sq_derivative_density_eq_sub
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in a..b, 2 * Real.log (2 + x) / (2 + x) =
      (Real.log (2 + b)) ^ 2 - (Real.log (2 + a)) ^ 2 := by
  let F : ℝ → ℝ := fun x => (Real.log (2 + x)) ^ 2
  let G : ℝ → ℝ := fun x => 2 * Real.log (2 + x) / (2 + x)
  have hderiv :
      ∀ x ∈ Set.uIcc a b, HasDerivAt F (G x) x := by
    intro x hx
    have hmin_left : min a b = a :=
      min_eq_left hab
    have hax_min : min a b ≤ x :=
      (Set.mem_uIcc.mp hx).1
    have hax : a ≤ x :=
      Eq.subst
        (motive := fun y : ℝ => y ≤ x)
        hmin_left
        hax_min
    have htwo_le_x : (2 : ℝ) ≤ x :=
      le_trans ha hax
    have hpos : (0 : ℝ) < 2 + x :=
      add_pos_of_pos_of_nonneg zero_lt_two
        (le_trans (show (0 : ℝ) ≤ 2 by exact le_of_lt zero_lt_two) htwo_le_x)
    exact real_hasDerivAt_log_two_add_sq hpos
  have hint : IntervalIntegrable G volume a b := by
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

theorem real_integral_Ioc_log_sq_derivative_density_le_endpoint_sq
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, 2 * Real.log (2 + x) / (2 + x) ≤
      (Real.log (2 + b)) ^ 2 := by
  have hset_interval :
      ∫ x in Set.Ioc a b, 2 * Real.log (2 + x) / (2 + x) =
        ∫ x in a..b, 2 * Real.log (2 + x) / (2 + x) :=
    (intervalIntegral.integral_of_le hab).symm
  have heval :
      ∫ x in a..b, 2 * Real.log (2 + x) / (2 + x) =
        (Real.log (2 + b)) ^ 2 - (Real.log (2 + a)) ^ 2 :=
    real_intervalIntegral_log_sq_derivative_density_eq_sub ha hab
  have hlower_nonneg : 0 ≤ (Real.log (2 + a)) ^ 2 :=
    sq_nonneg (Real.log (2 + a))
  have hsub :
      (Real.log (2 + b)) ^ 2 - (Real.log (2 + a)) ^ 2 ≤
        (Real.log (2 + b)) ^ 2 :=
    sub_le_self ((Real.log (2 + b)) ^ 2) hlower_nonneg
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ (Real.log (2 + b)) ^ 2)
    hset_interval.symm
    (le_trans (le_of_eq heval) hsub)

/-- Fundamental-theorem comparison for the finite `log(2+x)/x` integral. -/
theorem real_integral_Ioc_log_two_add_div_self_le_log_endpoint_sq_of_pointwise
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b)
    (hpointwise :
      ∀ x ∈ Set.Ioc a b,
        Real.log (2 + x) / x ≤
          2 * Real.log (2 + x) / (2 + x)) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ≤
      (Real.log (2 + b)) ^ 2 := by
  let f : ℝ → ℝ := fun x => Real.log (2 + x) / x
  let g : ℝ → ℝ := fun x => 2 * Real.log (2 + x) / (2 + x)
  have hf : Integrable f (volume.restrict (Set.Ioc a b)) := by
    fun_prop
  have hg : Integrable g (volume.restrict (Set.Ioc a b)) := by
    fun_prop
  have hle : f ≤ᵐ[volume.restrict (Set.Ioc a b)] g :=
    (ae_restrict_mem measurableSet_Ioc).mono hpointwise
  have hmono :
      ∫ x in Set.Ioc a b, Real.log (2 + x) / x ≤
        ∫ x in Set.Ioc a b, 2 * Real.log (2 + x) / (2 + x) :=
    integral_mono_ae hf hg hle
  exact le_trans hmono
    (real_integral_Ioc_log_sq_derivative_density_le_endpoint_sq ha hab)

/-- Canonical real-variable comparison for the finite `log(2+x)/x` integral.

On `2 ≤ a ≤ b`, the integrand is dominated by the derivative of
`(Real.log (2+x))^2`, since `1/x ≤ 2/(2+x)` and `Real.log (2+x) ≥ 0`.
This is the reusable scalar calculus theorem; the zeta cutoff theorem below is
only an endpoint instantiation. -/
theorem real_integral_Ioc_log_two_add_div_self_le_log_endpoint_sq
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ≤
      (Real.log (2 + b)) ^ 2 := by
  exact
    real_integral_Ioc_log_two_add_div_self_le_log_endpoint_sq_of_pointwise
      ha hab
      (fun x hx =>
        real_log_two_add_div_self_le_log_sq_derivative_density
          (le_trans ha (le_of_lt hx.1)))

/-- Nonnegativity of the reciprocal-density scalar integrand after `2`. -/
theorem real_log_two_add_div_sq_nonneg_of_two_le
    {x : ℝ}
    (hx : (2 : ℝ) ≤ x) :
    0 ≤ Real.log (2 + x) / x ^ 2 := by
  have hlog_nonneg : 0 ≤ Real.log (2 + x) :=
    real_log_two_add_nonneg_of_two_le hx
  have hx_pos : 0 < x :=
    lt_of_lt_of_le zero_lt_two hx
  have hx_sq_nonneg : 0 ≤ x ^ 2 :=
    sq_nonneg x
  exact div_nonneg hlog_nonneg hx_sq_nonneg

/-- Concrete finite integration-by-parts identity for
`u(x)=log(2+x)` and `v(x)=-1/x` on `[2,b]`. -/
theorem real_intervalIntegral_log_two_add_mul_inv_sq_eq_by_parts_core
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    let u : ℝ → ℝ := fun x => Real.log (2 + x)
    let v : ℝ → ℝ := fun x => -(1 / x)
    let u' : ℝ → ℝ := fun x => 1 / (2 + x)
    let v' : ℝ → ℝ := fun x => 1 / x ^ 2
    ∫ x in (2 : ℝ)..b, u x * v' x =
      u b * v b - u 2 * v 2 -
        ∫ x in (2 : ℝ)..b, u' x * v x := by
  let u : ℝ → ℝ := fun x => Real.log (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  let u' : ℝ → ℝ := fun x => 1 / (2 + x)
  let v' : ℝ → ℝ := fun x => 1 / x ^ 2
  have hu :
      ∀ x ∈ [[(2 : ℝ), b]], HasDerivAt u (u' x) x := by
    intro x hx
    have hleft : (2 : ℝ) ≤ x :=
      (Set.mem_uIcc.mp hx).1
    have htwo_add_pos : 0 < 2 + x :=
      add_pos_of_pos_of_nonneg zero_lt_two
        (le_trans (le_of_lt zero_lt_two) hleft)
    have hbase : HasDerivAt (fun y : ℝ => 2 + y) 1 x :=
      (hasDerivAt_id x).const_add 2
    have hlog :
        HasDerivAt (fun y : ℝ => Real.log (2 + y)) ((2 + x)⁻¹) x :=
      Real.hasDerivAt_log htwo_add_pos.ne'.symm |>.comp x hbase
    have hnormal : (2 + x)⁻¹ = 1 / (2 + x) :=
      (one_div (2 + x)).symm
    exact Eq.subst
      (motive := fun D : ℝ => HasDerivAt u D x)
      hnormal
      hlog
  have hv :
      ∀ x ∈ [[(2 : ℝ), b]], HasDerivAt v (v' x) x := by
    intro x hx
    have hleft : (2 : ℝ) ≤ x :=
      (Set.mem_uIcc.mp hx).1
    have hx_ne : x ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_two hleft)
    have hinv :
        HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x :=
      hasDerivAt_inv hx_ne
    have hneg :
        HasDerivAt (fun y : ℝ => -(y⁻¹)) (- (-(x ^ 2)⁻¹)) x :=
      hinv.neg
    have hfun :
        (fun y : ℝ => -(y⁻¹)) = v := by
      exact funext
        (fun y : ℝ =>
          congrArg Neg.neg (one_div y))
    have hnormal : - (-(x ^ 2)⁻¹) = 1 / x ^ 2 := by
      calc
        - (-(x ^ 2)⁻¹) = (x ^ 2)⁻¹ := neg_neg ((x ^ 2)⁻¹)
        _ = 1 / x ^ 2 := (one_div (x ^ 2)).symm
    exact Eq.subst
      (motive := fun D : ℝ => HasDerivAt v D x)
      hnormal
      (Eq.subst
        (motive := fun F : ℝ → ℝ => HasDerivAt F (- (-(x ^ 2)⁻¹)) x)
        hfun
        hneg)
  have hu_int : IntervalIntegrable u' volume (2 : ℝ) b := by
    fun_prop
  have hv_int : IntervalIntegrable v' volume (2 : ℝ) b := by
    fun_prop
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hv hu_int hv_int

/-- Algebraic normalization of the finite by-parts RHS for
`u(x)=log(2+x)` and `v(x)=-1/x`. -/
theorem real_by_parts_log_two_add_endpoint_normalize
    {b : ℝ} :
    let u : ℝ → ℝ := fun x => Real.log (2 + x)
    let v : ℝ → ℝ := fun x => -(1 / x)
    u b * v b - u 2 * v 2 =
      (-Real.log (2 + b) / b) - (-Real.log 4 / 2) := by
  let u : ℝ → ℝ := fun x => Real.log (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  have hvb : v b = -(1 / b) := rfl
  have hv2 : v 2 = -(1 / (2 : ℝ)) := rfl
  have hu2 : u 2 = Real.log 4 := by
    exact congrArg Real.log (show (2 : ℝ) + 2 = 4 by rfl)
  have hleft :
      u b * v b = -Real.log (2 + b) / b := by
    calc
      u b * v b = Real.log (2 + b) * (-(1 / b)) := rfl
      _ = -(Real.log (2 + b) * (1 / b)) :=
        (mul_neg (Real.log (2 + b)) (1 / b))
      _ = -(Real.log (2 + b) / b) := by
        exact congrArg Neg.neg
          (div_eq_mul_one_div (Real.log (2 + b)) b).symm
      _ = -Real.log (2 + b) / b :=
        (neg_div (Real.log (2 + b)) b).symm
  have hright :
      u 2 * v 2 = -Real.log 4 / 2 := by
    calc
      u 2 * v 2 = Real.log 4 * (-(1 / (2 : ℝ))) := by
        exact congrArg₂ (fun a c : ℝ => a * c) hu2 hv2
      _ = -(Real.log 4 * (1 / (2 : ℝ))) :=
        (mul_neg (Real.log 4) (1 / (2 : ℝ)))
      _ = -(Real.log 4 / 2) := by
        exact congrArg Neg.neg
          (div_eq_mul_one_div (Real.log 4) (2 : ℝ)).symm
      _ = -Real.log 4 / 2 :=
        (neg_div (Real.log 4) (2 : ℝ)).symm
  exact congrArg₂ (fun a c : ℝ => a - c) hleft hright

/-- Integral sign-change normalization for the finite by-parts remainder. -/
theorem real_intervalIntegral_log_two_add_by_parts_remainder_normalize
    {b : ℝ} :
    let u' : ℝ → ℝ := fun x => 1 / (2 + x)
    let v : ℝ → ℝ := fun x => -(1 / x)
    -(∫ x in (2 : ℝ)..b, u' x * v x) =
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) := by
  let u' : ℝ → ℝ := fun x => 1 / (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  let r : ℝ → ℝ := fun x => (1 : ℝ) / (x * (2 + x))
  have hpoint : (fun x : ℝ => u' x * v x) = (fun x : ℝ => -r x) := by
    exact funext
      (fun x : ℝ =>
        calc
          u' x * v x = (1 / (2 + x)) * (-(1 / x)) := rfl
          _ = -((1 / (2 + x)) * (1 / x)) :=
            mul_neg (1 / (2 + x)) (1 / x)
          _ = -((1 : ℝ) / (x * (2 + x))) := by
            exact congrArg Neg.neg
              (one_div_mul_one_div_rev (a := (2 + x)) (b := x))
          _ = -r x := rfl)
  have hintegral :
      ∫ x in (2 : ℝ)..b, u' x * v x =
        ∫ x in (2 : ℝ)..b, -r x :=
    congrArg
      (fun f : ℝ → ℝ => ∫ x in (2 : ℝ)..b, f x)
      hpoint
  calc
    -(∫ x in (2 : ℝ)..b, u' x * v x) =
        -(∫ x in (2 : ℝ)..b, -r x) := by
      exact congrArg Neg.neg hintegral
    _ = - (-(∫ x in (2 : ℝ)..b, r x)) := by
      exact congrArg Neg.neg (intervalIntegral.integral_neg r)
    _ = ∫ x in (2 : ℝ)..b, r x :=
      neg_neg (∫ x in (2 : ℝ)..b, r x)

theorem real_intervalIntegral_log_two_add_mul_inv_sq_by_parts_rhs_normalize
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    let u : ℝ → ℝ := fun x => Real.log (2 + x)
    let v : ℝ → ℝ := fun x => -(1 / x)
    let u' : ℝ → ℝ := fun x => 1 / (2 + x)
    u b * v b - u 2 * v 2 -
        ∫ x in (2 : ℝ)..b, u' x * v x =
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
        ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) := by
  let u : ℝ → ℝ := fun x => Real.log (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  let u' : ℝ → ℝ := fun x => 1 / (2 + x)
  have hendpoint :
      u b * v b - u 2 * v 2 =
        (-Real.log (2 + b) / b) - (-Real.log 4 / 2) :=
    real_by_parts_log_two_add_endpoint_normalize
  have hremainder :
      -(∫ x in (2 : ℝ)..b, u' x * v x) =
        ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) :=
    real_intervalIntegral_log_two_add_by_parts_remainder_normalize
  calc
    u b * v b - u 2 * v 2 -
        ∫ x in (2 : ℝ)..b, u' x * v x =
        (u b * v b - u 2 * v 2) +
          -(∫ x in (2 : ℝ)..b, u' x * v x) := by
      exact (sub_eq_add_neg
        (u b * v b - u 2 * v 2)
        (∫ x in (2 : ℝ)..b, u' x * v x))
    _ =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          -(∫ x in (2 : ℝ)..b, u' x * v x) := by
      exact congrArg
        (fun z : ℝ => z + -(∫ x in (2 : ℝ)..b, u' x * v x))
        hendpoint
    _ =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) := by
      exact congrArg
        (fun z : ℝ => ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) + z)
        hremainder

theorem real_intervalIntegral_log_two_add_mul_inv_sq_eq_by_parts
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, Real.log (2 + x) * (1 / x ^ 2) =
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
        ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) := by
  let u : ℝ → ℝ := fun x => Real.log (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  let u' : ℝ → ℝ := fun x => 1 / (2 + x)
  let v' : ℝ → ℝ := fun x => 1 / x ^ 2
  have hparts :
      ∫ x in (2 : ℝ)..b, u x * v' x =
        u b * v b - u 2 * v 2 -
          ∫ x in (2 : ℝ)..b, u' x * v x :=
    real_intervalIntegral_log_two_add_mul_inv_sq_eq_by_parts_core hb
  have hnormal :
      u b * v b - u 2 * v 2 -
          ∫ x in (2 : ℝ)..b, u' x * v x =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) :=
    real_intervalIntegral_log_two_add_mul_inv_sq_by_parts_rhs_normalize hb
  exact Eq.trans hparts hnormal

/-- Algebraic normalization of the scalar reciprocal-density integrand. -/
theorem real_integral_Ioc_log_two_add_div_sq_eq_mul_inv_sq
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
      ∫ x in (2 : ℝ)..b, Real.log (2 + x) * (1 / x ^ 2) := by
  have hset :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        ∫ x in (2 : ℝ)..b, Real.log (2 + x) / x ^ 2 :=
    (intervalIntegral.integral_of_le hb).symm
  have hpoint :
      (fun x : ℝ => Real.log (2 + x) / x ^ 2) =
        (fun x : ℝ => Real.log (2 + x) * (1 / x ^ 2)) := by
    exact funext
      (fun x : ℝ =>
        div_eq_mul_one_div (Real.log (2 + x)) (x ^ 2))
  exact Eq.trans hset
    (congrArg
      (fun f : ℝ → ℝ => ∫ x in (2 : ℝ)..b, f x)
      hpoint)

/-- Interval/set normalization for the by-parts remainder term. -/
theorem real_intervalIntegral_one_div_mul_two_add_eq_Ioc
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
      ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) := by
  exact intervalIntegral.integral_of_le hb

/-- Partial-fraction identity for the finite scalar reciprocal-density
integrand. -/
theorem real_one_div_mul_two_add_eq_half_sub
    {x : ℝ}
    (hx : x ≠ 0)
    (hx_two : 2 + x ≠ 0) :
    (1 : ℝ) / (x * (2 + x)) =
      (1 / 2 : ℝ) * ((1 : ℝ) / x - (1 : ℝ) / (2 + x)) := by
  have hdiff :
      (2 + x : ℝ) - x = 2 :=
    add_sub_cancel_right 2 x
  have hinv :
      (1 : ℝ) / x - (1 : ℝ) / (2 + x) =
        2 / (x * (2 + x)) := by
    calc
      (1 : ℝ) / x - (1 : ℝ) / (2 + x)
          = x⁻¹ - (2 + x)⁻¹ := by
              rw [one_div, one_div]
      _ = ((2 + x) - x) / (x * (2 + x)) :=
              inv_sub_inv hx hx_two
      _ = 2 / (x * (2 + x)) := by
              exact congrArg
                (fun y : ℝ => y / (x * (2 + x)))
                hdiff
  calc
    (1 : ℝ) / (x * (2 + x))
        = ((1 / 2 : ℝ) * 2) / (x * (2 + x)) := by
            rw [one_div_mul_cancel two_ne_zero, one_div]
    _ = (1 / 2 : ℝ) * (2 / (x * (2 + x))) := by
            rw [mul_div_assoc]
    _ = (1 / 2 : ℝ) * ((1 : ℝ) / x - (1 : ℝ) / (2 + x)) := by
            exact congrArg (fun y : ℝ => (1 / 2 : ℝ) * y) hinv.symm

/-- Interval integral of the first reciprocal term in the partial-fraction
expansion. -/
theorem real_intervalIntegral_one_div_eq_log_endpoint
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / x =
      Real.log b - Real.log 2 := by
  have hb_pos : 0 < b :=
    lt_of_lt_of_le zero_lt_two hb
  have hbase : 0 < (2 : ℝ) :=
    zero_lt_two
  have hintegral :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / x =
        Real.log (b / 2) :=
    Real.integral_one_div_of_pos hbase hb_pos
  have hlog :
      Real.log (b / 2) = Real.log b - Real.log 2 :=
    Real.log_div (ne_of_gt hb_pos) (ne_of_gt hbase)
  exact Eq.trans hintegral hlog

/-- Interval integral of the translated reciprocal term in the partial-fraction
expansion. -/
theorem real_intervalIntegral_one_div_two_add_eq_log_endpoint
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x) =
      Real.log (2 + b) - Real.log 4 := by
  have hb_shift_pos : 0 < b + 2 :=
    add_pos_of_nonneg_of_pos (le_trans (le_of_lt zero_lt_two) hb) zero_lt_two
  have hfour : ((2 : ℝ) + 2) = 4 :=
    rfl
  have hfour_pos : 0 < ((2 : ℝ) + 2) := by
    exact Eq.subst (motive := fun y : ℝ => 0 < y) hfour.symm zero_lt_four
  have htranslated :
      ∫ x in (2 : ℝ)..b, (fun y : ℝ => (1 : ℝ) / y) (x + 2) =
        ∫ x in ((2 : ℝ) + 2)..(b + 2), (1 : ℝ) / x :=
    intervalIntegral.integral_comp_add_right
      (fun y : ℝ => (1 : ℝ) / y) 2
  have hleft :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x) =
        ∫ x in (2 : ℝ)..b, (fun y : ℝ => (1 : ℝ) / y) (x + 2) := by
    exact congrArg
      (fun f : ℝ → ℝ => ∫ x in (2 : ℝ)..b, f x)
      (funext
        (fun x : ℝ =>
          congrArg (fun y : ℝ => (1 : ℝ) / y) (add_comm 2 x)))
  have heval :
      ∫ x in ((2 : ℝ) + 2)..(b + 2), (1 : ℝ) / x =
        Real.log (b + 2) - Real.log ((2 : ℝ) + 2) := by
    have hintegral :
        ∫ x in ((2 : ℝ) + 2)..(b + 2), (1 : ℝ) / x =
          Real.log ((b + 2) / ((2 : ℝ) + 2)) :=
      Real.integral_one_div_of_pos hfour_pos hb_shift_pos
    have hlog :
        Real.log ((b + 2) / ((2 : ℝ) + 2)) =
          Real.log (b + 2) - Real.log ((2 : ℝ) + 2) :=
      Real.log_div (ne_of_gt hb_shift_pos) (ne_of_gt hfour_pos)
    exact Eq.trans hintegral hlog
  have hnormalize :
      Real.log (b + 2) - Real.log ((2 : ℝ) + 2) =
        Real.log (2 + b) - Real.log 4 := by
    have hb_comm : b + 2 = 2 + b :=
      add_comm b 2
    exact Eq.trans
      (congrArg
        (fun y : ℝ => Real.log y - Real.log ((2 : ℝ) + 2))
        hb_comm)
      (congrArg
        (fun y : ℝ => Real.log (2 + b) - Real.log y)
        hfour)
  calc
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x)
        = ∫ x in (2 : ℝ)..b, (fun y : ℝ => (1 : ℝ) / y) (x + 2) :=
            hleft
    _ = ∫ x in ((2 : ℝ) + 2)..(b + 2), (1 : ℝ) / x :=
            htranslated
    _ = Real.log (b + 2) - Real.log ((2 : ℝ) + 2) :=
            heval
    _ = Real.log (2 + b) - Real.log 4 :=
            hnormalize

/-- The reciprocal function is interval-integrable on `[2,b]`. -/
theorem real_intervalIntegrable_one_div_two_to
    {b : ℝ} :
    IntervalIntegrable (fun x : ℝ => (1 : ℝ) / x) volume (2 : ℝ) b := by
  exact intervalIntegrable_one_div
    (fun x hx => by
      have hx_pos : 0 < x := by
        exact lt_of_lt_of_le zero_lt_two (Set.mem_uIcc.mp hx).1
      exact ne_of_gt hx_pos)
    continuousOn_id

/-- The translated reciprocal function is interval-integrable on `[2,b]`. -/
theorem real_intervalIntegrable_one_div_two_add_two_to
    {b : ℝ} :
    IntervalIntegrable (fun x : ℝ => (1 : ℝ) / (2 + x)) volume (2 : ℝ) b := by
  exact intervalIntegrable_one_div
    (fun x hx => by
      have hx_lower : (2 : ℝ) ≤ x :=
        (Set.mem_uIcc.mp hx).1
      have hpos : 0 < 2 + x :=
        add_pos_of_pos_of_nonneg zero_lt_two
          (le_trans (le_of_lt zero_lt_two) hx_lower)
      exact ne_of_gt hpos)
    (continuousOn_const.add continuousOn_id)

/-- Partial-fraction normalization under the interval integral. -/
theorem real_intervalIntegral_one_div_mul_two_add_eq_half_sub_integral
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
      (1 / 2 : ℝ) *
        (∫ x in (2 : ℝ)..b, (1 : ℝ) / x -
          ∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x)) := by
  have hpoint :
      EqOn
        (fun x : ℝ => (1 : ℝ) / (x * (2 + x)))
        (fun x : ℝ =>
          (1 / 2 : ℝ) * ((1 : ℝ) / x - (1 : ℝ) / (2 + x)))
        (Set.uIcc (2 : ℝ) b) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le zero_lt_two (Set.mem_uIcc.mp hx).1
    have hx_two_pos : 0 < 2 + x :=
      add_pos_of_pos_of_nonneg zero_lt_two (le_of_lt hx_pos)
    exact real_one_div_mul_two_add_eq_half_sub
      (ne_of_gt hx_pos)
      (ne_of_gt hx_two_pos)
  have hcongr :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
        ∫ x in (2 : ℝ)..b,
          (1 / 2 : ℝ) * ((1 : ℝ) / x - (1 : ℝ) / (2 + x)) :=
    intervalIntegral.integral_congr hpoint
  have hone : IntervalIntegrable (fun x : ℝ => (1 : ℝ) / x) volume (2 : ℝ) b :=
    real_intervalIntegrable_one_div_two_to
  have htwo :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / (2 + x)) volume (2 : ℝ) b :=
    real_intervalIntegrable_one_div_two_add_two_to
  have hlinear :
      ∫ x in (2 : ℝ)..b,
          (1 / 2 : ℝ) * ((1 : ℝ) / x - (1 : ℝ) / (2 + x)) =
        (1 / 2 : ℝ) *
          (∫ x in (2 : ℝ)..b, (1 : ℝ) / x -
            ∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x)) := by
    calc
      ∫ x in (2 : ℝ)..b,
          (1 / 2 : ℝ) * ((1 : ℝ) / x - (1 : ℝ) / (2 + x))
          =
        (1 / 2 : ℝ) *
          ∫ x in (2 : ℝ)..b, ((1 : ℝ) / x - (1 : ℝ) / (2 + x)) := by
            exact intervalIntegral.integral_const_mul (1 / 2 : ℝ)
              (fun x : ℝ => (1 : ℝ) / x - (1 : ℝ) / (2 + x))
      _ = (1 / 2 : ℝ) *
          (∫ x in (2 : ℝ)..b, (1 : ℝ) / x -
            ∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x)) := by
            exact congrArg (fun y : ℝ => (1 / 2 : ℝ) * y)
              (intervalIntegral.integral_sub hone htwo)
  exact Eq.trans hcongr hlinear

/-- Antiderivative evaluation for the reciprocal-density scalar integrand.

The antiderivative is `(log x - log (2 + x)) / 2`; the lower endpoint is
`2`, where the value is `(log 2 - log 4) / 2`. -/
theorem real_intervalIntegral_one_div_mul_two_add_eq_logs_interval_core
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
      ((Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4)) / 2 := by
  have hpartial :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
        (1 / 2 : ℝ) *
          (∫ x in (2 : ℝ)..b, (1 : ℝ) / x -
            ∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x)) :=
    real_intervalIntegral_one_div_mul_two_add_eq_half_sub_integral hb
  have hone :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / x =
        Real.log b - Real.log 2 :=
    real_intervalIntegral_one_div_eq_log_endpoint hb
  have htwo :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x) =
        Real.log (2 + b) - Real.log 4 :=
    real_intervalIntegral_one_div_two_add_eq_log_endpoint hb
  have hlogs :
      (1 / 2 : ℝ) *
          ((Real.log b - Real.log 2) -
            (Real.log (2 + b) - Real.log 4)) =
        ((Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4)) / 2 := by
    calc
      (1 / 2 : ℝ) *
          ((Real.log b - Real.log 2) -
            (Real.log (2 + b) - Real.log 4))
          =
        ((Real.log b - Real.log 2) -
          (Real.log (2 + b) - Real.log 4)) / 2 := by
            exact (mul_div_assoc
              ((Real.log b - Real.log 2) -
                (Real.log (2 + b) - Real.log 4)) 1 2).symm
      _ = ((Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4)) / 2 := by
            have halg :
                (Real.log b - Real.log 2) -
                  (Real.log (2 + b) - Real.log 4) =
                (Real.log b - Real.log (2 + b)) -
                  (Real.log 2 - Real.log 4) := by
              exact sub_sub_sub_comm
                (Real.log b) (Real.log 2) (Real.log (2 + b)) (Real.log 4)
            exact congrArg (fun y : ℝ => y / 2) halg
  exact Eq.trans hpartial
    (Eq.trans
      (congrArg
        (fun y : ℝ => (1 / 2 : ℝ) * y)
        (Eq.trans
          (congrArg
            (fun y : ℝ =>
              y - ∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x))
            hone)
          (congrArg
            (fun y : ℝ => (Real.log b - Real.log 2) - y)
            htwo)))
      hlogs)

/-- Endpoint evaluation of the interval integral of the scalar reciprocal
density in interval-integral notation. -/
theorem real_intervalIntegral_one_div_mul_two_add_eq_logs_interval
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
      ((Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4)) / 2 := by
  exact real_intervalIntegral_one_div_mul_two_add_eq_logs_interval_core hb

/-- Integration-by-parts identity for the finite scalar tail
`∫ log(2+x)/x²`.

This is the exact finite identity behind the tail bound:
the antiderivative of the main part is `-log(2+x)/x`, and the remaining
positive term is `1/(x*(2+x))`. -/
theorem real_integral_Ioc_log_two_add_div_sq_eq_by_parts
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
        ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) := by
  have hmain :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        ∫ x in (2 : ℝ)..b, Real.log (2 + x) * (1 / x ^ 2) :=
    real_integral_Ioc_log_two_add_div_sq_eq_mul_inv_sq hb
  have hparts :
      ∫ x in (2 : ℝ)..b, Real.log (2 + x) * (1 / x ^ 2) =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) :=
    real_intervalIntegral_log_two_add_mul_inv_sq_eq_by_parts hb
  have hremainder :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
        ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) :=
    real_intervalIntegral_one_div_mul_two_add_eq_Ioc hb
  exact Eq.trans hmain
    (Eq.trans hparts
      (congrArg
        (fun R : ℝ =>
          ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) + R)
        hremainder))

/-- Elementary endpoint bound for the finite scalar tail after the
integration-by-parts identity. -/
theorem real_intervalIntegral_one_div_mul_two_add_eq_logs
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) =
      ((Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4)) / 2 := by
  have hset :
      ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) =
        ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) :=
    (intervalIntegral.integral_of_le hb).symm
  have heval :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
        ((Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4)) / 2 :=
    real_intervalIntegral_one_div_mul_two_add_eq_logs_interval hb
  exact Eq.trans hset heval

theorem real_intervalIntegral_one_div_mul_two_add_le_half_log_two
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
      Real.log 2 / 2 := by
  have heval :
      ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) =
        ((Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4)) / 2 :=
    real_intervalIntegral_one_div_mul_two_add_eq_logs hb
  have hb_pos : 0 < b :=
    lt_of_lt_of_le zero_lt_two hb
  have hb_le_two_add : b ≤ 2 + b :=
    le_add_of_nonneg_left (le_of_lt zero_lt_two)
  have hlog_le : Real.log b ≤ Real.log (2 + b) :=
    Real.log_le_log hb_pos hb_le_two_add
  have hdiff_nonpos : Real.log b - Real.log (2 + b) ≤ 0 :=
    sub_nonpos.mpr hlog_le
  have hlog_two_four :
      Real.log 2 - Real.log 4 = -(Real.log 2) := by
    have hfour : (4 : ℝ) = 2 * 2 := by
      exact (show (2 : ℝ) * 2 = 4 by rfl).symm
    have hlog4 : Real.log 4 = Real.log 2 + Real.log 2 := by
      calc
        Real.log 4 = Real.log (2 * 2) := congrArg Real.log hfour
        _ = Real.log 2 + Real.log 2 :=
          Real.log_mul (ne_of_gt zero_lt_two) (ne_of_gt zero_lt_two)
    calc
      Real.log 2 - Real.log 4 =
          Real.log 2 - (Real.log 2 + Real.log 2) := by
        exact congrArg (fun y : ℝ => Real.log 2 - y) hlog4
      _ = -(Real.log 2) := by
        exact sub_add_cancel (Real.log 2) (Real.log 2) ▸ rfl
  have hnum_le :
      (Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4) ≤ Real.log 2 := by
    have hrewrite :
        (Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4) =
          (Real.log b - Real.log (2 + b)) + Real.log 2 := by
      calc
        (Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4) =
          (Real.log b - Real.log (2 + b)) - (-(Real.log 2)) := by
          exact congrArg
            (fun y : ℝ => (Real.log b - Real.log (2 + b)) - y)
            hlog_two_four
        _ = (Real.log b - Real.log (2 + b)) + Real.log 2 :=
          sub_neg_eq_add (Real.log b - Real.log (2 + b)) (Real.log 2)
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ Real.log 2)
      hrewrite.symm
      (calc
        (Real.log b - Real.log (2 + b)) + Real.log 2 ≤
            0 + Real.log 2 :=
          add_le_add_right hdiff_nonpos (Real.log 2)
        _ = Real.log 2 :=
          zero_add (Real.log 2))
  have hhalf_nonneg : (0 : ℝ) ≤ 2 :=
    le_of_lt zero_lt_two
  have hbound :
      ((Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4)) / 2 ≤ Real.log 2 / 2 :=
    div_le_div_of_nonneg_right hnum_le hhalf_nonneg
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ Real.log 2 / 2)
    heval.symm
    hbound

/-- Endpoint contribution after integration by parts is bounded by `log 4 / 2`. -/
theorem real_log_two_add_by_parts_endpoint_le_log_four_half
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    (-Real.log (2 + b) / b) - (-Real.log 4 / 2) ≤
      Real.log 4 / 2 := by
  have hb_pos : 0 < b :=
    lt_of_lt_of_le zero_lt_two hb
  have hlog_nonneg : 0 ≤ Real.log (2 + b) :=
    real_log_two_add_nonneg_of_two_le hb
  have hdiv_nonneg : 0 ≤ Real.log (2 + b) / b :=
    div_nonneg hlog_nonneg (le_of_lt hb_pos)
  have hneg_nonpos : -Real.log (2 + b) / b ≤ 0 := by
    have hneg : -(Real.log (2 + b) / b) ≤ 0 :=
      neg_nonpos.mpr hdiv_nonneg
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ 0)
      (neg_div (Real.log (2 + b)) b)
      hneg
  calc
    (-Real.log (2 + b) / b) - (-Real.log 4 / 2) =
        (-Real.log (2 + b) / b) + Real.log 4 / 2 := by
      exact sub_neg_eq_add (-Real.log (2 + b) / b) (Real.log 4 / 2)
    _ ≤ 0 + Real.log 4 / 2 :=
      add_le_add_right hneg_nonpos (Real.log 4 / 2)
    _ = Real.log 4 / 2 :=
      zero_add (Real.log 4 / 2)

/-- The sharp partial-fractions remainder and endpoint estimates fit under
the available `log 4` budget. -/
theorem real_log_four_half_add_log_two_half_le_log_four :
    Real.log 4 / 2 + Real.log 2 / 2 ≤ Real.log 4 := by
  have hlog_two_le_log_four : Real.log 2 ≤ Real.log 4 :=
    Real.log_le_log zero_lt_two
      (Eq.subst
        (motive := fun y : ℝ => (2 : ℝ) ≤ y)
        (show (2 : ℝ) + 2 = 4 by rfl)
        (le_add_of_nonneg_right (le_of_lt zero_lt_two)))
  have hhalf_nonneg : (0 : ℝ) ≤ 2 :=
    le_of_lt zero_lt_two
  have hhalf :
      Real.log 2 / 2 ≤ Real.log 4 / 2 :=
    div_le_div_of_nonneg_right hlog_two_le_log_four hhalf_nonneg
  have hsum :
      Real.log 4 / 2 + Real.log 2 / 2 ≤
        Real.log 4 / 2 + Real.log 4 / 2 :=
    add_le_add_left hhalf (Real.log 4 / 2)
  exact le_trans hsum (le_of_eq (add_halves (Real.log 4)))

theorem real_integral_Ioc_log_two_add_div_sq_by_parts_terms_le_log_four
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
        ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
      Real.log 4 := by
  have hendpoint :
      (-Real.log (2 + b) / b) - (-Real.log 4 / 2) ≤
        Real.log 4 / 2 :=
    real_log_two_add_by_parts_endpoint_le_log_four_half hb
  have hremainder :
      ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
        Real.log 2 / 2 :=
    real_intervalIntegral_one_div_mul_two_add_le_half_log_two hb
  have hsum :
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
        Real.log 4 / 2 + Real.log 2 / 2 :=
    add_le_add hendpoint hremainder
  exact le_trans hsum real_log_four_half_add_log_two_half_le_log_four

/-- Standard finite integration-by-parts tail estimate for
`log(2+x)/x²` from the canonical cutoff `2`.

The proof is the real-variable identity
`d(-log(2+x)/x) = log(2+x)/x² - 1/(x(2+x))`, followed by the elementary
endpoint estimate
`log 4 / 2 + ∫₂^∞ 1/(x(2+x)) ≤ log 4`. -/
theorem real_integral_Ioc_two_log_two_add_div_sq_tail_bound_by_parts
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 ≤
      Real.log 4 := by
  have hparts :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) :=
    real_integral_Ioc_log_two_add_div_sq_eq_by_parts hb
  have hbound :
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
        Real.log 4 :=
    real_integral_Ioc_log_two_add_div_sq_by_parts_terms_le_log_four hb
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ Real.log 4)
    hparts.symm
    hbound

/-- Fixed improper-tail bound from the canonical cutoff `2`. -/
theorem real_integral_Ioc_two_log_two_add_div_sq_tail_bound
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 ≤
      Real.log 4 := by
  exact real_integral_Ioc_two_log_two_add_div_sq_tail_bound_by_parts hb

/-- Adjacent `Ioc` intervals split the finite reciprocal-density scalar
integral. -/
theorem real_integral_Ioc_log_two_add_div_sq_adjacent_split
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
      ∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2 +
        ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 := by
  let f : ℝ → ℝ := fun x => Real.log (2 + x) / x ^ 2
  have htwo_b : (2 : ℝ) ≤ b :=
    le_trans ha hab
  have hleft :
      ∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2 =
        ∫ x in (2 : ℝ)..a, f x :=
    (intervalIntegral.integral_of_le ha).symm
  have hright :
      ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 =
        ∫ x in a..b, f x :=
    (intervalIntegral.integral_of_le hab).symm
  have hall :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        ∫ x in (2 : ℝ)..b, f x :=
    (intervalIntegral.integral_of_le htwo_b).symm
  have hleft_interval : IntervalIntegrable f volume (2 : ℝ) a := by
    fun_prop
  have hright_interval : IntervalIntegrable f volume a b := by
    fun_prop
  have hadd :
      (∫ x in (2 : ℝ)..a, f x) + ∫ x in a..b, f x =
        ∫ x in (2 : ℝ)..b, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      hleft_interval hright_interval
  exact Eq.trans hall
    (Eq.trans hadd.symm
      (congrArg₂ (fun u v : ℝ => u + v) hleft.symm hright.symm))

/-- Improper-tail comparison for `log(2+x)/x²` after the cutoff `2`.

This is the canonical real-analysis theorem behind the reciprocal-density
scalar estimate.  It is independent of zeta and is normally proved by
integration by parts:
`d(-log(2+x)/x) = log(2+x)/x² - 1/(x(2+x))`, followed by nonnegativity of the
remainder and endpoint evaluation at `x = 2`. -/
theorem real_integral_Ioc_log_two_add_div_sq_tail_bound_of_two_le
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
      Real.log 4 := by
  have htwo_le_b : (2 : ℝ) ≤ b :=
    le_trans ha hab
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (2 : ℝ) a)]
        (fun x : ℝ => Real.log (2 + x) / x ^ 2) :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx =>
        real_log_two_add_div_sq_nonneg_of_two_le (le_of_lt hx.1))
  have htail_split :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        ∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2 +
          ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 := by
    exact real_integral_Ioc_log_two_add_div_sq_adjacent_split ha hab
  have hleft_nonneg :
      0 ≤ ∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2 :=
    integral_nonneg_of_ae hnonneg
  have hle_tail :
      ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
        ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 := by
    have hadd :
        ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
          ∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2 +
            ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 :=
      le_add_of_nonneg_left hleft_nonneg
    exact Eq.subst
      (motive := fun y : ℝ =>
        ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤ y)
      htail_split.symm
      hadd
  exact le_trans hle_tail
    (real_integral_Ioc_two_log_two_add_div_sq_tail_bound htwo_le_b)

theorem real_integral_Ioc_log_two_add_div_sq_tail_bound
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
      Real.log 4 := by
  exact
    real_integral_Ioc_log_two_add_div_sq_tail_bound_of_two_le
      ha hab

/-- Canonical real-variable comparison for the finite `log(2+x)/x²` integral.

On any interval beginning after `2`, the tail integral is bounded uniformly by
the full tail from `2` to infinity; that tail is below `Real.log 4`.  The
displayed height parameter is only used through `1 ≤ H`, hence
`Real.log 4 ≤ Real.log (3+H)`. -/
theorem real_integral_Ioc_log_two_add_div_sq_le_log_three_add_height
    {H a b : ℝ}
    (hH : (1 : ℝ) ≤ H)
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
      Real.log (3 + H) := by
  have htail :
      ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤ Real.log 4 :=
    real_integral_Ioc_log_two_add_div_sq_tail_bound ha hab
  have hfour_le : (4 : ℝ) ≤ 3 + H := by
    calc
      (4 : ℝ) = 3 + 1 := by
        rfl
      _ ≤ 3 + H :=
        add_le_add_left hH 3
  have hlog_four_le : Real.log 4 ≤ Real.log (3 + H) := by
    have hfour_pos : (0 : ℝ) < 4 := by
      exact zero_lt_four
    exact Real.log_le_log hfour_pos hfour_le
  exact le_trans htail hlog_four_le

/-- Scalar calculus owner for the `log(2+x)/x` post-cutoff integral.

Proof route: on the post-cutoff interval, `2 ≤ x`, hence
`log(2+x)/x ≤ 2 * log(2+x)/(2+x)`, the derivative of
`(Real.log (2+x))^2`.  The fundamental theorem of calculus and endpoint
monotonicity then bound the finite interval by the right endpoint square. -/
theorem scalarReciprocalDensity_log_over_x_integral_bound_calculus
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        Real.log (2 + x) / x ≤
      (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 := by
  have hN_two :
      (2 : ℝ) ≤ (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    scalarReciprocalDensity_two_le_cutoff_real t
  have hNM_real :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ ((M : ℕ) : ℝ) :=
    Nat.cast_le.mpr hNM
  exact
    real_integral_Ioc_log_two_add_div_self_le_log_endpoint_sq
      hN_two hNM_real

/-- Scalar calculus owner for the `log(2+x)/x²` post-cutoff integral.

Proof route: use `Real.log_div_self_rpow_antitoneOn` for the decreasing
positive tail profile after the cutoff, or equivalently integrate by parts:
`∫ log(2+x)/x²` is bounded by the cutoff endpoint contribution plus the
integrable `1/(x(2+x))` remainder.  Since the cutoff is at least `2+|t|`, the
result is dominated by `Real.log (3 + ‖t‖)`. -/
theorem scalarReciprocalDensity_log_over_x_sq_integral_bound_calculus
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        Real.log (2 + x) / x ^ 2 ≤
      Real.log (3 + ‖t‖) := by
  have hN_two :
      (2 : ℝ) ≤ (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    scalarReciprocalDensity_two_le_cutoff_real t
  have hNM_real :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ ((M : ℕ) : ℝ) :=
    Nat.cast_le.mpr hNM
  exact
    real_integral_Ioc_log_two_add_div_sq_le_log_three_add_height
      ht hN_two hNM_real


/-- Finite-endpoint calculus bound for the `log(2+x)/x` contribution. -/
theorem scalarReciprocalDensity_log_over_x_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        Real.log (2 + x) / x ≤
      (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 := by
  exact scalarReciprocalDensity_log_over_x_integral_bound_calculus t ht hNM

/-- Finite-endpoint calculus bound for the `log(2+x)/x^2` contribution. -/
theorem scalarReciprocalDensity_log_over_x_sq_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        Real.log (2 + x) / x ^ 2 ≤
      Real.log (3 + ‖t‖) := by
  exact scalarReciprocalDensity_log_over_x_sq_integral_bound_calculus t ht hNM

/-- Pointwise algebraic split of the coarse reciprocal-density majorant.

The factor `x / |t|` contributes the `log(2+x)/x` term, using `1 ≤ |t|`; the
remaining `sqrt(1+|t|)` term contributes `log(2+x)/x²`. -/
theorem scalarReciprocalDensityMajorant_pointwise_split
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : 0 < x) :
    ((1 : ℝ) / x ^ 2) *
        (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      8 * (Real.log (2 + x) / x) +
        8 * Real.sqrt (1 + ‖t‖) * (Real.log (2 + x) / x ^ 2) := by
  let L : ℝ := Real.log (2 + x)
  let S : ℝ := Real.sqrt (1 + ‖t‖)
  let T : ℝ := ‖t‖
  have hT_pos : 0 < T :=
    lt_of_lt_of_le zero_lt_one ht
  have hx_nonneg : 0 ≤ x :=
    le_of_lt hx
  have hx_sq_pos : 0 < x ^ 2 :=
    sq_pos_of_pos hx
  have hx_sq_nonneg : 0 ≤ x ^ 2 :=
    le_of_lt hx_sq_pos
  have hL_nonneg : 0 ≤ L := by
    have hone_le_two : (1 : ℝ) ≤ 2 := by
      calc
        (1 : ℝ) ≤ 1 + 1 := le_add_of_nonneg_right zero_le_one
        _ = 2 := by
          rfl
    have htwo_le_two_add : (2 : ℝ) ≤ 2 + x :=
      add_le_add_left hx_nonneg 2
    exact Real.log_nonneg (le_trans hone_le_two htwo_le_two_add)
  have hS_nonneg : 0 ≤ S :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have height_nonneg : 0 ≤ (8 : ℝ) :=
    ofNat_nonneg 8
  have hweight_nonneg : 0 ≤ (1 : ℝ) / x ^ 2 := by
    exact div_nonneg zero_le_one hx_sq_nonneg
  have hfirst_ratio : x / T ≤ x := by
    have hmul_le : x ≤ x * T := by
      calc
        x = x * 1 := by
          exact (mul_one x).symm
        _ ≤ x * T :=
          mul_le_mul_of_nonneg_left ht hx_nonneg
    exact (div_le_iff₀ hT_pos).mpr hmul_le
  have hsum_le : (x / T) + S ≤ x + S :=
    add_le_add_right hfirst_ratio S
  have hmajor_le :
      8 * ((x / T) + S) * L ≤ 8 * (x + S) * L := by
    have hscaled :
        8 * ((x / T) + S) ≤ 8 * (x + S) :=
      mul_le_mul_of_nonneg_left hsum_le height_nonneg
    exact mul_le_mul_of_nonneg_right hscaled hL_nonneg
  have hweighted_major :
      ((1 : ℝ) / x ^ 2) * (8 * ((x / T) + S) * L) ≤
        ((1 : ℝ) / x ^ 2) * (8 * (x + S) * L) :=
    mul_le_mul_of_nonneg_left hmajor_le hweight_nonneg
  have hexpanded_bound :
      ((1 : ℝ) / x ^ 2) * (8 * (x + S) * L) =
        8 * (L / x) + 8 * S * (L / x ^ 2) := by
    calc
      ((1 : ℝ) / x ^ 2) * (8 * (x + S) * L) =
          ((1 : ℝ) / x ^ 2) * ((8 * x + 8 * S) * L) := by
        exact congrArg
          (fun y : ℝ => ((1 : ℝ) / x ^ 2) * (y * L))
          (mul_add 8 x S)
      _ = ((1 : ℝ) / x ^ 2) * (8 * x * L + 8 * S * L) := by
        exact congrArg
          (fun y : ℝ => ((1 : ℝ) / x ^ 2) * y)
          (add_mul (8 * x) (8 * S) L)
      _ =
          ((1 : ℝ) / x ^ 2) * (8 * x * L) +
            ((1 : ℝ) / x ^ 2) * (8 * S * L) := by
        exact mul_add ((1 : ℝ) / x ^ 2) (8 * x * L) (8 * S * L)
      _ = 8 * (L / x) +
            ((1 : ℝ) / x ^ 2) * (8 * S * L) := by
        have hx_ne : x ≠ 0 :=
          ne_of_gt hx
        have hx_sq_ne : x ^ 2 ≠ 0 :=
          pow_ne_zero 2 hx_ne
        have hfirst :
            ((1 : ℝ) / x ^ 2) * (8 * x * L) = 8 * (L / x) := by
          calc
            ((1 : ℝ) / x ^ 2) * (8 * x * L) =
                8 * L * (x / x ^ 2) := by
              ac_rfl
            _ = 8 * L * (1 / x) := by
              have hx_cancel : x / x ^ 2 = 1 / x := by
                calc
                  x / x ^ 2 = x / (x * x) := by
                    exact congrArg (fun y : ℝ => x / y) (sq x)
                  _ = 1 / x := by
                    exact div_mul_cancel_left₀ hx_ne x
              exact congrArg (fun y : ℝ => 8 * L * y) hx_cancel
            _ = 8 * (L / x) := by
              calc
                8 * L * (1 / x) = 8 * (L * (1 / x)) := by
                  exact mul_assoc 8 L (1 / x)
                _ = 8 * (L / x) := by
                  exact congrArg (fun y : ℝ => 8 * y) (div_eq_mul_one_div L x).symm
        exact congrArg
          (fun y : ℝ => y + ((1 : ℝ) / x ^ 2) * (8 * S * L))
          hfirst
      _ = 8 * (L / x) + 8 * S * (L / x ^ 2) := by
        have hsecond :
            ((1 : ℝ) / x ^ 2) * (8 * S * L) =
              8 * S * (L / x ^ 2) := by
          calc
            ((1 : ℝ) / x ^ 2) * (8 * S * L) =
                8 * S * (L * ((1 : ℝ) / x ^ 2)) := by
              ac_rfl
            _ = 8 * S * (L / x ^ 2) := by
              exact congrArg
                (fun y : ℝ => 8 * S * y)
                (div_eq_mul_one_div L (x ^ 2)).symm
        exact congrArg (fun y : ℝ => 8 * (L / x) + y) hsecond
  exact le_trans hweighted_major (le_of_eq hexpanded_bound)

/-- Integral transport of the pointwise scalar split over the post-cutoff
interval. -/
theorem scalarReciprocalDensityMajorant_integral_split_le_components
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        (8 * (Real.log (2 + x) / x) +
          8 * Real.sqrt (1 + ‖t‖) * (Real.log (2 + x) / x ^ 2)) := by
  let s : Set ℝ :=
    Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)
  let f : ℝ → ℝ := fun x =>
    ((1 : ℝ) / x ^ 2) *
      (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
  let g : ℝ → ℝ := fun x =>
    8 * (Real.log (2 + x) / x) +
      8 * Real.sqrt (1 + ‖t‖) * (Real.log (2 + x) / x ^ 2)
  have hf : Integrable f (volume.restrict s) := by
    fun_prop
  have hg : Integrable g (volume.restrict s) := by
    fun_prop
  have hle : f ≤ᵐ[volume.restrict s] g :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx =>
        scalarReciprocalDensityMajorant_pointwise_split
          t ht (scalarReciprocalDensity_Ioc_point_pos t hx))
  exact integral_mono_ae hf hg hle

/-- The component integral bounds imply the finite-endpoint bound for the
split scalar majorant. -/
theorem scalarReciprocalDensityMajorant_components_le_endpoint_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hlog_over_x :
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          Real.log (2 + x) / x ≤
        (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2)
    (hlog_over_x_sq :
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          Real.log (2 + x) / x ^ 2 ≤
        Real.log (3 + ‖t‖)) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        (8 * (Real.log (2 + x) / x) +
          8 * Real.sqrt (1 + ‖t‖) * (Real.log (2 + x) / x ^ 2)) ≤
      8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
        8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
  let s : Set ℝ :=
    Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)
  let f : ℝ → ℝ := fun x => Real.log (2 + x) / x
  let g : ℝ → ℝ := fun x => Real.log (2 + x) / x ^ 2
  let A : ℝ := (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2
  let B : ℝ := Real.log (3 + ‖t‖)
  let S : ℝ := Real.sqrt (1 + ‖t‖)
  have hf : Integrable (fun x => 8 * f x) (volume.restrict s) := by
    fun_prop
  have hg : Integrable (fun x => 8 * S * g x) (volume.restrict s) := by
    fun_prop
  have hsum_eq :
      (∫ x in s, (8 * f x + 8 * S * g x)) =
        (∫ x in s, 8 * f x) + ∫ x in s, 8 * S * g x :=
    integral_add hf hg
  have hf_scale :
      (∫ x in s, 8 * f x) = 8 * ∫ x in s, f x :=
    integral_mul_left 8 f
  have hg_scale :
      (∫ x in s, 8 * S * g x) = (8 * S) * ∫ x in s, g x :=
    integral_mul_left (8 * S) g
  have height_nonneg : 0 ≤ (8 : ℝ) := by
    exact ofNat_nonneg 8
  have hS_nonneg : 0 ≤ S :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have hheightS_nonneg : 0 ≤ 8 * S :=
    mul_nonneg height_nonneg hS_nonneg
  have hfirst :
      (∫ x in s, 8 * f x) ≤ 8 * A := by
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ 8 * A)
      hf_scale.symm
      (mul_le_mul_of_nonneg_left hlog_over_x height_nonneg)
  have hsecond :
      (∫ x in s, 8 * S * g x) ≤ (8 * S) * B := by
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ (8 * S) * B)
      hg_scale.symm
      (mul_le_mul_of_nonneg_left hlog_over_x_sq hheightS_nonneg)
  have hsum_bound :
      (∫ x in s, 8 * f x) + ∫ x in s, 8 * S * g x ≤
        8 * A + (8 * S) * B :=
    add_le_add hfirst hsecond
  have htarget_eq :
      8 * A + (8 * S) * B =
        8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
          8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
    rfl
  exact Eq.subst
    (motive := fun y : ℝ =>
      y ≤
        8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
          8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖))
    hsum_eq.symm
    (le_trans hsum_bound (le_of_eq htarget_eq))

/-- Algebraic split of the coarse reciprocal-density scalar majorant into the
two real calculus integrals it requires. -/
theorem scalarReciprocalDensityMajorant_integral_split_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hlog_over_x :
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          Real.log (2 + x) / x ≤
        (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2)
    (hlog_over_x_sq :
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          Real.log (2 + x) / x ^ 2 ≤
        Real.log (3 + ‖t‖)) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
        8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
  exact
    le_trans
      (scalarReciprocalDensityMajorant_integral_split_le_components t ht hNM)
      (scalarReciprocalDensityMajorant_components_le_endpoint_bound
        t ht hNM hlog_over_x hlog_over_x_sq)

/-- Finite-endpoint real calculus bound for the coarse reciprocal-density
majorant.

The coarse first-derivative partial-sum majorant contains an `x / |t|` term, so
integrating it against `x⁻²` produces logarithmic growth in the right endpoint.
This is the honest scalar comparison; the uniform Abel/Euler-Maclaurin integral
bound must use the oscillatory cancellation theorem below, not this coarse
majorant alone. -/
theorem scalarReciprocalDensityMajorant_finiteEndpoint_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
        8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
  exact
    scalarReciprocalDensityMajorant_integral_split_bound
      t ht hNM
      (scalarReciprocalDensity_log_over_x_integral_bound t ht hNM)
      (scalarReciprocalDensity_log_over_x_sq_integral_bound t ht hNM)

/-- Finite real calculus estimate for the scalar reciprocal-density majorant.

This wrapper keeps the older local name while the owner theorem records the
finite-endpoint growth explicitly. -/
theorem reciprocalDensityIntegral_scalar_majorant_finite_endpoint_bound_calculus
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
        8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
  exact scalarReciprocalDensityMajorant_finiteEndpoint_integral_bound t ht hNM

/-- Oscillatory reciprocal-density integral estimate after the canonical cutoff.

This is not a consequence of integrating the coarse scalar majorant: that scalar
integral grows with the right endpoint.  The uniform bound is the
Euler-Maclaurin/first-derivative cancellation estimate for the concrete
reciprocal-amplitude term. -/
theorem partialSummation_reciprocalAmplitude_oscillatoryIntegral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  sorry

/-- Oscillatory reciprocal-density integral estimate after the canonical cutoff.

This is the concrete Abel/partial-summation estimate for the reciprocal
amplitude, consuming the already isolated partial-sum and reciprocal-density
inputs. -/
theorem oscillatoryReciprocalDensity_logarithmicPhase_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    partialSummation_reciprocalAmplitude_oscillatoryIntegral_bound
      t ht hpartial hNM hreciprocal_density

/-- Oscillatory reciprocal-density integral estimate after the canonical cutoff.

This local wrapper exposes the owner theorem under the reciprocal-density API. -/
theorem reciprocalDensityIntegral_oscillatory_le_log_cutoff
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    oscillatoryReciprocalDensity_logarithmicPhase_integral_bound
      t ht hpartial hNM hreciprocal_density

/-- Concrete reciprocal total-variation integral estimate after the
reciprocal derivative density has been identified. -/
theorem reciprocalDensityIntegral_logarithmicPhase_bound_of_partialSum_majorant
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    reciprocalDensityIntegral_oscillatory_le_log_cutoff
      t ht hpartial hNM hreciprocal_density

/-- Concrete reciprocal total-variation integral estimate after the
reciprocal derivative density has been identified. -/
theorem concreteReciprocalVariation_logarithmicPhase_integral_bound_of_density
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    reciprocalDensityIntegral_logarithmicPhase_bound_of_partialSum_majorant
      t ht hpartial hNM hreciprocal_density

/-- Concrete reciprocal total-variation integral estimate.

This is the real-variable Abel/Euler-Maclaurin variation step for the concrete
amplitude `u ↦ 1 / u`: after the cutoff `N = ⌊2 + |t|⌋₊`, the normalized
reciprocal derivative has total variation small enough that the first-derivative
partial-sum majorant gives the displayed logarithmic bound. -/
theorem concreteReciprocalVariation_logarithmicPhase_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    (hreciprocal_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) u =
          (-(1 : ℂ) / (u : ℂ) ^ 2))
    (hreciprocal_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) u‖ =
          (1 : ℝ) / u ^ 2)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    concreteReciprocalVariation_logarithmicPhase_integral_bound_of_density
      t ht hpartial hNM
      (concreteReciprocalVariation_density_bound_on_cutoff_interval t hNM)

/-- Concrete total-variation estimate for the reciprocal-amplitude term after
the logarithmic-phase first-derivative bound. -/
theorem oscillatoryEulerMaclaurin_logarithmicPhase_reciprocalVariation_bound_of_partialSums
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    (hreciprocal_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) u =
          (-(1 : ℂ) / (u : ℂ) ^ 2))
    (hreciprocal_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) u‖ =
          (1 : ℝ) / u ^ 2)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    concreteReciprocalVariation_logarithmicPhase_integral_bound
      t ht hpartial hreciprocal_deriv hreciprocal_deriv_norm hNM

/-- Concrete reciprocal-variation integral estimate for the logarithmic phase.

This is the variation term in Abel/Euler-Maclaurin summation for the amplitude
`u ↦ 1 / u` and the concrete oscillator `u ↦ exp (-i t log u)`.  The
reciprocal derivative is normalized as `‖(1/u)'‖ = 1/u^2`; the remaining
analytic input is the same first-derivative cancellation used for the
logarithmic-phase partial sums. -/
theorem oscillatoryEulerMaclaurin_logarithmicPhase_reciprocalVariation_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hphase_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u =
          (((-(t : ℂ) * Complex.I) / (u : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhaseFunction t u))
    (hphase_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u‖ =
          ‖t‖ / u)
    (hreciprocal_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) u =
          (-(1 : ℂ) / (u : ℂ) ^ 2))
    (hreciprocal_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) u‖ =
          (1 : ℝ) / u ^ 2)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  have hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
    intro x hx
    exact
      firstDerivativeEulerMaclaurin_logarithmicPhase_partialSum_bound
        t ht hphase_deriv hphase_deriv_norm hx
  exact
    oscillatoryEulerMaclaurin_logarithmicPhase_reciprocalVariation_bound_of_partialSums
      t ht hpartial hreciprocal_deriv hreciprocal_deriv_norm hNM

/-- Sharper reciprocal-derivative integral estimate in the logarithmic-phase
partial-summation package.

This is the variation part of the oscillatory Euler-Maclaurin argument.  The
estimate keeps cancellation in the logarithmic phase before integrating against
the reciprocal derivative; it is not a consequence of the coarse primitive
majorant alone. -/
theorem oscillatoryEulerMaclaurin_logarithmicPhase_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    oscillatoryEulerMaclaurin_logarithmicPhase_reciprocalVariation_integral_bound
      t ht
      (fun hu => boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_eq t hu)
      (fun hu => boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq t hu)
      (fun hu => complexReciprocalOfReal_deriv_eq hu)
      (fun hu => complexReciprocalOfReal_deriv_norm_eq hu)
      hNM

/-- Integral arithmetic for the reciprocal-derivative term in the finite Abel
decomposition.

This is the variation side of partial summation for the weight `x ↦ 1 / x`.
After the first-derivative Euler-Maclaurin estimate bounds the logarithmic-phase
primitive, this theorem owns the monotone reciprocal-variation integral and the
normalization to the cutoff logarithm.  Cf. Edwards, *Riemann's Zeta Function*,
Euler-Maclaurin derivations. -/
theorem eulerMaclaurin_logarithmicPhase_finiteAbel_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact oscillatoryEulerMaclaurin_logarithmicPhase_integral_bound t ht hNM

/-- Deep Euler-Maclaurin arithmetic owner for the finite Abel endpoint and
reciprocal-derivative integral terms.

This is the remaining bookkeeping attached to the first-derivative
Euler-Maclaurin estimate: the reciprocal endpoint weights and the integral of
the reciprocal derivative are both normalized to the same logarithmic cutoff
constant. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_endpoint_integral_arithmetic
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖)) ∧
    (‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖)) := by
  exact
    ⟨eulerMaclaurin_logarithmicPhase_finiteAbel_endpoint_bound t ht hNM,
      eulerMaclaurin_logarithmicPhase_finiteAbel_integral_bound t ht hNM⟩

/-- Exact endpoint arithmetic for the finite Abel package.  This is the
reciprocal-weight endpoint part after the first-derivative estimate has been
applied at `M` and at the canonical cutoff. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_endpoint_arithmetic
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    (logarithmicPhase_firstDerivative_finiteAbel_endpoint_integral_arithmetic
      t ht hNM).1

/-- Exact reciprocal-derivative integral arithmetic for the finite Abel package.
The analytic input is the first-derivative partial-sum estimate; this lemma owns
the endpoint and logarithmic integral bookkeeping. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_integral_arithmetic
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    (logarithmicPhase_firstDerivative_finiteAbel_endpoint_integral_arithmetic
      t ht hNM).2

/-- Algebraic endpoint extraction from the logarithmic-phase first-derivative
partial-sum estimate.

This is not a separate analytic input: the two reciprocal endpoint weights are
controlled after the canonical cutoff by applying
`logarithmicPhasePartialSum_firstDerivative_bound` at `M` and at the cutoff. -/
theorem logarithmicPhase_firstDerivative_eulerMaclaurin_finiteAbel_package
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊((M : ℕ) : ℝ)⌋₊‖ ≤
        8 * ((((M : ℕ) : ℝ) / ‖t‖) + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ((M : ℕ) : ℝ))) ∧
    (‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖)) ∧
    (‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖)) := by
  exact
    ⟨logarithmicPhase_firstDerivative_finiteAbel_rightPartial_bound t ht hNM,
      logarithmicPhase_firstDerivative_finiteAbel_endpoint_arithmetic t ht hNM,
      logarithmicPhase_firstDerivative_finiteAbel_integral_arithmetic t ht hNM⟩

/-- Explicit finite Abel-tail constant for the logarithmic-phase oscillator
after the canonical cutoff.

The constant is intentionally not normalized to `1`: the owner estimate must
record the actual Abel endpoint and reciprocal-derivative contribution rather
than hiding it behind a false unit-bound surface. -/
def boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant
    (t : ℝ) : ℝ :=
  4 + 16 * Real.log (3 + ‖t‖)

/-- Owner API: endpoint contribution in the finite Abel decomposition after the
canonical cutoff. -/
theorem reciprocalDensity_logarithmicPhase_finiteAbelEndpoint_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ +
      ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    (logarithmicPhase_firstDerivative_eulerMaclaurin_finiteAbel_package
      t ht hNM).2.1

/-- Owner API: reciprocal-derivative integral contribution in the finite Abel
decomposition after the canonical cutoff. -/
theorem reciprocalDensity_logarithmicPhase_finiteAbelDerivativeIntegral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    (logarithmicPhase_firstDerivative_eulerMaclaurin_finiteAbel_package
      t ht hNM).2.2

/-- Finite reciprocal-weighted logarithmic-phase tail estimate after the
canonical cutoff.

This is the owner theorem needed by Abel transport: the finite tail of
`n⁻¹ n^{-it}` is controlled by the endpoint and reciprocal-derivative terms in
the Abel/Euler-Maclaurin identity. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  let SM : ℂ :=
    ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        ⌊((M : ℕ) : ℝ)⌋₊
  let SN : ℂ :=
    (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        ⌊(((N : ℕ) : ℝ))⌋₊
  let J : ℂ :=
    ∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ),
      deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊
  have hf_diff :
      ∀ x ∈ Set.Icc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x := by
    intro x hx
    fun_prop
  have hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ)) := by
    fun_prop
  have hidentity :
      (∑ k ∈ Finset.Ioc ⌊(((N : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
          ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        SM - SN - J := by
    exact
      abelSummation_boundaryLineOnePointRealParam_cutoff_finite_tail_endpoint_derivative_identity
        t hNM hf_diff hf_int
  have hendpoint :
      ‖SM‖ + ‖SN‖ ≤ 2 + 8 * Real.log (3 + ‖t‖) := by
    exact
      reciprocalDensity_logarithmicPhase_finiteAbelEndpoint_bound
        t ht hNM
  have hintegral :
      ‖J‖ ≤ 2 + 8 * Real.log (3 + ‖t‖) := by
    exact
      reciprocalDensity_logarithmicPhase_finiteAbelDerivativeIntegral_bound
        t ht hNM
  have htriangle :
      ‖SM - SN - J‖ ≤ ‖SM‖ + ‖SN‖ + ‖J‖ := by
    have hfirst : ‖SM - SN - J‖ ≤ ‖SM - SN‖ + ‖J‖ :=
      norm_sub_le (SM - SN) J
    have hsecond : ‖SM - SN‖ ≤ ‖SM‖ + ‖SN‖ :=
      norm_sub_le SM SN
    exact le_trans hfirst (add_le_add_right hsecond ‖J‖)
  have hpost_triangle :
      ‖SM‖ + ‖SN‖ + ‖J‖ ≤
        (2 + 8 * Real.log (3 + ‖t‖)) +
          (2 + 8 * Real.log (3 + ‖t‖)) := by
    exact add_le_add hendpoint hintegral
  have hconstant :
      (2 + 8 * Real.log (3 + ‖t‖)) +
          (2 + 8 * Real.log (3 + ‖t‖)) =
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
    let L : ℝ := Real.log (3 + ‖t‖)
    have hadd :
        (2 + 8 * L) + (2 + 8 * L) =
          (2 + 2) + (8 * L + 8 * L) := by
      ac_rfl
    have htwo : (2 : ℝ) + 2 = 4 := by
      rfl
    have height_coeff : (8 : ℝ) + 8 = 16 := by
      rfl
    have height : (8 : ℝ) * L + 8 * L = 16 * L := by
      calc
        (8 : ℝ) * L + 8 * L = ((8 : ℝ) + 8) * L := by
          exact (add_mul (8 : ℝ) 8 L).symm
        _ = 16 * L := by
          exact congrArg (fun c : ℝ => c * L) height_coeff
    calc
      (2 + 8 * Real.log (3 + ‖t‖)) +
          (2 + 8 * Real.log (3 + ‖t‖)) =
          (2 + 8 * L) + (2 + 8 * L) := by
        rfl
      _ = (2 + 2) + (8 * L + 8 * L) :=
        hadd
      _ = 4 + (8 * L + 8 * L) := by
        exact congrArg (fun x : ℝ => x + (8 * L + 8 * L)) htwo
      _ = 4 + 16 * L := by
        exact congrArg (fun x : ℝ => 4 + x) height
      _ = boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
        rfl
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
    hidentity.symm
    (le_trans htriangle (le_trans hpost_triangle (le_of_eq hconstant)))

end
end LFunctions
end Boundary
