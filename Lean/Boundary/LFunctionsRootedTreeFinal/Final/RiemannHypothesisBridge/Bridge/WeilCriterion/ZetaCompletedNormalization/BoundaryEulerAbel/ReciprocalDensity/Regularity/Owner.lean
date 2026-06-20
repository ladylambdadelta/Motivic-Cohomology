import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalVariation.Owner

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

/-- Local regularity of the reciprocal-square density away from zero. -/
theorem scalarReciprocalDensity_reciprocalSquare_continuousAt
    {x : ℝ}
    (hx : x ≠ 0) :
    ContinuousAt (fun y : ℝ => (1 : ℝ) / y ^ 2) x := by
  have hx_sq : x ^ 2 ≠ 0 :=
    pow_ne_zero 2 hx
  exact continuousAt_const.div (continuousAt_id.pow 2) hx_sq

/-- Local regularity of the shifted logarithm on its nonzero domain. -/
theorem scalarReciprocalDensity_logTwoAdd_continuousAt
    {x : ℝ}
    (hx : 2 + x ≠ 0) :
    ContinuousAt (fun y : ℝ => Real.log (2 + y)) x := by
  exact
    (continuousAt_log hx).comp
      (continuousAt_const.add continuousAt_id)

/-- Local regularity of `log(2+x) / x` away from the two singular points. -/
theorem scalarReciprocalDensity_logTwoAdd_div_self_continuousAt
    {x : ℝ}
    (hx : x ≠ 0)
    (hlog : 2 + x ≠ 0) :
    ContinuousAt (fun y : ℝ => Real.log (2 + y) / y) x := by
  exact
    (scalarReciprocalDensity_logTwoAdd_continuousAt hlog).div
      continuousAt_id
      hx

/-- Local regularity of `2 * log(2+x) / (2+x)` off the shifted-log pole. -/
theorem scalarReciprocalDensity_logSqDerivativeDensity_continuousAt
    {x : ℝ}
    (hx : 2 + x ≠ 0) :
    ContinuousAt
      (fun y : ℝ => 2 * Real.log (2 + y) / (2 + y))
      x := by
  have hnum :
      ContinuousAt (fun y : ℝ => 2 * Real.log (2 + y)) x :=
    continuousAt_const.mul
      (scalarReciprocalDensity_logTwoAdd_continuousAt hx)
  have hden :
      ContinuousAt (fun y : ℝ => 2 + y) x :=
    continuousAt_const.add continuousAt_id
  exact hnum.div hden hx

/-- Local regularity of `log(2+x) / x^2` away from the reciprocal and log poles. -/
theorem scalarReciprocalDensity_logTwoAdd_div_square_continuousAt
    {x : ℝ}
    (hx : x ≠ 0)
    (hlog : 2 + x ≠ 0) :
    ContinuousAt (fun y : ℝ => Real.log (2 + y) / y ^ 2) x := by
  have hx_sq : x ^ 2 ≠ 0 :=
    pow_ne_zero 2 hx
  exact
    (scalarReciprocalDensity_logTwoAdd_continuousAt hlog).div
      (continuousAt_id.pow 2)
      hx_sq

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
  exact
    fun x hx =>
      have hcutoff_pos : 0 < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
        Nat.cast_pos.mpr (boundaryLineOnePointRealParam_cutoff_pos t)
      reciprocalDerivative_norm_eq_on_positive_interval hcutoff_pos hx

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
  exact
    fun x hx =>
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
      Eq.subst
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
  have hcutoff_pos : 0 < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (boundaryLineOnePointRealParam_cutoff_pos t)
  have hg_cont :
      ContinuousOn g
        (Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)) := by
    exact
      fun x hx =>
        have hx_pos : x ≠ 0 :=
          ne_of_gt (lt_of_lt_of_le hcutoff_pos hx.1)
        have hlog_arg_pos : 2 + x ≠ 0 := by
          have htwo_add_pos : 0 < 2 + x :=
            add_pos_of_pos_of_nonneg zero_lt_two (le_of_lt (lt_of_lt_of_le hcutoff_pos hx.1))
          exact ne_of_gt htwo_add_pos
        have hreciprocal :
            ContinuousAt (fun y : ℝ => (1 : ℝ) / y ^ 2) x :=
          scalarReciprocalDensity_reciprocalSquare_continuousAt hx_pos
        have hquotient :
            ContinuousAt (fun y : ℝ => y / ‖t‖) x :=
          continuousAt_id.div_const ‖t‖
        have hshifted :
            ContinuousAt (fun y : ℝ => y / ‖t‖ + Real.sqrt (1 + ‖t‖)) x :=
          hquotient.add continuousAt_const
        have hweighted :
            ContinuousAt
              (fun y : ℝ => 8 * (y / ‖t‖ + Real.sqrt (1 + ‖t‖)))
              x :=
          continuousAt_const.mul hshifted
        have hlog :
            ContinuousAt (fun y : ℝ => Real.log (2 + y)) x :=
          scalarReciprocalDensity_logTwoAdd_continuousAt hlog_arg_pos
        have hright :
            ContinuousAt
              (fun y : ℝ =>
                8 * (y / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + y))
              x :=
          hweighted.mul hlog
        (hreciprocal.mul hright).continuousWithinAt
  have hg : Integrable g (volume.restrict s) :=
    (ContinuousOn.integrableOn_Icc hg_cont).mono_set Ioc_subset_Icc_self
  have hbound : ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx => hpointwise x hx)
  exact norm_integral_le_of_norm_le hg hbound

/- The public Bochner domination wrapper lives in `ReciprocalDensity.Calculus.Owner`. -/

end
end LFunctions
end Boundary
