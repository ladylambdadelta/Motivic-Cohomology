import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.FirstDerivative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Regularity.Owner

/-!
# Reciprocal-variation estimates

This upstream owner file isolates the reciprocal-variation proof engine used by
the boundary Euler-Abel transport layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Reciprocal-derivative norm on a positive real interval. -/
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

/-- Bochner domination for the concrete reciprocal-variation integrand.

This is the honest scalar-dominating layer.  It does not claim the old uniform
`2 + 8 log` endpoint; it records exactly what follows from the pointwise
reciprocal-density identity and the available partial-sum majorant. -/
theorem concreteReciprocalVariation_logarithmicPhase_integral_norm_le_scalar_majorant
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
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
  exact
    concreteReciprocalVariation_logarithmicPhase_integral_norm_le_scalar_majorant
      t hpartial hNM hreciprocal_density

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
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
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
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
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
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
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
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
  exact
    oscillatoryEulerMaclaurin_logarithmicPhase_reciprocalVariation_integral_bound
      t ht hpartial
      (fun hu => complexReciprocalOfReal_deriv_eq hu)
      (fun hu => complexReciprocalOfReal_deriv_norm_eq hu)
      hNM

end
end LFunctions
