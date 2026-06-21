import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Owner

/-!
# Abel transport setup: endpoint and derivative contributions

This file owns the foundational Abel-transport theorems for logarithmic-phase
endpoint and reciprocal-derivative contributions in finite Abel decompositions,
along with the basic summation identities.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem logarithmicPhase_finiteAbelEndpoint_bound
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
  exact logarithmicPhase_firstDerivative_finiteAbel_endpoint_arithmetic
    t ht hNM

/-- Endpoint contribution in the finite Abel decomposition after the canonical
cutoff.  This consumes the first-derivative logarithmic-phase primitive bound at
the two natural endpoints and the reciprocal endpoint weights. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelEndpoint_norm_le
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
  exact logarithmicPhase_finiteAbelEndpoint_bound t ht hNM

/-- Owner API: reciprocal-derivative integral contribution in the finite Abel
decomposition after the canonical cutoff. -/
theorem logarithmicPhase_finiteAbelDerivativeIntegral_bound
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
    logarithmicPhase_firstDerivative_finiteAbel_integral_arithmetic
      t ht hpartial hNM

/-- Reciprocal-derivative integral contribution in the finite Abel decomposition.
The integrand is the product of the derivative of `u ↦ 1/u` and the
first-derivative logarithmic-phase primitive bound. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelDerivativeIntegral_norm_le
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
  exact logarithmicPhase_finiteAbelDerivativeIntegral_bound t ht hpartial hNM

/-- Concrete finite Abel-tail estimate obtained through Mathlib's Abel
summation theorem.

The finite summation-by-parts identity is supplied by
`sum_mul_eq_sub_sub_integral_mul`, via
`abelSummation_boundaryLineOnePointRealParam_cutoff_finite_tail_endpoint_derivative_identity`;
this theorem only exposes that canonical route under an explicit owner name. -/
theorem mathlibAbelSummation_boundaryLineOnePointRealParam_logarithmicPhase_finiteTail_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M := by
  exact boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
    t ht hpartial hNM

/-- The completed Abel/Euler-Maclaurin tail package for the logarithmic-phase
oscillator after the canonical cutoff.

The pointwise primitive has an unavoidable `x / |t|` component, so the owner
bound carries the explicit cutoff constant
`boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t`.  The
classical proof combines Abel summation with cancellation in the endpoint and
reciprocal-derivative terms at `N = ⌊2 + |t|⌋₊`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_abelTail_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
      t ht hpartial hNM

/-- The right endpoint in the finite Abel decomposition is controlled by the
reciprocal weight times the owner partial-sum bound. -/
theorem abelSummation_boundaryLineOnePointRealParam_right_endpoint_norm_le
    (t : ℝ)
    {M : ℕ}
    (K : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hpartial :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        ⌊((M : ℕ) : ℝ)⌋₊‖ ≤ K) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ ≤
      (1 / (M : ℝ)) * K := by
  have hM_factor :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ = 1 / (M : ℝ) := by
    calc
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ =
          ‖((((M : ℕ) : ℝ) : ℂ))‖⁻¹ := by
        exact norm_inv ((((M : ℕ) : ℝ) : ℂ))
      _ = |(M : ℝ)|⁻¹ := by
        exact congrArg Inv.inv (RCLike.norm_ofReal (K := ℂ) (M : ℝ))
      _ = (M : ℝ)⁻¹ := by
        have hM_nonneg : 0 ≤ (M : ℝ) :=
          Nat.cast_nonneg M
        exact congrArg Inv.inv (abs_of_nonneg hM_nonneg)
      _ = 1 / (M : ℝ) := by
        exact (one_div (M : ℝ)).symm
  have hM_factor_nonneg : 0 ≤ (1 / (M : ℝ)) := by
    exact Eq.subst
      (motive := fun r : ℝ => 0 ≤ r)
      hM_factor
      (norm_nonneg (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))
  calc
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ =
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ *
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ := by
          exact norm_mul (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))
            (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
              ⌊((M : ℕ) : ℝ)⌋₊)
    _ ≤ (1 / (M : ℝ)) * K := by
          exact mul_le_mul (le_of_eq hM_factor) hpartial
            (norm_nonneg
              (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
                ⌊((M : ℕ) : ℝ)⌋₊))
            hM_factor_nonneg

/-- The cutoff endpoint in the finite Abel decomposition is controlled by the
cutoff reciprocal weight times the owner partial-sum bound. -/
theorem abelSummation_boundaryLineOnePointRealParam_cutoff_endpoint_norm_le
    (t : ℝ)
    (K : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hpartial :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤ K) :
    ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
      (1 / (⌊2 + ‖t‖⌋₊ : ℝ)) * K := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  have hN_factor :
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ = 1 / (N : ℝ) := by
    calc
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ =
          ‖((((N : ℕ) : ℝ) : ℂ))‖⁻¹ := by
        exact norm_inv ((((N : ℕ) : ℝ) : ℂ))
      _ = |(N : ℝ)|⁻¹ := by
        exact congrArg Inv.inv (RCLike.norm_ofReal (K := ℂ) (N : ℝ))
      _ = (N : ℝ)⁻¹ := by
        have hN_nonneg : 0 ≤ (N : ℝ) :=
          Nat.cast_nonneg N
        exact congrArg Inv.inv (abs_of_nonneg hN_nonneg)
      _ = 1 / (N : ℝ) := by
        exact (one_div (N : ℝ)).symm
  have hN_factor_nonneg : 0 ≤ (1 / (N : ℝ)) := by
    exact Eq.subst
      (motive := fun r : ℝ => 0 ≤ r)
      hN_factor
      (norm_nonneg (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))
  calc
    ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ =
        ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((N : ℕ) : ℝ))⌋₊‖ := by
          rfl
    _ = ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ *
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((N : ℕ) : ℝ))⌋₊‖ := by
          exact norm_mul (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))
            (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
              ⌊(((N : ℕ) : ℝ))⌋₊)
    _ ≤ (1 / (N : ℝ)) * K := by
          exact mul_le_mul (le_of_eq hN_factor) hpartial
            (norm_nonneg
              (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
                ⌊(((N : ℕ) : ℝ))⌋₊))
            hN_factor_nonneg

/-- Finite Abel reduction for the post-cutoff boundary-line oscillatory tail.

This is the algebraic/order part of the Euler-Maclaurin tail route: once the
oscillatory primitives
`∑_{0 ≤ k ≤ floor x} k^{-it}` and the reciprocal-derivative integral have been
bounded, the finite weighted tail is bounded by the two endpoint terms and the
integral term. -/
theorem abelSummation_boundaryLineOnePointRealParam_cutoff_finite_tail_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M := by
  exact boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
    t ht hpartial hNM

end

end LFunctions
end Boundary
