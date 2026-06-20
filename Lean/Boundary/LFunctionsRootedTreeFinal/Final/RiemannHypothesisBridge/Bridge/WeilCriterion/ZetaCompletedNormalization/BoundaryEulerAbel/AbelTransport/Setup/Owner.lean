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
      2 + 8 * Real.log (3 + ‖t‖) := by
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
      2 + 8 * Real.log (3 + ‖t‖) := by
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
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
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
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
      t ht hpartial hNM

/-- Abel summation in the precise finite form needed for the boundary-line tail:
coefficients are the logarithmic-phase oscillatory partial sums of `n^{-it}` and
the weight is `1/x`. -/
theorem abelSummation_boundaryLineOnePointRealParam_finite_tail_identity
    (t : ℝ)
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b)
    (hf_diff :
      ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc a b)) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ((b : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊b⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ((a : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊a⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ∫ x in Set.Ioc a b,
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
              (k : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  exact sum_mul_eq_sub_sub_integral_mul
    (fun k : ℕ => (k : ℂ) ^ (-(t : ℂ) * Complex.I))
    ha
    hab
    hf_diff
    hf_int

/-- Abel summation specialized to natural endpoints.  The floor terms are left
visible so the theorem is definitionally aligned with mathlib's statement. -/
theorem abelSummation_boundaryLineOnePointRealParam_finite_nat_tail_identity
    (t : ℝ)
    {N M : ℕ}
    (hNM : N ≤ M)
    (hf_diff :
      ∀ x ∈ Set.Icc ((N : ℕ) : ℝ) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc ((N : ℕ) : ℝ) ((M : ℕ) : ℝ))) :
    ∑ k ∈ Finset.Ioc ⌊((N : ℕ) : ℝ)⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊((M : ℕ) : ℝ)⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊((N : ℕ) : ℝ)⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ∫ x in Set.Ioc ((N : ℕ) : ℝ) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
              (k : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  have ha : (0 : ℝ) ≤ ((N : ℕ) : ℝ) :=
    Nat.cast_nonneg N
  have hab : ((N : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) :=
    Nat.cast_le.mpr hNM
  exact abelSummation_boundaryLineOnePointRealParam_finite_tail_identity
    t ha hab hf_diff hf_int

/-- Abel summation with the canonical boundary-line cutoff as the left endpoint.
The floor terms are kept visible so this remains a direct transport of mathlib's
finite Abel identity. -/
theorem abelSummation_boundaryLineOnePointRealParam_cutoff_nat_tail_identity
    (t : ℝ)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hf_diff :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ))) :
    ∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊((M : ℕ) : ℝ)⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          (∑ k ∈ Finset.Icc 0 ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
              (k : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  exact abelSummation_boundaryLineOnePointRealParam_finite_nat_tail_identity
    t hNM hf_diff hf_int

/-- Exact finite Abel summation endpoint/deivative decomposition at the canonical
boundary-line cutoff, written in terms of the owner partial-sum primitive. -/
theorem abelSummation_boundaryLineOnePointRealParam_cutoff_finite_tail_endpoint_derivative_identity
    (t : ℝ)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hf_diff :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ))) :
    ∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊ -
        (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ -
        ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊ := by
  exact abelSummation_boundaryLineOnePointRealParam_cutoff_nat_tail_identity
    t hNM hf_diff hf_int

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
      _ = ‖((M : ℝ))‖⁻¹ := by
        exact congrArg Inv.inv (Complex.norm_ofReal (M : ℝ))
      _ = (M : ℝ)⁻¹ := by
        have hM_nonneg : 0 ≤ (M : ℝ) :=
          Nat.cast_nonneg M
        exact congrArg Inv.inv (Real.norm_of_nonneg hM_nonneg)
      _ = 1 / (M : ℝ) := by
        exact (one_div (M : ℝ)).symm
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
          exact mul_le_mul (le_of_eq hM_factor) hpartial hK_nonneg
            (norm_nonneg (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))

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
      _ = ‖((N : ℝ))‖⁻¹ := by
        exact congrArg Inv.inv (Complex.norm_ofReal (N : ℝ))
      _ = (N : ℝ)⁻¹ := by
        have hN_nonneg : 0 ≤ (N : ℝ) :=
          Nat.cast_nonneg N
        exact congrArg Inv.inv (Real.norm_of_nonneg hN_nonneg)
      _ = 1 / (N : ℝ) := by
        exact (one_div (N : ℝ)).symm
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
          exact mul_le_mul (le_of_eq hN_factor) hpartial hK_nonneg
            (norm_nonneg (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))

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
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
    t ht hpartial hNM

end

end LFunctions
end Boundary
