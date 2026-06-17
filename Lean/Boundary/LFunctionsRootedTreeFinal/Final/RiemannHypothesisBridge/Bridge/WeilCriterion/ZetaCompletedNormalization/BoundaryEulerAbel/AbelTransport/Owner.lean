import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Owner

/-!
# Abel transport for boundary zeta tails

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.BoundaryEulerAbel.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Owner API: endpoint contribution in the finite Abel decomposition after the
canonical cutoff. -/
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
  exact (logarithmicPhase_firstDerivative_eulerMaclaurin_finiteAbel_package
    t ht hNM).2.1

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
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    (logarithmicPhase_firstDerivative_eulerMaclaurin_finiteAbel_package
      t ht hNM).2.2

/-- Reciprocal-derivative integral contribution in the finite Abel decomposition.
The integrand is the product of the derivative of `u ↦ 1/u` and the
first-derivative logarithmic-phase primitive bound. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelDerivativeIntegral_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact logarithmicPhase_finiteAbelDerivativeIntegral_bound t ht hNM

/-- Concrete finite Abel-tail estimate obtained through Mathlib's Abel
summation theorem.

The finite summation-by-parts identity is supplied by
`sum_mul_eq_sub_sub_integral_mul`, via
`abelSummation_boundaryLineOnePointRealParam_cutoff_finite_tail_endpoint_derivative_identity`;
this theorem only exposes that canonical route under an explicit owner name. -/
theorem mathlibAbelSummation_boundaryLineOnePointRealParam_logarithmicPhase_finiteTail_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
    t ht hNM

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
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
      t ht hNM

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
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hf_diff :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)))
    (K I : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hpartial :
      ∀ x : ℝ,
        x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ) →
        ‖∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
          (k : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤ K)
    (hintegral :
      ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
              (k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ I) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      (1 / (M : ℝ)) * K +
        (1 / (⌊2 + ‖t‖⌋₊ : ℝ)) * K + I := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  let a : ℝ := ((N : ℕ) : ℝ)
  let b : ℝ := ((M : ℕ) : ℝ)
  let SM : ℂ :=
    ∑ k ∈ Finset.Icc 0 ⌊b⌋₊,
      (k : ℂ) ^ (-(t : ℂ) * Complex.I)
  let SN : ℂ :=
    ∑ k ∈ Finset.Icc 0 ⌊a⌋₊,
      (k : ℂ) ^ (-(t : ℂ) * Complex.I)
  let J : ℂ :=
    ∫ x in Set.Ioc a b,
      deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
        (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
          (k : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hidentity :
      (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
          ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) * SM -
          (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN - J := by
    exact abelSummation_boundaryLineOnePointRealParam_cutoff_nat_tail_identity
      t hNM hf_diff hf_int
  have hM_mem :
      b ∈ Set.Icc a b := by
    have hN_le_M_real : ((N : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) :=
      Nat.cast_le.mpr hNM
    exact ⟨hN_le_M_real, le_rfl⟩
  have hN_mem :
      a ∈ Set.Icc a b := by
    have hN_le_M_real : ((N : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) :=
      Nat.cast_le.mpr hNM
    exact ⟨le_rfl, hN_le_M_real⟩
  have hSM_norm : ‖SM‖ ≤ K :=
    hpartial b hM_mem
  have hSN_norm : ‖SN‖ ≤ K :=
    hpartial a hN_mem
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
  have hM_term :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ ≤
        (1 / (M : ℝ)) * K := by
    calc
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ =
          ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ * ‖SM‖ := by
        exact norm_mul (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) SM
      _ ≤ (1 / (M : ℝ)) * K := by
        exact mul_le_mul (le_of_eq hM_factor) hSM_norm hK_nonneg
          (norm_nonneg (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))
  have hN_term :
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ ≤
        (1 / (N : ℝ)) * K := by
    calc
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ =
          ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ * ‖SN‖ := by
        exact norm_mul (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) SN
      _ ≤ (1 / (N : ℝ)) * K := by
        exact mul_le_mul (le_of_eq hN_factor) hSN_norm hK_nonneg
          (norm_nonneg (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))
  have htriangle :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
          (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN - J‖ ≤
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ +
          ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ + ‖J‖ := by
    have hfirst :
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
            (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN - J‖ ≤
          ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
            (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ + ‖J‖ :=
      norm_sub_le
        (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
          (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN)
        J
    have hsecond :
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
            (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ ≤
          ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ +
            ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ :=
      norm_sub_le
        (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM)
        (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN)
    exact le_trans hfirst (add_le_add_right hsecond ‖J‖)
  have hterms :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ +
          ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ + ‖J‖ ≤
        (1 / (M : ℝ)) * K + (1 / (N : ℝ)) * K + I :=
    add_le_add (add_le_add hM_term hN_term) hintegral
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ (1 / (M : ℝ)) * K + (1 / (N : ℝ)) * K + I)
    hidentity.symm
    (le_trans htriangle hterms)

/-- Pointwise transport of the post-cutoff boundary-line Dirichlet tail to the
Abel-normalized oscillatory tail. -/
theorem boundaryLineOnePointRealParam_post_cutoff_dirichletTerm_eq_inv_mul_oscillation
    (t : ℝ)
    (n : ℕ) :
    (if ⌊2 + ‖t‖⌋₊ < n then
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
      else
        0) =
      if ⌊2 + ‖t‖⌋₊ < n then
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
      else
        0 := by
  if hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n then
    have hn_pos : 0 < n :=
      lt_trans (boundaryLineOnePointRealParam_cutoff_pos t) hcutoff_lt_n
    have hleft :
        (if ⌊2 + ‖t‖⌋₊ < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0) =
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) :=
      if_pos hcutoff_lt_n
    have hterm :
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
      boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left
        t hn_pos
    have hright :
        (if ⌊2 + ‖t‖⌋₊ < n then
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
          else
            0) =
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
      if_pos hcutoff_lt_n
    exact Eq.trans hleft (Eq.trans hterm hright.symm)
  else
    have hleft :
        (if ⌊2 + ‖t‖⌋₊ < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0) =
          0 :=
      if_neg hcutoff_lt_n
    have hright :
        (if ⌊2 + ‖t‖⌋₊ < n then
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
          else
            0) =
          0 :=
      if_neg hcutoff_lt_n
    exact Eq.trans hleft hright.symm

/-- The zeroth boundary-line Dirichlet monomial vanishes.  This is the only extra
index left after removing `Icc 1 N` from the natural-indexed Dirichlet series. -/
theorem boundaryLineOnePointRealParam_dirichletTerm_zero
    (t : ℝ) :
    (1 : ℂ) / ((0 : ℂ) ^ boundaryLineOnePointRealParam t) = 0 := by
  have hpoint_ne_zero : boundaryLineOnePointRealParam t ≠ 0 := by
    intro hpoint_zero
    have hre_zero :
        (boundaryLineOnePointRealParam t).re = (0 : ℂ).re :=
      congrArg Complex.re hpoint_zero
    have hre_one :
        (boundaryLineOnePointRealParam t).re = 1 :=
      boundaryLineOnePointRealParam_re t
    have hone_eq_zero : (1 : ℝ) = 0 :=
      Eq.trans hre_one.symm hre_zero
    exact one_ne_zero hone_eq_zero
  have hpow_zero :
      (0 : ℂ) ^ boundaryLineOnePointRealParam t = 0 := by
    exact (cpow_eq_zero_iff).mpr ⟨rfl, hpoint_ne_zero⟩
  calc
    (1 : ℂ) / ((0 : ℂ) ^ boundaryLineOnePointRealParam t) =
        (1 : ℂ) / 0 := by
          exact congrArg (fun z : ℂ => (1 : ℂ) / z) hpow_zero
    _ = 0 := by
          exact div_zero (1 : ℂ)

/-- The complement indicator obtained from removing `Icc 1 N` from the natural-indexed
Dirichlet series is exactly the post-cutoff tail indicator. -/
theorem boundaryLineOnePointRealParam_dirichlet_tail_indicator_eq_cutoff_if
    (t : ℝ)
    (N n : ℕ) :
    ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator
        (fun m : ℕ =>
          (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t)) n) =
      if N < n then
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
      else
        0 := by
  if hN_lt_n : N < n then
    have hn_not_mem : n ∉ Finset.Icc 1 N := by
      intro hn_mem
      have hn_le_N : n ≤ N :=
        (Finset.mem_Icc.mp hn_mem).2
      exact (Nat.not_lt_of_ge hn_le_N) hN_lt_n
    have hn_mem_tail : n ∈ {m : ℕ | m ∉ Finset.Icc 1 N} :=
      hn_not_mem
    have hleft :
        ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator
            (fun m : ℕ =>
              (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t)) n) =
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) :=
      Set.indicator_of_mem hn_mem_tail
        (fun m : ℕ =>
          (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t))
    have hright :
        (if N < n then
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
        else
          0) =
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) :=
      if_pos hN_lt_n
    exact Eq.trans hleft hright.symm
  else
    if hn_zero : n = 0 then
      have hn_not_mem : n ∉ Finset.Icc 1 N := by
        intro hn_mem
        have hone_le_n : 1 ≤ n :=
          (Finset.mem_Icc.mp hn_mem).1
        have hone_le_zero : (1 : ℕ) ≤ 0 :=
          Eq.subst (motive := fun m : ℕ => 1 ≤ m) hn_zero hone_le_n
        exact (Nat.not_succ_le_zero 0) hone_le_zero
      have hn_mem_tail : n ∈ {m : ℕ | m ∉ Finset.Icc 1 N} :=
        hn_not_mem
      have hleft :
          ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator
              (fun m : ℕ =>
                (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t)) n) =
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) :=
        Set.indicator_of_mem hn_mem_tail
          (fun m : ℕ =>
            (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t))
      have hterm_zero :
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) = 0 :=
        Eq.subst
          (motive := fun m : ℕ =>
            (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t) = 0)
          hn_zero.symm
          (boundaryLineOnePointRealParam_dirichletTerm_zero t)
      have hright :
          (if N < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0) =
            0 :=
        if_neg hN_lt_n
      exact Eq.trans hleft (Eq.trans hterm_zero hright.symm)
    else
      have hn_pos : 0 < n :=
        Nat.pos_of_ne_zero hn_zero
      have hone_le_n : 1 ≤ n :=
        Nat.succ_le_of_lt hn_pos
      have hn_le_N : n ≤ N :=
        Nat.le_of_not_gt hN_lt_n
      have hn_mem_Icc : n ∈ Finset.Icc 1 N :=
        Finset.mem_Icc.mpr ⟨hone_le_n, hn_le_N⟩
      have hn_not_mem_tail : n ∉ {m : ℕ | m ∉ Finset.Icc 1 N} := by
        intro hn_mem_tail
        exact hn_mem_tail hn_mem_Icc
      have hleft :
          ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator
              (fun m : ℕ =>
                (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t)) n) =
            0 :=
        Set.indicator_of_not_mem hn_not_mem_tail
          (fun m : ℕ =>
            (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t))
      have hright :
          (if N < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0) =
            0 :=
        if_neg hN_lt_n
      exact Eq.trans hleft hright.symm

/-- Removing a finite Dirichlet truncation from a natural-indexed boundary-line
Dirichlet series gives the exact post-cutoff Dirichlet tail. -/
theorem boundaryLineOnePointRealParam_dirichlet_tail_after_cutoff_hasSum_zeta_remainder_of_dirichlet_series
    (t : ℝ)
    (N : ℕ)
    (hζ :
      HasSum
        (fun n : ℕ =>
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t))
        (riemannZeta (boundaryLineOnePointRealParam t))) :
    HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0)
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) := by
  have htail_compl :
      HasSum
        (fun x : {n : ℕ // n ∉ Finset.Icc 1 N} =>
          (1 : ℂ) / (((x : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t))
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) :=
    ((Finset.Icc 1 N).hasSum_iff_compl).mp hζ
  have htail_indicator :
      HasSum
        ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator
          (fun n : ℕ =>
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)))
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) := by
    exact
      (hasSum_subtype_iff_indicator
        (s := {n : ℕ | n ∉ Finset.Icc 1 N})
        (f := fun n : ℕ =>
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t))).mp
        htail_compl
  exact htail_indicator.congr_fun
    (fun n : ℕ =>
      (boundaryLineOnePointRealParam_dirichlet_tail_indicator_eq_cutoff_if
        t N n).symm)

/-- The boundary point `1 + it` is away from the zeta pole when `|t| ≥ 1`. -/
theorem boundaryLineOnePointRealParam_ne_one_of_one_le_norm
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam t ≠ (1 : ℂ) := by
  intro hpoint
  have him_eq :
      t = 0 :=
    Eq.trans (boundaryLineOnePointRealParam_im t).symm
      (Eq.trans (congrArg Complex.im hpoint) rfl)
  have hnorm_eq :
      ‖t‖ = 0 :=
    norm_eq_zero.mpr him_eq
  have hone_le_zero :
      (1 : ℝ) ≤ 0 :=
    Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ x)
      hnorm_eq
      ht
  exact not_lt_of_ge hone_le_zero zero_lt_one

/-- Analytic-continuation continuity of `ζ` at the boundary point `1 + it`, away
from the pole. -/
theorem boundaryLineOnePointRealParam_riemannZeta_continuousAt
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ContinuousAt riemannZeta (boundaryLineOnePointRealParam t) := by
  exact
    (differentiableAt_riemannZeta
      (boundaryLineOnePointRealParam_ne_one_of_one_le_norm t ht)).continuousAt

/-- The right-half-plane Abel family approaching the boundary point `1 + it`. -/
def boundaryLineOnePointRealParam_abscissaShift
    (σ t : ℝ) : ℂ :=
  (σ : ℂ) + (t : ℂ) * Complex.I

/-- Abel continuation of the half-plane Dirichlet identity to the boundary point
`1 + it`.

The ordinary boundary series `∑ n^{-1-it}` is not asserted to converge.  The
correct owner statement is the Abel-limit theorem: the half-plane sums
`∑ n^{-σ-it}` tend to the analytic-continuation value of `ζ` as
`σ ↓ 1`. -/
theorem boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t))
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (boundaryLineOnePointRealParam t))) := by
  have habscissa_path_continuousAt :
      ContinuousAt
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (1 : ℝ) := by
    show ContinuousAt (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) (1 : ℝ)
    exact
      Complex.continuous_ofReal.continuousAt.add
        continuousAt_const
  have habscissa_path_tendsto_raw :
      Tendsto
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (𝓝[>] (1 : ℝ))
        (𝓝 (boundaryLineOnePointRealParam_abscissaShift 1 t)) :=
    habscissa_path_continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have habscissa_path_endpoint :
      boundaryLineOnePointRealParam_abscissaShift 1 t =
        boundaryLineOnePointRealParam t := by
    exact Complex.ext rfl rfl
  have habscissa_path_tendsto_boundary :
      Tendsto
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (𝓝[>] (1 : ℝ))
        (𝓝 (boundaryLineOnePointRealParam t)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
          (𝓝[>] (1 : ℝ))
          (𝓝 z))
      habscissa_path_endpoint
      habscissa_path_tendsto_raw
  have hzeta_path_tendsto :
      Tendsto
        (fun σ : ℝ =>
          riemannZeta (boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t))) :=
    (boundaryLineOnePointRealParam_riemannZeta_continuousAt t ht).tendsto.comp
      habscissa_path_tendsto_boundary
  have hdirichlet_eq_eventually :
      (fun σ : ℝ =>
        ∑' n : ℕ,
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t)) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun σ : ℝ =>
          riemannZeta (boundaryLineOnePointRealParam_abscissaShift σ t)) := by
    exact
      Filter.Eventually.mono
        self_mem_nhdsWithin
        (fun σ hσ => by
          have hσ_re :
              (boundaryLineOnePointRealParam_abscissaShift σ t).re = σ := by
            rfl
          have hhalf_plane :
              1 < (boundaryLineOnePointRealParam_abscissaShift σ t).re :=
            Eq.subst
              (motive := fun x : ℝ => 1 < x)
              hσ_re.symm
              hσ
          exact (zeta_eq_tsum_one_div_nat_cpow hhalf_plane).symm)
  exact Tendsto.congr' hdirichlet_eq_eventually hzeta_path_tendsto

/-- The Abel boundary value of the Dirichlet presentation is the analytic
continuation value of `ζ(1 + it)`. -/
theorem boundaryLineOnePointRealParam_dirichlet_series_abel_boundaryValue_eq_riemannZeta
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ∃ V : ℂ,
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 V) ∧
      V = riemannZeta (boundaryLineOnePointRealParam t) := by
  exact
    ⟨riemannZeta (boundaryLineOnePointRealParam t),
      boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta
        t ht,
      rfl⟩

/-- The Abel-damped finite cutoff prefix. -/
def abelBoundary_logarithmicPhase_dampedPrefix
    (t σ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
    (1 : ℂ) /
      ((n : ℂ) ^
        boundaryLineOnePointRealParam_abscissaShift σ t)

/-- The boundary finite cutoff prefix. -/
def abelBoundary_logarithmicPhase_boundaryPrefix
    (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
    ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))

/-- Termwise Abel-prefix continuity at the boundary point `σ = 1`.

For a fixed positive integer `n`, the half-plane term
`n^(-σ-it)` tends to its boundary logarithmic-phase value
`n⁻¹ n^(-it)`. -/
theorem abelBoundary_logarithmicPhase_dampedPrefix_term_tendsto
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    Tendsto
      (fun σ : ℝ =>
        (1 : ℂ) /
          ((n : ℂ) ^
            boundaryLineOnePointRealParam_abscissaShift σ t))
      (𝓝[>] (1 : ℝ))
      (𝓝 (((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  have hn_complex_ne : (n : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have habscissa_cont :
      ContinuousAt
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (1 : ℝ) := by
    show ContinuousAt (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) (1 : ℝ)
    exact
      Complex.continuous_ofReal.continuousAt.add
        continuousAt_const
  have habscissa_tendsto :
      Tendsto
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (𝓝[>] (1 : ℝ))
        (𝓝 (boundaryLineOnePointRealParam_abscissaShift 1 t)) :=
    habscissa_cont.tendsto.mono_left nhdsWithin_le_nhds
  have hterm_tendsto_raw :
      Tendsto
        (fun σ : ℝ =>
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝
          ((1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift 1 t))) := by
    exact tendsto_const_nhds.div
      ((continuousAt_const_cpow hn_complex_ne).tendsto.comp
        habscissa_tendsto)
  have habscissa_endpoint :
      boundaryLineOnePointRealParam_abscissaShift 1 t =
        boundaryLineOnePointRealParam t :=
    Complex.ext rfl rfl
  have hboundary_term :
      (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift 1 t) =
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
    exact Eq.trans
      (congrArg
        (fun z : ℂ => (1 : ℂ) / ((n : ℂ) ^ z))
        habscissa_endpoint)
      (boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left
        t hn)
  exact Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun σ : ℝ =>
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 z))
    hboundary_term
    hterm_tendsto_raw

/-- Finite-sum Abel-prefix continuity over a fixed cutoff interval. -/
theorem abelBoundary_logarithmicPhase_dampedPrefix_sum_tendsto
    (t : ℝ)
    (N : ℕ) :
    Tendsto
      (fun σ : ℝ =>
        ∑ n ∈ Finset.Icc 1 N,
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t))
      (𝓝[>] (1 : ℝ))
        (𝓝
        (∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  exact Finset.Tendsto.sum
    (fun n hn_mem => by
      have hn_one_le : 1 ≤ n :=
        (Finset.mem_Icc.mp hn_mem).1
      have hn_pos : 0 < n :=
        Nat.lt_of_succ_le hn_one_le
      exact abelBoundary_logarithmicPhase_dampedPrefix_term_tendsto t hn_pos)

/-- The Abel-damped prefix tends to the boundary prefix as `σ → 1+`.

This is finite-sum continuity plus the term identity at the boundary point. -/
theorem abelBoundary_logarithmicPhase_dampedPrefix_tendsto_boundaryPrefix
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    Tendsto
      (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedPrefix t σ)
      (𝓝[>] (1 : ℝ))
      (𝓝 (abelBoundary_logarithmicPhase_boundaryPrefix t)) := by
  exact abelBoundary_logarithmicPhase_dampedPrefix_sum_tendsto
    t ⌊2 + ‖t‖⌋₊

/-- Abel-limit identity after subtracting the damped cutoff prefix.

This is pure limit algebra from the Abel convergence of the Dirichlet
presentation: subtracting the damped finite prefix from the Abel family
subtracts the boundary prefix in the limit. -/
theorem abelBoundary_dirichletSeries_dampedPrefix_subtracted_tendsto_zeta_remainder
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (habel :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t)))) :
    Tendsto
      (fun σ : ℝ =>
        (∑' n : ℕ,
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t)) -
          abelBoundary_logarithmicPhase_dampedPrefix t σ)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (boundaryLineOnePointRealParam t) -
          abelBoundary_logarithmicPhase_boundaryPrefix t)) := by
  exact habel.sub
    (abelBoundary_logarithmicPhase_dampedPrefix_tendsto_boundaryPrefix t ht)

/-- The Abel-damped post-cutoff logarithmic-phase tail.

This is a right-half-plane object: the ordinary boundary tail at `σ = 1` is
not asserted to converge. -/
def abelBoundary_logarithmicPhase_dampedTail
    (t σ : ℝ) : ℂ :=
  (∑' n : ℕ,
    (1 : ℂ) /
      ((n : ℂ) ^
        boundaryLineOnePointRealParam_abscissaShift σ t)) -
    abelBoundary_logarithmicPhase_dampedPrefix t σ

/-- Abel-tail normalization after removing the fixed cutoff prefix.

This theorem owns the index and term normalization between the Abel-regularized
Dirichlet remainder and the damped logarithmic-phase post-cutoff tail.  It is
the place where `Icc 1 N` prefix subtraction and the identity between
`n^{-(σ+it)}` and the damped reciprocal logarithmic oscillator are matched.  No
ordinary boundary `HasSum` or undamped tail convergence is asserted here. -/
theorem abelBoundary_logarithmicPhase_dampedTail_index_normalization
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hprefix :
      Tendsto
        (fun σ : ℝ =>
          (∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t)) -
            abelBoundary_logarithmicPhase_dampedPrefix t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝
          (riemannZeta (boundaryLineOnePointRealParam t) -
            abelBoundary_logarithmicPhase_boundaryPrefix t))) :
    Tendsto
      (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  exact hprefix

/-- Owner convergence theorem for Abel-damped tails after the canonical cutoff.

This is the exact limiting statement behind the Abel boundary transport: the
post-cutoff Abel-damped tail converges to the analytic-continuation zeta value
with the finite cutoff truncation removed.  The proof is the fixed-prefix Abel
limit, the identity between Dirichlet terms and damped reciprocal logarithmic
oscillators in the half-plane, and the Abel limit
`boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta`.
It deliberately does not assert ordinary boundary `HasSum`. -/
theorem abelBoundary_logarithmicPhase_dampedTail_tendsto_zeta_remainder
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (habel :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t)))) :
    Tendsto
      (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  have hprefix :
      Tendsto
        (fun σ : ℝ =>
          (∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t)) -
            abelBoundary_logarithmicPhase_dampedPrefix t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝
          (riemannZeta (boundaryLineOnePointRealParam t) -
            abelBoundary_logarithmicPhase_boundaryPrefix t)) :=
    abelBoundary_dirichletSeries_dampedPrefix_subtracted_tendsto_zeta_remainder
      t ht habel
  exact
    abelBoundary_logarithmicPhase_dampedTail_index_normalization
      t ht hprefix

/-- A complex limit of an eventually norm-bounded family is norm-bounded by the
same constant.

This is the reusable pure-topology closure step for Abel transport: the closed
ball `{z | ‖z‖ ≤ C}` contains the eventual tail, hence contains the limit. -/
theorem complex_norm_le_of_eventually_norm_le_of_tendsto
    {ι : Type*}
    {l : Filter ι}
    [NeBot l]
    {u : ι → ℂ}
    {z : ℂ}
    {C : ℝ}
    (hu : Tendsto u l (𝓝 z))
    (hbound : ∀ᶠ i in l, ‖u i‖ ≤ C) :
    ‖z‖ ≤ C := by
  have hclosed : IsClosed {w : ℂ | ‖w‖ ≤ C} :=
    isClosed_le continuous_norm continuous_const
  exact hclosed.mem_of_tendsto hu hbound

/-- Norm transport from a uniformly bounded Abel-damped tail family to its Abel
boundary limit.

This is the topological endpoint of the Abel argument: once the damped tails are
eventually uniformly bounded as `σ → 1+` and converge to the analytic boundary
remainder, the same bound holds for the remainder. -/
theorem abelBoundary_logarithmicPhase_dampedTail_uniform_bound_transport
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hdamped_bound :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
    (hdamped :
      Tendsto
        (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝
          (riemannZeta (boundaryLineOnePointRealParam t) -
            ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
              ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))))) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  let limit : ℂ :=
    riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
  have htail_tendsto :
      Tendsto
        (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝 limit) :=
    hdamped
  exact
    complex_norm_le_of_eventually_norm_le_of_tendsto
      htail_tendsto
      hdamped_bound

/-- In a left-neighborhood of `1`, the Abel parameter is eventually nonnegative. -/
theorem abel_left_neighborhood_eventually_nonnegative :
    ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ r := by
  have hpositive_nhds : ∀ᶠ r : ℝ in 𝓝 (1 : ℝ), 0 < r :=
    isOpen_Ioi.mem_nhds zero_lt_one
  exact
    (eventually_nhdsWithin_of_eventually_nhds hpositive_nhds).mono
      (fun r hr => le_of_lt hr)

/-- Algebraic step in the shifted finite Abel transform. -/
theorem abel_positive_weighted_tail_step_algebra
    (p q A B x : ℂ) :
    p * A + B + p * x =
      q * (A + x) + (B + (p - q) * (A + x)) := by
  have hcombine :
      q * (A + x) + (p - q) * (A + x) =
        p * (A + x) := by
    calc
      q * (A + x) + (p - q) * (A + x)
          = (q + (p - q)) * (A + x) :=
            (add_mul q (p - q) (A + x)).symm
      _ = p * (A + x) := by
        exact congrArg (fun z : ℂ => z * (A + x)) (add_sub_cancel_left q p)
  have hright :
      q * (A + x) + (B + (p - q) * (A + x)) =
        B + (q * (A + x) + (p - q) * (A + x)) := by
    calc
      q * (A + x) + (B + (p - q) * (A + x))
          = (q * (A + x) + B) + (p - q) * (A + x) :=
            (add_assoc (q * (A + x)) B ((p - q) * (A + x))).symm
      _ = (B + q * (A + x)) + (p - q) * (A + x) := by
        exact congrArg (fun z : ℂ => z + (p - q) * (A + x))
          (add_comm (q * (A + x)) B)
      _ = B + (q * (A + x) + (p - q) * (A + x)) :=
        add_assoc B (q * (A + x)) ((p - q) * (A + x))
  have hleft :
      p * A + B + p * x =
        B + (p * A + p * x) := by
    calc
      p * A + B + p * x
          = (B + p * A) + p * x := by
            exact congrArg (fun z : ℂ => z + p * x)
              (add_comm (p * A) B)
      _ = B + (p * A + p * x) :=
        add_assoc B (p * A) (p * x)
  calc
    p * A + B + p * x
        = B + (p * A + p * x) := hleft
    _ = B + p * (A + x) := by
      exact congrArg (fun z : ℂ => B + z) (mul_add p A x).symm
    _ = B + (q * (A + x) + (p - q) * (A + x)) := by
      exact congrArg (fun z : ℂ => B + z) hcombine.symm
    _ = q * (A + x) + (B + (p - q) * (A + x)) :=
      hright.symm

/-- Finite Abel summation identity for positive real weights on a natural tail.

The weighted finite tail is a convex positive combination of the finite partial
tail sums, plus the terminal weighted partial sum.  This is the finite
summation-by-parts identity underlying the abstract Abel theorem. -/
theorem abel_positive_weighted_tail_finite_summation_by_parts
    {u : ℕ → ℂ}
    {w : ℕ → ℝ}
    {N M : ℕ}
    (hNM : N ≤ M) :
    (∑ k ∈ Finset.Ioc N M, ((w k : ℝ) : ℂ) * u k) =
      ((w (M + 1) : ℝ) : ℂ) *
          (∑ k ∈ Finset.Ioc N M, u k) +
        ∑ k ∈ Finset.Ioc N M,
          (((w k - w (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.Ioc N k, u j)) := by
  apply Nat.le_induction
  · have hinterval : Finset.Ioc N N = ∅ :=
      Finset.Ioc_self N
    have hleft :
        (∑ k ∈ Finset.Ioc N N, ((w k : ℝ) : ℂ) * u k) = 0 := by
      exact Eq.trans
        (congrArg
          (fun s : Finset ℕ => ∑ k ∈ s, ((w k : ℝ) : ℂ) * u k)
          hinterval)
        (Finset.sum_empty (fun k : ℕ => ((w k : ℝ) : ℂ) * u k))
    have hpartial :
        (∑ k ∈ Finset.Ioc N N, u k) = 0 := by
      exact Eq.trans
        (congrArg (fun s : Finset ℕ => ∑ k ∈ s, u k) hinterval)
        (Finset.sum_empty u)
    have hvariation :
        (∑ k ∈ Finset.Ioc N N,
          (((w k - w (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.Ioc N k, u j))) = 0 := by
      exact Eq.trans
        (congrArg
          (fun s : Finset ℕ =>
            ∑ k ∈ s,
              (((w k - w (k + 1) : ℝ) : ℂ) *
                (∑ j ∈ Finset.Ioc N k, u j)))
          hinterval)
        (Finset.sum_empty
          (fun k : ℕ =>
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))))
    have hright :
        ((w (N + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N N, u k) +
          ∑ k ∈ Finset.Ioc N N,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j)) = 0 := by
      calc
        ((w (N + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N N, u k) +
          ∑ k ∈ Finset.Ioc N N,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))
            =
          ((w (N + 1) : ℝ) : ℂ) * 0 + 0 := by
            exact congrArg₂ (fun x y : ℂ => x + y)
              (congrArg (fun z : ℂ => ((w (N + 1) : ℝ) : ℂ) * z) hpartial)
              hvariation
        _ = 0 + 0 := by
          exact congrArg (fun z : ℂ => z + 0)
            (mul_zero ((w (N + 1) : ℝ) : ℂ))
        _ = 0 := zero_add 0
    exact hleft.trans hright.symm
  · intro M hNM ih
    have hleft_step :
        (∑ k ∈ Finset.Ioc N (M + 1), ((w k : ℝ) : ℂ) * u k) =
          (∑ k ∈ Finset.Ioc N M, ((w k : ℝ) : ℂ) * u k) +
            ((w (M + 1) : ℝ) : ℂ) * u (M + 1) := by
      exact Finset.sum_Ioc_succ_top hNM
    have hpartial_step :
        (∑ k ∈ Finset.Ioc N (M + 1), u k) =
          (∑ k ∈ Finset.Ioc N M, u k) + u (M + 1) := by
      exact Finset.sum_Ioc_succ_top hNM
    have hvariation_step :
        (∑ k ∈ Finset.Ioc N (M + 1),
          (((w k - w (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.Ioc N k, u j))) =
          (∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))) +
            (((w (M + 1) - w ((M + 1) + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N (M + 1), u j)) := by
      exact Finset.sum_Ioc_succ_top hNM
    have hdiff_cast :
        ((w (M + 1) - w ((M + 1) + 1) : ℝ) : ℂ) =
          ((w (M + 1) : ℝ) : ℂ) -
            ((w ((M + 1) + 1) : ℝ) : ℂ) :=
      Complex.ofReal_sub (w (M + 1)) (w ((M + 1) + 1))
    let A : ℂ := ∑ k ∈ Finset.Ioc N M, u k
    let B : ℂ :=
      ∑ k ∈ Finset.Ioc N M,
        (((w k - w (k + 1) : ℝ) : ℂ) *
          (∑ j ∈ Finset.Ioc N k, u j))
    let p : ℂ := ((w (M + 1) : ℝ) : ℂ)
    let q : ℂ := ((w ((M + 1) + 1) : ℝ) : ℂ)
    let x : ℂ := u (M + 1)
    have htarget_algebra :
        p * A + B + p * x =
          q * (A + x) + (B + (p - q) * (A + x)) :=
      abel_positive_weighted_tail_step_algebra p q A B x
    calc
      (∑ k ∈ Finset.Ioc N (M + 1), ((w k : ℝ) : ℂ) * u k)
          =
        (∑ k ∈ Finset.Ioc N M, ((w k : ℝ) : ℂ) * u k) +
          ((w (M + 1) : ℝ) : ℂ) * u (M + 1) := hleft_step
      _ =
        (((w (M + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N M, u k) +
          ∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))) +
          ((w (M + 1) : ℝ) : ℂ) * u (M + 1) := by
        exact congrArg
          (fun z : ℂ => z + ((w (M + 1) : ℝ) : ℂ) * u (M + 1))
          ih
      _ =
        ((w ((M + 1) + 1) : ℝ) : ℂ) *
            ((∑ k ∈ Finset.Ioc N M, u k) + u (M + 1)) +
          ((∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))) +
            ((((w (M + 1) : ℝ) : ℂ) -
              ((w ((M + 1) + 1) : ℝ) : ℂ)) *
              ((∑ k ∈ Finset.Ioc N M, u k) + u (M + 1)))) := by
        exact htarget_algebra
      _ =
        ((w ((M + 1) + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N (M + 1), u k) +
          ((∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))) +
            (((w (M + 1) - w ((M + 1) + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N (M + 1), u j))) := by
        exact congrArg₂ (fun x y : ℂ => x + y)
          (congrArg
            (fun z : ℂ => ((w ((M + 1) + 1) : ℝ) : ℂ) * z)
            hpartial_step.symm)
          (congrArg₂ (fun x y : ℂ => x + y)
            rfl
            (congrArg₂ (fun x y : ℂ => x * y) hdiff_cast.symm hpartial_step.symm))
      _ =
        ((w ((M + 1) + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N (M + 1), u k) +
          ∑ k ∈ Finset.Ioc N (M + 1),
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j)) := by
        exact congrArg
          (fun z : ℂ =>
            ((w ((M + 1) + 1) : ℝ) : ℂ) *
              (∑ k ∈ Finset.Ioc N (M + 1), u k) + z)
          hvariation_step.symm
  exact hNM

/-- Bounded tail partial sums force the bounding constant to be nonnegative. -/
theorem abel_positive_weighted_tail_bound_constant_nonneg
    {u : ℕ → ℂ}
    {N : ℕ}
    {C : ℝ}
    (hpartial :
      ∀ K : ℕ,
        N ≤ K →
        ‖∑ k ∈ Finset.Ioc N K, u k‖ ≤ C) :
    0 ≤ C := by
  have hinterval : Finset.Ioc N N = ∅ :=
    Finset.Ioc_self N
  have hsum :
      (∑ k ∈ Finset.Ioc N N, u k) = 0 := by
    exact Eq.trans
      (congrArg (fun s : Finset ℕ => ∑ k ∈ s, u k) hinterval)
      (Finset.sum_empty u)
  have hnorm :
      ‖∑ k ∈ Finset.Ioc N N, u k‖ = 0 := by
    exact congrArg norm hsum
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ C)
      hnorm.symm
      (hpartial N le_rfl)

/-- Nonnegative adjacent weight difference from antitonicity. -/
theorem abel_positive_weighted_tail_weight_difference_nonneg
    {w : ℕ → ℝ}
    {N k : ℕ}
    (hw_antitone : ∀ a b : ℕ, N < a → a ≤ b → w b ≤ w a)
    (hk : N < k) :
    0 ≤ w k - w (k + 1) := by
  have hnext : w (k + 1) ≤ w k :=
    hw_antitone k (k + 1) hk (Nat.le_succ k)
  exact sub_nonneg.mpr hnext

/-- Finite positive-weight Abel bound from bounded finite partial tail sums. -/
theorem abel_positive_weighted_tail_finite_norm_le_of_bounded_partial_sums
    {u : ℕ → ℂ}
    {w : ℕ → ℝ}
    {N M : ℕ}
    {C : ℝ}
    (hNM : N ≤ M)
    (hpartial :
      ∀ K : ℕ,
        N ≤ K →
        ‖∑ k ∈ Finset.Ioc N K, u k‖ ≤ C)
    (hw_nonneg : ∀ k : ℕ, N < k → 0 ≤ w k)
    (hw_antitone : ∀ k l : ℕ, N < k → k ≤ l → w l ≤ w k)
    (hw_variation :
      w (M + 1) + ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) ≤ 1) :
    ‖∑ k ∈ Finset.Ioc N M, ((w k : ℝ) : ℂ) * u k‖ ≤ C := by
  have hC_nonneg : 0 ≤ C :=
    abel_positive_weighted_tail_bound_constant_nonneg hpartial
  have hidentity :
      (∑ k ∈ Finset.Ioc N M, ((w k : ℝ) : ℂ) * u k) =
        ((w (M + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N M, u k) +
          ∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j)) :=
    abel_positive_weighted_tail_finite_summation_by_parts hNM
  have hterminal_nonneg : 0 ≤ w (M + 1) := by
    exact hw_nonneg (M + 1) (Nat.lt_succ_of_le hNM)
  have hterminal_norm :
      ‖((w (M + 1) : ℝ) : ℂ) *
          (∑ k ∈ Finset.Ioc N M, u k)‖ ≤
        w (M + 1) * C := by
    have hmul :
        ‖((w (M + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N M, u k)‖ =
          ‖((w (M + 1) : ℝ) : ℂ)‖ *
            ‖∑ k ∈ Finset.Ioc N M, u k‖ :=
      norm_mul ((w (M + 1) : ℝ) : ℂ)
        (∑ k ∈ Finset.Ioc N M, u k)
    have hreal_norm :
        ‖((w (M + 1) : ℝ) : ℂ)‖ = w (M + 1) := by
      have hcomplex_real : ‖((w (M + 1) : ℝ) : ℂ)‖ = ‖w (M + 1)‖ :=
        RCLike.norm_ofReal (w (M + 1))
      have hreal_abs : ‖w (M + 1)‖ = w (M + 1) :=
        Real.norm_of_nonneg hterminal_nonneg
      exact hcomplex_real.trans hreal_abs
    have hmul_bound :
        ‖((w (M + 1) : ℝ) : ℂ)‖ *
            ‖∑ k ∈ Finset.Ioc N M, u k‖ ≤
          w (M + 1) * C := by
      exact mul_le_mul
        (le_of_eq hreal_norm)
        (hpartial M hNM)
        hC_nonneg
        (norm_nonneg ((w (M + 1) : ℝ) : ℂ))
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ w (M + 1) * C)
      hmul.symm
      hmul_bound
  have hsum_norm :
      ‖∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
        (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * C := by
    have hterm :
        ∀ k ∈ Finset.Ioc N M,
          ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
            (w k - w (k + 1)) * C := by
      intro k hk_mem
      have hk_tail : N < k :=
        (Finset.mem_Ioc.mp hk_mem).1
      have hk_le_M : k ≤ M :=
        (Finset.mem_Ioc.mp hk_mem).2
      have hdiff_nonneg : 0 ≤ w k - w (k + 1) :=
        abel_positive_weighted_tail_weight_difference_nonneg
          hw_antitone hk_tail
      have hmul :
          ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ =
            ‖((w k - w (k + 1) : ℝ) : ℂ)‖ *
              ‖∑ j ∈ Finset.Ioc N k, u j‖ :=
        norm_mul ((w k - w (k + 1) : ℝ) : ℂ)
          (∑ j ∈ Finset.Ioc N k, u j)
      have hreal_norm :
          ‖((w k - w (k + 1) : ℝ) : ℂ)‖ =
            w k - w (k + 1) := by
        have hcomplex_real :
            ‖((w k - w (k + 1) : ℝ) : ℂ)‖ =
              ‖w k - w (k + 1)‖ :=
          RCLike.norm_ofReal (w k - w (k + 1))
        have hreal_abs : ‖w k - w (k + 1)‖ = w k - w (k + 1) :=
          Real.norm_of_nonneg hdiff_nonneg
        exact hcomplex_real.trans hreal_abs
      have hbound :
          ‖((w k - w (k + 1) : ℝ) : ℂ)‖ *
              ‖∑ j ∈ Finset.Ioc N k, u j‖ ≤
            (w k - w (k + 1)) * C := by
        exact mul_le_mul
          (le_of_eq hreal_norm)
          (hpartial k (Nat.le_of_lt hk_tail))
          hC_nonneg
          (norm_nonneg ((w k - w (k + 1) : ℝ) : ℂ))
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ (w k - w (k + 1)) * C)
        hmul.symm
        hbound
    have hsum_le :
        ‖∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
          ∑ k ∈ Finset.Ioc N M,
            ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ :=
      norm_sum_le
        (Finset.Ioc N M)
        (fun k : ℕ =>
          (((w k - w (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.Ioc N k, u j)))
    have hsum_bound :
        (∑ k ∈ Finset.Ioc N M,
            ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖) ≤
          ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) * C :=
      Finset.sum_le_sum hterm
    have hfactor :
        (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) * C) =
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * C := by
      exact (Finset.sum_mul (Finset.Ioc N M)
        (fun k : ℕ => w k - w (k + 1)) C).symm
    exact le_trans hsum_le (hsum_bound.trans_eq hfactor)
  have htriangle :
      ‖((w (M + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N M, u k) +
          ∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
        w (M + 1) * C +
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * C :=
    (norm_add_le
      (((w (M + 1) : ℝ) : ℂ) *
        (∑ k ∈ Finset.Ioc N M, u k))
      (∑ k ∈ Finset.Ioc N M,
        (((w k - w (k + 1) : ℝ) : ℂ) *
          (∑ j ∈ Finset.Ioc N k, u j)))).trans
      (add_le_add hterminal_norm hsum_norm)
  have hvariation_mul :
      w (M + 1) * C +
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * C ≤
        C := by
    have hfactor :
        w (M + 1) * C +
            (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * C =
          (w (M + 1) +
            ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * C := by
      exact (add_mul (w (M + 1))
        (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) C).symm
    have hscaled :
        (w (M + 1) +
            ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * C ≤
          1 * C :=
      mul_le_mul_of_nonneg_right hw_variation hC_nonneg
    have hone_mul : (1 : ℝ) * C = C :=
      one_mul C
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ C)
      hfactor.symm
      (hscaled.trans_eq hone_mul)
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ C)
    hidentity.symm
    (le_trans htriangle hvariation_mul)

/-- Sequential finite partial-sum bounds pass to an existing infinite sum.

This is the topological closure step separated from Abel summation itself.  It
does not assert conditional Dirichlet convergence as a `tsum`; that input must
be supplied by a genuine `HasSum`/summability theorem for the concrete weighted
tail. -/
theorem complex_norm_le_of_hasSum_and_range_partial_bounds
    {f : ℕ → ℂ}
    {S : ℂ}
    {C : ℝ}
    (hf : HasSum f S)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.range n, f k‖ ≤ C) :
    ‖S‖ ≤ C := by
  exact
    le_of_tendsto
      hf.tendsto_sum_nat.norm
      (Eventually.of_forall hbound)

/-- Existing `HasSum` plus sequential partial-sum bounds gives the corresponding
`tsum` norm bound. -/
theorem complex_norm_tsum_le_of_hasSum_and_range_partial_bounds
    {f : ℕ → ℂ}
    {S : ℂ}
    {C : ℝ}
    (hf : HasSum f S)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.range n, f k‖ ≤ C) :
    ‖∑' k : ℕ, f k‖ ≤ C := by
  have hS_bound : ‖S‖ ≤ C :=
    complex_norm_le_of_hasSum_and_range_partial_bounds hf hbound
  have hS_eq_tsum : S = ∑' k : ℕ, f k :=
    hf.tsum_eq
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ C)
    hS_eq_tsum
    hS_bound

/-- The abstract Abel theorem reduced to finite summation by parts and the
standard `tsum` limit passage. -/
theorem abel_positive_weighted_tail_norm_le_of_bounded_partial_sums_from_finite
    {u : ℕ → ℂ}
    {w : ℕ → ℝ}
    {N : ℕ}
    {C : ℝ}
    (hpartial :
      ∀ M : ℕ,
        N ≤ M →
        ‖∑ k ∈ Finset.Ioc N M, u k‖ ≤ C)
    (hw_nonneg : ∀ k : ℕ, N < k → 0 ≤ w k)
    (hw_antitone : ∀ k l : ℕ, N < k → k ≤ l → w l ≤ w k)
    (hw_variation : ∀ M : ℕ, N ≤ M → w (M + 1) +
        ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) ≤ 1)
    (hw_tendsto : Tendsto (fun M : ℕ => w M) atTop (𝓝 0))
    (hhas :
      HasSum
        (fun k : ℕ => if N < k then ((w k : ℝ) : ℂ) * u k else 0)
        (∑' k : ℕ, if N < k then ((w k : ℝ) : ℂ) * u k else 0))
    (hrange_bound :
      ∀ n : ℕ,
        ‖∑ k ∈ Finset.range n,
          if N < k then ((w k : ℝ) : ℂ) * u k else 0‖ ≤ C) :
    ‖∑' k : ℕ, if N < k then ((w k : ℝ) : ℂ) * u k else 0‖ ≤ C := by
  exact
    complex_norm_tsum_le_of_hasSum_and_range_partial_bounds
      hhas
      hrange_bound

/-- Abstract Abel transform bound from bounded finite tail sums.

This is the positive-weight summation-by-parts core: for a tail sequence whose
finite partial sums from `N` onward are bounded by `C`, a positive decreasing
weight family of total variation at most `1` gives a weighted tail bounded by
the same `C`.  This is the convex-combination form of Abel's theorem for
bounded partial sums. -/
theorem abel_positive_weighted_tail_norm_le_of_bounded_partial_sums
    {u : ℕ → ℂ}
    {w : ℕ → ℝ}
    {N : ℕ}
    {C : ℝ}
    (hpartial :
      ∀ M : ℕ,
        N ≤ M →
        ‖∑ k ∈ Finset.Ioc N M, u k‖ ≤ C) :
    (hw_nonneg : ∀ k : ℕ, N < k → 0 ≤ w k)
    (hw_antitone : ∀ k l : ℕ, N < k → k ≤ l → w l ≤ w k)
    (hw_variation : ∀ M : ℕ, N ≤ M → w (M + 1) +
        ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) ≤ 1)
    (hw_tendsto : Tendsto (fun M : ℕ => w M) atTop (𝓝 0))
    (hhas :
      HasSum
        (fun k : ℕ => if N < k then ((w k : ℝ) : ℂ) * u k else 0)
        (∑' k : ℕ, if N < k then ((w k : ℝ) : ℂ) * u k else 0))
    (hrange_bound :
      ∀ n : ℕ,
        ‖∑ k ∈ Finset.range n,
          if N < k then ((w k : ℝ) : ℂ) * u k else 0‖ ≤ C) :
    ‖∑' k : ℕ, if N < k then ((w k : ℝ) : ℂ) * u k else 0‖ ≤ C := by
  exact
    abel_positive_weighted_tail_norm_le_of_bounded_partial_sums_from_finite
      hpartial hw_nonneg hw_antitone hw_variation hw_tendsto hhas
      hrange_bound

/-- Complement of `Icc 1 N` as a post-cutoff indicator for functions whose
zeroth term vanishes. -/
theorem nat_not_Icc_one_indicator_eq_cutoff_if_of_zero
    {E : Type*}
    [Zero E]
    (f : ℕ → E)
    (N n : ℕ)
    (hf_zero : f 0 = 0) :
    ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator f n) =
      if N < n then f n else 0 := by
  if hN_lt_n : N < n then
    have hn_not_mem : n ∉ Finset.Icc 1 N := by
      intro hn_mem
      have hn_le_N : n ≤ N :=
        (Finset.mem_Icc.mp hn_mem).2
      exact (Nat.not_lt_of_ge hn_le_N) hN_lt_n
    have hn_mem_tail : n ∈ {m : ℕ | m ∉ Finset.Icc 1 N} :=
      hn_not_mem
    have hleft :
        ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator f n) = f n :=
      Set.indicator_of_mem hn_mem_tail f
    have hright :
        (if N < n then f n else 0) = f n :=
      if_pos hN_lt_n
    exact Eq.trans hleft hright.symm
  else
    if hn_zero : n = 0 then
      have hn_not_mem : n ∉ Finset.Icc 1 N := by
        intro hn_mem
        have hone_le_n : 1 ≤ n :=
          (Finset.mem_Icc.mp hn_mem).1
        have hone_le_zero : (1 : ℕ) ≤ 0 :=
          Eq.subst (motive := fun m : ℕ => 1 ≤ m) hn_zero hone_le_n
        exact (Nat.not_succ_le_zero 0) hone_le_zero
      have hn_mem_tail : n ∈ {m : ℕ | m ∉ Finset.Icc 1 N} :=
        hn_not_mem
      have hleft :
          ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator f n) = f n :=
        Set.indicator_of_mem hn_mem_tail f
      have hf_n_zero : f n = 0 :=
        Eq.subst (motive := fun m : ℕ => f m = 0) hn_zero.symm hf_zero
      have hright :
          (if N < n then f n else 0) = 0 :=
        if_neg hN_lt_n
      exact Eq.trans hleft (Eq.trans hf_n_zero hright.symm)
    else
      have hn_pos : 0 < n :=
        Nat.pos_of_ne_zero hn_zero
      have hone_le_n : 1 ≤ n :=
        Nat.succ_le_of_lt hn_pos
      have hn_le_N : n ≤ N :=
        Nat.le_of_not_gt hN_lt_n
      have hn_mem_Icc : n ∈ Finset.Icc 1 N :=
        Finset.mem_Icc.mpr ⟨hone_le_n, hn_le_N⟩
      have hn_not_mem_tail : n ∉ {m : ℕ | m ∉ Finset.Icc 1 N} := by
        intro hn_mem_tail
        exact hn_mem_tail hn_mem_Icc
      have hleft :
          ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator f n) = 0 :=
        Set.indicator_of_not_mem hn_not_mem_tail f
      have hright :
          (if N < n then f n else 0) = 0 :=
        if_neg hN_lt_n
      exact Eq.trans hleft hright.symm

/-- Removing the damped finite prefix from the half-plane Dirichlet series gives
the damped post-cutoff tail as an indicator `tsum`. -/
theorem abelBoundary_logarithmicPhase_dampedTail_eq_indicator_tsum
    (t σ : ℝ)
    (hσ : 1 < σ) :
    abelBoundary_logarithmicPhase_dampedTail t σ =
      ∑' k : ℕ,
        if ⌊2 + ‖t‖⌋₊ < k then
          (1 : ℂ) /
            ((k : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t)
        else
          0 := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  let f : ℕ → ℂ := fun n : ℕ =>
    (1 : ℂ) /
      ((n : ℂ) ^
        boundaryLineOnePointRealParam_abscissaShift σ t)
  have hσ_re :
      (boundaryLineOnePointRealParam_abscissaShift σ t).re = σ := by
    rfl
  have hhalf_plane :
      1 < (boundaryLineOnePointRealParam_abscissaShift σ t).re :=
    Eq.subst
      (motive := fun x : ℝ => 1 < x)
      hσ_re.symm
      hσ
  have hf_summable : Summable f :=
    (Complex.summable_one_div_nat_cpow
      (p := boundaryLineOnePointRealParam_abscissaShift σ t)).mpr
      hhalf_plane
  have hf_has :
      HasSum f (∑' n : ℕ, f n) :=
    hf_summable.hasSum
  have htail_compl :
      HasSum
        (fun x : {n : ℕ // n ∉ Finset.Icc 1 N} => f x)
        ((∑' n : ℕ, f n) - ∑ n ∈ Finset.Icc 1 N, f n) :=
    ((Finset.Icc 1 N).hasSum_iff_compl).mp hf_has
  have htail_indicator :
      HasSum
        ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f)
        ((∑' n : ℕ, f n) - ∑ n ∈ Finset.Icc 1 N, f n) := by
    exact
      (hasSum_subtype_iff_indicator
        (s := {n : ℕ | n ∉ Finset.Icc 1 N})
        (f := f)).mp
        htail_compl
  have hf_zero : f 0 = 0 := by
    have hpoint_ne_zero :
        boundaryLineOnePointRealParam_abscissaShift σ t ≠ 0 := by
      intro hpoint_zero
      have hre_zero :
          (boundaryLineOnePointRealParam_abscissaShift σ t).re = (0 : ℂ).re :=
        congrArg Complex.re hpoint_zero
      have hσ_zero : σ = 0 :=
        Eq.trans hσ_re.symm hre_zero
      have hone_lt_zero : (1 : ℝ) < 0 :=
        Eq.subst (motive := fun x : ℝ => 1 < x) hσ_zero hσ
      exact not_lt_of_ge zero_le_one hone_lt_zero
    have hpow_zero :
        (0 : ℂ) ^ boundaryLineOnePointRealParam_abscissaShift σ t = 0 := by
      exact (cpow_eq_zero_iff).mpr ⟨rfl, hpoint_ne_zero⟩
    calc
      f 0 = (1 : ℂ) /
          ((0 : ℂ) ^ boundaryLineOnePointRealParam_abscissaShift σ t) := by
        rfl
      _ = (1 : ℂ) / 0 := by
        exact congrArg (fun z : ℂ => (1 : ℂ) / z) hpow_zero
      _ = 0 := by
        exact div_zero (1 : ℂ)
  have htail_if :
      HasSum
        (fun k : ℕ => if N < k then f k else 0)
        ((∑' n : ℕ, f n) - ∑ n ∈ Finset.Icc 1 N, f n) :=
    htail_indicator.congr_fun
      (fun n : ℕ =>
        nat_not_Icc_one_indicator_eq_cutoff_if_of_zero f N n hf_zero)
  exact htail_if.tsum_eq.symm

/-- The Dirichlet damping weight for a fixed abscissa. -/
def abelBoundary_logarithmicPhase_dirichletWeight
    (σ : ℝ)
    (k : ℕ) : ℝ :=
  ((k : ℝ) ^ (1 - σ : ℝ))

/-- Exponent normal form for the Abel-damped logarithmic-phase factorization. -/
theorem abelBoundary_logarithmicPhase_damped_exponent_eq
    (t σ : ℝ) :
    ((1 - σ : ℝ) : ℂ) + (-1 : ℂ) + (-(t : ℂ) * Complex.I) =
      -boundaryLineOnePointRealParam_abscissaShift σ t := by
  show ((1 - σ : ℝ) : ℂ) + (-1 : ℂ) + (-(t : ℂ) * Complex.I) =
    -((σ : ℂ) + (t : ℂ) * Complex.I)
  exact Complex.ext rfl rfl

/-- Positive-natural complex-power normalization for the Abel-damped boundary
term.

This is the exact `cpow` algebra sink: split the exponent
`σ + it` into the reciprocal boundary factor and the real Dirichlet damping
weight `k^(1-σ)`. -/
theorem abelBoundary_logarithmicPhase_positiveNat_cpow_damped_factorization
    (t σ : ℝ)
    {k : ℕ}
    (hk : 0 < k) :
    (1 : ℂ) /
        ((k : ℂ) ^
          boundaryLineOnePointRealParam_abscissaShift σ t) =
      ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
        (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) := by
  let x : ℂ := (k : ℂ)
  have hx_ne : x ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) :=
    Nat.cast_nonneg k
  have hweight :
      ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) =
        x ^ (((1 - σ : ℝ) : ℂ)) := by
    exact Complex.ofReal_cpow hk_nonneg (1 - σ)
  have hinv :
      ((k : ℂ)⁻¹ : ℂ) = x ^ (-1 : ℂ) := by
    exact (Complex.cpow_neg_one x).symm
  have hproduct_one :
      ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
          (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        x ^ (((1 - σ : ℝ) : ℂ)) *
          (x ^ (-1 : ℂ) * x ^ (-(t : ℂ) * Complex.I)) := by
    exact congrArg₂ (fun a b : ℂ => a * b) hweight
      (congrArg₂ (fun a b : ℂ => a * b) hinv rfl)
  have hproduct_two :
      x ^ (((1 - σ : ℝ) : ℂ)) *
          (x ^ (-1 : ℂ) * x ^ (-(t : ℂ) * Complex.I)) =
        x ^ ((((1 - σ : ℝ) : ℂ) + (-1 : ℂ)) +
          (-(t : ℂ) * Complex.I)) := by
    have hleft :
        x ^ (((1 - σ : ℝ) : ℂ)) * x ^ (-1 : ℂ) =
          x ^ (((1 - σ : ℝ) : ℂ) + (-1 : ℂ)) :=
      (Complex.cpow_add (((1 - σ : ℝ) : ℂ)) (-1 : ℂ) hx_ne).symm
    have hright :
        x ^ ((((1 - σ : ℝ) : ℂ) + (-1 : ℂ)) +
            (-(t : ℂ) * Complex.I)) =
          x ^ (((1 - σ : ℝ) : ℂ) + (-1 : ℂ)) *
            x ^ (-(t : ℂ) * Complex.I) :=
      Complex.cpow_add
        (((1 - σ : ℝ) : ℂ) + (-1 : ℂ))
        (-(t : ℂ) * Complex.I)
        hx_ne
    calc
      x ^ (((1 - σ : ℝ) : ℂ)) *
          (x ^ (-1 : ℂ) * x ^ (-(t : ℂ) * Complex.I)) =
          (x ^ (((1 - σ : ℝ) : ℂ)) * x ^ (-1 : ℂ)) *
            x ^ (-(t : ℂ) * Complex.I) := by
        exact (mul_assoc
          (x ^ (((1 - σ : ℝ) : ℂ)))
          (x ^ (-1 : ℂ))
          (x ^ (-(t : ℂ) * Complex.I))).symm
      _ = x ^ (((1 - σ : ℝ) : ℂ) + (-1 : ℂ)) *
            x ^ (-(t : ℂ) * Complex.I) := by
        exact congrArg
          (fun y : ℂ => y * x ^ (-(t : ℂ) * Complex.I))
          hleft
      _ = x ^ ((((1 - σ : ℝ) : ℂ) + (-1 : ℂ)) +
            (-(t : ℂ) * Complex.I)) := by
        exact hright.symm
  have hproduct_three :
      x ^ ((((1 - σ : ℝ) : ℂ) + (-1 : ℂ)) +
          (-(t : ℂ) * Complex.I)) =
        x ^ (-boundaryLineOnePointRealParam_abscissaShift σ t) := by
    exact congrArg (fun z : ℂ => x ^ z)
      (abelBoundary_logarithmicPhase_damped_exponent_eq t σ)
  have hleft :
      (1 : ℂ) /
          ((k : ℂ) ^
            boundaryLineOnePointRealParam_abscissaShift σ t) =
        x ^ (-boundaryLineOnePointRealParam_abscissaShift σ t) := by
    calc
      (1 : ℂ) /
          ((k : ℂ) ^
            boundaryLineOnePointRealParam_abscissaShift σ t) =
          ((x ^ boundaryLineOnePointRealParam_abscissaShift σ t)⁻¹) := by
        exact one_div (x ^ boundaryLineOnePointRealParam_abscissaShift σ t)
      _ = x ^ (-boundaryLineOnePointRealParam_abscissaShift σ t) := by
        exact (Complex.cpow_neg x
          (boundaryLineOnePointRealParam_abscissaShift σ t)).symm
  exact Eq.trans hleft
    (Eq.trans hproduct_three.symm
      (Eq.trans hproduct_two.symm hproduct_one.symm))

/-- A right-half-plane post-cutoff term is the Dirichlet damping weight times the boundary
oscillatory term. -/
theorem abelBoundary_logarithmicPhase_dampedTail_term_eq_weighted_boundaryTerm
    (t σ : ℝ)
    {k : ℕ}
    (hk : 0 < k) :
    (1 : ℂ) /
        ((k : ℂ) ^
          boundaryLineOnePointRealParam_abscissaShift σ t) =
      ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
        (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) := by
  exact
    abelBoundary_logarithmicPhase_positiveNat_cpow_damped_factorization
      t σ hk

/-- The damped tail indicator `tsum` is the abstract Abel weighted tail. -/
theorem abelBoundary_logarithmicPhase_dampedTail_indicator_tsum_eq_abstract_weighted_tail
    (t σ : ℝ)
    (hσ : 1 < σ) :
    (∑' k : ℕ,
        if ⌊2 + ‖t‖⌋₊ < k then
          (1 : ℂ) /
            ((k : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t)
        else
          0) =
      ∑' k : ℕ,
        if ⌊2 + ‖t‖⌋₊ < k then
          ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
            (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
        else
          0 := by
  exact tsum_congr
    (fun k => by
      if hk : ⌊2 + ‖t‖⌋₊ < k then
        have hkpos : 0 < k :=
          lt_trans (boundaryLineOnePointRealParam_cutoff_pos t) hk
        exact Eq.trans
          (if_pos hk)
          (Eq.trans
            (abelBoundary_logarithmicPhase_dampedTail_term_eq_weighted_boundaryTerm
              t σ hkpos)
            (if_pos hk).symm)
      else
        exact Eq.trans (if_neg hk) (if_neg hk).symm)

/-- Identification of the logarithmic-phase damped tail with the abstract Abel
weighted tail.

For `σ > 1`, the damping weight is `k^(1 - σ)`, not a geometric weight. -/
theorem abelBoundary_logarithmicPhase_dampedTail_eq_abstract_weighted_tail
    (t σ : ℝ)
    (hσ : 1 < σ) :
    abelBoundary_logarithmicPhase_dampedTail t σ =
      ∑' k : ℕ,
        if ⌊2 + ‖t‖⌋₊ < k then
          ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
            (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
        else
          0 := by
  exact Eq.trans
    (abelBoundary_logarithmicPhase_dampedTail_eq_indicator_tsum t σ hσ)
    (abelBoundary_logarithmicPhase_dampedTail_indicator_tsum_eq_abstract_weighted_tail
      t σ hσ)

/-- Dirichlet weights after the cutoff are nonnegative. -/
theorem abelBoundary_logarithmicPhase_dirichletWeight_nonneg
    (σ : ℝ)
    {k : ℕ}
    (hk : 0 < k) :
    0 ≤ abelBoundary_logarithmicPhase_dirichletWeight σ k := by
  exact Real.rpow_nonneg (Nat.cast_nonneg k) (1 - σ)

/-- Dirichlet weights are decreasing on the post-cutoff tail for `σ > 1`. -/
theorem abelBoundary_logarithmicPhase_dirichletWeight_antitone
    (σ : ℝ)
    (hσ : 1 < σ) :
    ∀ k l : ℕ,
      0 < k →
      k ≤ l →
      abelBoundary_logarithmicPhase_dirichletWeight σ l ≤
        abelBoundary_logarithmicPhase_dirichletWeight σ k := by
  intro k l hk hkl
  have hk_real_pos : (0 : ℝ) < (k : ℝ) := by
    exact Nat.cast_pos.mpr hk
  have hkl_real : (k : ℝ) ≤ (l : ℝ) := by
    exact Nat.cast_le.mpr hkl
  have hexponent_nonpos : 1 - σ ≤ 0 :=
    sub_nonpos.mpr (le_of_lt hσ)
  exact
    Real.rpow_le_rpow_of_nonpos
      hk_real_pos
      hkl_real
      hexponent_nonpos

/-- The first Dirichlet weight on any natural tail is at most one. -/
theorem abelBoundary_logarithmicPhase_dirichletWeight_succ_le_one
    (σ : ℝ)
    (hσ : 1 < σ)
    (N : ℕ) :
    abelBoundary_logarithmicPhase_dirichletWeight σ (N + 1) ≤ 1 := by
  have hone_le_base : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact Nat.cast_le.mpr (Nat.succ_le_succ (Nat.zero_le N))
  have hexponent_nonpos : 1 - σ ≤ 0 :=
    sub_nonpos.mpr (le_of_lt hσ)
  exact
    Real.rpow_le_one_of_one_le_of_nonpos
      hone_le_base
      hexponent_nonpos

/-- The additive cancellation used in adjacent-difference telescoping. -/
theorem real_adjacent_difference_telescope_step
    (a b c : ℝ) :
    a + (b + (c - a)) = c + b := by
  calc
    a + (b + (c - a)) = a + ((c - a) + b) := by
      exact congrArg (fun x : ℝ => a + x) (add_comm b (c - a))
    _ = (a + (c - a)) + b := by
      exact (add_assoc a (c - a) b).symm
    _ = c + b := by
      exact congrArg (fun x : ℝ => x + b) (add_sub_cancel_left a c)

/-- Finite variation of any adjacent-difference tail telescopes on `Ioc`. -/
theorem finset_Ioc_adjacent_difference_telescope
    (w : ℕ → ℝ)
    (N M : ℕ)
    (hNM : N ≤ M) :
    w (M + 1) + ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) =
      w (N + 1) := by
  apply Nat.le_induction
  · have hinterval : Finset.Ioc N N = ∅ :=
      Finset.Ioc_self N
    have hsum :
        (∑ k ∈ Finset.Ioc N N, (w k - w (k + 1))) = 0 := by
      exact Eq.trans
        (congrArg
          (fun s : Finset ℕ => ∑ k ∈ s, (w k - w (k + 1)))
          hinterval)
        (Finset.sum_empty (fun k : ℕ => w k - w (k + 1)))
    calc
      w (N + 1) + ∑ k ∈ Finset.Ioc N N, (w k - w (k + 1)) =
          w (N + 1) + 0 := by
        exact congrArg (fun x : ℝ => w (N + 1) + x) hsum
      _ = w (N + 1) := by
        exact add_zero (w (N + 1))
  · intro M hNM hM
    have hsum_succ :
        (∑ k ∈ Finset.Ioc N (M + 1), (w k - w (k + 1))) =
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) +
            (w (M + 1) - w ((M + 1) + 1)) := by
      exact Finset.sum_Ioc_succ_top hNM
        (fun k : ℕ => w k - w (k + 1))
    calc
      w ((M + 1) + 1) +
          ∑ k ∈ Finset.Ioc N (M + 1), (w k - w (k + 1)) =
          w ((M + 1) + 1) +
            ((∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) +
              (w (M + 1) - w ((M + 1) + 1))) := by
        exact congrArg (fun x : ℝ => w ((M + 1) + 1) + x) hsum_succ
      _ = w (M + 1) +
            ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) := by
        exact real_adjacent_difference_telescope_step
          (w ((M + 1) + 1))
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)))
          (w (M + 1))
      _ = w (N + 1) := hM
  exact hNM

/-- The finite variation of Dirichlet weights on a post-cutoff tail is at most
the first weight, hence at most `1`. -/
theorem abelBoundary_logarithmicPhase_dirichletWeight_variation_le_one
    (σ : ℝ)
    (hσ : 1 < σ)
    (N : ℕ) :
    ∀ M : ℕ,
      N ≤ M →
      abelBoundary_logarithmicPhase_dirichletWeight σ (M + 1) +
          ∑ k ∈ Finset.Ioc N M,
            (abelBoundary_logarithmicPhase_dirichletWeight σ k -
              abelBoundary_logarithmicPhase_dirichletWeight σ (k + 1)) ≤
        1 := by
  intro M hNM
  have htelescopes :
      abelBoundary_logarithmicPhase_dirichletWeight σ (M + 1) +
          ∑ k ∈ Finset.Ioc N M,
            (abelBoundary_logarithmicPhase_dirichletWeight σ k -
              abelBoundary_logarithmicPhase_dirichletWeight σ (k + 1)) =
        abelBoundary_logarithmicPhase_dirichletWeight σ (N + 1) :=
    finset_Ioc_adjacent_difference_telescope
      (abelBoundary_logarithmicPhase_dirichletWeight σ)
      N M hNM
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 1)
      htelescopes.symm
      (abelBoundary_logarithmicPhase_dirichletWeight_succ_le_one σ hσ N)

/-- Dirichlet weights tend to zero for `σ > 1`. -/
theorem abelBoundary_logarithmicPhase_dirichletWeight_tendsto_zero
    (σ : ℝ)
    (hσ : 1 < σ) :
    Tendsto
      (fun k : ℕ => abelBoundary_logarithmicPhase_dirichletWeight σ k)
      atTop
      (𝓝 0) := by
  have hexponent_pos : 0 < σ - 1 :=
    sub_pos.mpr hσ
  have hraw :
      Tendsto
        (fun x : ℝ => x ^ (-(σ - 1)))
        atTop
        (𝓝 0) :=
    tendsto_rpow_neg_atTop hexponent_pos
  have hnat :
      Tendsto
        (fun k : ℕ => ((k : ℝ) ^ (-(σ - 1))))
        atTop
        (𝓝 0) :=
    hraw.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  exact hnat.congr'
    (Eventually.of_forall
      (fun k : ℕ =>
        congrArg (fun exponent : ℝ => ((k : ℝ) ^ exponent))
          (neg_sub σ 1)))

/-- The concrete Abel-damped logarithmic-phase tail is an honest `HasSum`.

This is the summability input missing from the generic Abel API: for `σ > 1`
the damped tail is absolutely summable, so its `tsum` is represented by a
genuine `HasSum`. -/
theorem abelBoundary_logarithmicPhase_abstract_weighted_tail_hasSum
    (t σ : ℝ)
    (hσ : 1 < σ) :
    HasSum
      (fun k : ℕ =>
        if ⌊2 + ‖t‖⌋₊ < k then
          ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
            (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
        else
          0)
      (∑' k : ℕ,
        if ⌊2 + ‖t‖⌋₊ < k then
          ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
            (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
        else
          0) := by
  let p : ℂ := boundaryLineOnePointRealParam_abscissaShift σ t
  let f : ℕ → ℂ := fun k : ℕ => (1 : ℂ) / ((k : ℂ) ^ p)
  let g : ℕ → ℂ := fun k : ℕ =>
    if ⌊2 + ‖t‖⌋₊ < k then f k else 0
  let h : ℕ → ℂ := fun k : ℕ =>
    if ⌊2 + ‖t‖⌋₊ < k then
      ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
        (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
    else
      0
  have hp_re : p.re = σ := by
    rfl
  have hp_half_plane : 1 < p.re :=
    Eq.subst
      (motive := fun x : ℝ => 1 < x)
      hp_re.symm
      hσ
  have hf_summable : Summable f :=
    (Complex.summable_one_div_nat_cpow (p := p)).mpr hp_half_plane
  have hg_summable : Summable g :=
    Summable.indicator hf_summable {k : ℕ | ⌊2 + ‖t‖⌋₊ < k}
  have h_eq_g_pointwise : ∀ k : ℕ, h k = g k := by
    intro k
    if hk : ⌊2 + ‖t‖⌋₊ < k then
      have hk_pos : 0 < k :=
        lt_trans (boundaryLineOnePointRealParam_cutoff_pos t) hk
      have hfactor :
          f k =
            ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
              (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) :=
        abelBoundary_logarithmicPhase_positiveNat_cpow_damped_factorization
          t σ hk_pos
      have hh :
          h k =
            ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
              (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) :=
        if_pos hk
      have hg :
          g k = f k :=
        if_pos hk
      exact Eq.trans hh (Eq.trans hfactor.symm hg.symm)
    else
      have hh : h k = 0 :=
        if_neg hk
      have hg : g k = 0 :=
        if_neg hk
      exact Eq.trans hh hg.symm
  have hh_summable : Summable h :=
    Summable.congr hg_summable
      (fun k : ℕ => (h_eq_g_pointwise k).symm)
  have htarget_eq : h =
      (fun k : ℕ =>
        if ⌊2 + ‖t‖⌋₊ < k then
          ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
            (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
        else
          0) :=
    rfl
  exact Eq.subst
    (motive := fun q : ℕ → ℂ => HasSum q (∑' k : ℕ, q k))
    htarget_eq
    hh_summable.hasSum

/-- Filtering a finite range by a strict post-cutoff condition gives the
corresponding `Ioc` interval with terminal index `n - 1`. -/
theorem finset_range_filter_strict_cutoff_eq_Ioc_pred
    (N n : ℕ)
    (hn : 0 < n) :
    (Finset.range n).filter (fun k : ℕ => N < k) =
      Finset.Ioc N (n - 1) := by
  ext k
  constructor
  · intro hk
    have hk_range : k ∈ Finset.range n :=
      (Finset.mem_filter.mp hk).1
    have hN_lt_k : N < k :=
      (Finset.mem_filter.mp hk).2
    have hk_lt_n : k < n :=
      Finset.mem_range.mp hk_range
    have hk_le_pred : k ≤ n - 1 :=
      (Nat.lt_iff_le_pred hn).mp hk_lt_n
    exact Finset.mem_Ioc.mpr ⟨hN_lt_k, hk_le_pred⟩
  · intro hk
    have hN_lt_k : N < k :=
      (Finset.mem_Ioc.mp hk).1
    have hk_le_pred : k ≤ n - 1 :=
      (Finset.mem_Ioc.mp hk).2
    have hk_lt_n : k < n :=
      (Nat.lt_iff_le_pred hn).mpr hk_le_pred
    have hk_range : k ∈ Finset.range n :=
      Finset.mem_range.mpr hk_lt_n
    exact Finset.mem_filter.mpr ⟨hk_range, hN_lt_k⟩

/-- Concrete range partial sums of the Abel-damped logarithmic-phase tail are
bounded by the finite Abel estimate.

This is the range-index bridge needed to feed the topological `HasSum` limit
passage. The proof is finite index bookkeeping: a range partial sum of the
post-cutoff indicator tail is either empty or an `Ioc` finite tail, and the
finite Abel estimate applies to that terminal index. -/
theorem abelBoundary_logarithmicPhase_abstract_weighted_tail_range_bound_of_finiteAbel
    (t σ C : ℝ)
    (hσ : 1 < σ)
    (hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C) :
    ∀ n : ℕ,
      ‖∑ k ∈ Finset.range n,
        if ⌊2 + ‖t‖⌋₊ < k then
          ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
            (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
        else
          0‖ ≤ C := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  let u : ℕ → ℂ := fun k : ℕ =>
    ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))
  let w : ℕ → ℝ := abelBoundary_logarithmicPhase_dirichletWeight σ
  have hC_nonneg : 0 ≤ C :=
    abel_positive_weighted_tail_bound_constant_nonneg
      (u := u) (N := N) hfinite
  intro n
  if hn_zero : n = 0 then
    have hrange_empty : Finset.range n = ∅ := by
      exact Eq.subst
        (motive := fun m : ℕ => Finset.range m = ∅)
        hn_zero.symm
        Finset.range_zero
    have hsum_zero :
        (∑ k ∈ Finset.range n,
          if N < k then ((w k : ℝ) : ℂ) * u k else 0) = 0 := by
      exact Eq.trans
        (congrArg
          (fun s : Finset ℕ =>
            ∑ k ∈ s, if N < k then ((w k : ℝ) : ℂ) * u k else 0)
          hrange_empty)
        (Finset.sum_empty
          (fun k : ℕ => if N < k then ((w k : ℝ) : ℂ) * u k else 0))
    have hnorm_zero :
        ‖∑ k ∈ Finset.range n,
          if N < k then ((w k : ℝ) : ℂ) * u k else 0‖ = 0 :=
      congrArg norm hsum_zero
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ C)
      hnorm_zero.symm
      hC_nonneg
  else
    have hn_pos : 0 < n :=
      Nat.pos_of_ne_zero hn_zero
    have hsum_filter :
        (∑ k ∈ Finset.range n,
          if N < k then ((w k : ℝ) : ℂ) * u k else 0) =
          ∑ k ∈ (Finset.range n).filter (fun k : ℕ => N < k),
            ((w k : ℝ) : ℂ) * u k := by
      exact (Finset.sum_filter (s := Finset.range n)
        (p := fun k : ℕ => N < k)
        (f := fun k : ℕ => ((w k : ℝ) : ℂ) * u k)).symm
    have hfilter_eq :
        (Finset.range n).filter (fun k : ℕ => N < k) =
          Finset.Ioc N (n - 1) :=
      finset_range_filter_strict_cutoff_eq_Ioc_pred N n hn_pos
    have hsum_ioc :
        (∑ k ∈ Finset.range n,
          if N < k then ((w k : ℝ) : ℂ) * u k else 0) =
          ∑ k ∈ Finset.Ioc N (n - 1), ((w k : ℝ) : ℂ) * u k :=
      Eq.trans hsum_filter
        (congrArg
          (fun s : Finset ℕ => ∑ k ∈ s, ((w k : ℝ) : ℂ) * u k)
          hfilter_eq)
    if hN_le_pred : N ≤ n - 1 then
      have hfinite_bound :
          ‖∑ k ∈ Finset.Ioc N (n - 1), ((w k : ℝ) : ℂ) * u k‖ ≤ C :=
        abel_positive_weighted_tail_finite_norm_le_of_bounded_partial_sums
          (u := u) (w := w) (N := N) (M := n - 1) (C := C)
          hN_le_pred
          hfinite
          (fun k hk =>
            abelBoundary_logarithmicPhase_dirichletWeight_nonneg σ
              (lt_of_le_of_lt (Nat.zero_le N) hk))
          (fun k l hk hkl =>
            abelBoundary_logarithmicPhase_dirichletWeight_antitone σ hσ k l
              (lt_of_le_of_lt (Nat.zero_le N) hk) hkl)
          (abelBoundary_logarithmicPhase_dirichletWeight_variation_le_one σ hσ
            N (n - 1) hN_le_pred)
      exact Eq.subst
        (motive := fun z : ℂ => ‖z‖ ≤ C)
        hsum_ioc.symm
        hfinite_bound
    else
      have hpred_le_N : n - 1 ≤ N :=
        Nat.le_of_lt (Nat.lt_of_not_ge hN_le_pred)
      have hioc_empty : Finset.Ioc N (n - 1) = ∅ :=
        Finset.Ioc_eq_empty_of_le hpred_le_N
      have hsum_ioc_zero :
          (∑ k ∈ Finset.Ioc N (n - 1), ((w k : ℝ) : ℂ) * u k) = 0 := by
        exact Eq.trans
          (congrArg
            (fun s : Finset ℕ => ∑ k ∈ s, ((w k : ℝ) : ℂ) * u k)
            hioc_empty)
          (Finset.sum_empty (fun k : ℕ => ((w k : ℝ) : ℂ) * u k))
      have hsum_zero :
          (∑ k ∈ Finset.range n,
            if N < k then ((w k : ℝ) : ℂ) * u k else 0) = 0 :=
        Eq.trans hsum_ioc hsum_ioc_zero
      have hnorm_zero :
          ‖∑ k ∈ Finset.range n,
            if N < k then ((w k : ℝ) : ℂ) * u k else 0‖ = 0 :=
        congrArg norm hsum_zero
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ C)
        hnorm_zero.symm
        hC_nonneg

/-- Transport the abstract Abel weighted-tail bound to the logarithmic-phase
damped tail as `σ → 1+`. -/
theorem abelBoundary_logarithmicPhase_dampedTail_bound_of_abstract_abel
    (t : ℝ)
    (C : ℝ)
    (hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤ C := by
  have hpartial :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C := by
    intro M hM
    have hleft :
        ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ = ⌊2 + ‖t‖⌋₊ :=
      Nat.floor_natCast ⌊2 + ‖t‖⌋₊
    have hright :
        ⌊((M : ℕ) : ℝ)⌋₊ = M :=
      Nat.floor_natCast M
    have hsource :
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C :=
      hfinite M hM
    have hleft_transport :
        ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C :=
      Eq.subst
        (motive := fun N : ℕ =>
          ‖∑ k ∈ Finset.Ioc N ⌊((M : ℕ) : ℝ)⌋₊,
              ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C)
        hleft
        hsource
    exact
      Eq.subst
        (motive := fun R : ℕ =>
          ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ R,
              ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C)
        hright
        hleft_transport
  have habstract :
      ∀ σ : ℝ,
        1 < σ →
        ‖∑' k : ℕ,
          if ⌊2 + ‖t‖⌋₊ < k then
            ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
              (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
          else
            0‖ ≤ C := by
    intro σ hσ
    exact
      abel_positive_weighted_tail_norm_le_of_bounded_partial_sums
      (u := fun k : ℕ =>
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
      (w := abelBoundary_logarithmicPhase_dirichletWeight σ)
      (N := ⌊2 + ‖t‖⌋₊)
      (C := C)
      hpartial
      (fun k hk =>
        abelBoundary_logarithmicPhase_dirichletWeight_nonneg σ
          (lt_of_le_of_lt (Nat.zero_le ⌊2 + ‖t‖⌋₊) hk))
      (fun k l hk hkl =>
        abelBoundary_logarithmicPhase_dirichletWeight_antitone σ hσ k l
          (lt_of_le_of_lt (Nat.zero_le ⌊2 + ‖t‖⌋₊) hk) hkl)
      (abelBoundary_logarithmicPhase_dirichletWeight_variation_le_one σ hσ
        ⌊2 + ‖t‖⌋₊)
      (abelBoundary_logarithmicPhase_dirichletWeight_tendsto_zero σ hσ)
      (abelBoundary_logarithmicPhase_abstract_weighted_tail_hasSum t σ hσ)
      (abelBoundary_logarithmicPhase_abstract_weighted_tail_range_bound_of_finiteAbel
        t σ C hσ hpartial)
  exact
    Filter.Eventually.mono
      self_mem_nhdsWithin
      (fun σ hσ => by
        have htail_eq :
            abelBoundary_logarithmicPhase_dampedTail t σ =
              ∑' k : ℕ,
                if ⌊2 + ‖t‖⌋₊ < k then
                  ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
                    (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
                else
                  0 :=
          abelBoundary_logarithmicPhase_dampedTail_eq_abstract_weighted_tail
            t σ hσ
        exact Eq.subst
          (motive := fun z : ℂ => ‖z‖ ≤ C)
          htail_eq.symm
          (habstract σ hσ))

/-- Abel damping theorem for a tail with bounded finite partial sums.

If every finite tail partial sum after the cutoff is bounded by `C`, then the
Abel-damped tail is eventually bounded by `C` as the damping parameter tends to
the boundary from the right.  This is the positive-weight Abel summation
principle: the damped tail is obtained as the limit of convex weighted averages
of the bounded finite partial sums. -/
theorem abel_damped_tail_norm_le_of_bounded_finite_tail_sums
    (t : ℝ)
    (C : ℝ)
    (hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤ C := by
  exact abelBoundary_logarithmicPhase_dampedTail_bound_of_abstract_abel
    t C hfinite

/-- Abel damping comparison for the logarithmic-phase post-cutoff tail.

This is the honest bridge from uniformly bounded finite post-cutoff Abel sums to
an eventual bound for the Abel-damped post-cutoff tail as `σ → 1+`.  Its proof
is Abel's theorem for bounded partial sums applied to the cutoff tail, not
ordinary convergence of the undamped boundary series. -/
theorem abelBoundary_logarithmicPhase_dampedTail_bound_of_finiteAbel
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact
    abel_damped_tail_norm_le_of_bounded_finite_tail_sums
      t
      (boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
      hfinite

/-- Deep Abel-limit transport for the canonical post-cutoff logarithmic-phase
tail.

This is the limiting passage from the uniformly bounded finite Abel tails after
`N = ⌊2 + |t|⌋₊` to the analytic-continuation boundary value supplied by
`boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta`.  It
does not assert ordinary convergence of the boundary Dirichlet series. -/
theorem abelBoundary_logarithmicPhase_oscillatory_tail_after_cutoff_bound_of_finiteAbel
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
    (habel :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t)))) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  have htails :
      Tendsto
        (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝
          (riemannZeta (boundaryLineOnePointRealParam t) -
            ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
              ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) :=
    abelBoundary_logarithmicPhase_dampedTail_tendsto_zeta_remainder
      t ht habel
  have hdamped_bound :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t :=
    abelBoundary_logarithmicPhase_dampedTail_bound_of_finiteAbel
      t ht hfinite
  exact
    abelBoundary_logarithmicPhase_dampedTail_uniform_bound_transport
      t ht hdamped_bound htails

/-- Owner Abel-boundary API for the canonical post-cutoff oscillatory tail.

This is the boundary-value passage from finite Abel tails to the analytic
continuation value of `ζ(1 + it)`, after the endpoint and derivative-integral
Abel estimates have been isolated. The proof chain is Abel summation for finite
tails, the logarithmic-phase first-derivative estimate, Abel limiting from the
right half-plane, and the Dirichlet-continuation boundary identity; cf.
Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem abelBoundary_logarithmicPhase_oscillatory_tail_after_cutoff_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  have hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
    intro M hNM
    exact
      boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
        t ht hNM
  have habel :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t))) :=
    boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta
      t ht
  exact
    abelBoundary_logarithmicPhase_oscillatory_tail_after_cutoff_bound_of_finiteAbel
      t ht hfinite habel

/-- Explicit Abel/Euler-Maclaurin estimate for the exact post-cutoff oscillatory
boundary-line zeta remainder.

Intended proof chain:
apply `abelSummation_boundaryLineOnePointRealParam_cutoff_nat_tail_identity` to
finite tails, bound the oscillatory partial sums
`∑_{0 ≤ n ≤ M} n^{-it}` on the range `1 ≤ |t|` by the logarithmic-phase
Euler/van-der-Corput estimate, use
`positive_nat_reciprocal_antitone` for the decreasing Abel weight, identify the
Abel boundary value with the analytic continuation of `ζ`, and combine the endpoint
and integral estimates at `N = ⌊2 + |t|⌋₊`; cf. Titchmarsh, *The Theory of the
Riemann Zeta-function*, §3.5. -/
theorem abelEulerMaclaurin_boundaryLineOnePointRealParam_oscillatory_tail_after_cutoff_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact abelBoundary_logarithmicPhase_oscillatory_tail_after_cutoff_bound t ht

/-- Exact post-cutoff oscillatory tail after the cutoff `N = ⌊2 + |t|⌋₊`.

The proof is now only the conjunction of the peeled Dirichlet-continuation
identity and the explicit Abel/Euler-Maclaurin endpoint/integral estimate. -/
theorem eulerMaclaurin_boundaryLineOnePointRealParam_oscillatory_tail_after_cutoff_hasSum_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact
    (abelEulerMaclaurin_boundaryLineOnePointRealParam_oscillatory_tail_after_cutoff_norm_le_explicit
      t ht)

/-- Transport a boundary-line tail norm estimate from the Abel-normalized oscillatory
finite truncation back to the original Dirichlet monomials. -/
theorem boundaryLineOnePointRealParam_tail_norm_le_explicit_of_oscillatory_tail_norm_le_explicit
    (t : ℝ)
    (hosc :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  have hfinite :
      (∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    boundaryLineOnePointRealParam_finite_truncation_eq_inv_mul_oscillation_sum
      t ⌊2 + ‖t‖⌋₊
  have htail_transport :
      riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
      riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    congrArg
      (fun S : ℂ => riemannZeta (boundaryLineOnePointRealParam t) - S)
      hfinite
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
    htail_transport.symm
    hosc

/-- Classical Euler-Maclaurin tail estimate after truncation at
`N = ⌊2 + |t|⌋₊`.

This is now only the mechanical transport from the oscillatory Abel-tail form
`n⁻¹ n⁻ⁱᵗ` back to the original boundary-line Dirichlet monomials. -/

end
end LFunctions
end Boundary
