import LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.ReciprocalDensity

/-!
# Abel tail on the boundary line

This file owns the post-cutoff Abel/Euler-Maclaurin tail estimate for
`ζ(1 + it)`.  The nonzero-frequency guard is part of the owner surface.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The boundary-line Dirichlet monomial is the reciprocal weight times the
logarithmic oscillator. -/
theorem Complex.boundaryLineOnePointRealParam_dirichletTerm_eq_reciprocal_mul_oscillation
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹ =
      ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  have hn_complex_ne : (n : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hpoint :
      Complex.boundaryLineOnePointRealParam t = 1 + (t : ℂ) * Complex.I := by
    rfl
  have hpow_add :
      (n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t) =
        (n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
    exact Eq.subst
      (motive := fun z : ℂ =>
        (n : ℂ) ^ z =
          (n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ ((t : ℂ) * Complex.I))
      hpoint.symm
      (Complex.cpow_add (1 : ℂ) ((t : ℂ) * Complex.I) hn_complex_ne)
  have hinv_osc :
      ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ =
        (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
    have hneg :
        -((t : ℂ) * Complex.I) = -(t : ℂ) * Complex.I := by
      exact neg_mul (t : ℂ) Complex.I
    exact Eq.subst
      (motive := fun z : ℂ =>
        ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ = (n : ℂ) ^ z)
      hneg
      (Complex.cpow_neg (n : ℂ) ((t : ℂ) * Complex.I)).symm
  calc
    ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹ =
        ((n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ := by
      exact congrArg Inv.inv hpow_add
    _ = ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ *
          ((n : ℂ) ^ (1 : ℂ))⁻¹ := by
      exact mul_inv_rev ((n : ℂ) ^ (1 : ℂ)) ((n : ℂ) ^ ((t : ℂ) * Complex.I))
    _ = (n : ℂ) ^ (-(t : ℂ) * Complex.I) *
          ((n : ℂ) ^ (1 : ℂ))⁻¹ := by
      exact congrArg
        (fun z : ℂ => z * ((n : ℂ) ^ (1 : ℂ))⁻¹)
        hinv_osc
    _ = (n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ)⁻¹ := by
      exact congrArg
        (fun z : ℂ => (n : ℂ) ^ (-(t : ℂ) * Complex.I) * z⁻¹)
        (Complex.cpow_one (n : ℂ))
    _ = ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
      exact mul_comm ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) ((n : ℂ)⁻¹ : ℂ)

/-- Finite boundary-line Dirichlet truncations are exactly the
reciprocal-weighted logarithmic-phase sums. -/
theorem Complex.riemannZetaBoundaryLineTruncation_eq_weighted_logarithmicPhase_sum
    (t : ℝ)
    (N : ℕ) :
    Complex.riemannZetaBoundaryLineTruncation t N =
      ∑ n ∈ Finset.Icc 1 N,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  refine Finset.sum_congr rfl ?_
  intro n hn_mem
  have hn_one_le : 1 ≤ n :=
    (Finset.mem_Icc.mp hn_mem).1
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one_le
  exact
    Complex.boundaryLineOnePointRealParam_dirichletTerm_eq_reciprocal_mul_oscillation
      t hn_pos

/-- Finite reciprocal-weight Abel summation for the logarithmic phase from
the owner partial-sum estimate.  This is the analytic summation-by-parts
bridge: the oscillatory partial sums are first controlled on blocks, then the
monotone reciprocal density is peeled by Abel summation. -/
theorem Complex.boundaryLineOnePointRealParam_reciprocalWeightedTail_bound_of_phasePartialSums :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ∀ M : ℕ,
                N ≤ M →
                  ‖∑ n ∈ Finset.Ioc N M,
                    ((n : ℂ)⁻¹ : ℂ) *
                      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                    A * Real.log (2 + ‖t‖) := by
  /-
  Intended proof chain:
  `boundaryLineOnePointRealParam_logarithmicPhasePartialSum_bound`
  -> block partial sums on dyadic annuli
  -> finite Abel summation with the decreasing density `n ↦ 1 / n`
  -> summation of the dyadic reciprocal increments, bounded by `log (2 + |t|)`.

  The key point is that the reciprocal weight is introduced here, not by
  replacing the damped tail with an undamped pointwise tail.
  -/
  sorry

/-- Blockwise finite partial summation for reciprocal weights applied to the
logarithmic phase.

This is the honest Abel-summation input: the global first-derivative estimate
alone has a square-root transition term and is not the right primitive for the
uniform logarithmic boundary tail. -/
theorem Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound_from_block_phase :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ∀ M : ℕ,
                N ≤ M →
                  ‖∑ n ∈ Finset.Ioc N M,
                    ((n : ℂ)⁻¹ : ℂ) *
                      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                    A * Real.log (2 + ‖t‖) := by
  exact
    Complex.boundaryLineOnePointRealParam_reciprocalWeightedTail_bound_of_phasePartialSums

/-- Finite partial-summation primitive for reciprocal weights applied to the
standard logarithmic-phase input. -/
theorem Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound_from_phase_standard :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ∀ M : ℕ,
                N ≤ M →
                  ‖∑ n ∈ Finset.Ioc N M,
                    ((n : ℂ)⁻¹ : ℂ) *
                      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                    A * Real.log (2 + ‖t‖) := by
  exact Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound_from_block_phase

/-- Finite Abel-summation estimate for the post-cutoff reciprocal-weighted
logarithmic phase.

This is the finite partial-summation step: combine the first-derivative
oscillatory estimate for `∑ n^{-it}` with monotonicity of the reciprocal
weight.  Cf. Apostol, *Introduction to Analytic Number Theory*, Ch. 3. -/
theorem Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound_standard :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ∀ M : ℕ,
                N ≤ M →
                  ‖∑ n ∈ Finset.Ioc N M,
                    ((n : ℂ)⁻¹ : ℂ) *
                      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                    A * Real.log (2 + ‖t‖) := by
  exact Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound_from_phase_standard

/-- Canonical-cutoff finite Abel-tail estimate after `⌊2 + |t|⌋₊`. -/
theorem Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound_at_cutoff :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ M : ℕ,
            ⌊2 + ‖t‖⌋₊ ≤ M →
              ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
                ((n : ℂ)⁻¹ : ℂ) *
                  ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                A * Real.log (2 + ‖t‖) := by
  rcases Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound_standard with
    ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht M hM
  have hcutoff_one : 1 ≤ ⌊2 + ‖t‖⌋₊ := by
    have htwo_le : (2 : ℝ) ≤ 2 + ‖t‖ :=
      le_add_of_nonneg_right (norm_nonneg t)
    have hfloor_two : 2 ≤ ⌊2 + ‖t‖⌋₊ :=
      (Nat.le_floor_iff zero_lt_two).mpr htwo_le
    exact le_trans (by decide : 1 ≤ 2) hfloor_two
  exact hbound t ht ⌊2 + ‖t‖⌋₊ hcutoff_one M hM

/-- Finite Abel-summation estimate obtained from the first-derivative
logarithmic-phase bound. -/
theorem Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound_of_firstDerivative :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ∀ M : ℕ,
                N ≤ M →
                  ‖∑ n ∈ Finset.Ioc N M,
                    ((n : ℂ)⁻¹ : ℂ) *
                      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                    A * Real.log (2 + ‖t‖) := by
  exact Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound_standard

/-- Finite Abel-summation estimate for the post-cutoff reciprocal-weighted
logarithmic phase. -/
theorem Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ∀ M : ℕ,
                N ≤ M →
                  ‖∑ n ∈ Finset.Ioc N M,
                    ((n : ℂ)⁻¹ : ℂ) *
                      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                    A * Real.log (2 + ‖t‖) := by
  exact Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound_of_firstDerivative

/-- Abel damping preserves a uniform finite-tail bound for a fixed tail.

The damping is kept explicit: this theorem bounds the damped infinite Abel
tail by taking limits of damped finite tails, not by identifying the damped
tail pointwise with the undamped finite tail. -/
theorem Complex.abelDampedTail_bound_of_uniform_finite_tail_bound
    {a : ℕ → ℂ}
    {B : ℝ}
    (N : ℕ)
    (hN : 1 ≤ N)
    (hfinite :
      ∀ M : ℕ,
        N ≤ M →
          ‖∑ n ∈ Finset.Ioc N M, a n‖ ≤ B) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      ‖∑' n : ℕ,
        if N < n then
          a n * ((n : ℝ) ^ (-(σ - 1)) : ℂ)
        else
          0‖ ≤ B := by
  /-
  Intended proof chain:
  finite Abel summation for the positive decreasing weights
  `n ↦ n ^ (-(σ - 1))` when `σ > 1`
  -> each damped finite tail is a convex/Stieltjes average of undamped finite
     tails, hence has norm at most `B`
  -> absolute convergence for `σ > 1`
  -> passage from finite damped tails to the `tsum`.
  -/
  sorry

/-- Positive Abel damping preserves the uniform finite Abel-tail estimate. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedTail_bound_from_finiteAbel :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
                ‖∑' n : ℕ,
                  if N < n then
                    ((n : ℂ)⁻¹ : ℂ) *
                      ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) *
                        ((n : ℝ) ^ (-(σ - 1)) : ℂ)
                  else
                    0‖ ≤
                  A * Real.log (2 + ‖t‖) := by
  rcases Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound with
    ⟨A, hA_pos, hfinite⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht N hN
  let a : ℕ → ℂ :=
    fun n : ℕ =>
      ((n : ℂ)⁻¹ : ℂ) *
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hfinite_tail :
      ∀ M : ℕ,
        N ≤ M →
          ‖∑ n ∈ Finset.Ioc N M, a n‖ ≤ A * Real.log (2 + ‖t‖) := by
    intro M hNM
    exact hfinite t ht N hN M hNM
  have hdamped :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ‖∑' n : ℕ,
          if N < n then
            a n * ((n : ℝ) ^ (-(σ - 1)) : ℂ)
          else
            0‖ ≤
          A * Real.log (2 + ‖t‖) :=
    Complex.abelDampedTail_bound_of_uniform_finite_tail_bound
      N hN hfinite_tail
  refine hdamped.mono ?_
  intro σ hσ
  simpa [a] using hσ

/-- Abel boundary passage for the post-cutoff reciprocal-weighted logarithmic
phase.

This is the genuine limiting analytic root: finite Abel tail bounds are
transported through Abel damping and the Dirichlet-continuation boundary value
of `ζ(1 + it)`. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedTail_bound_standard :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
                ‖∑' n : ℕ,
                  if N < n then
                    ((n : ℂ)⁻¹ : ℂ) *
                      ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) *
                        ((n : ℝ) ^ (-(σ - 1)) : ℂ)
                  else
                    0‖ ≤
                  A * Real.log (2 + ‖t‖) := by
  exact Complex.boundaryLineOnePointRealParam_abelDampedTail_bound_from_finiteAbel

/-- Positive-weight Abel damping theorem for tails with uniformly bounded
finite Abel sums. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedTail_bound_of_finiteAbel :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
                ‖∑' n : ℕ,
                  if N < n then
                    ((n : ℂ)⁻¹ : ℂ) *
                      ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) *
                        ((n : ℝ) ^ (-(σ - 1)) : ℂ)
                  else
                    0‖ ≤
                  A * Real.log (2 + ‖t‖) := by
  exact Complex.boundaryLineOnePointRealParam_abelDampedTail_bound_standard

/-- Abel-damped Dirichlet monomial in reciprocal-weighted logarithmic-phase
form, for the convergent half-plane side of the boundary approach. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedDirichletTerm_eq_weighted
    (t σ : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹ =
      ((n : ℂ)⁻¹ : ℂ) *
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) *
          ((n : ℝ) ^ (-(σ - 1)) : ℂ) := by
  have hn_complex_ne : (n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hn_real_nonneg : 0 ≤ (n : ℝ) :=
    Nat.cast_nonneg n
  have hreal_weight :
      ((n : ℝ) ^ (-(σ - 1)) : ℂ) =
        (n : ℂ) ^ ((-(σ - 1) : ℝ) : ℂ) := by
    exact Complex.ofReal_cpow hn_real_nonneg (-(σ - 1))
  have hsigma_decomp :
      (σ : ℂ) = (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) := by
    norm_num [sub_eq_add_neg, add_assoc]
  have hneg_sigma_decomp :
      -((σ : ℂ) + (t : ℂ) * Complex.I) =
        (-1 : ℂ) + (-(t : ℂ) * Complex.I) +
          ((-(σ - 1 : ℝ) : ℝ) : ℂ) := by
    rw [hsigma_decomp]
    ring
  have hcpow_neg :
      ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹ =
        (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    exact (Complex.cpow_neg (n : ℂ) ((σ : ℂ) + (t : ℂ) * Complex.I)).symm
  have hsplit_left :
      (n : ℂ) ^ ((-1 : ℂ) + (-(t : ℂ) * Complex.I)) =
        (n : ℂ) ^ (-1 : ℂ) * (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
    exact Complex.cpow_add (-1 : ℂ) (-(t : ℂ) * Complex.I) hn_complex_ne
  have hsplit :
      (n : ℂ) ^
          (((-1 : ℂ) + (-(t : ℂ) * Complex.I)) +
            ((-(σ - 1 : ℝ) : ℝ) : ℂ)) =
        ((n : ℂ) ^ (-1 : ℂ) * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) *
          (n : ℂ) ^ (((-(σ - 1 : ℝ) : ℝ) : ℂ)) := by
    have hadd :
        (n : ℂ) ^
            (((-1 : ℂ) + (-(t : ℂ) * Complex.I)) +
              ((-(σ - 1 : ℝ) : ℝ) : ℂ)) =
          (n : ℂ) ^ ((-1 : ℂ) + (-(t : ℂ) * Complex.I)) *
            (n : ℂ) ^ (((-(σ - 1 : ℝ) : ℝ) : ℂ)) :=
      Complex.cpow_add
        ((-1 : ℂ) + (-(t : ℂ) * Complex.I))
        (((-(σ - 1 : ℝ) : ℝ) : ℂ))
        hn_complex_ne
    exact Eq.trans hadd (congrArg (fun z : ℂ => z *
      (n : ℂ) ^ (((-(σ - 1 : ℝ) : ℝ) : ℂ))) hsplit_left)
  have hcpow_neg_one :
      (n : ℂ) ^ (-1 : ℂ) = ((n : ℂ)⁻¹ : ℂ) := by
    simpa using Complex.cpow_neg_one (n : ℂ)
  calc
    ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹ =
        (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) := hcpow_neg
    _ = (n : ℂ) ^
          (((-1 : ℂ) + (-(t : ℂ) * Complex.I)) +
            ((-(σ - 1 : ℝ) : ℝ) : ℂ)) := by
      exact congrArg (fun z : ℂ => (n : ℂ) ^ z) hneg_sigma_decomp
    _ = ((n : ℂ) ^ (-1 : ℂ) * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) *
          (n : ℂ) ^ (((-(σ - 1 : ℝ) : ℝ) : ℂ)) := hsplit
    _ = ((n : ℂ)⁻¹ : ℂ) *
          ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) *
            ((n : ℝ) ^ (-(σ - 1)) : ℂ) := by
      rw [hcpow_neg_one, hreal_weight]

/-- Pointwise equality between the Abel-damped Dirichlet tail and its
reciprocal-weighted logarithmic-phase form. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedTail_eq_weightedTail
    (t σ : ℝ)
    (N : ℕ)
    (hN : 1 ≤ N) :
    (∑' n : ℕ,
      if N < n then
        ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
      else
        0) =
      (∑' n : ℕ,
        if N < n then
          ((n : ℂ)⁻¹ : ℂ) *
            ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) *
              ((n : ℝ) ^ (-(σ - 1)) : ℂ)
        else
          0) := by
  refine tsum_congr ?_
  intro n
  by_cases hn_tail : N < n
  · have hn_pos : 0 < n :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one (le_of_lt (lt_of_le_of_lt hN hn_tail))
    exact
      if_pos hn_tail ▸
        if_pos hn_tail ▸
          Complex.boundaryLineOnePointRealParam_abelDampedDirichletTerm_eq_weighted
            t σ hn_pos
  · exact if_neg hn_tail ▸ if_neg hn_tail ▸ rfl

/-- Early owner copy of the summable Nat tail split, used before the Abel
boundary theorem consumes it. -/
theorem Complex.summable_nat_tail_eq_tsum_sub_Icc_of_zero_for_abel_boundary
    {f : ℕ → ℂ}
    (hf : Summable f)
    (hf_zero : f 0 = 0)
    (N : ℕ)
    (hN : 1 ≤ N) :
    (∑' n : ℕ, if N < n then f n else 0) =
      (∑' n : ℕ, f n) - ∑ n ∈ Finset.Icc 1 N, f n := by
  let S : Finset ℕ := Finset.Icc 1 N
  have hzero_not_mem : 0 ∉ S := by
    intro hmem
    have hone_le_zero : 1 ≤ 0 := (Finset.mem_Icc.mp hmem).1
    exact (not_le_of_gt zero_lt_one) hone_le_zero
  have htail_eq_compl :
      (fun n : ℕ => if N < n then f n else 0) =
        fun n : ℕ => if n ∈ (S : Set ℕ)ᶜ then f n else 0 := by
    funext n
    by_cases hn_tail : N < n
    · have hn_not_mem : n ∉ S := by
        intro hn_mem
        have hn_le_N : n ≤ N := (Finset.mem_Icc.mp hn_mem).2
        exact (not_le_of_gt hn_tail) hn_le_N
      rw [if_pos hn_tail, if_pos hn_not_mem]
    · have hn_mem_or_zero : n ∈ S ∨ n = 0 := by
        have hn_le_N : n ≤ N := le_of_not_gt hn_tail
        cases n with
        | zero =>
            exact Or.inr rfl
        | succ k =>
            have hn_one_le : 1 ≤ Nat.succ k := Nat.succ_le_succ (Nat.zero_le k)
            exact Or.inl (Finset.mem_Icc.mpr ⟨hn_one_le, hn_le_N⟩)
      cases hn_mem_or_zero with
      | inl hn_mem =>
          rw [if_neg hn_tail, if_neg]
          exact Set.mem_compl_iff.mp.mt hn_mem
      | inr hn_zero =>
          rw [if_neg hn_tail, if_pos]
          · exact hf_zero.symm
          · rw [hn_zero]
            exact hzero_not_mem
  have hsum_split :
      ∑ n ∈ S, f n + ∑' n : (S : Set ℕ)ᶜ, f n = ∑' n : ℕ, f n :=
    sum_add_tsum_compl (s := S) hf
  have htail_tsum_eq :
      (∑' n : ℕ, if n ∈ (S : Set ℕ)ᶜ then f n else 0) =
        ∑' n : (S : Set ℕ)ᶜ, f n := by
    exact (tsum_subtype (s := (S : Set ℕ)ᶜ) (f := f)).symm
  have hfinite_eq :
      ∑ n ∈ S, f n = ∑ n ∈ Finset.Icc 1 N, f n := rfl
  calc
    (∑' n : ℕ, if N < n then f n else 0) =
        ∑' n : ℕ, if n ∈ (S : Set ℕ)ᶜ then f n else 0 := by
      exact congrArg (fun g : ℕ → ℂ => ∑' n : ℕ, g n) htail_eq_compl
    _ = ∑' n : (S : Set ℕ)ᶜ, f n := htail_tsum_eq
    _ = (∑' n : ℕ, f n) - ∑ n ∈ S, f n := by
      exact eq_sub_of_add_eq' hsum_split
    _ = (∑' n : ℕ, f n) - ∑ n ∈ Finset.Icc 1 N, f n := by
      exact congrArg (fun z : ℂ => (∑' n : ℕ, f n) - z) hfinite_eq

/-- Early summability of the Abel-damped boundary Dirichlet series in the open
half-plane. -/
theorem Complex.boundaryLineOnePointRealParam_abelDirichletSeries_summable_for_tail
    (t σ : ℝ)
    (hσ : 1 < σ) :
    Summable
      (fun n : ℕ =>
        ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) := by
  have hexponent :
      1 < (((σ : ℂ) + (t : ℂ) * Complex.I).re) := by
    simpa using hσ
  have hsummable :
      Summable
        (fun n : ℕ =>
          1 / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    Complex.summable_one_div_nat_cpow.mpr hexponent
  exact hsummable

/-- Early finite-truncation algebra for an Abel-damped boundary Dirichlet
series. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedTail_eq_series_sub_truncation_for_tail
    (t σ : ℝ)
    (hσ : 1 < σ)
    (N : ℕ)
    (hN : 1 ≤ N) :
    (∑' n : ℕ,
      if N < n then
        ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
      else
        0) =
      (∑' n : ℕ,
        ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) -
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹ := by
  let f : ℕ → ℂ :=
    fun n : ℕ =>
      ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
  have hf_zero : f 0 = 0 := by
    simp [f]
  exact
    Complex.summable_nat_tail_eq_tsum_sub_Icc_of_zero_for_abel_boundary
      (Complex.boundaryLineOnePointRealParam_abelDirichletSeries_summable_for_tail
        t σ hσ)
      hf_zero N hN

/-- Early Abel-damped finite block convergence to the boundary-line finite
truncation. -/
theorem Complex.boundaryLineOnePointRealParam_abelFiniteTruncation_tendsto_boundaryTruncation_for_tail
    (t : ℝ)
    (N : ℕ) :
    Tendsto
      (fun σ : ℝ =>
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
      (𝓝[>] (1 : ℝ))
      (𝓝 (Complex.riemannZetaBoundaryLineTruncation t N)) := by
  have hpath :
      Tendsto
        (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)
        (𝓝[>] (1 : ℝ))
        (𝓝 (Complex.boundaryLineOnePointRealParam t)) := by
    have hreal :
        Tendsto
          (fun σ : ℝ => (σ : ℂ))
          (𝓝[>] (1 : ℝ))
          (𝓝 (1 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    have hconst :
        Tendsto
          (fun _ : ℝ => (t : ℂ) * Complex.I)
          (𝓝[>] (1 : ℝ))
          (𝓝 ((t : ℂ) * Complex.I)) :=
      tendsto_const_nhds
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)
            (𝓝[>] (1 : ℝ))
            (𝓝 z))
        (show (1 : ℂ) + (t : ℂ) * Complex.I =
            Complex.boundaryLineOnePointRealParam t by rfl)
        (hreal.add hconst)
  unfold Complex.riemannZetaBoundaryLineTruncation
  refine tendsto_finset_sum (Finset.Icc 1 N) ?_
  intro n hn_mem
  have hn_one_le : 1 ≤ n :=
    (Finset.mem_Icc.mp hn_mem).1
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one_le
  have hn_complex_ne : (n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn_pos)
  have hpow_ne :
      (n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hn_complex_ne]
    exact Complex.exp_ne_zero _
  exact
    ((Complex.continuousAt_const_cpow hn_complex_ne).tendsto.comp hpath).inv₀
      hpow_ne

/-- Early one-sided Abel boundary value of the zeta Dirichlet series on
`1 + it`, used by the first tail-limit owner theorem. -/
theorem Complex.boundaryLineOnePointRealParam_boundaryDirichletSeries_abel_tendsto_riemannZeta_for_tail
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (Complex.boundaryLineOnePointRealParam t))) := by
  have hboundary_ne_one :
      Complex.boundaryLineOnePointRealParam t ≠ 1 := by
    intro hboundary
    have him :
        (Complex.boundaryLineOnePointRealParam t).im = (1 : ℂ).im :=
      congrArg Complex.im hboundary
    have ht_zero : t = 0 := by
      simpa [Complex.boundaryLineOnePointRealParam] using him
    have hle_zero : (1 : ℝ) ≤ 0 := by
      simpa [ht_zero] using ht
    exact (not_le_of_gt zero_lt_one) hle_zero
  have hpath :
      Tendsto
        (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)
        (𝓝[>] (1 : ℝ))
        (𝓝 (Complex.boundaryLineOnePointRealParam t)) := by
    have hreal :
        Tendsto
          (fun σ : ℝ => (σ : ℂ))
          (𝓝[>] (1 : ℝ))
          (𝓝 (1 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    have hconst :
        Tendsto
          (fun _ : ℝ => (t : ℂ) * Complex.I)
          (𝓝[>] (1 : ℝ))
          (𝓝 ((t : ℂ) * Complex.I)) :=
      tendsto_const_nhds
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)
            (𝓝[>] (1 : ℝ))
            (𝓝 z))
        (show (1 : ℂ) + (t : ℂ) * Complex.I =
            Complex.boundaryLineOnePointRealParam t by rfl)
        (hreal.add hconst)
  have hzeta_path :
      Tendsto
        (fun σ : ℝ =>
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (Complex.boundaryLineOnePointRealParam t))) :=
    (Complex.differentiableAt_riemannZeta hboundary_ne_one).continuousAt.tendsto.comp
      hpath
  have hseries_eq :
      (fun σ : ℝ =>
        ∑' n : ℕ,
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun σ : ℝ =>
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    filter_upwards [eventually_mem_nhdsWithin] with σ hσ
    have hexponent :
        1 < (((σ : ℂ) + (t : ℂ) * Complex.I).re) := by
      simpa using hσ
    exact
      (Complex.zeta_eq_tsum_one_div_nat_cpow
        (s := (σ : ℂ) + (t : ℂ) * Complex.I) hexponent).symm
  exact
    (tendsto_congr' hseries_eq).mpr hzeta_path

/-- Dirichlet-series form of the Abel-damped post-cutoff tail boundary value.
This is the one-sided Abel statement used before converting terms to the
reciprocal-weighted logarithmic-phase normalization. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedDirichletTail_tendsto_zeta_remainder
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ)
    (hN : 1 ≤ N) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          if N < n then
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
          else
            0)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          Complex.riemannZetaBoundaryLineTruncation t N)) := by
  have hseries :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (Complex.boundaryLineOnePointRealParam t))) :=
    Complex.boundaryLineOnePointRealParam_boundaryDirichletSeries_abel_tendsto_riemannZeta_for_tail
      t ht
  have htail_eq :
      (fun σ : ℝ =>
        ∑' n : ℕ,
          if N < n then
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
          else
            0) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun σ : ℝ =>
          (∑' n : ℕ,
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) -
            ∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) := by
    filter_upwards [eventually_mem_nhdsWithin] with σ hσ
    exact
      Complex.boundaryLineOnePointRealParam_abelDampedTail_eq_series_sub_truncation_for_tail
        t σ hσ N hN
  have hfinite :
      Tendsto
        (fun σ : ℝ =>
          ∑ n ∈ Finset.Icc 1 N,
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
        (𝓝[>] (1 : ℝ))
        (𝓝 (Complex.riemannZetaBoundaryLineTruncation t N)) :=
    Complex.boundaryLineOnePointRealParam_abelFiniteTruncation_tendsto_boundaryTruncation_for_tail
      t N
  exact
    (tendsto_congr' htail_eq).mpr
      (hseries.sub hfinite)

/-- The Abel-damped post-cutoff logarithmic-phase tail tends to the
analytic-continuation boundary remainder of `ζ(1 + it)`.

This is the boundary Dirichlet-continuation theorem: it is not a definitional
unfolding of `riemannZeta` at `re = 1`. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedTail_tendsto_zeta_remainder
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ)
    (hN : 1 ≤ N) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          if N < n then
            ((n : ℂ)⁻¹ : ℂ) *
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) *
                ((n : ℝ) ^ (-(σ - 1)) : ℂ)
          else
            0)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            ((n : ℂ)⁻¹ : ℂ) *
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  have hdirichlet :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            if N < n then
              ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
            else
              0)
        (𝓝[>] (1 : ℝ))
        (𝓝
          (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
            Complex.riemannZetaBoundaryLineTruncation t N)) :=
    Complex.boundaryLineOnePointRealParam_abelDampedDirichletTail_tendsto_zeta_remainder
      t ht N hN
  have htail_eq :
      (fun σ : ℝ =>
        ∑' n : ℕ,
          if N < n then
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
          else
            0) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun σ : ℝ =>
          ∑' n : ℕ,
            if N < n then
              ((n : ℂ)⁻¹ : ℂ) *
                ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) *
                  ((n : ℝ) ^ (-(σ - 1)) : ℂ)
            else
              0) := by
    filter_upwards [eventually_mem_nhdsWithin] with σ hσ
    exact
      Complex.boundaryLineOnePointRealParam_abelDampedTail_eq_weightedTail
        t σ N hN
  have htrunc :
      Complex.riemannZetaBoundaryLineTruncation t N =
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ)⁻¹ : ℂ) *
            ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    Complex.riemannZetaBoundaryLineTruncation_eq_weighted_logarithmicPhase_sum
      t N
  have hlimit :
      riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          Complex.riemannZetaBoundaryLineTruncation t N =
        riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            ((n : ℂ)⁻¹ : ℂ) *
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    congrArg (fun z : ℂ => riemannZeta (Complex.boundaryLineOnePointRealParam t) - z)
      htrunc
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun σ : ℝ =>
            ∑' n : ℕ,
              if N < n then
                ((n : ℂ)⁻¹ : ℂ) *
                  ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) *
                    ((n : ℝ) ^ (-(σ - 1)) : ℂ)
              else
                0)
          (𝓝[>] (1 : ℝ))
          (𝓝 z))
      hlimit
      (Tendsto.congr' htail_eq hdirichlet)

/-- Transport an eventually uniform Abel-damped bound to the boundary
remainder. -/
theorem Complex.boundaryLineOnePointRealParam_abelBoundaryTail_bound_of_damped
    (hbounded :
      ∃ A : ℝ,
        0 < A ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
            ∀ N : ℕ,
              1 ≤ N →
                ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
                  ‖∑' n : ℕ,
                    if N < n then
                      ((n : ℂ)⁻¹ : ℂ) *
                        ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) *
                          ((n : ℝ) ^ (-(σ - 1)) : ℂ)
                    else
                      0‖ ≤
                    A * Real.log (2 + ‖t‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
                ∑ n ∈ Finset.Icc 1 N,
                  ((n : ℂ)⁻¹ : ℂ) *
                    ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                A * Real.log (2 + ‖t‖) := by
  rcases hbounded with ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht N hN
  have htendsto :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            if N < n then
              ((n : ℂ)⁻¹ : ℂ) *
                ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) *
                  ((n : ℝ) ^ (-(σ - 1)) : ℂ)
            else
              0)
        (𝓝[>] (1 : ℝ))
        (𝓝
          (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
            ∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ)⁻¹ : ℂ) *
                ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) :=
    Complex.boundaryLineOnePointRealParam_abelDampedTail_tendsto_zeta_remainder
      t ht N hN
  have heventually :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ‖∑' n : ℕ,
          if N < n then
            ((n : ℂ)⁻¹ : ℂ) *
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) *
                ((n : ℝ) ^ (-(σ - 1)) : ℂ)
          else
            0‖ ≤
          A * Real.log (2 + ‖t‖) :=
    hbound t ht N hN
  exact
    le_of_tendsto_of_tendsto'
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => A * Real.log (2 + ‖t‖))
        (𝓝[>] (1 : ℝ)) (𝓝 (A * Real.log (2 + ‖t‖))))
      (htendsto.norm)
      heventually

/-- Abel boundary passage for the post-cutoff reciprocal-weighted logarithmic
phase. -/
theorem Complex.boundaryLineOnePointRealParam_abelBoundaryTail_bound_of_finiteAbel :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
                ∑ n ∈ Finset.Icc 1 N,
                  ((n : ℂ)⁻¹ : ℂ) *
                    ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                A * Real.log (2 + ‖t‖) := by
  exact
    Complex.boundaryLineOnePointRealParam_abelBoundaryTail_bound_of_damped
      Complex.boundaryLineOnePointRealParam_abelDampedTail_bound_of_finiteAbel

/-- Abel boundary passage for the post-cutoff reciprocal-weighted logarithmic
phase. -/
theorem Complex.boundaryLineOnePointRealParam_abelBoundaryTail_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
                ∑ n ∈ Finset.Icc 1 N,
                  ((n : ℂ)⁻¹ : ℂ) *
                    ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                A * Real.log (2 + ‖t‖) := by
  exact Complex.boundaryLineOnePointRealParam_abelBoundaryTail_bound_of_finiteAbel

/-- One-sided Abel boundary value of the zeta Dirichlet series on `1 + it`.

This is the owner statement for the analytic-continuation boundary passage; it
does not assert ordinary convergence of the Dirichlet series on `re = 1`. -/
theorem Complex.boundaryLineOnePointRealParam_boundaryDirichletSeries_abel_tendsto_riemannZeta_from_dirichletContinuation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (Complex.boundaryLineOnePointRealParam t))) := by
  have hboundary_ne_one :
      Complex.boundaryLineOnePointRealParam t ≠ 1 := by
    intro hboundary
    have him :
        (Complex.boundaryLineOnePointRealParam t).im = (1 : ℂ).im :=
      congrArg Complex.im hboundary
    have ht_zero : t = 0 := by
      simpa [Complex.boundaryLineOnePointRealParam] using him
    have hle_zero : (1 : ℝ) ≤ 0 := by
      simpa [ht_zero] using ht
    exact (not_le_of_gt zero_lt_one) hle_zero
  have hpath :
      Tendsto
        (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)
        (𝓝[>] (1 : ℝ))
        (𝓝 (Complex.boundaryLineOnePointRealParam t)) := by
    have hreal :
        Tendsto
          (fun σ : ℝ => (σ : ℂ))
          (𝓝[>] (1 : ℝ))
          (𝓝 (1 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    have hconst :
        Tendsto
          (fun _ : ℝ => (t : ℂ) * Complex.I)
          (𝓝[>] (1 : ℝ))
          (𝓝 ((t : ℂ) * Complex.I)) :=
      tendsto_const_nhds
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)
            (𝓝[>] (1 : ℝ))
            (𝓝 z))
        (show (1 : ℂ) + (t : ℂ) * Complex.I =
            Complex.boundaryLineOnePointRealParam t by rfl)
        (hreal.add hconst)
  have hzeta_path :
      Tendsto
        (fun σ : ℝ =>
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (Complex.boundaryLineOnePointRealParam t))) :=
    (Complex.differentiableAt_riemannZeta hboundary_ne_one).continuousAt.tendsto.comp
      hpath
  have hseries_eq :
      (fun σ : ℝ =>
        ∑' n : ℕ,
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun σ : ℝ =>
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    filter_upwards [eventually_mem_nhdsWithin] with σ hσ
    have hexponent :
        1 < (((σ : ℂ) + (t : ℂ) * Complex.I).re) := by
      simpa using hσ
    exact
      (Complex.zeta_eq_tsum_one_div_nat_cpow
        (s := (σ : ℂ) + (t : ℂ) * Complex.I) hexponent).symm
  exact
    (tendsto_congr' hseries_eq).mpr hzeta_path

/-- Abel boundary value of the boundary-line Dirichlet series at `1 + it`.

This is deliberately a one-sided Abel limit, not ordinary convergence of the
Dirichlet series on `re = 1`. -/
theorem Complex.boundaryLineOnePointRealParam_boundaryDirichletSeries_abel_tendsto_riemannZeta
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (Complex.boundaryLineOnePointRealParam t))) := by
  exact
    Complex.boundaryLineOnePointRealParam_boundaryDirichletSeries_abel_tendsto_riemannZeta_from_dirichletContinuation
      t ht

/-- Absolute convergence of the Abel-damped boundary Dirichlet series in the
open half-plane `σ > 1`. -/
theorem Complex.boundaryLineOnePointRealParam_abelDirichletSeries_summable
    (t σ : ℝ)
    (hσ : 1 < σ) :
    Summable
      (fun n : ℕ =>
        ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) := by
  have hexponent :
      1 < (((σ : ℂ) + (t : ℂ) * Complex.I).re) := by
    simpa using hσ
  have hsummable :
      Summable
        (fun n : ℕ =>
          1 / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    Complex.summable_one_div_nat_cpow.mpr hexponent
  exact hsummable

/-- A summable Nat series whose zeroth term vanishes splits as a finite
`Icc 1 N` block plus the strict post-`N` tail. -/
theorem Complex.summable_nat_tail_eq_tsum_sub_Icc_of_zero
    {f : ℕ → ℂ}
    (hf : Summable f)
    (hf_zero : f 0 = 0)
    (N : ℕ)
    (hN : 1 ≤ N) :
    (∑' n : ℕ, if N < n then f n else 0) =
      (∑' n : ℕ, f n) - ∑ n ∈ Finset.Icc 1 N, f n := by
  let S : Finset ℕ := Finset.Icc 1 N
  have hzero_not_mem : 0 ∉ S := by
    intro hmem
    have hone_le_zero : 1 ≤ 0 := (Finset.mem_Icc.mp hmem).1
    exact (not_le_of_gt zero_lt_one) hone_le_zero
  have htail_eq_compl :
      (fun n : ℕ => if N < n then f n else 0) =
        fun n : ℕ => if n ∈ (S : Set ℕ)ᶜ then f n else 0 := by
    funext n
    by_cases hn_tail : N < n
    · have hn_not_mem : n ∉ S := by
        intro hn_mem
        have hn_le_N : n ≤ N := (Finset.mem_Icc.mp hn_mem).2
        exact (not_le_of_gt hn_tail) hn_le_N
      rw [if_pos hn_tail, if_pos hn_not_mem]
    · have hn_mem_or_zero : n ∈ S ∨ n = 0 := by
        have hn_le_N : n ≤ N := le_of_not_gt hn_tail
        cases n with
        | zero =>
            exact Or.inr rfl
        | succ k =>
            have hn_one_le : 1 ≤ Nat.succ k := Nat.succ_le_succ (Nat.zero_le k)
            exact Or.inl (Finset.mem_Icc.mpr ⟨hn_one_le, hn_le_N⟩)
      cases hn_mem_or_zero with
      | inl hn_mem =>
          rw [if_neg hn_tail, if_neg]
          exact Set.mem_compl_iff.mp.mt hn_mem
      | inr hn_zero =>
          rw [if_neg hn_tail, if_pos]
          · exact hf_zero.symm
          · rw [hn_zero]
            exact hzero_not_mem
  have hsum_split :
      ∑ n ∈ S, f n + ∑' n : (S : Set ℕ)ᶜ, f n = ∑' n : ℕ, f n :=
    sum_add_tsum_compl (s := S) hf
  have htail_tsum_eq :
      (∑' n : ℕ, if n ∈ (S : Set ℕ)ᶜ then f n else 0) =
        ∑' n : (S : Set ℕ)ᶜ, f n := by
    exact (tsum_subtype (s := (S : Set ℕ)ᶜ) (f := f)).symm
  have hfinite_eq :
      ∑ n ∈ S, f n = ∑ n ∈ Finset.Icc 1 N, f n := rfl
  calc
    (∑' n : ℕ, if N < n then f n else 0) =
        ∑' n : ℕ, if n ∈ (S : Set ℕ)ᶜ then f n else 0 := by
      exact congrArg (fun g : ℕ → ℂ => ∑' n : ℕ, g n) htail_eq_compl
    _ = ∑' n : (S : Set ℕ)ᶜ, f n := htail_tsum_eq
    _ = (∑' n : ℕ, f n) - ∑ n ∈ S, f n := by
      exact eq_sub_of_add_eq' hsum_split
    _ = (∑' n : ℕ, f n) - ∑ n ∈ Finset.Icc 1 N, f n := by
      exact congrArg (fun z : ℂ => (∑' n : ℕ, f n) - z) hfinite_eq

/-- Finite truncation algebra for an Abel-damped boundary Dirichlet series in
the open half-plane. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedTail_eq_series_sub_truncation_of_summable
    (t σ : ℝ)
    (N : ℕ)
    (hN : 1 ≤ N)
    (hsummable :
      Summable
        (fun n : ℕ =>
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)) :
    (∑' n : ℕ,
      if N < n then
        ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
      else
        0) =
      (∑' n : ℕ,
        ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) -
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹ := by
  let f : ℕ → ℂ :=
    fun n : ℕ =>
      ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
  have hf_zero : f 0 = 0 := by
    simp [f]
  exact
    Complex.summable_nat_tail_eq_tsum_sub_Icc_of_zero
      hsummable hf_zero N hN

/-- Pointwise finite-truncation identity for Abel-damped boundary Dirichlet
series.  The tail is the full Abel series minus its Abel-damped finite block. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedTail_eq_series_sub_truncation
    (t σ : ℝ)
    (hσ : 1 < σ)
    (N : ℕ)
    (hN : 1 ≤ N) :
    (∑' n : ℕ,
      if N < n then
        ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
      else
        0) =
      (∑' n : ℕ,
        ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) -
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹ := by
  exact
    Complex.boundaryLineOnePointRealParam_abelDampedTail_eq_series_sub_truncation_of_summable
      t σ N hN
      (Complex.boundaryLineOnePointRealParam_abelDirichletSeries_summable
        t σ hσ)

/-- The Abel-damped finite block tends to the boundary-line finite truncation
as `σ → 1+`. -/
theorem Complex.boundaryLineOnePointRealParam_abelFiniteTruncation_tendsto_boundaryTruncation
    (t : ℝ)
    (N : ℕ) :
    Tendsto
      (fun σ : ℝ =>
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
      (𝓝[>] (1 : ℝ))
      (𝓝 (Complex.riemannZetaBoundaryLineTruncation t N)) := by
  have hpath :
      Tendsto
        (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)
        (𝓝[>] (1 : ℝ))
        (𝓝 (Complex.boundaryLineOnePointRealParam t)) := by
    have hreal :
        Tendsto
          (fun σ : ℝ => (σ : ℂ))
          (𝓝[>] (1 : ℝ))
          (𝓝 (1 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    have hconst :
        Tendsto
          (fun _ : ℝ => (t : ℂ) * Complex.I)
          (𝓝[>] (1 : ℝ))
          (𝓝 ((t : ℂ) * Complex.I)) :=
      tendsto_const_nhds
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)
            (𝓝[>] (1 : ℝ))
            (𝓝 z))
        (show (1 : ℂ) + (t : ℂ) * Complex.I =
            Complex.boundaryLineOnePointRealParam t by rfl)
        (hreal.add hconst)
  unfold Complex.riemannZetaBoundaryLineTruncation
  refine tendsto_finset_sum (Finset.Icc 1 N) ?_
  intro n hn_mem
  have hn_one_le : 1 ≤ n :=
    (Finset.mem_Icc.mp hn_mem).1
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one_le
  have hn_complex_ne : (n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn_pos)
  have hpow_ne :
      (n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hn_complex_ne]
    exact Complex.exp_ne_zero _
  exact
    ((Complex.continuousAt_const_cpow hn_complex_ne).tendsto.comp hpath).inv₀
      hpow_ne

/-- Removing the first `N` terms from a one-sided Abel-damped Dirichlet series
is compatible with the Abel boundary limit. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedTail_tendsto_zeta_remainder_from_series
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ)
    (hN : 1 ≤ N)
    (hseries :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (Complex.boundaryLineOnePointRealParam t)))) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          if N < n then
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
          else
            0)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          Complex.riemannZetaBoundaryLineTruncation t N)) := by
  have htail_eq :
      (fun σ : ℝ =>
        ∑' n : ℕ,
          if N < n then
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
          else
            0) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun σ : ℝ =>
          (∑' n : ℕ,
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) -
            ∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) := by
    filter_upwards [eventually_mem_nhdsWithin] with σ hσ
    exact
      Complex.boundaryLineOnePointRealParam_abelDampedTail_eq_series_sub_truncation
        t σ hσ N hN
  have hfinite :
      Tendsto
        (fun σ : ℝ =>
          ∑ n ∈ Finset.Icc 1 N,
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
        (𝓝[>] (1 : ℝ))
        (𝓝 (Complex.riemannZetaBoundaryLineTruncation t N)) :=
    Complex.boundaryLineOnePointRealParam_abelFiniteTruncation_tendsto_boundaryTruncation
      t N
  exact
    (tendsto_congr' htail_eq).mpr
      (hseries.sub hfinite)

/-- Removing a finite truncation from the Abel-damped Dirichlet series leaves
the Abel-damped post-cutoff tail. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedTail_tendsto_zeta_remainder_of_series
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ)
    (hN : 1 ≤ N) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          if N < n then
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
          else
            0)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          Complex.riemannZetaBoundaryLineTruncation t N)) := by
  exact
    Complex.boundaryLineOnePointRealParam_abelDampedTail_tendsto_zeta_remainder_from_series
      t ht N hN
      (Complex.boundaryLineOnePointRealParam_boundaryDirichletSeries_abel_tendsto_riemannZeta
        t ht)

/-- The Abel boundary tail has the zeta-remainder boundary value. -/
theorem Complex.boundaryLineOnePointRealParam_boundaryDirichletTail_abel_tendsto_zeta_remainder
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ)
    (hN : 1 ≤ N) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          if N < n then
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
          else
            0)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          Complex.riemannZetaBoundaryLineTruncation t N)) := by
  exact
    Complex.boundaryLineOnePointRealParam_abelDampedTail_tendsto_zeta_remainder_of_series
      t ht N hN

/-- Abel-boundary post-cutoff tail bound written in boundary-line Dirichlet
monomials. -/
theorem Complex.boundaryLineOnePointRealParam_abelBoundaryDirichletTail_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
                  Complex.riemannZetaBoundaryLineTruncation t N‖ ≤
                A * Real.log (2 + ‖t‖) := by
  rcases Complex.boundaryLineOnePointRealParam_abelBoundaryTail_bound with
    ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht N hN
  have htrunc :
      Complex.riemannZetaBoundaryLineTruncation t N =
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    Complex.riemannZetaBoundaryLineTruncation_eq_weighted_logarithmicPhase_sum t N
  have hbound_weighted :
      ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        A * Real.log (2 + ‖t‖) :=
    hbound t ht N hN
  have hbound_trunc :
      ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          Complex.riemannZetaBoundaryLineTruncation t N‖ ≤
        A * Real.log (2 + ‖t‖) :=
    Eq.subst
      (motive := fun S : ℂ =>
        ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) - S‖ ≤
          A * Real.log (2 + ‖t‖))
      htrunc.symm
      hbound_weighted
  exact hbound_trunc

/-- Boundary-line Abel tail bound in the zeta-remainder form. -/
theorem Complex.boundaryLineOnePointRealParam_zetaRemainder_bound_of_abelBoundary :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
                  Complex.riemannZetaBoundaryLineTruncation t N‖ ≤
                A * Real.log (2 + ‖t‖) := by
  exact Complex.boundaryLineOnePointRealParam_abelBoundaryDirichletTail_bound

/-- Euler-Maclaurin post-cutoff tail for zeta on the boundary line, in
Abel-boundary zeta-remainder form. -/
theorem Complex.boundaryLineOnePointRealParam_eulerMaclaurinTail_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
                  Complex.riemannZetaBoundaryLineTruncation t N‖ ≤
                A * Real.log (2 + ‖t‖) := by
  exact Complex.boundaryLineOnePointRealParam_zetaRemainder_bound_of_abelBoundary

/-- Transport from the Abel boundary remainder to the guarded finite
truncation comparison for zeta on the boundary line. -/
theorem Complex.riemannZeta_boundaryLine_truncated_dirichlet_remainder_bound_of_abelBoundary :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
                Complex.riemannZetaBoundaryLineTruncation t N‖ ≤
                  A * Real.log (2 + ‖t‖) := by
  rcases Complex.boundaryLineOnePointRealParam_abelBoundaryTail_bound with
    ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht N hN
  have htrunc :
      Complex.riemannZetaBoundaryLineTruncation t N =
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    Complex.riemannZetaBoundaryLineTruncation_eq_weighted_logarithmicPhase_sum
      t N
  have hnorm :
      ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        A * Real.log (2 + ‖t‖) :=
    hbound t ht N hN
  exact Eq.subst
    (motive := fun S : ℂ =>
      ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) - S‖ ≤
        A * Real.log (2 + ‖t‖))
    htrunc.symm
    hnorm

/-- Guarded finite truncation comparison for zeta on the boundary line. -/
theorem Complex.riemannZeta_boundaryLine_truncated_dirichlet_remainder_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
                Complex.riemannZetaBoundaryLineTruncation t N‖ ≤
                  A * Real.log (2 + ‖t‖) := by
  exact Complex.riemannZeta_boundaryLine_truncated_dirichlet_remainder_bound_of_abelBoundary

end

end LFunctions
end Boundary
