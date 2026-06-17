import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.ReciprocalDensity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Owner

/-!
# Finite Abel tails on the boundary line

This file owns the finite reciprocal-weight Abel estimates used by the
boundary-line Abel tail argument for `ζ(1 + it)`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.seventy_four_pos_for_abelTail : 0 < (74 : ℝ) :=
  Nat.cast_pos.mpr (show (0 : ℕ) < 74 from Nat.succ_pos 73)

theorem Nat.one_le_two_for_abelTail : (1 : ℕ) ≤ 2 :=
  Nat.succ_le_succ (Nat.zero_le 1)

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
  exact Finset.sum_congr rfl
    (fun n hn_mem =>
      let hn_one_le : 1 ≤ n := (Finset.mem_Icc.mp hn_mem).1
      let hn_pos : 0 < n := Nat.lt_of_succ_le hn_one_le
      Complex.boundaryLineOnePointRealParam_dirichletTerm_eq_reciprocal_mul_oscillation
        t hn_pos)

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
  exact Exists.intro (74 : ℝ)
    (And.intro Real.seventy_four_pos_for_abelTail
      (fun t ht N hN M hNM =>
        boundaryLineOnePointRealParam_logarithmicPhase_finiteTail_norm_le
          t ht hN hNM))

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
  exact
    match Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound_standard with
    | ⟨A, hA_pos, hbound⟩ =>
        Exists.intro A
          (And.intro hA_pos
            (fun t ht M hM =>
              let hcutoff_one : 1 ≤ ⌊2 + ‖t‖⌋₊ := by
                have htwo_le : (2 : ℝ) ≤ 2 + ‖t‖ :=
                  le_add_of_nonneg_right (norm_nonneg t)
                have hfloor_two : 2 ≤ ⌊2 + ‖t‖⌋₊ :=
                  (Nat.le_floor_iff zero_lt_two).mpr htwo_le
                exact le_trans Nat.one_le_two_for_abelTail hfloor_two
              hbound t ht ⌊2 + ‖t‖⌋₊ hcutoff_one M hM))

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

end

end LFunctions
end Boundary
