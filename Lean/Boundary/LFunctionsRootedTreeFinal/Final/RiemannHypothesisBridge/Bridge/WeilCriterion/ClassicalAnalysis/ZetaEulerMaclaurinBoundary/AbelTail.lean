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

/-- Finite Abel-summation estimate for the post-cutoff reciprocal-weighted
logarithmic phase.

This is the finite partial-summation step: combine the first-derivative
oscillatory estimate for `∑ n^{-it}` with monotonicity of the reciprocal
weight.  Cf. Apostol, *Introduction to Analytic Number Theory*, Ch. 3. -/
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
  sorry

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

/-- Abel boundary passage for the post-cutoff reciprocal-weighted logarithmic
phase.

This is the genuine limiting analytic root: finite Abel tail bounds are
transported through Abel damping and the Dirichlet-continuation boundary value
of `ζ(1 + it)`. -/
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
  sorry

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

/-- Transport from the Abel boundary remainder to the post-cutoff `tsum` tail
written in boundary-line Dirichlet monomials. -/
theorem Complex.boundaryLineOnePointRealParam_tsumTail_eq_zeta_remainder
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ)
    (hN : 1 ≤ N) :
    (∑' n : ℕ,
        if N < n then
          ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹
        else
          0) =
      riemannZeta (Complex.boundaryLineOnePointRealParam t) -
        Complex.riemannZetaBoundaryLineTruncation t N := by
  sorry

/-- Transport from the Abel boundary remainder to the post-cutoff `tsum` tail
written in boundary-line Dirichlet monomials. -/
theorem Complex.boundaryLineOnePointRealParam_tsumTail_bound_of_abelBoundary_transport :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ‖∑' n : ℕ,
                if N < n then
                  ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹
                else
                  0‖ ≤
                A * Real.log (2 + ‖t‖) := by
  rcases Complex.boundaryLineOnePointRealParam_abelBoundaryTail_bound with
    ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht N hN
  have htail :
      (∑' n : ℕ,
          if N < n then
            ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹
          else
            0) =
        riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          Complex.riemannZetaBoundaryLineTruncation t N :=
    Complex.boundaryLineOnePointRealParam_tsumTail_eq_zeta_remainder t ht N hN
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
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ A * Real.log (2 + ‖t‖))
    htail.symm
    hbound_trunc

/-- Transport from the Abel boundary remainder to the post-cutoff `tsum` tail
written in boundary-line Dirichlet monomials. -/
theorem Complex.boundaryLineOnePointRealParam_tsumTail_bound_of_abelBoundary :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ‖∑' n : ℕ,
                if N < n then
                  ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹
                else
                  0‖ ≤
                A * Real.log (2 + ‖t‖) := by
  exact Complex.boundaryLineOnePointRealParam_tsumTail_bound_of_abelBoundary_transport

/-- Euler-Maclaurin post-cutoff tail for zeta on the boundary line, with the
nonzero-frequency guard exposed.

The infinite tail is the Abel boundary value of the reciprocal-weighted
logarithmic phase after transporting back to the boundary-line Dirichlet
monomial. -/
theorem Complex.boundaryLineOnePointRealParam_eulerMaclaurinTail_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ‖∑' n : ℕ,
                if N < n then
                  ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹
                else
                  0‖ ≤
                A * Real.log (2 + ‖t‖) := by
  exact Complex.boundaryLineOnePointRealParam_tsumTail_bound_of_abelBoundary

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
