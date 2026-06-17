import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.AbelTail.Continuation

/-!
# Abel tail on the boundary line

This file owns the post-cutoff Abel/Euler-Maclaurin tail estimate for
`ζ(1 + it)`.  The nonzero-frequency guard is part of the owner surface.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Fixed-constant form of the positive Abel damping step for the boundary
line tail. -/
theorem Complex.boundaryLineOnePointRealParam_abelDampedTail_bound_from_finiteAbel_constant
    {A : ℝ}
    (hfinite :
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ∀ M : ℕ,
                N ≤ M →
                  ‖∑ n ∈ Finset.Ioc N M,
                    ((n : ℂ)⁻¹ : ℂ) *
                      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                    A * Real.log (2 + ‖t‖)) :
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
  have hsummable_tail :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        Summable
          (fun n : ℕ =>
            if N < n then
              a n * ((n : ℝ) ^ (-(σ - 1)) : ℂ)
            else
              0) := by
    filter_upwards [eventually_mem_nhdsWithin] with σ hσ
    have hdirichlet :
        Summable
          (fun n : ℕ =>
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) :=
      Complex.boundaryLineOnePointRealParam_abelDirichletSeries_summable_for_tail
        t σ hσ
  have htail_dirichlet :
      Summable
          (fun n : ℕ =>
            if N < n then
              ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹
            else
              0) := by
      exact hdirichlet.congr_cofinite
        (by
          filter_upwards [eventually_ge_atTop (N + 1)] with n hn
          have hn_tail : N < n := Nat.lt_of_succ_le hn
          exact if_pos hn_tail)
  exact htail_dirichlet.congr
    (fun n =>
      match Classical.em (N < n) with
      | Or.inl hn_tail =>
          have hn_pos : 0 < n :=
            Nat.lt_of_lt_of_le Nat.zero_lt_one (le_of_lt (lt_of_le_of_lt hN hn_tail))
          if_pos hn_tail ▸
            (Complex.boundaryLineOnePointRealParam_abelDampedDirichletTerm_eq_weighted
              t σ hn_pos).symm
      | Or.inr hn_tail =>
          if_neg hn_tail ▸ rfl)
  have hdamped :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ‖∑' n : ℕ,
          if N < n then
            a n * ((n : ℝ) ^ (-(σ - 1)) : ℂ)
          else
            0‖ ≤
          A * Real.log (2 + ‖t‖) :=
    Complex.abelDampedTail_bound_of_uniform_finite_tail_bound
      N hN hsummable_tail hfinite_tail
  exact hdamped.mono (fun σ hσ => hσ)

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
  exact
    match Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound with
    | ⟨A, hA_pos, hfinite⟩ =>
        Exists.intro A
          (And.intro hA_pos
            (Complex.boundaryLineOnePointRealParam_abelDampedTail_bound_from_finiteAbel_constant
              hfinite))

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

/-- Transport an eventually uniform Abel-damped bound to the boundary
remainder. -/
theorem Complex.boundaryLineOnePointRealParam_abelBoundaryTail_bound_of_damped_constant
    {A : ℝ}
    (hbound :
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
    ∀ t : ℝ,
      1 ≤ ‖t‖ →
        ∀ N : ℕ,
          1 ≤ N →
            ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
              ∑ n ∈ Finset.Icc 1 N,
                ((n : ℂ)⁻¹ : ℂ) *
                  ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
              A * Real.log (2 + ‖t‖) := by
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
  exact
    match hbounded with
    | ⟨A, hA_pos, hbound⟩ =>
        Exists.intro A
          (And.intro hA_pos
            (Complex.boundaryLineOnePointRealParam_abelBoundaryTail_bound_of_damped_constant
              hbound))

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
  exact
    match Complex.boundaryLineOnePointRealParam_abelBoundaryTail_bound with
    | ⟨A, hA_pos, hbound⟩ =>
        Exists.intro A
          (And.intro hA_pos
            (fun t ht N hN =>
              let htrunc :
                  Complex.riemannZetaBoundaryLineTruncation t N =
                    ∑ n ∈ Finset.Icc 1 N,
                      ((n : ℂ)⁻¹ : ℂ) *
                        ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
                Complex.riemannZetaBoundaryLineTruncation_eq_weighted_logarithmicPhase_sum t N
              let hbound_weighted :
                  ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
                      ∑ n ∈ Finset.Icc 1 N,
                        ((n : ℂ)⁻¹ : ℂ) *
                          ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                    A * Real.log (2 + ‖t‖) :=
                hbound t ht N hN
              Eq.subst
                (motive := fun S : ℂ =>
                  ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) - S‖ ≤
                    A * Real.log (2 + ‖t‖))
                htrunc.symm
                hbound_weighted))

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
  exact
    match Complex.boundaryLineOnePointRealParam_abelBoundaryTail_bound with
    | ⟨A, hA_pos, hbound⟩ =>
        Exists.intro A
          (And.intro hA_pos
            (fun t ht N hN =>
              let htrunc :
                  Complex.riemannZetaBoundaryLineTruncation t N =
                    ∑ n ∈ Finset.Icc 1 N,
                      ((n : ℂ)⁻¹ : ℂ) *
                        ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
                Complex.riemannZetaBoundaryLineTruncation_eq_weighted_logarithmicPhase_sum
                  t N
              let hnorm :
                  ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
                      ∑ n ∈ Finset.Icc 1 N,
                        ((n : ℂ)⁻¹ : ℂ) *
                          ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                    A * Real.log (2 + ‖t‖) :=
                hbound t ht N hN
              Eq.subst
                (motive := fun S : ℂ =>
                  ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) - S‖ ≤
                    A * Real.log (2 + ‖t‖))
                htrunc.symm
                hnorm))

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
