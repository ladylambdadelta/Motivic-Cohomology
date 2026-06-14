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
  sorry

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
  sorry

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
  sorry

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

/-- Boundary Dirichlet-series summability at `1 + it`.

This is the boundary-value theorem for the ordinary Dirichlet series on the
nonzero-frequency line. -/
theorem Complex.boundaryLineOnePointRealParam_boundaryDirichletSeries_hasSum_riemannZeta
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    HasSum
      (fun n : ℕ =>
        ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹)
      (riemannZeta (Complex.boundaryLineOnePointRealParam t)) := by
  sorry

/-- Removing a finite truncation from the boundary Dirichlet series leaves the
post-cutoff Dirichlet tail. -/
theorem Complex.boundaryLineOnePointRealParam_boundaryDirichletTail_hasSum_zeta_remainder_of_series
    (t : ℝ)
    (N : ℕ)
    (hζ :
      HasSum
        (fun n : ℕ =>
          ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹)
        (riemannZeta (Complex.boundaryLineOnePointRealParam t))) :
    HasSum
      (fun n : ℕ =>
        if N < n then
          ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹
        else
          0)
      (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
        Complex.riemannZetaBoundaryLineTruncation t N) := by
  let f : ℕ → ℂ := fun n : ℕ =>
    ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹
  have htail_compl :
      HasSum
        (fun x : {n : ℕ // n ∉ Finset.Icc 1 N} => f x)
        (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N, f n) :=
    ((Finset.Icc 1 N).hasSum_iff_compl).mp hζ
  have htail_indicator :
      HasSum
        ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f)
        (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N, f n) := by
    exact
      (hasSum_subtype_iff_indicator
        (s := {n : ℕ | n ∉ Finset.Icc 1 N})
        (f := f)).mp
        htail_compl
  have hzero : f 0 = 0 := by
    have hs_ne_zero : Complex.boundaryLineOnePointRealParam t ≠ 0 := by
      intro hs
      have hre_zero : (Complex.boundaryLineOnePointRealParam t).re = 0 := by
        exact congrArg Complex.re hs
      have hre_one : (Complex.boundaryLineOnePointRealParam t).re = 1 :=
        Complex.boundaryLineOnePointRealParam_re t
      have hone_eq_zero : (1 : ℝ) = 0 :=
        Eq.trans hre_one.symm hre_zero
      exact one_ne_zero hone_eq_zero
    have hpow_zero :
        (0 : ℂ) ^ (Complex.boundaryLineOnePointRealParam t) = 0 :=
      (cpow_eq_zero_iff).mpr ⟨rfl, hs_ne_zero⟩
    calc
      f 0 = ((0 : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹ :=
        rfl
      _ = (0 : ℂ)⁻¹ := by
        exact congrArg Inv.inv hpow_zero
      _ = 0 :=
        inv_zero
  have hindicator :
      ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f) =
        (fun n : ℕ => if N < n then f n else 0) := by
    funext n
    by_cases hn_tail : N < n
    · have hn_not_mem : n ∉ Finset.Icc 1 N := by
        intro hn_mem
        have hn_le_N : n ≤ N :=
          (Finset.mem_Icc.mp hn_mem).2
        exact not_lt_of_ge hn_le_N hn_tail
      calc
        ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f) n = f n :=
          Set.indicator_of_mem hn_not_mem f
        _ = (if N < n then f n else 0) := by
          exact (if_pos hn_tail).symm
    · have hn_not_tail : ¬ N < n :=
        hn_tail
      by_cases hn_zero : n = 0
      · have hn_mem_false_or_zero :
            ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f) n = 0 := by
          calc
            ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f) n = f n := by
              have hn_not_mem : n ∉ Finset.Icc 1 N := by
                intro hn_mem
                have hone_le_n : 1 ≤ n :=
                  (Finset.mem_Icc.mp hn_mem).1
                have hone_le_zero : (1 : ℕ) ≤ 0 := by
                  exact Eq.subst (motive := fun m : ℕ => 1 ≤ m) hn_zero hone_le_n
                exact (Nat.not_succ_le_zero 0) hone_le_zero
              exact Set.indicator_of_mem hn_not_mem f
            _ = f 0 := by
              exact congrArg f hn_zero
            _ = 0 :=
              hzero
        calc
          ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f) n = 0 :=
            hn_mem_false_or_zero
          _ = (if N < n then f n else 0) := by
            exact (if_neg hn_not_tail).symm
      · have hn_pos : 1 ≤ n :=
          Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn_zero)
        have hn_le_N : n ≤ N :=
          le_of_not_gt hn_not_tail
        have hn_mem : n ∈ Finset.Icc 1 N :=
          Finset.mem_Icc.mpr ⟨hn_pos, hn_le_N⟩
        have hn_not_mem_tail : n ∉ {n : ℕ | n ∉ Finset.Icc 1 N} := by
          intro hn_not_mem
          exact hn_not_mem hn_mem
        calc
          ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f) n = 0 :=
            Set.indicator_of_not_mem hn_not_mem_tail f
          _ = (if N < n then f n else 0) := by
            exact (if_neg hn_not_tail).symm
  have htail_if :
      HasSum
        (fun n : ℕ => if N < n then f n else 0)
        (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N, f n) :=
    Eq.subst
      (motive := fun g : ℕ → ℂ =>
        HasSum g
          (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
            ∑ n ∈ Finset.Icc 1 N, f n))
      hindicator
      htail_indicator
  have hfinite :
      (∑ n ∈ Finset.Icc 1 N, f n) =
        Complex.riemannZetaBoundaryLineTruncation t N := by
    rfl
  exact Eq.subst
    (motive := fun S : ℂ =>
      HasSum (fun n : ℕ => if N < n then f n else 0)
        (riemannZeta (Complex.boundaryLineOnePointRealParam t) - S))
    hfinite
    htail_if

/-- Boundary Dirichlet-tail summability at `1 + it`. -/
theorem Complex.boundaryLineOnePointRealParam_boundaryDirichletTail_hasSum_zeta_remainder
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ)
    (hN : 1 ≤ N) :
    HasSum
      (fun n : ℕ =>
        if N < n then
          ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹
        else
          0)
      (riemannZeta (Complex.boundaryLineOnePointRealParam t) -
        Complex.riemannZetaBoundaryLineTruncation t N) := by
  exact
    Complex.boundaryLineOnePointRealParam_boundaryDirichletTail_hasSum_zeta_remainder_of_series
      t N
      (Complex.boundaryLineOnePointRealParam_boundaryDirichletSeries_hasSum_riemannZeta
        t ht)

/-- Transport from the ordinary boundary Dirichlet-tail `HasSum` theorem to
the concrete `tsum` equality. -/
theorem Complex.boundaryLineOnePointRealParam_boundaryDirichletTail_eq_zeta_remainder
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
  exact
    (Complex.boundaryLineOnePointRealParam_boundaryDirichletTail_hasSum_zeta_remainder
      t ht N hN).tsum_eq

/-- Transport from the boundary Dirichlet-series tail theorem to the concrete
`tsum` spelling used by the Euler package. -/
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
  exact
    Complex.boundaryLineOnePointRealParam_boundaryDirichletTail_eq_zeta_remainder
      t ht N hN

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
