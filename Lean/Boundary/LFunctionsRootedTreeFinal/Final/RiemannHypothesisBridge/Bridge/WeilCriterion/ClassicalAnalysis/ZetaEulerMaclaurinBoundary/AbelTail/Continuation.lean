import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.AbelTail.DirichletLimit

/-!
# Abel continuation for boundary tails

This file owns the public one-sided Abel-continuation lemmas that bridge the
Dirichlet half-plane series to the boundary-line zeta remainder.
-/

namespace Boundary
namespace LFunctions

noncomputable section

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
      calc
        t = (Complex.boundaryLineOnePointRealParam t).im := by
          exact (Complex.boundaryLineOnePointRealParam_im t).symm
        _ = (1 : ℂ).im := him
        _ = 0 := rfl
    have hle_zero : (1 : ℝ) ≤ 0 := by
      subst ht_zero
      exact ht
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
      exact hσ
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
    exact hσ
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
    exact
      match Classical.em (N < n) with
      | Or.inl hn_tail =>
          have hn_not_mem : n ∉ S := by
            intro hn_mem
            have hn_le_N : n ≤ N := (Finset.mem_Icc.mp hn_mem).2
            exact (not_le_of_gt hn_tail) hn_le_N
          if_pos hn_tail ▸ if_pos hn_not_mem ▸ rfl
      | Or.inr hn_tail =>
          have hn_mem_or_zero : n ∈ S ∨ n = 0 := by
            have hn_le_N : n ≤ N := le_of_not_gt hn_tail
            cases n with
            | zero =>
                exact Or.inr rfl
            | succ k =>
                have hn_one_le : 1 ≤ Nat.succ k := Nat.succ_le_succ (Nat.zero_le k)
                exact Or.inl (Finset.mem_Icc.mpr ⟨hn_one_le, hn_le_N⟩)
          match hn_mem_or_zero with
          | Or.inl hn_mem =>
              if_neg hn_tail ▸ if_neg (Set.mem_compl_iff.mp.mt hn_mem) ▸ rfl
          | Or.inr hn_zero =>
              Eq.subst
                (motive := fun q : ℕ =>
                  (if N < q then f q else 0) =
                    if q ∈ (S : Set ℕ)ᶜ then f q else 0)
                hn_zero.symm
                (if_neg (Nat.not_lt_zero N) ▸ if_pos hzero_not_mem ▸ hf_zero.symm)
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
    rfl
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
  exact tendsto_finset_sum (Finset.Icc 1 N)
    (fun n hn_mem =>
      let hn_one_le : 1 ≤ n := (Finset.mem_Icc.mp hn_mem).1
      let hn_pos : 0 < n := Nat.lt_of_succ_le hn_one_le
      let hn_complex_ne : (n : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn_pos)
      let hpow_ne :
          (n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t) ≠ 0 :=
        Complex.cpow_def_of_ne_zero hn_complex_ne
      ((Complex.continuousAt_const_cpow hn_complex_ne).tendsto.comp hpath).inv₀
        hpow_ne)

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

end

end LFunctions
end Boundary
