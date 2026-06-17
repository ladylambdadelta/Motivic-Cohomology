import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.AbelTail.Abstract

/-!
# Dirichlet limits for Abel boundary tails

This file owns the term conversion and one-sided Dirichlet-series limit lemmas
used by the Abel boundary-tail estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

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
    calc
      (σ : ℂ) = ((1 + (σ - 1) : ℝ) : ℂ) := by
        exact congrArg (fun x : ℝ => (x : ℂ))
          (Real.one_add_sub_one_eq_for_abelTail σ).symm
      _ = (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) := by
        exact Complex.ofReal_add 1 (σ - 1)
  have hneg_sigma_decomp :
      -((σ : ℂ) + (t : ℂ) * Complex.I) =
        (-1 : ℂ) + (-(t : ℂ) * Complex.I) +
          ((-(σ - 1 : ℝ) : ℝ) : ℂ) := by
    let d : ℂ := ((σ - 1 : ℝ) : ℂ)
    let T : ℂ := (t : ℂ) * Complex.I
    have hT_neg : -T = -(t : ℂ) * Complex.I := by
      exact neg_mul (t : ℂ) Complex.I
    have hd_neg : -d = ((-(σ - 1 : ℝ) : ℝ) : ℂ) := by
      exact (Complex.ofReal_neg (σ - 1)).symm
    calc
      -((σ : ℂ) + (t : ℂ) * Complex.I) =
          -(((1 : ℂ) + d) + T) := by
        exact congrArg (fun z : ℂ => -(z + T)) hsigma_decomp
      _ = (-1 : ℂ) + -T + -d :=
        Complex.neg_add_add_comm_for_abelTail (1 : ℂ) d T
      _ = (-1 : ℂ) + (-(t : ℂ) * Complex.I) + -d := by
        exact congrArg (fun z : ℂ => (-1 : ℂ) + z + -d) hT_neg
      _ = (-1 : ℂ) + (-(t : ℂ) * Complex.I) +
          ((-(σ - 1 : ℝ) : ℝ) : ℂ) := by
        exact congrArg (fun z : ℂ => (-1 : ℂ) + (-(t : ℂ) * Complex.I) + z) hd_neg
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
    exact Complex.cpow_neg_one (n : ℂ)
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
      exact by
        congr
        · exact hcpow_neg_one
        · exact hreal_weight

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
  exact tsum_congr
    (fun n =>
      match Classical.em (N < n) with
      | Or.inl hn_tail =>
          have hn_pos : 0 < n :=
            Nat.lt_of_lt_of_le Nat.zero_lt_one (le_of_lt (lt_of_le_of_lt hN hn_tail))
          if_pos hn_tail ▸
            if_pos hn_tail ▸
              Complex.boundaryLineOnePointRealParam_abelDampedDirichletTerm_eq_weighted
                t σ hn_pos
      | Or.inr hn_tail =>
          if_neg hn_tail ▸ if_neg hn_tail ▸ rfl)

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
              if_neg hn_tail ▸ if_neg (Set.mem_compl_iff.mp.mt hn_mem)
          | Or.inr hn_zero =>
              if_neg hn_tail ▸
                if_pos
                  (by
                    subst hn_zero
                    exact hzero_not_mem) ▸
                  hf_zero.symm
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
    exact hσ
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
    rfl
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

end

end LFunctions
end Boundary
