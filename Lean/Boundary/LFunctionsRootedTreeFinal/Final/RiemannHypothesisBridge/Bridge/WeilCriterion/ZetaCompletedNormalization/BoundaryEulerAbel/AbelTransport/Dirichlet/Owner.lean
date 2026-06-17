import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.AbelTransport.Setup.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Owner

/-!
# Abel transport: Dirichlet series and oscillatory forms

This file owns the theorems transforming the post-cutoff oscillatory tail into
Dirichlet series form, including indicator functions and tail manipulations.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

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

end

end LFunctions
end Boundary
