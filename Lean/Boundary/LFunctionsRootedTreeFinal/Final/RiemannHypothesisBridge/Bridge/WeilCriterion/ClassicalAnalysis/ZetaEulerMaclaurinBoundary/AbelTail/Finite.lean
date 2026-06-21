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

theorem Nat.two_le_seventy_four_for_abelTail : (2 : ℕ) ≤ 74 :=
  Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 72))

theorem Nat.thirty_eight_le_seventy_four_for_abelTail : (38 : ℕ) ≤ 74 :=
  Nat.le.intro (show 38 + 36 = 74 from rfl)

theorem Nat.seventy_two_le_seventy_four_for_abelTail : (72 : ℕ) ≤ 74 :=
  Nat.le.intro (show 72 + 2 = 74 from rfl)

theorem Real.thirty_six_add_thirty_six_eq_seventy_two_for_abelTail :
    (36 : ℝ) + 36 = 72 := by
  have hnat : (36 : ℕ) + 36 = 72 :=
    rfl
  have hcast :
      (((36 : ℕ) + 36 : ℕ) : ℝ) = (72 : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) hnat
  exact Eq.trans (Nat.cast_add 36 36).symm hcast

theorem Real.two_add_thirty_six_eq_thirty_eight_for_abelTail :
    (2 : ℝ) + 36 = 38 := by
  have hnat : (2 : ℕ) + 36 = 38 :=
    rfl
  have hcast :
      (((2 : ℕ) + 36 : ℕ) : ℝ) = (38 : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) hnat
  exact Eq.trans (Nat.cast_add 2 36).symm hcast

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
        -((t : ℂ) * Complex.I) = -(t : ℂ) * Complex.I :=
      (neg_mul (t : ℂ) Complex.I).symm
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
          (∀ M : ℕ,
            ⌊2 + ‖t‖⌋₊ ≤ M →
              ‖∑ k ∈ Finset.Ioc
                  ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊
                  ⌊((M : ℕ) : ℝ)⌋₊,
                  ((k : ℂ)⁻¹ : ℂ) *
                    ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t) →
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
      (fun t ht hfinite N hN M hNM =>
        by
          let C : ℕ := ⌊2 + ‖t‖⌋₊
          let f : ℕ → ℂ :=
            fun n : ℕ =>
              ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
          have hconstant :
              boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t ≤
                36 * Real.log (2 + ‖t‖) :=
            boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant_le_log t ht
          have htwo_log_le :
              2 * Real.log (2 + ‖t‖) ≤ 74 * Real.log (2 + ‖t‖) := by
            have hlog_nonneg : 0 ≤ Real.log (2 + ‖t‖) := by
              exact le_trans zero_le_one (one_le_log_two_add_norm_of_one_le_norm ht)
            have htwo_le : (2 : ℝ) ≤ 74 := by
              exact Nat.cast_le.mpr Nat.two_le_seventy_four_for_abelTail
            exact mul_le_mul_of_nonneg_right htwo_le hlog_nonneg
          have hseventy_two_log_le :
              72 * Real.log (2 + ‖t‖) ≤ 74 * Real.log (2 + ‖t‖) := by
            have hlog_nonneg : 0 ≤ Real.log (2 + ‖t‖) := by
              exact le_trans zero_le_one (one_le_log_two_add_norm_of_one_le_norm ht)
            have hle : (72 : ℝ) ≤ 74 := by
              exact Nat.cast_le.mpr Nat.seventy_two_le_seventy_four_for_abelTail
            exact mul_le_mul_of_nonneg_right hle hlog_nonneg
          have hthirty_eight_log_le :
              38 * Real.log (2 + ‖t‖) ≤ 74 * Real.log (2 + ‖t‖) := by
            have hlog_nonneg : 0 ≤ Real.log (2 + ‖t‖) := by
              exact le_trans zero_le_one (one_le_log_two_add_norm_of_one_le_norm ht)
            have hle : (38 : ℝ) ≤ 74 := by
              exact Nat.cast_le.mpr Nat.thirty_eight_le_seventy_four_for_abelTail
            exact mul_le_mul_of_nonneg_right hle hlog_nonneg
          match Decidable.em (M ≤ C) with
          | Or.inl hMcut =>
              have hpre :
                  ‖∑ n ∈ Finset.Ioc N M, f n‖ ≤
                    2 * Real.log (2 + ‖t‖) :=
                boundaryLineOnePointRealParam_logarithmicPhase_preCutoff_finiteTail_norm_le
                  t ht hN hMcut
              exact le_trans hpre htwo_log_le
          | Or.inr hMcut =>
              have hC_le_M : C ≤ M :=
                Nat.le_of_not_ge hMcut
              match Decidable.em (C ≤ N) with
              | Or.inl hC_le_N =>
                  have hsplit :
                      (∑ n ∈ Finset.Ioc N M, f n) =
                        (∑ n ∈ Finset.Ioc C M, f n) -
                          ∑ n ∈ Finset.Ioc C N, f n :=
                    finite_sum_Ioc_eq_sub_left hC_le_N hNM f
                  have hM_floor : ⌊((M : ℕ) : ℝ)⌋₊ = M :=
                    Nat.floor_natCast M
                  have hN_floor : ⌊((N : ℕ) : ℝ)⌋₊ = N :=
                    Nat.floor_natCast N
                  have hC_floor : ⌊(((C : ℕ) : ℝ))⌋₊ = C :=
                    Nat.floor_natCast C
                  have hM_tail :
                      ‖∑ n ∈ Finset.Ioc C M, f n‖ ≤
                        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
                    have hraw := hfinite M hC_le_M
                    exact Eq.subst
                      (motive := fun s : Finset ℕ =>
                        ‖∑ n ∈ s, f n‖ ≤
                          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
                      (congrArg₂ Finset.Ioc hC_floor hM_floor)
                      hraw
                  have hN_tail :
                      ‖∑ n ∈ Finset.Ioc C N, f n‖ ≤
                        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
                    have hraw := hfinite N hC_le_N
                    exact Eq.subst
                      (motive := fun s : Finset ℕ =>
                        ‖∑ n ∈ s, f n‖ ≤
                          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
                      (congrArg₂ Finset.Ioc hC_floor hN_floor)
                      hraw
                  have htriangle :
                      ‖(∑ n ∈ Finset.Ioc C M, f n) -
                          ∑ n ∈ Finset.Ioc C N, f n‖ ≤
                        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
                          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t :=
                    le_trans
                      (norm_sub_le (∑ n ∈ Finset.Ioc C M, f n) (∑ n ∈ Finset.Ioc C N, f n))
                      (add_le_add hM_tail hN_tail)
                  have htwo_constants :
                      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
                          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t ≤
                        72 * Real.log (2 + ‖t‖) := by
                    have hadd :
                        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
                            boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t ≤
                          36 * Real.log (2 + ‖t‖) +
                            36 * Real.log (2 + ‖t‖) :=
                      add_le_add hconstant hconstant
                    have hsum :
                        36 * Real.log (2 + ‖t‖) +
                            36 * Real.log (2 + ‖t‖) =
                          72 * Real.log (2 + ‖t‖) := by
                      calc
                        36 * Real.log (2 + ‖t‖) +
                            36 * Real.log (2 + ‖t‖) =
                          (36 + 36) * Real.log (2 + ‖t‖) :=
                            (add_mul 36 36 (Real.log (2 + ‖t‖))).symm
                        _ = 72 * Real.log (2 + ‖t‖) := by
                          exact congrArg
                            (fun c : ℝ => c * Real.log (2 + ‖t‖))
                            Real.thirty_six_add_thirty_six_eq_seventy_two_for_abelTail
                    exact Eq.subst
                      (motive := fun r : ℝ =>
                        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
                            boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t ≤ r)
                      hsum
                      hadd
                  exact Eq.subst
                    (motive := fun z : ℂ => ‖z‖ ≤ 74 * Real.log (2 + ‖t‖))
                    hsplit.symm
                    (le_trans htriangle (le_trans htwo_constants hseventy_two_log_le))
              | Or.inr hC_le_N =>
                  have hN_le_C : N ≤ C :=
                    Nat.le_of_not_ge hC_le_N
                  have hsplit_union :
                      Finset.Ioc N C ∪ Finset.Ioc C M = Finset.Ioc N M :=
                    Finset.Ioc_union_Ioc_eq_Ioc hN_le_C hC_le_M
                  have hdisjoint :
                      Disjoint (Finset.Ioc N C) (Finset.Ioc C M) := by
                    exact Finset.disjoint_left.mpr
                      (fun n hn_left hn_right =>
                        let hn_le_C : n ≤ C := (Finset.mem_Ioc.mp hn_left).2
                        let hC_lt_n : C < n := (Finset.mem_Ioc.mp hn_right).1
                        not_le_of_gt hC_lt_n hn_le_C)
                  have hsplit_sum :
                      (∑ n ∈ Finset.Ioc N M, f n) =
                        (∑ n ∈ Finset.Ioc N C, f n) +
                          ∑ n ∈ Finset.Ioc C M, f n := by
                    calc
                      (∑ n ∈ Finset.Ioc N M, f n) =
                          ∑ n ∈ Finset.Ioc N C ∪ Finset.Ioc C M, f n := by
                        exact congrArg (fun s : Finset ℕ => ∑ n ∈ s, f n) hsplit_union.symm
                      _ = (∑ n ∈ Finset.Ioc N C, f n) +
                          ∑ n ∈ Finset.Ioc C M, f n :=
                        Finset.sum_union hdisjoint
                  have hpre :
                      ‖∑ n ∈ Finset.Ioc N C, f n‖ ≤
                        2 * Real.log (2 + ‖t‖) :=
                    boundaryLineOnePointRealParam_logarithmicPhase_preCutoff_finiteTail_norm_le
                      t ht hN (le_rfl : C ≤ C)
                  have hM_floor : ⌊((M : ℕ) : ℝ)⌋₊ = M :=
                    Nat.floor_natCast M
                  have hC_floor : ⌊(((C : ℕ) : ℝ))⌋₊ = C :=
                    Nat.floor_natCast C
                  have hcut :
                      ‖∑ n ∈ Finset.Ioc C M, f n‖ ≤
                        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
                    have hraw := hfinite M hC_le_M
                    exact Eq.subst
                      (motive := fun s : Finset ℕ =>
                        ‖∑ n ∈ s, f n‖ ≤
                          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
                      (congrArg₂ Finset.Ioc hC_floor hM_floor)
                      hraw
                  have htriangle :
                      ‖(∑ n ∈ Finset.Ioc N C, f n) +
                          ∑ n ∈ Finset.Ioc C M, f n‖ ≤
                        2 * Real.log (2 + ‖t‖) +
                          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t :=
                    le_trans
                      (norm_add_le (∑ n ∈ Finset.Ioc N C, f n) (∑ n ∈ Finset.Ioc C M, f n))
                      (add_le_add hpre hcut)
                  have hsum_bound :
                      2 * Real.log (2 + ‖t‖) +
                          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t ≤
                        38 * Real.log (2 + ‖t‖) := by
                    have hraw :
                        2 * Real.log (2 + ‖t‖) +
                            boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t ≤
                          2 * Real.log (2 + ‖t‖) +
                            36 * Real.log (2 + ‖t‖) :=
                      add_le_add_left hconstant (2 * Real.log (2 + ‖t‖))
                    have hsum :
                        2 * Real.log (2 + ‖t‖) +
                            36 * Real.log (2 + ‖t‖) =
                          38 * Real.log (2 + ‖t‖) := by
                      calc
                        2 * Real.log (2 + ‖t‖) +
                            36 * Real.log (2 + ‖t‖) =
                          (2 + 36) * Real.log (2 + ‖t‖) :=
                            (add_mul 2 36 (Real.log (2 + ‖t‖))).symm
                        _ = 38 * Real.log (2 + ‖t‖) := by
                          exact congrArg
                            (fun c : ℝ => c * Real.log (2 + ‖t‖))
                            Real.two_add_thirty_six_eq_thirty_eight_for_abelTail
                    exact Eq.subst
                      (motive := fun r : ℝ =>
                        2 * Real.log (2 + ‖t‖) +
                            boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t ≤ r)
                      hsum
                      hraw
                  exact Eq.subst
                    (motive := fun z : ℂ => ‖z‖ ≤ 74 * Real.log (2 + ‖t‖))
                    hsplit_sum.symm
                    (le_trans htriangle (le_trans hsum_bound hthirty_eight_log_le))))

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
          (∀ M : ℕ,
            ⌊2 + ‖t‖⌋₊ ≤ M →
              ‖∑ k ∈ Finset.Ioc
                  ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊
                  ⌊((M : ℕ) : ℝ)⌋₊,
                  ((k : ℂ)⁻¹ : ℂ) *
                    ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t) →
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
          (∀ M : ℕ,
            ⌊2 + ‖t‖⌋₊ ≤ M →
              ‖∑ k ∈ Finset.Ioc
                  ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊
                  ⌊((M : ℕ) : ℝ)⌋₊,
                  ((k : ℂ)⁻¹ : ℂ) *
                    ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t) →
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
          (∀ M : ℕ,
            ⌊2 + ‖t‖⌋₊ ≤ M →
              ‖∑ k ∈ Finset.Ioc
                  ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊
                  ⌊((M : ℕ) : ℝ)⌋₊,
                  ((k : ℂ)⁻¹ : ℂ) *
                    ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t) →
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
          (∀ M : ℕ,
            ⌊2 + ‖t‖⌋₊ ≤ M →
              ‖∑ k ∈ Finset.Ioc
                  ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊
                  ⌊((M : ℕ) : ℝ)⌋₊,
                  ((k : ℂ)⁻¹ : ℂ) *
                    ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t) →
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
            (fun t ht hfinite M hM =>
              let hcutoff_one : 1 ≤ ⌊2 + ‖t‖⌋₊ := by
                have htwo_le : (2 : ℝ) ≤ 2 + ‖t‖ :=
                  le_add_of_nonneg_right (norm_nonneg t)
                have hnonneg : (0 : ℝ) ≤ 2 + ‖t‖ :=
                  le_trans (show (0 : ℝ) ≤ 2 from Nat.cast_nonneg 2) htwo_le
                have hfloor_two : 2 ≤ ⌊2 + ‖t‖⌋₊ :=
                  (Nat.le_floor_iff hnonneg).mpr htwo_le
                exact le_trans Nat.one_le_two_for_abelTail hfloor_two
              hbound t ht hfinite ⌊2 + ‖t‖⌋₊ hcutoff_one M hM))

/-- Finite Abel-summation estimate obtained from the first-derivative
logarithmic-phase bound. -/
theorem Complex.boundaryLineOnePointRealParam_finiteAbelTail_bound_of_firstDerivative :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          (∀ M : ℕ,
            ⌊2 + ‖t‖⌋₊ ≤ M →
              ‖∑ k ∈ Finset.Ioc
                  ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊
                  ⌊((M : ℕ) : ℝ)⌋₊,
                  ((k : ℂ)⁻¹ : ℂ) *
                    ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t) →
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
          (∀ M : ℕ,
            ⌊2 + ‖t‖⌋₊ ≤ M →
              ‖∑ k ∈ Finset.Ioc
                  ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊
                  ⌊((M : ℕ) : ℝ)⌋₊,
                  ((k : ℂ)⁻¹ : ℂ) *
                    ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t) →
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
