import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.AbelTail

/-!
# Boundary growth of raw zeta

This file owns the logarithmic growth estimate for `ζ(1 + it)` obtained from
the Abel/Euler-Maclaurin tail and finite truncation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- On the logarithmic boundary range, the canonical logarithm controls one
after multiplying by the fixed positive constant `(log (2 + 1))⁻¹`. -/
theorem Complex.one_le_inv_log_three_mul_log_two_add_norm_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    (1 : ℝ) ≤ (Real.log (2 + 1))⁻¹ * Real.log (2 + ‖t‖) := by
  have hbase_le : (2 : ℝ) + 1 ≤ 2 + ‖t‖ :=
    add_le_add_left ht 2
  have hbase_pos : (0 : ℝ) < 2 + 1 :=
    add_pos zero_lt_two zero_lt_one
  have hone_lt_base : (1 : ℝ) < 2 + 1 :=
    lt_add_of_pos_left 1 zero_lt_two
  have hlog_base_pos : 0 < Real.log (2 + 1) :=
    Real.log_pos hone_lt_base
  have hlog_le :
      Real.log (2 + 1) ≤ Real.log (2 + ‖t‖) :=
    Real.log_le_log hbase_pos hbase_le
  have hinv_pos : 0 < (Real.log (2 + 1))⁻¹ :=
    inv_pos.mpr hlog_base_pos
  have hmul_le :
      (Real.log (2 + 1))⁻¹ * Real.log (2 + 1) ≤
        (Real.log (2 + 1))⁻¹ * Real.log (2 + ‖t‖) :=
    mul_le_mul_of_nonneg_left hlog_le (le_of_lt hinv_pos)
  have hone_eq :
      (1 : ℝ) = (Real.log (2 + 1))⁻¹ * Real.log (2 + 1) := by
    exact (inv_mul_cancel₀ (ne_of_gt hlog_base_pos)).symm
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ (Real.log (2 + 1))⁻¹ * Real.log (2 + ‖t‖))
    hone_eq.symm
    hmul_le

/-- The first boundary-line Dirichlet truncation is the single term `1`. -/
theorem Complex.riemannZetaBoundaryLineTruncation_one
    (t : ℝ) :
    Complex.riemannZetaBoundaryLineTruncation t 1 = 1 := by
  have hterm :
      ((((1 : ℕ) : ℂ)⁻¹ : ℂ) *
          (((1 : ℕ) : ℂ) ^ (-(t : ℂ) * Complex.I))) = 1 := by
    calc
      ((((1 : ℕ) : ℂ)⁻¹ : ℂ) *
          (((1 : ℕ) : ℂ) ^ (-(t : ℂ) * Complex.I))) =
          ((1 : ℂ)⁻¹ : ℂ) * ((1 : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
        exact congrArg
          (fun x : ℂ => (x⁻¹ : ℂ) * (x ^ (-(t : ℂ) * Complex.I)))
          (Nat.cast_one : ((1 : ℕ) : ℂ) = 1)
      _ =
          (1 : ℂ) * ((1 : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
        exact congrArg (fun x : ℂ => x * ((1 : ℂ) ^ (-(t : ℂ) * Complex.I))) inv_one
      _ = (1 : ℂ) * 1 := by
        exact congrArg (fun x : ℂ => (1 : ℂ) * x)
          (Complex.one_cpow (-(t : ℂ) * Complex.I))
      _ = 1 := by
        exact one_mul 1
  have htrunc :
      Complex.riemannZetaBoundaryLineTruncation t 1 =
        ∑ n ∈ Finset.Icc (1 : ℕ) 1,
          ((n : ℂ)⁻¹ : ℂ) *
            ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    Complex.riemannZetaBoundaryLineTruncation_eq_weighted_logarithmicPhase_sum t 1
  have hIcc :
      Finset.Icc (1 : ℕ) 1 = ({1} : Finset ℕ) :=
    Finset.Icc_self 1
  have hsum_singleton :
      (∑ n ∈ ({1} : Finset ℕ),
          ((n : ℂ)⁻¹ : ℂ) *
            ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        ((((1 : ℕ) : ℂ)⁻¹ : ℂ) *
          (((1 : ℕ) : ℂ) ^ (-(t : ℂ) * Complex.I))) :=
    Finset.sum_singleton
      (fun n : ℕ =>
        ((n : ℂ)⁻¹ : ℂ) *
          ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))
      1
  calc
    Complex.riemannZetaBoundaryLineTruncation t 1 =
        ∑ n ∈ Finset.Icc (1 : ℕ) 1,
          ((n : ℂ)⁻¹ : ℂ) *
            ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
      htrunc
    _ = ∑ n ∈ ({1} : Finset ℕ),
          ((n : ℂ)⁻¹ : ℂ) *
            ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
      exact congrArg
        (fun s : Finset ℕ =>
          ∑ n ∈ s,
            ((n : ℂ)⁻¹ : ℂ) *
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))
        hIcc
    _ = ((((1 : ℕ) : ℂ)⁻¹ : ℂ) *
          (((1 : ℕ) : ℂ) ^ (-(t : ℂ) * Complex.I))) :=
      hsum_singleton
    _ = 1 :=
      hterm

/-- The first boundary-line Dirichlet truncation has norm one. -/
theorem Complex.riemannZetaBoundaryLineTruncation_one_norm
    (t : ℝ) :
    ‖Complex.riemannZetaBoundaryLineTruncation t 1‖ = 1 := by
  calc
    ‖Complex.riemannZetaBoundaryLineTruncation t 1‖ = ‖(1 : ℂ)‖ := by
      exact congrArg norm (Complex.riemannZetaBoundaryLineTruncation_one t)
    _ = 1 :=
      norm_one

/-- The guarded truncation comparison and the finite first term give the
boundary-line logarithmic growth bound for zeta. -/
theorem Complex.riemannZeta_boundaryLine_log_bound_of_truncated_remainder :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          Complex.boundaryLineOnePointRealParam_cutoffPhasePartialSumBound t →
          ‖riemannZeta (Complex.boundaryLineOnePointRealParam t)‖ ≤
            A * Real.log (2 + ‖t‖) := by
  exact
    match Complex.riemannZeta_boundaryLine_truncated_dirichlet_remainder_bound with
    | ⟨A, hA_pos, hremainder⟩ =>
        Exists.intro (A + (Real.log (2 + 1))⁻¹)
          (And.intro
            (add_pos hA_pos
              (inv_pos.mpr (Real.log_pos (lt_add_of_pos_left 1 zero_lt_two))))
            (fun t ht hphase => by
              let L : ℝ := Real.log (2 + ‖t‖)
              let S : ℂ := Complex.riemannZetaBoundaryLineTruncation t 1
              have hsplit :
                  riemannZeta (Complex.boundaryLineOnePointRealParam t) =
                    (riemannZeta (Complex.boundaryLineOnePointRealParam t) - S) + S :=
                (sub_add_cancel (riemannZeta (Complex.boundaryLineOnePointRealParam t)) S).symm
              have htriangle :
                  ‖riemannZeta (Complex.boundaryLineOnePointRealParam t)‖ ≤
                    ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) - S‖ + ‖S‖ :=
                Eq.subst
                  (motive := fun z : ℂ =>
                    ‖z‖ ≤
                      ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) - S‖ + ‖S‖)
                  hsplit.symm
                  (norm_add_le (riemannZeta (Complex.boundaryLineOnePointRealParam t) - S) S)
              have hrem :
                  ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) - S‖ ≤
                    A * L :=
                hremainder t ht hphase 1 (Nat.le_refl 1)
              have hS :
                  ‖S‖ ≤ (Real.log (2 + 1))⁻¹ * L := by
                have hnorm : ‖S‖ = 1 :=
                  Complex.riemannZetaBoundaryLineTruncation_one_norm t
                exact Eq.subst
                  (motive := fun x : ℝ => x ≤ (Real.log (2 + 1))⁻¹ * L)
                  hnorm.symm
                  (Complex.one_le_inv_log_three_mul_log_two_add_norm_of_one_le_norm ht)
              have hsum :
                  ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) - S‖ + ‖S‖ ≤
                    A * L + (Real.log (2 + 1))⁻¹ * L :=
                add_le_add hrem hS
              have htarget :
                  A * L + (Real.log (2 + 1))⁻¹ * L =
                    (A + (Real.log (2 + 1))⁻¹) * L :=
                (add_mul A (Real.log (2 + 1))⁻¹ L).symm
              exact le_trans htriangle
                (Eq.subst
                  (motive := fun x : ℝ =>
                    ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) - S‖ + ‖S‖ ≤ x)
                  htarget
                  hsum)))

/-- Boundary-line logarithmic growth bound for zeta at `1 + it`. -/
theorem Complex.riemannZeta_boundaryLine_log_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          Complex.boundaryLineOnePointRealParam_cutoffPhasePartialSumBound t →
          ‖riemannZeta (Complex.boundaryLineOnePointRealParam t)‖ ≤
            A * Real.log (2 + ‖t‖) := by
  exact Complex.riemannZeta_boundaryLine_log_bound_of_truncated_remainder

end

end LFunctions
end Boundary
