import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.AbelTail

/-!
# Boundary growth of raw zeta

This file owns the logarithmic growth estimate for `ζ(1 + it)` obtained from
the Abel/Euler-Maclaurin tail and finite truncation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- On the logarithmic boundary range, the canonical logarithm is at least one. -/
theorem Complex.one_le_log_two_add_norm_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    (1 : ℝ) ≤ Real.log (2 + ‖t‖) := by
  have hthree_le : (3 : ℝ) ≤ 2 + ‖t‖ := by
    calc
      (3 : ℝ) = 2 + 1 := rfl
      _ ≤ 2 + ‖t‖ :=
        add_le_add_left ht 2
  have hexp_one_le_three : Real.exp (1 : ℝ) ≤ 3 := by
    have hexp_le_d9 : Real.exp (1 : ℝ) ≤ 2.7182818286 :=
      le_of_lt Real.exp_one_lt_d9
    have hd9_eq :
        (2.7182818286 : ℝ) =
          (27182818286 : ℝ) / 10000000000 := rfl
    have hden_pos : (0 : ℝ) < 10000000000 := by
      exact_mod_cast (show (0 : ℕ) < 10000000000 by decide)
    have hnum_le :
        (27182818286 : ℝ) ≤ 3 * (10000000000 : ℝ) := by
      exact_mod_cast
        (show (27182818286 : ℕ) ≤ 3 * 10000000000 by decide)
    have hd9_le_three : (2.7182818286 : ℝ) ≤ 3 := by
      have hfrac :
          (27182818286 : ℝ) / 10000000000 ≤ 3 :=
        (div_le_iff₀ hden_pos).mpr hnum_le
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ 3)
        hd9_eq.symm
        hfrac
    exact le_trans hexp_le_d9 hd9_le_three
  have hexp_one_le : Real.exp (1 : ℝ) ≤ 2 + ‖t‖ :=
    le_trans hexp_one_le_three hthree_le
  exact Real.le_log_of_exp_le
    (lt_of_lt_of_le Real.exp_pos hexp_one_le)
    hexp_one_le

/-- The first boundary-line Dirichlet truncation is the single term `1`. -/
theorem Complex.riemannZetaBoundaryLineTruncation_one
    (t : ℝ) :
    Complex.riemannZetaBoundaryLineTruncation t 1 = 1 := by
  have hterm :
      ((1 : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹ = 1 := by
    calc
      ((1 : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹ =
          (1 : ℂ)⁻¹ := by
        exact congrArg Inv.inv (Complex.one_cpow (Complex.boundaryLineOnePointRealParam t))
      _ = 1 := by
        exact inv_one
  calc
    Complex.riemannZetaBoundaryLineTruncation t 1 =
        ∑ n ∈ Finset.Icc 1 1,
          ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹ := by
      rfl
    _ = ((1 : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹ := by
      exact Finset.sum_Icc_singleton
        (fun n : ℕ => ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹)
        1
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
          ‖riemannZeta (Complex.boundaryLineOnePointRealParam t)‖ ≤
            A * Real.log (2 + ‖t‖) := by
  rcases Complex.riemannZeta_boundaryLine_truncated_dirichlet_remainder_bound with
    ⟨A, hA_pos, hremainder⟩
  refine ⟨A + 1, add_pos hA_pos zero_lt_one, ?_⟩
  intro t ht
  let L : ℝ := Real.log (2 + ‖t‖)
  let S : ℂ := Complex.riemannZetaBoundaryLineTruncation t 1
  have hsplit :
      riemannZeta (Complex.boundaryLineOnePointRealParam t) =
        (riemannZeta (Complex.boundaryLineOnePointRealParam t) - S) + S := by
    exact (sub_add_cancel (riemannZeta (Complex.boundaryLineOnePointRealParam t)) S).symm
  have htriangle :
      ‖riemannZeta (Complex.boundaryLineOnePointRealParam t)‖ ≤
        ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) - S‖ + ‖S‖ := by
    exact Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) - S‖ + ‖S‖)
      hsplit.symm
      (norm_add_le (riemannZeta (Complex.boundaryLineOnePointRealParam t) - S) S)
  have hrem :
      ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) - S‖ ≤
        A * L := by
    exact hremainder t ht 1 (Nat.le_refl 1)
  have hS :
      ‖S‖ ≤ L := by
    have hnorm : ‖S‖ = 1 :=
      Complex.riemannZetaBoundaryLineTruncation_one_norm t
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ L)
      hnorm.symm
      (Complex.one_le_log_two_add_norm_of_one_le_norm ht)
  have hsum :
      ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) - S‖ + ‖S‖ ≤
        A * L + L :=
    add_le_add hrem hS
  have htarget : A * L + L = (A + 1) * L := by
    calc
      A * L + L = A * L + 1 * L := by
        exact congrArg (fun x : ℝ => A * L + x) (one_mul L).symm
      _ = (A + 1) * L := by
        exact (add_mul A 1 L).symm
  exact le_trans htriangle
    (Eq.subst
      (motive := fun x : ℝ =>
        ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) - S‖ + ‖S‖ ≤ x)
      htarget
      hsum)

/-- Boundary-line logarithmic growth bound for zeta at `1 + it`. -/
theorem Complex.riemannZeta_boundaryLine_log_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ‖riemannZeta (Complex.boundaryLineOnePointRealParam t)‖ ≤
            A * Real.log (2 + ‖t‖) := by
  exact Complex.riemannZeta_boundaryLine_log_bound_of_truncated_remainder

end

end LFunctions
end Boundary
