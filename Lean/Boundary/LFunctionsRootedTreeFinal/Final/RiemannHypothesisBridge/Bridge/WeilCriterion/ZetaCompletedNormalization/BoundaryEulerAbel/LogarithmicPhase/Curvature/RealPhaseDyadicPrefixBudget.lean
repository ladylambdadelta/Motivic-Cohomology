import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.DyadicBlockBudgets
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseDyadicCurvature

/-!
# Curvature budget for a dyadically decomposed logarithmic prefix

The endpoint term is summed geometrically at its actual dyadic size.  Only the
stationary square-root term is multiplied by the number of blocks.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

/-- The concrete sum on a canonical dyadic finset is the inclusive block sum
consumed by the curvature theorem. -/
theorem Complex.logarithmicPhase_dyadicBlock_sum_eq_Icc
    (t : ℝ)
    {N j : ℕ}
    (hnonempty :
      Nat.dyadicBlockLeft j <
        min (N + 1) (Nat.dyadicBlockRightExclusive j)) :
    (∑ n ∈ Nat.dyadicBlock N j,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) =
      ∑ n ∈ Finset.Icc
          (Nat.dyadicBlockLeft j) (Nat.dyadicBlockUpper N j),
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  exact congrArg
    (fun block : Finset ℕ =>
      ∑ n ∈ block, ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))
    (Nat.dyadicBlock_eq_Icc hnonempty)

/-- The existing dyadic curvature theorem bounds the sum over the canonical
dyadic finset itself. -/
theorem Complex.logarithmicPhase_dyadicBlockFinset_norm_le_unconditional
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {N j : ℕ}
    (hnonempty :
      Nat.dyadicBlockLeft j <
        min (N + 1) (Nat.dyadicBlockRightExclusive j)) :
    ‖∑ n ∈ Nat.dyadicBlock N j,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 *
        ((((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ) / ‖t‖) +
          Real.sqrt (1 + ‖t‖)) := by
  have hIcc :=
    Complex.logarithmicPhase_dyadicBlock_norm_le_unconditional
      t ht hnonempty
  have hsum :=
    Complex.logarithmicPhase_dyadicBlock_sum_eq_Icc t hnonempty
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤
        80 *
          ((((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ) / ‖t‖) +
            Real.sqrt (1 + ‖t‖)))
    hsum.symm
    hIcc

/-- Exact separation of endpoint and stationary terms in a finite dyadic
budget. -/
theorem Finset.sum_dyadic_curvature_budget_eq
    (s : Finset ℕ)
    (U : ℕ → ℕ)
    (T S : ℝ) :
    (∑ j ∈ s, 80 * (((U j : ℕ) : ℝ) / T + S)) =
      80 *
        (((∑ j ∈ s, ((U j : ℕ) : ℝ)) / T) +
          (s.card : ℝ) * S) := by
  have hfactor :
      (∑ j ∈ s, 80 * (((U j : ℕ) : ℝ) / T + S)) =
        80 * (∑ j ∈ s, (((U j : ℕ) : ℝ) / T + S)) :=
    (Finset.mul_sum s
      (fun j : ℕ => (((U j : ℕ) : ℝ) / T + S)) 80).symm
  have hsplit :
      (∑ j ∈ s, (((U j : ℕ) : ℝ) / T + S)) =
        (∑ j ∈ s, ((U j : ℕ) : ℝ) / T) +
          ∑ _j ∈ s, S :=
    Finset.sum_add_distrib
  have hdivision :
      (∑ j ∈ s, ((U j : ℕ) : ℝ) / T) =
        (∑ j ∈ s, ((U j : ℕ) : ℝ)) / T :=
    (Finset.sum_div s (fun j : ℕ => ((U j : ℕ) : ℝ)) T).symm
  have hconstant :
      (∑ _j ∈ s, S) = (s.card : ℝ) * S :=
    Eq.trans (Finset.sum_const S) (nsmul_eq_mul s.card S)
  exact Eq.trans hfactor
    (congrArg (fun z : ℝ => 80 * z)
      (Eq.trans hsplit
        (Eq.trans
          (congrArg
            (fun z : ℝ => z + ∑ _j ∈ s, S)
            hdivision)
          (congrArg
            (fun z : ℝ =>
              (∑ j ∈ s, ((U j : ℕ) : ℝ)) / T + z)
            hconstant))))

/-- Cast transport for the geometric endpoint budget. -/
theorem Nat.sum_dyadicBlockUpper_add_one_cast_le_three_mul
    {N : ℕ}
    (hN : 0 < N) :
    (∑ j ∈ Nat.dyadicBlockIndexRange N,
        (((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ))) ≤
      3 * (N : ℝ) := by
  have hnat := Nat.sum_dyadicBlockUpper_add_one_le_three_mul hN
  have hcast :
      (((∑ j ∈ Nat.dyadicBlockIndexRange N,
          (Nat.dyadicBlockUpper N j + 1) : ℕ) : ℕ) : ℝ) ≤
        ((3 * N : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  have hsum_cast :
      (((∑ j ∈ Nat.dyadicBlockIndexRange N,
          (Nat.dyadicBlockUpper N j + 1) : ℕ) : ℕ) : ℝ) =
        ∑ j ∈ Nat.dyadicBlockIndexRange N,
          (((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ)) :=
    Nat.cast_sum
      (Nat.dyadicBlockIndexRange N)
      (fun j : ℕ => Nat.dyadicBlockUpper N j + 1)
  have hright_cast : ((3 * N : ℕ) : ℝ) = 3 * (N : ℝ) :=
    Nat.cast_mul 3 N
  exact Eq.subst
    (motive := fun left : ℝ => left ≤ 3 * (N : ℝ))
    hsum_cast
    (Eq.subst
      (motive := fun right : ℝ =>
        (((∑ j ∈ Nat.dyadicBlockIndexRange N,
          (Nat.dyadicBlockUpper N j + 1) : ℕ) : ℕ) : ℝ) ≤ right)
      hright_cast
      hcast)

/-- The norm of a positive logarithmic prefix is bounded by the sum of the
actual dyadic curvature budgets. -/
theorem Complex.logarithmicPhase_dyadicPrefix_norm_le_sum_budget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {N : ℕ}
    (hN : 0 < N) :
    ‖∑ n ∈ Finset.Icc 1 N,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      ∑ j ∈ Nat.dyadicBlockIndexRange N,
        80 *
          ((((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ) / ‖t‖) +
            Real.sqrt (1 + ‖t‖)) := by
  have htriangle :=
    Finset.norm_sum_Icc_one_le_sum_norm_dyadicBlocks
      (fun n : ℕ => ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) N
  have hpoint :
      (∑ j ∈ Nat.dyadicBlockIndexRange N,
          ‖∑ n ∈ Nat.dyadicBlock N j,
            ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖) ≤
        ∑ j ∈ Nat.dyadicBlockIndexRange N,
          80 *
            ((((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ) / ‖t‖) +
              Real.sqrt (1 + ‖t‖)) :=
    Finset.sum_le_sum
      (fun j hj =>
        Complex.logarithmicPhase_dyadicBlockFinset_norm_le_unconditional
          t ht (Nat.dyadicBlock_nonempty_of_mem_indexRange hN hj))
  exact le_trans htriangle hpoint

/-- Dyadic-prefix curvature budget with geometric endpoint accounting. -/
theorem Complex.logarithmicPhase_dyadicPrefix_Icc_norm_le_budget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {N : ℕ}
    (hN : 0 < N) :
    ‖∑ n ∈ Finset.Icc 1 N,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 *
        (3 * (N : ℝ) / ‖t‖ +
          ((Nat.log2 N + 1 : ℕ) : ℝ) * Real.sqrt (1 + ‖t‖)) := by
  have hsum :=
    Complex.logarithmicPhase_dyadicPrefix_norm_le_sum_budget t ht hN
  have hbudget_eq :=
    Finset.sum_dyadic_curvature_budget_eq
      (Nat.dyadicBlockIndexRange N)
      (fun j : ℕ => Nat.dyadicBlockUpper N j + 1)
      ‖t‖ (Real.sqrt (1 + ‖t‖))
  have hendpoint :=
    Nat.sum_dyadicBlockUpper_add_one_cast_le_three_mul hN
  have hnorm_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hendpoint_div :
      (∑ j ∈ Nat.dyadicBlockIndexRange N,
          (((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ))) / ‖t‖ ≤
        (3 * (N : ℝ)) / ‖t‖ :=
    div_le_div_of_nonneg_right hendpoint (le_of_lt hnorm_pos)
  have hcard_cast :
      (((Nat.dyadicBlockIndexRange N).card : ℕ) : ℝ) =
        ((Nat.log2 N + 1 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ))
      (Nat.dyadicBlockIndexRange_card_eq_log2_add_one N)
  have hinsides :
      ((∑ j ∈ Nat.dyadicBlockIndexRange N,
          (((Nat.dyadicBlockUpper N j + 1 : ℕ) : ℝ))) / ‖t‖) +
          (((Nat.dyadicBlockIndexRange N).card : ℕ) : ℝ) *
            Real.sqrt (1 + ‖t‖) ≤
        3 * (N : ℝ) / ‖t‖ +
          ((Nat.log2 N + 1 : ℕ) : ℝ) * Real.sqrt (1 + ‖t‖) := by
    exact add_le_add hendpoint_div
      (le_of_eq
        (congrArg
          (fun z : ℝ => z * Real.sqrt (1 + ‖t‖))
          hcard_cast))
  have hscaled :=
    mul_le_mul_of_nonneg_left hinsides
      (show (0 : ℝ) ≤ 80 from Nat.cast_nonneg 80)
  exact le_trans hsum
    (Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          80 *
            (3 * (N : ℝ) / ‖t‖ +
              ((Nat.log2 N + 1 : ℕ) : ℝ) *
                Real.sqrt (1 + ‖t‖)))
      hbudget_eq.symm
      hscaled)

/-- Public partial-sum form of the dyadic-prefix curvature budget. -/
theorem Complex.logarithmicPhase_dyadicPrefix_norm_le_budget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {N : ℕ}
    (hN : 0 < N) :
    ‖Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum t N‖ ≤
      80 *
        (3 * (N : ℝ) / ‖t‖ +
          ((Nat.log2 N + 1 : ℕ) : ℝ) * Real.sqrt (1 + ‖t‖)) := by
  have hIcc :=
    Complex.logarithmicPhase_dyadicPrefix_Icc_norm_le_budget t ht hN
  have hpartial :
      Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum t N =
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq
      (t := t) (N := N)
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤
        80 *
          (3 * (N : ℝ) / ‖t‖ +
            ((Nat.log2 N + 1 : ℕ) : ℝ) *
              Real.sqrt (1 + ‖t‖)))
    hpartial.symm
    hIcc

end

end LFunctions
end Boundary
