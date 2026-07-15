import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.DyadicBlocks

/-!
# Endpoint budgets for canonical dyadic blocks

This file owns the elementary geometric accounting needed when a positive
prefix is reconstructed from canonical dyadic blocks.  In particular, the
inclusive upper endpoints are summed at their actual sizes; they are not
replaced by a worst-block endpoint.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

/-- Every index in the canonical range determines a nonempty dyadic block
when the ambient endpoint is positive. -/
theorem Nat.dyadicBlock_nonempty_of_mem_indexRange
    {N j : ℕ}
    (hN : 0 < N)
    (hj : j ∈ Nat.dyadicBlockIndexRange N) :
    Nat.dyadicBlockLeft j <
      min (N + 1) (Nat.dyadicBlockRightExclusive j) := by
  have hj_lt : j < Nat.log2 N + 1 :=
    Finset.mem_range.mp hj
  have hj_le : j ≤ Nat.log2 N :=
    Nat.le_of_lt_succ hj_lt
  have hpow_le_log : 2 ^ j ≤ 2 ^ Nat.log2 N :=
    Nat.pow_le_pow_right (Nat.zero_lt_succ 1) hj_le
  have hN_ne : N ≠ 0 :=
    Nat.ne_of_gt hN
  have hlog_le_N : 2 ^ Nat.log2 N ≤ N :=
    Eq.subst
      (motive := fun k : ℕ => 2 ^ k ≤ N)
      Nat.log2_eq_log_two.symm
      (Nat.pow_log_le_self 2 hN_ne)
  have hleft_le_N : Nat.dyadicBlockLeft j ≤ N :=
    le_trans hpow_le_log hlog_le_N
  have hleft_lt_N_succ : Nat.dyadicBlockLeft j < N + 1 :=
    Nat.lt_succ_of_le hleft_le_N
  have hleft_lt_right :
      Nat.dyadicBlockLeft j < Nat.dyadicBlockRightExclusive j := by
    have hpow_pos : 0 < 2 ^ j :=
      pow_pos (Nat.zero_lt_succ 1) j
    have hdouble :
        Nat.dyadicBlockRightExclusive j =
          Nat.dyadicBlockLeft j + Nat.dyadicBlockLeft j := by
      exact Eq.trans
        (Nat.dyadicBlockRightExclusive_eq_two_mul_left j)
        (two_mul (Nat.dyadicBlockLeft j))
    have hself_lt_add :
        Nat.dyadicBlockLeft j <
          Nat.dyadicBlockLeft j + Nat.dyadicBlockLeft j :=
      Nat.lt_add_of_pos_right hpow_pos
    exact Eq.subst
      (motive := fun right : ℕ => Nat.dyadicBlockLeft j < right)
      hdouble.symm
      hself_lt_add
  exact lt_min hleft_lt_N_succ hleft_lt_right

/-- Successor of a nonempty block's upper endpoint is at most its power-of-two
exclusive endpoint. -/
theorem Nat.dyadicBlockUpper_add_one_le_rightExclusive
    {N j : ℕ}
    (hnonempty :
      Nat.dyadicBlockLeft j <
        min (N + 1) (Nat.dyadicBlockRightExclusive j)) :
    Nat.dyadicBlockUpper N j + 1 ≤ Nat.dyadicBlockRightExclusive j := by
  have heq :
      Nat.dyadicBlockUpper N j + 1 =
        min (N + 1) (Nat.dyadicBlockRightExclusive j) :=
    Nat.dyadicBlockUpper_add_one_eq_truncatedRight hnonempty
  exact Eq.subst
    (motive := fun left : ℕ =>
      left ≤ Nat.dyadicBlockRightExclusive j)
    heq.symm
    (min_le_right (N + 1) (Nat.dyadicBlockRightExclusive j))

/-- Successor of a nonempty block's upper endpoint is at most the ambient
successor. -/
theorem Nat.dyadicBlockUpper_add_one_le_ambient
    {N j : ℕ}
    (hnonempty :
      Nat.dyadicBlockLeft j <
        min (N + 1) (Nat.dyadicBlockRightExclusive j)) :
    Nat.dyadicBlockUpper N j + 1 ≤ N + 1 := by
  have heq :
      Nat.dyadicBlockUpper N j + 1 =
        min (N + 1) (Nat.dyadicBlockRightExclusive j) :=
    Nat.dyadicBlockUpper_add_one_eq_truncatedRight hnonempty
  exact Eq.subst
    (motive := fun left : ℕ => left ≤ N + 1)
    heq.symm
    (min_le_left (N + 1) (Nat.dyadicBlockRightExclusive j))

/-- The canonical index family has exactly `log2 N + 1` members. -/
theorem Nat.dyadicBlockIndexRange_card_eq_log2_add_one
    (N : ℕ) :
    (Nat.dyadicBlockIndexRange N).card = Nat.log2 N + 1 := by
  exact Finset.card_range (Nat.log2 N + 1)

/-- Twice the geometric prefix has the cancellation needed at the terminal
dyadic block. -/
theorem Nat.sum_range_two_mul_two_pow_add_two
    (k : ℕ) :
    (∑ j ∈ Finset.range k, 2 * 2 ^ j) + 2 = 2 ^ (k + 1) := by
  induction k with
  | zero =>
      exact Eq.refl 2
  | succ k hk =>
      have hsum_succ :
          (∑ j ∈ Finset.range (k + 1), 2 * 2 ^ j) =
            (∑ j ∈ Finset.range k, 2 * 2 ^ j) + 2 * 2 ^ k :=
        Finset.sum_range_succ (fun j : ℕ => 2 * 2 ^ j) k
      have hreassociate :
          ((∑ j ∈ Finset.range k, 2 * 2 ^ j) + 2 * 2 ^ k) + 2 =
            ((∑ j ∈ Finset.range k, 2 * 2 ^ j) + 2) + 2 * 2 ^ k := by
        calc
          ((∑ j ∈ Finset.range k, 2 * 2 ^ j) + 2 * 2 ^ k) + 2 =
              (∑ j ∈ Finset.range k, 2 * 2 ^ j) + (2 * 2 ^ k + 2) :=
            Nat.add_assoc _ _ _
          _ = (∑ j ∈ Finset.range k, 2 * 2 ^ j) + (2 + 2 * 2 ^ k) := by
            exact congrArg
              (fun z : ℕ => (∑ j ∈ Finset.range k, 2 * 2 ^ j) + z)
              (Nat.add_comm (2 * 2 ^ k) 2)
          _ = ((∑ j ∈ Finset.range k, 2 * 2 ^ j) + 2) + 2 * 2 ^ k :=
            (Nat.add_assoc _ _ _).symm
      have hpower_double :
          2 ^ (k + 1) + 2 * 2 ^ k = 2 ^ ((k + 1) + 1) := by
        have hpow_succ : 2 ^ (k + 1) = 2 ^ k * 2 :=
          Nat.pow_succ 2 k
        have hpow_commute : 2 ^ k * 2 = 2 * 2 ^ k :=
          Nat.mul_comm (2 ^ k) 2
        have hleft_eq : 2 ^ (k + 1) = 2 * 2 ^ k :=
          Eq.trans hpow_succ hpow_commute
        have hsum_double :
            2 * 2 ^ k + 2 * 2 ^ k = 2 * (2 * 2 ^ k) :=
          (two_mul (2 * 2 ^ k)).symm
        have hnext : 2 ^ ((k + 1) + 1) = 2 ^ (k + 1) * 2 :=
          Nat.pow_succ 2 (k + 1)
        have hnext_commute :
            2 ^ (k + 1) * 2 = 2 * 2 ^ (k + 1) :=
          Nat.mul_comm (2 ^ (k + 1)) 2
        exact Eq.trans
          (congrArg (fun z : ℕ => z + 2 * 2 ^ k) hleft_eq)
          (Eq.trans hsum_double
            (Eq.trans
              (congrArg (fun z : ℕ => 2 * z) hleft_eq.symm)
              (Eq.trans hnext_commute.symm hnext.symm)))
      exact Eq.trans
        (congrArg (fun z : ℕ => z + 2) hsum_succ)
        (Eq.trans hreassociate
          (Eq.trans
            (congrArg (fun z : ℕ => z + 2 * 2 ^ k) hk)
            hpower_double))

/-- The terminal dyadic block through a positive endpoint is truncated exactly
at that endpoint. -/
theorem Nat.dyadicBlockUpper_log2_add_one_eq_ambient
    {N : ℕ}
    (hN : 0 < N) :
    Nat.dyadicBlockUpper N (Nat.log2 N) + 1 = N + 1 := by
  have hright : N < Nat.dyadicBlockRightExclusive (Nat.log2 N) :=
    Nat.lt_dyadicBlockRightExclusive_log2 N
  have hN_succ_le : N + 1 ≤ Nat.dyadicBlockRightExclusive (Nat.log2 N) :=
    Nat.succ_le_of_lt hright
  have hmin :
      min (N + 1) (Nat.dyadicBlockRightExclusive (Nat.log2 N)) = N + 1 :=
    min_eq_left hN_succ_le
  have hnonempty :
      Nat.dyadicBlockLeft (Nat.log2 N) <
        min (N + 1) (Nat.dyadicBlockRightExclusive (Nat.log2 N)) :=
    Nat.dyadicBlock_nonempty_of_mem_indexRange hN
      (Finset.mem_range.mpr (Nat.lt_succ_self (Nat.log2 N)))
  exact Eq.trans
    (Nat.dyadicBlockUpper_add_one_eq_truncatedRight hnonempty)
    hmin

/-- The sum of the actual dyadic upper endpoints is at most three times the
ambient endpoint.  The final block is kept truncated; only preceding blocks
are replaced by their power-of-two endpoints. -/
theorem Nat.sum_dyadicBlockUpper_add_one_le_three_mul
    {N : ℕ}
    (hN : 0 < N) :
    (∑ j ∈ Nat.dyadicBlockIndexRange N,
        (Nat.dyadicBlockUpper N j + 1)) ≤ 3 * N := by
  let k : ℕ := Nat.log2 N
  have hsplit :
      (∑ j ∈ Nat.dyadicBlockIndexRange N,
          (Nat.dyadicBlockUpper N j + 1)) =
        (∑ j ∈ Finset.range k,
          (Nat.dyadicBlockUpper N j + 1)) +
          (Nat.dyadicBlockUpper N k + 1) := by
    exact Finset.sum_range_succ
      (fun j : ℕ => Nat.dyadicBlockUpper N j + 1) k
  have hearlier :
      (∑ j ∈ Finset.range k,
          (Nat.dyadicBlockUpper N j + 1)) ≤
        ∑ j ∈ Finset.range k, 2 * 2 ^ j := by
    exact Finset.sum_le_sum
      (fun j hj =>
        have hj_index : j ∈ Nat.dyadicBlockIndexRange N :=
          Finset.mem_range.mpr
            (lt_trans (Finset.mem_range.mp hj) (Nat.lt_succ_self k))
        have hnonempty :=
          Nat.dyadicBlock_nonempty_of_mem_indexRange hN hj_index
        have hright :=
          Nat.dyadicBlockUpper_add_one_le_rightExclusive hnonempty
        Eq.subst
          (motive := fun right : ℕ =>
            Nat.dyadicBlockUpper N j + 1 ≤ right)
          (Nat.dyadicBlockRightExclusive_eq_two_mul_left j)
          hright)
  have hterminal : Nat.dyadicBlockUpper N k + 1 = N + 1 :=
    Nat.dyadicBlockUpper_log2_add_one_eq_ambient hN
  have hpow_le : 2 ^ k ≤ N := by
    have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
    exact Eq.subst
      (motive := fun exponent : ℕ => 2 ^ exponent ≤ N)
      Nat.log2_eq_log_two.symm
      (Nat.pow_log_le_self 2 hN_ne)
  have hgeom :
      (∑ j ∈ Finset.range k, 2 * 2 ^ j) + 2 = 2 ^ (k + 1) :=
    Nat.sum_range_two_mul_two_pow_add_two k
  have hpow_succ : 2 ^ (k + 1) = 2 * 2 ^ k := by
    exact Eq.trans (Nat.pow_succ 2 k) (Nat.mul_comm (2 ^ k) 2)
  have hpower_bound : 2 ^ (k + 1) ≤ 2 * N :=
    Eq.subst
      (motive := fun left : ℕ => left ≤ 2 * N)
      hpow_succ.symm
      (Nat.mul_le_mul_left 2 hpow_le)
  have hsum_plus_one :
      (∑ j ∈ Nat.dyadicBlockIndexRange N,
          (Nat.dyadicBlockUpper N j + 1)) + 1 ≤ 3 * N := by
    have hcombined :
        (∑ j ∈ Nat.dyadicBlockIndexRange N,
            (Nat.dyadicBlockUpper N j + 1)) + 1 ≤
          ((∑ j ∈ Finset.range k, 2 * 2 ^ j) + 2) + N := by
      have hadd := Nat.add_le_add hearlier (le_of_eq hterminal)
      have hadd_one := Nat.add_le_add_right hadd 1
      have hleft_reassociate :
          ((∑ j ∈ Finset.range k,
              (Nat.dyadicBlockUpper N j + 1)) +
              (Nat.dyadicBlockUpper N k + 1)) + 1 =
            (∑ j ∈ Nat.dyadicBlockIndexRange N,
              (Nat.dyadicBlockUpper N j + 1)) + 1 :=
        congrArg (fun z : ℕ => z + 1) hsplit.symm
      have hright_reassociate :
          ((∑ j ∈ Finset.range k, 2 * 2 ^ j) + (N + 1)) + 1 =
            ((∑ j ∈ Finset.range k, 2 * 2 ^ j) + 2) + N := by
        have hsuccessors : (N + 1) + 1 = 2 + N := by
          calc
            (N + 1) + 1 = N + (1 + 1) :=
              Nat.add_assoc N 1 1
            _ = N + 2 :=
              congrArg (fun z : ℕ => N + z) (Eq.refl 2)
            _ = 2 + N :=
              Nat.add_comm N 2
        calc
          ((∑ j ∈ Finset.range k, 2 * 2 ^ j) + (N + 1)) + 1 =
              (∑ j ∈ Finset.range k, 2 * 2 ^ j) + ((N + 1) + 1) :=
            Nat.add_assoc _ _ _
          _ = (∑ j ∈ Finset.range k, 2 * 2 ^ j) + (2 + N) := by
            exact congrArg
              (fun z : ℕ =>
                (∑ j ∈ Finset.range k, 2 * 2 ^ j) + z)
              hsuccessors
          _ = ((∑ j ∈ Finset.range k, 2 * 2 ^ j) + 2) + N :=
            (Nat.add_assoc _ _ _).symm
      exact Eq.subst
        (motive := fun left : ℕ => left ≤
          ((∑ j ∈ Finset.range k, 2 * 2 ^ j) + 2) + N)
        hleft_reassociate
        (Eq.subst
          (motive := fun right : ℕ =>
            ((∑ j ∈ Finset.range k,
                (Nat.dyadicBlockUpper N j + 1)) +
                (Nat.dyadicBlockUpper N k + 1)) + 1 ≤ right)
          hright_reassociate
          hadd_one)
    have hgeom_bound :
        ((∑ j ∈ Finset.range k, 2 * 2 ^ j) + 2) + N ≤
          2 * N + N := by
      exact Nat.add_le_add_right
        (Eq.subst
          (motive := fun left : ℕ => left ≤ 2 * N)
          hgeom.symm
          hpower_bound)
        N
    have hthree : 2 * N + N = 3 * N := by
      calc
        2 * N + N = 2 * N + 1 * N := by
          exact congrArg (fun z : ℕ => 2 * N + z) (Nat.one_mul N).symm
        _ = (2 + 1) * N :=
          (Nat.add_mul 2 1 N).symm
        _ = 3 * N :=
          Eq.refl (3 * N)
    exact le_trans hcombined
      (Eq.subst (motive := fun right : ℕ =>
        ((∑ j ∈ Finset.range k, 2 * 2 ^ j) + 2) + N ≤ right)
        hthree hgeom_bound)
  exact le_trans (Nat.le_add_right _ 1) hsum_plus_one

end

end LFunctions
end Boundary
