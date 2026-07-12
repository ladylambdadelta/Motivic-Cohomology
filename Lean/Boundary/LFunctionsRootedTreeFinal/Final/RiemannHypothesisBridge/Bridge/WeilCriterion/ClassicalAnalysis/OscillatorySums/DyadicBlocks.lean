import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Canonical finite dyadic blocks

This file owns the finite power-of-two partition used by oscillatory block
estimates.  The block with index `j` is

`[2^j, min N (2^(j+1)-1)]`.

The definitions and elementary membership lemmas are independent of every
phase and every analytic estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

/-- The left endpoint of the dyadic block with index `j`. -/
def Nat.dyadicBlockLeft (j : ℕ) : ℕ :=
  2 ^ j

/-- The exclusive right endpoint of the dyadic block with index `j`. -/
def Nat.dyadicBlockRightExclusive (j : ℕ) : ℕ :=
  2 ^ (j + 1)

/-- The canonical dyadic block with index `j`, truncated at `N`. -/
def Nat.dyadicBlock (N j : ℕ) : Finset ℕ :=
  Finset.Ico (Nat.dyadicBlockLeft j)
    (min (N + 1) (Nat.dyadicBlockRightExclusive j))

/-- Inclusive right endpoint associated to a truncated dyadic block.  It is
used only when the block's exclusive endpoints are strictly ordered. -/
def Nat.dyadicBlockUpper (N j : ℕ) : ℕ :=
  min (N + 1) (Nat.dyadicBlockRightExclusive j) - 1

/-- The finite range of block indices needed to cover the positive integers
through `N`. -/
def Nat.dyadicBlockIndexRange (N : ℕ) : Finset ℕ :=
  Finset.range (Nat.log2 N + 1)

/-- Union of all canonical dyadic blocks through `N`. -/
def Nat.dyadicBlockFamilyUnion (N : ℕ) : Finset ℕ :=
  (Nat.dyadicBlockIndexRange N).biUnion (Nat.dyadicBlock N)

/-- A dyadic block's exclusive right endpoint is twice its left endpoint. -/
theorem Nat.dyadicBlockRightExclusive_eq_two_mul_left
    (j : ℕ) :
    Nat.dyadicBlockRightExclusive j =
      2 * Nat.dyadicBlockLeft j := by
  have hpower : 2 ^ (j + 1) = 2 ^ j * 2 :=
    Nat.pow_succ 2 j
  have hcommute : 2 ^ j * 2 = 2 * 2 ^ j :=
    Nat.mul_comm (2 ^ j) 2
  exact Eq.trans hpower hcommute

/-- The truncated exclusive endpoint of a dyadic block is at most twice its
left endpoint. -/
theorem Nat.dyadicBlock_truncatedRight_le_two_mul_left
    (N j : ℕ) :
    min (N + 1) (Nat.dyadicBlockRightExclusive j) ≤
      2 * Nat.dyadicBlockLeft j := by
  have hmin :
      min (N + 1) (Nat.dyadicBlockRightExclusive j) ≤
        Nat.dyadicBlockRightExclusive j :=
    min_le_right (N + 1) (Nat.dyadicBlockRightExclusive j)
  exact
    Eq.subst
      (motive := fun right : ℕ =>
        min (N + 1) (Nat.dyadicBlockRightExclusive j) ≤ right)
      (Nat.dyadicBlockRightExclusive_eq_two_mul_left j)
      hmin

/-- Every sample in a dyadic block is strictly below twice the block's left
endpoint. -/
theorem Nat.lt_two_mul_dyadicBlockLeft_of_mem
    {N j n : ℕ}
    (hn : n ∈ Nat.dyadicBlock N j) :
    n < 2 * Nat.dyadicBlockLeft j := by
  have hright :
      n < min (N + 1) (Nat.dyadicBlockRightExclusive j) :=
    (Finset.mem_Ico.mp hn).2
  exact lt_of_lt_of_le hright
    (Nat.dyadicBlock_truncatedRight_le_two_mul_left N j)

/-- For a nonempty dyadic block, successor of the inclusive upper endpoint is
the truncated exclusive endpoint. -/
theorem Nat.dyadicBlockUpper_add_one_eq_truncatedRight
    {N j : ℕ}
    (hnonempty :
      Nat.dyadicBlockLeft j <
        min (N + 1) (Nat.dyadicBlockRightExclusive j)) :
    Nat.dyadicBlockUpper N j + 1 =
      min (N + 1) (Nat.dyadicBlockRightExclusive j) := by
  have hright_pos :
      0 < min (N + 1) (Nat.dyadicBlockRightExclusive j) :=
    lt_of_le_of_lt (Nat.zero_le (Nat.dyadicBlockLeft j)) hnonempty
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt hright_pos)

/-- A nonempty canonical dyadic block is the corresponding closed natural
interval. -/
theorem Nat.dyadicBlock_eq_Icc
    {N j : ℕ}
    (hnonempty :
      Nat.dyadicBlockLeft j <
        min (N + 1) (Nat.dyadicBlockRightExclusive j)) :
    Nat.dyadicBlock N j =
      Finset.Icc (Nat.dyadicBlockLeft j) (Nat.dyadicBlockUpper N j) := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hn_Ico := Finset.mem_Ico.mp hn
          have hsucc :
              n + 1 ≤ min (N + 1) (Nat.dyadicBlockRightExclusive j) :=
            Nat.succ_le_of_lt hn_Ico.2
          have hupper : n ≤ Nat.dyadicBlockUpper N j :=
            Nat.le_sub_of_add_le hsucc
          Finset.mem_Icc.mpr ⟨hn_Ico.1, hupper⟩)
        (fun hn =>
          have hn_Icc := Finset.mem_Icc.mp hn
          have hupper_succ :
              Nat.dyadicBlockUpper N j + 1 =
                min (N + 1) (Nat.dyadicBlockRightExclusive j) :=
            Nat.dyadicBlockUpper_add_one_eq_truncatedRight hnonempty
          have hstrict :
              n < min (N + 1) (Nat.dyadicBlockRightExclusive j) :=
            Eq.subst
              (motive := fun right : ℕ => n < right)
              hupper_succ
              (Nat.lt_succ_of_le hn_Icc.2)
          Finset.mem_Ico.mpr ⟨hn_Icc.1, hstrict⟩))

/-- A positive integer is at least the left endpoint of the block selected by
its binary logarithm. -/
theorem Nat.dyadicBlockLeft_log2_le
    {n : ℕ}
    (hn : 1 ≤ n) :
    Nat.dyadicBlockLeft (Nat.log2 n) ≤ n := by
  have hn_ne : n ≠ 0 :=
    Nat.ne_of_gt (Nat.lt_of_succ_le hn)
  have hlog :
      2 ^ Nat.log 2 n ≤ n :=
    Nat.pow_log_le_self 2 hn_ne
  exact
    Eq.subst
      (motive := fun exponent : ℕ => 2 ^ exponent ≤ n)
      Nat.log2_eq_log_two.symm
      hlog

/-- A positive integer is strictly below the exclusive right endpoint of the
block selected by its binary logarithm. -/
theorem Nat.lt_dyadicBlockRightExclusive_log2
    (n : ℕ) :
    n < Nat.dyadicBlockRightExclusive (Nat.log2 n) := by
  have hlog :
      n < 2 ^ (Nat.log 2 n).succ :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two n
  have hsuccessor :
      (Nat.log 2 n).succ = Nat.log 2 n + 1 :=
    rfl
  have hlog_add :
      n < 2 ^ (Nat.log 2 n + 1) :=
    Eq.subst
      (motive := fun exponent : ℕ => n < 2 ^ exponent)
      hsuccessor
      hlog
  exact
    Eq.subst
      (motive := fun exponent : ℕ => n < 2 ^ (exponent + 1))
      Nat.log2_eq_log_two.symm
      hlog_add

/-- The binary logarithm of a positive sample is one of the canonical block
indices through any ambient endpoint containing that sample. -/
theorem Nat.log2_mem_dyadicBlockIndexRange
    {n N : ℕ}
    (hn : 1 ≤ n)
    (hnN : n ≤ N) :
    Nat.log2 n ∈ Nat.dyadicBlockIndexRange N := by
  have _hn_ne : n ≠ 0 :=
    Nat.ne_of_gt (Nat.lt_of_succ_le hn)
  have hlog_le : Nat.log 2 n ≤ Nat.log 2 N :=
    Nat.log_mono_right hnN
  have hlog2_le : Nat.log2 n ≤ Nat.log2 N :=
    Eq.subst
      (motive := fun left : ℕ => left ≤ Nat.log2 N)
      Nat.log2_eq_log_two.symm
      (Eq.subst
        (motive := fun right : ℕ => Nat.log 2 n ≤ right)
        Nat.log2_eq_log_two.symm
        hlog_le)
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hlog2_le)

/-- Every positive sample through `N` belongs to its canonically selected
truncated dyadic block. -/
theorem Nat.mem_dyadicBlock_log2
    {n N : ℕ}
    (hn : 1 ≤ n)
    (hnN : n ≤ N) :
    n ∈ Nat.dyadicBlock N (Nat.log2 n) := by
  have hleft :
      Nat.dyadicBlockLeft (Nat.log2 n) ≤ n :=
    Nat.dyadicBlockLeft_log2_le hn
  have hN_succ : n < N + 1 :=
    Nat.lt_succ_of_le hnN
  have hright :
      n < Nat.dyadicBlockRightExclusive (Nat.log2 n) :=
    Nat.lt_dyadicBlockRightExclusive_log2 n
  have hmin :
      n < min (N + 1)
        (Nat.dyadicBlockRightExclusive (Nat.log2 n)) :=
    lt_min hN_succ hright
  exact Finset.mem_Ico.mpr ⟨hleft, hmin⟩

/-- Every sample of a truncated dyadic block is positive. -/
theorem Nat.one_le_of_mem_dyadicBlock
    {N j n : ℕ}
    (hn : n ∈ Nat.dyadicBlock N j) :
    1 ≤ n := by
  have hleft : Nat.dyadicBlockLeft j ≤ n :=
    (Finset.mem_Ico.mp hn).1
  have hone_le_pow : 1 ≤ 2 ^ j :=
    Nat.one_le_pow j 2 (show 0 < (2 : ℕ) from Nat.zero_lt_succ 1)
  exact le_trans hone_le_pow hleft

/-- Every sample of a truncated dyadic block lies at or below its ambient
endpoint. -/
theorem Nat.le_of_mem_dyadicBlock
    {N j n : ℕ}
    (hn : n ∈ Nat.dyadicBlock N j) :
    n ≤ N := by
  have hright :
      n < min (N + 1) (Nat.dyadicBlockRightExclusive j) :=
    (Finset.mem_Ico.mp hn).2
  have hN_succ : n < N + 1 :=
    lt_of_lt_of_le hright (min_le_left (N + 1) (Nat.dyadicBlockRightExclusive j))
  exact Nat.le_of_lt_succ hN_succ

/-- Distinct canonical dyadic blocks are disjoint. -/
theorem Nat.dyadicBlock_disjoint
    (N : ℕ)
    {j k : ℕ}
    (hjk : j ≠ k) :
    Disjoint (Nat.dyadicBlock N j) (Nat.dyadicBlock N k) := by
  exact Finset.disjoint_left.mpr
    (fun n hnj hnk =>
      match lt_or_gt_of_ne hjk with
      | Or.inl hj_lt_k =>
          have hj_succ_le_k : j + 1 ≤ k :=
            Nat.succ_le_of_lt hj_lt_k
          have hpow_le :
              Nat.dyadicBlockRightExclusive j ≤ Nat.dyadicBlockLeft k :=
            Nat.pow_le_pow_right
              (show 0 < (2 : ℕ) from Nat.zero_lt_succ 1)
              hj_succ_le_k
          have hn_lt_right :
              n < Nat.dyadicBlockRightExclusive j :=
            lt_of_lt_of_le (Finset.mem_Ico.mp hnj).2
              (min_le_right (N + 1) (Nat.dyadicBlockRightExclusive j))
          have hleft_le_n : Nat.dyadicBlockLeft k ≤ n :=
            (Finset.mem_Ico.mp hnk).1
          have hn_lt_n : n < n :=
            lt_of_lt_of_le hn_lt_right (le_trans hpow_le hleft_le_n)
          Nat.lt_irrefl n hn_lt_n
      | Or.inr hk_lt_j =>
          have hk_succ_le_j : k + 1 ≤ j :=
            Nat.succ_le_of_lt hk_lt_j
          have hpow_le :
              Nat.dyadicBlockRightExclusive k ≤ Nat.dyadicBlockLeft j :=
            Nat.pow_le_pow_right
              (show 0 < (2 : ℕ) from Nat.zero_lt_succ 1)
              hk_succ_le_j
          have hn_lt_right :
              n < Nat.dyadicBlockRightExclusive k :=
            lt_of_lt_of_le (Finset.mem_Ico.mp hnk).2
              (min_le_right (N + 1) (Nat.dyadicBlockRightExclusive k))
          have hleft_le_n : Nat.dyadicBlockLeft j ≤ n :=
            (Finset.mem_Ico.mp hnj).1
          have hn_lt_n : n < n :=
            lt_of_lt_of_le hn_lt_right (le_trans hpow_le hleft_le_n)
          Nat.lt_irrefl n hn_lt_n)

/-- The canonical dyadic block family covers exactly the positive integer
interval through `N`. -/
theorem Nat.dyadicBlockFamilyUnion_eq_Icc (N : ℕ) :
    Nat.dyadicBlockFamilyUnion N = Finset.Icc 1 N := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn_union =>
          have hn_data := Finset.mem_biUnion.mp hn_union
          match hn_data with
          | ⟨j, hj, hnj⟩ =>
              Finset.mem_Icc.mpr
                ⟨Nat.one_le_of_mem_dyadicBlock hnj,
                  Nat.le_of_mem_dyadicBlock hnj⟩)
        (fun hn_interval =>
          have hn_bounds : 1 ≤ n ∧ n ≤ N :=
            Finset.mem_Icc.mp hn_interval
          have hindex :
              Nat.log2 n ∈ Nat.dyadicBlockIndexRange N :=
            Nat.log2_mem_dyadicBlockIndexRange hn_bounds.1 hn_bounds.2
          have hblock :
              n ∈ Nat.dyadicBlock N (Nat.log2 n) :=
            Nat.mem_dyadicBlock_log2 hn_bounds.1 hn_bounds.2
          Finset.mem_biUnion.mpr ⟨Nat.log2 n, hindex, hblock⟩))

/-- Exact decomposition of a finite positive-index sum into its canonical
dyadic blocks. -/
theorem Finset.sum_Icc_one_eq_sum_dyadicBlocks
    {M : Type*}
    [AddCommMonoid M]
    (f : ℕ → M)
    (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) =
      ∑ j ∈ Nat.dyadicBlockIndexRange N,
        ∑ n ∈ Nat.dyadicBlock N j, f n := by
  have hdisjoint :
      ∀ j ∈ Nat.dyadicBlockIndexRange N,
        ∀ k ∈ Nat.dyadicBlockIndexRange N,
          j ≠ k →
            Disjoint (Nat.dyadicBlock N j) (Nat.dyadicBlock N k) := by
    intro j _hj k _hk hjk
    exact Nat.dyadicBlock_disjoint N hjk
  have hunion :
      Nat.dyadicBlockFamilyUnion N = Finset.Icc 1 N :=
    Nat.dyadicBlockFamilyUnion_eq_Icc N
  have hsum :
      (∑ n ∈ Nat.dyadicBlockFamilyUnion N, f n) =
        ∑ j ∈ Nat.dyadicBlockIndexRange N,
          ∑ n ∈ Nat.dyadicBlock N j, f n :=
    Finset.sum_biUnion hdisjoint
  exact
    Eq.subst
      (motive := fun block : Finset ℕ =>
        (∑ n ∈ block, f n) =
          ∑ j ∈ Nat.dyadicBlockIndexRange N,
            ∑ n ∈ Nat.dyadicBlock N j, f n)
      hunion
      hsum

/-- The norm of a positive-index sum is bounded by the sum of the norms of
its canonical dyadic block sums. -/
theorem Finset.norm_sum_Icc_one_le_sum_norm_dyadicBlocks
    {E : Type*}
    [SeminormedAddCommGroup E]
    (f : ℕ → E)
    (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤
      ∑ j ∈ Nat.dyadicBlockIndexRange N,
        ‖∑ n ∈ Nat.dyadicBlock N j, f n‖ := by
  have hdecomposition :
      (∑ n ∈ Finset.Icc 1 N, f n) =
        ∑ j ∈ Nat.dyadicBlockIndexRange N,
          ∑ n ∈ Nat.dyadicBlock N j, f n :=
    Finset.sum_Icc_one_eq_sum_dyadicBlocks f N
  have htriangle :
      ‖∑ j ∈ Nat.dyadicBlockIndexRange N,
          ∑ n ∈ Nat.dyadicBlock N j, f n‖ ≤
        ∑ j ∈ Nat.dyadicBlockIndexRange N,
          ‖∑ n ∈ Nat.dyadicBlock N j, f n‖ :=
    norm_sum_le
      (Nat.dyadicBlockIndexRange N)
      (fun j : ℕ => ∑ n ∈ Nat.dyadicBlock N j, f n)
  exact
    Eq.subst
      (motive := fun value : E =>
        ‖value‖ ≤
          ∑ j ∈ Nat.dyadicBlockIndexRange N,
            ‖∑ n ∈ Nat.dyadicBlock N j, f n‖)
      hdecomposition.symm
      htriangle

/-- A uniform bound for every canonical dyadic block gives the corresponding
block-count multiple for the full positive-index sum. -/
theorem Finset.norm_sum_Icc_one_le_card_mul_of_dyadicBlock_bound
    {E : Type*}
    [SeminormedAddCommGroup E]
    (f : ℕ → E)
    (N : ℕ)
    (B : ℝ)
    (hblock :
      ∀ j : ℕ,
        j ∈ Nat.dyadicBlockIndexRange N →
          ‖∑ n ∈ Nat.dyadicBlock N j, f n‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤
      ((Nat.dyadicBlockIndexRange N).card : ℝ) * B := by
  have htriangle :
      ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤
        ∑ j ∈ Nat.dyadicBlockIndexRange N,
          ‖∑ n ∈ Nat.dyadicBlock N j, f n‖ :=
    Finset.norm_sum_Icc_one_le_sum_norm_dyadicBlocks f N
  have hsum_bound :
      (∑ j ∈ Nat.dyadicBlockIndexRange N,
          ‖∑ n ∈ Nat.dyadicBlock N j, f n‖) ≤
        ∑ _j ∈ Nat.dyadicBlockIndexRange N, B := by
    exact Finset.sum_le_sum
      (fun j hj => hblock j hj)
  have hconstant_sum :
      (∑ _j ∈ Nat.dyadicBlockIndexRange N, B) =
        ((Nat.dyadicBlockIndexRange N).card : ℝ) * B := by
    exact Eq.trans
      (Finset.sum_const B)
      (nsmul_eq_mul (Nat.dyadicBlockIndexRange N).card B)
  exact le_trans htriangle
    (le_trans hsum_bound (le_of_eq hconstant_sum))

end

end LFunctions
end Boundary
