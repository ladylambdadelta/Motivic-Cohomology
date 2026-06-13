import Boundary.LFunctions.ZetaPolynomialTailSummability
import Boundary.LFunctions.ZetaZeroSideDefinitions

/-!
# Completed zero multiplicity counting

This file owns the multiplicity-aware zero-counting surface used by the zero-tail
majorant.  The analytic input is the coarse finite-order/Jensen theorem: completed zeta
zeros, counted with analytic multiplicity, have polynomial growth in centered height.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The singleton-supported real family at `a` has sum `u a`. -/
theorem hasSum_singletonSupport_real
    {α : Type*} (u : α → ℝ) (a : α) :
    HasSum
      (fun x : α => if x = a then u a else 0)
      (u a) := by
  classical
  let s : Finset α := {a}
  have hoff :
      ∀ x : α, x ∉ s →
        (if x = a then u a else 0) = 0 := by
    intro x hx
    have hne : x ≠ a := by
      intro hxa
      have hxmem : x ∈ s :=
        Eq.subst
          (motive := fun y : α => x ∈ ({y} : Finset α))
          hxa.symm
          (Finset.mem_singleton_self x)
      exact hx hxmem
    exact if_neg hne
  have hsum :
      HasSum
        (fun x : α => if x = a then u a else 0)
        (∑ x in s, if x = a then u a else 0) :=
    hasSum_sum_of_ne_finset_zero hoff
  have hfinite :
      (∑ x in s, if x = a then u a else 0) = u a := by
    have hsingleton :
        (∑ x in s, if x = a then u a else 0) =
          (if a = a then u a else 0) :=
      Finset.sum_singleton (fun x : α => if x = a then u a else 0)
    have hvalue :
        (if a = a then u a else 0) = u a :=
      if_pos rfl
    exact Eq.trans hsingleton hvalue
  exact Eq.subst
    (motive := fun t : ℝ =>
      HasSum (fun x : α => if x = a then u a else 0) t)
    hfinite
    hsum

/-- A nonnegative summable real family dominates each of its terms by its total `tsum`. -/
theorem real_term_le_tsum_of_summable_nonnegative
    {α : Type*} (u : α → ℝ)
    (hu : Summable u)
    (h_nonneg : ∀ a : α, 0 ≤ u a)
    (a : α) :
    u a ≤ ∑' x : α, u x := by
  classical
  let v : α → ℝ := fun x : α => if x = a then u a else 0
  have hv_hasSum : HasSum v (u a) :=
    hasSum_singletonSupport_real u a
  have hv_summable : Summable v :=
    ⟨u a, hv_hasSum⟩
  have hv_tsum : (∑' x : α, v x) = u a :=
    hv_hasSum.tsum_eq
  have hv_le_u : ∀ x : α, v x ≤ u x := by
    intro x
    by_cases hxa : x = a
    · have hxvalue : v x = u a := by
        unfold v
        exact if_pos hxa
      have htarget : u a = u x :=
        congrArg u hxa.symm
      exact Eq.subst
        (motive := fun y : ℝ => v x ≤ y)
        htarget
        (Eq.subst
          (motive := fun y : ℝ => y ≤ u a)
          hxvalue
          (le_refl (u a)))
    · have hxvalue : v x = 0 := by
        unfold v
        exact if_neg hxa
      exact Eq.subst
        (motive := fun y : ℝ => y ≤ u x)
        hxvalue.symm
        (h_nonneg x)
  have htsum_le :
      (∑' x : α, v x) ≤ ∑' x : α, u x :=
    tsum_le_tsum hv_le_u hv_summable hu
  exact Eq.subst
    (motive := fun t : ℝ => t ≤ ∑' x : α, u x)
    hv_tsum
    htsum_le

/-- Height-ball multiplicity summands are nonnegative. -/
theorem completedZeroMultiplicityHeightBallSummand_nonnegative
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    0 ≤ completedZeroMultiplicityHeightBallSummand T ρ := by
  unfold completedZeroMultiplicityHeightBallSummand
  by_cases hρ : zetaCompletedZeroCenteredHeight ρ ≤ T
  · exact Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (if_pos hρ).symm
      (Nat.cast_nonneg (zetaZeroMultiplicity (ρ : ℂ)))
  · exact Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (if_neg hρ).symm
      (le_refl (0 : ℝ))

/-- Height-ball summands are monotone in the radius. -/
theorem completedZeroMultiplicityHeightBallSummand_mono
    {S T : ℝ} (hST : S ≤ T)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedZeroMultiplicityHeightBallSummand S ρ ≤
      completedZeroMultiplicityHeightBallSummand T ρ := by
  unfold completedZeroMultiplicityHeightBallSummand
  by_cases hS : zetaCompletedZeroCenteredHeight ρ ≤ S
  · have hT : zetaCompletedZeroCenteredHeight ρ ≤ T :=
      le_trans hS hST
    exact Eq.subst
      (motive := fun x : ℝ =>
        x ≤ if zetaCompletedZeroCenteredHeight ρ ≤ T then
          (zetaZeroMultiplicity (ρ : ℂ) : ℝ) else 0)
      (if_pos hS).symm
      (Eq.subst
        (motive := fun x : ℝ =>
          (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤ x)
        (if_pos hT).symm
        (le_refl (zetaZeroMultiplicity (ρ : ℂ) : ℝ)))
  · by_cases hT : zetaCompletedZeroCenteredHeight ρ ≤ T
    · exact Eq.subst
        (motive := fun x : ℝ =>
          x ≤ if zetaCompletedZeroCenteredHeight ρ ≤ T then
            (zetaZeroMultiplicity (ρ : ℂ) : ℝ) else 0)
        (if_neg hS).symm
        (Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          (if_pos hT).symm
          (Nat.cast_nonneg (zetaZeroMultiplicity (ρ : ℂ))))
    · exact Eq.subst
        (motive := fun x : ℝ =>
          x ≤ if zetaCompletedZeroCenteredHeight ρ ≤ T then
            (zetaZeroMultiplicity (ρ : ℂ) : ℝ) else 0)
        (if_neg hS).symm
        (Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          (if_neg hT).symm
          (le_refl (0 : ℝ)))

/-- A completed zero lies in its own centered height ball. -/
theorem zetaCompletedZero_mem_heightBall_self
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ρ ∈ completedZerosInCenteredHeightBall
      (zetaCompletedZeroCenteredHeight ρ) := by
  unfold completedZerosInCenteredHeightBall
  exact le_refl (zetaCompletedZeroCenteredHeight ρ)

/-- At its own height, a completed zero contributes its full multiplicity to the
height-ball summand. -/
theorem completedZeroMultiplicityHeightBallSummand_self
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedZeroMultiplicityHeightBallSummand
        (zetaCompletedZeroCenteredHeight ρ) ρ =
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) := by
  unfold completedZeroMultiplicityHeightBallSummand
  exact if_pos (le_refl (zetaCompletedZeroCenteredHeight ρ))

/-- Height-ball multiplicity summands vanish outside the height ball. -/
theorem completedZeroMultiplicityHeightBallSummand_eq_zero_of_not_mem
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∉ completedZerosInCenteredHeightBall T) :
    completedZeroMultiplicityHeightBallSummand T ρ = 0 := by
  unfold completedZerosInCenteredHeightBall at hρ
  unfold completedZeroMultiplicityHeightBallSummand
  exact if_neg hρ

/-- Finite height balls make the height-ball multiplicity summand summable. -/
theorem summable_completedZeroMultiplicityHeightBallSummand_of_finite_heightBall
    (T : ℝ)
    (hfinite : (completedZerosInCenteredHeightBall T).Finite) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityHeightBallSummand T ρ) := by
  exact summable_of_finite_support_real
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      completedZeroMultiplicityHeightBallSummand T ρ)
    (completedZerosInCenteredHeightBall T)
    hfinite
    (completedZeroMultiplicityHeightBallSummand_eq_zero_of_not_mem T)

/-- Height-ball multiplicity summands are summable.

This is the finite-height-ball bookkeeping consequence of local finiteness of the completed
zero divisor, counted with analytic multiplicity. -/
theorem summable_completedZeroMultiplicityHeightBallSummand
    (T : ℝ) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityHeightBallSummand T ρ) := by
  exact summable_completedZeroMultiplicityHeightBallSummand_of_finite_heightBall
    T
    (finite_completedZerosInCenteredHeightBall T)

/-- One nonnegative height-ball summand is bounded by the full height-ball count. -/
theorem completedZeroMultiplicityHeightBallSummand_le_counting
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedZeroMultiplicityHeightBallSummand T ρ ≤
      completedZeroMultiplicityCountingInCenteredHeightBall T := by
  unfold completedZeroMultiplicityCountingInCenteredHeightBall
  exact real_term_le_tsum_of_summable_nonnegative
    (fun η : {ρ : ℂ // ZetaCompletedZero ρ} =>
      completedZeroMultiplicityHeightBallSummand T η)
    (summable_completedZeroMultiplicityHeightBallSummand T)
    (completedZeroMultiplicityHeightBallSummand_nonnegative T)
    ρ

/-- Completed zero multiplicity counts are nonnegative. -/
theorem completedZeroMultiplicityCountingInCenteredHeightBall_nonnegative
    (T : ℝ) :
    0 ≤ completedZeroMultiplicityCountingInCenteredHeightBall T := by
  unfold completedZeroMultiplicityCountingInCenteredHeightBall
  have hzeroSummable :
      Summable
        (fun _ρ : {ρ : ℂ // ZetaCompletedZero ρ} => (0 : ℝ)) :=
    summable_zero
  have hsummand :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          completedZeroMultiplicityHeightBallSummand T ρ) :=
    summable_completedZeroMultiplicityHeightBallSummand T
  have hle :
      (∑' _ρ : {ρ : ℂ // ZetaCompletedZero ρ}, (0 : ℝ)) ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          completedZeroMultiplicityHeightBallSummand T ρ :=
    tsum_le_tsum
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityHeightBallSummand_nonnegative T ρ)
      hzeroSummable
      hsummand
  have hzero :
      (∑' _ρ : {ρ : ℂ // ZetaCompletedZero ρ}, (0 : ℝ)) = 0 :=
    tsum_zero
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          completedZeroMultiplicityHeightBallSummand T ρ)
    hzero.symm
    hle

/-- Completed zero multiplicity counts are monotone in the height radius. -/
theorem completedZeroMultiplicityCountingInCenteredHeightBall_mono
    {S T : ℝ} (hST : S ≤ T) :
    completedZeroMultiplicityCountingInCenteredHeightBall S ≤
      completedZeroMultiplicityCountingInCenteredHeightBall T := by
  unfold completedZeroMultiplicityCountingInCenteredHeightBall
  exact tsum_le_tsum
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      completedZeroMultiplicityHeightBallSummand_mono hST ρ)
    (summable_completedZeroMultiplicityHeightBallSummand S)
    (summable_completedZeroMultiplicityHeightBallSummand T)

/-- Each zero's analytic multiplicity is bounded by the height-ball counting function at
that zero's own height. -/
theorem zetaZeroMultiplicity_le_countingFunction_at_height
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤
      completedZeroMultiplicityCountingInCenteredHeightBall
        (zetaCompletedZeroCenteredHeight ρ) := by
  have hsummand :
      completedZeroMultiplicityHeightBallSummand
          (zetaCompletedZeroCenteredHeight ρ) ρ =
        (zetaZeroMultiplicity (ρ : ℂ) : ℝ) :=
    completedZeroMultiplicityHeightBallSummand_self ρ
  have hle :
      completedZeroMultiplicityHeightBallSummand
          (zetaCompletedZeroCenteredHeight ρ) ρ ≤
        completedZeroMultiplicityCountingInCenteredHeightBall
          (zetaCompletedZeroCenteredHeight ρ) :=
    completedZeroMultiplicityHeightBallSummand_le_counting
      (zetaCompletedZeroCenteredHeight ρ) ρ
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ completedZeroMultiplicityCountingInCenteredHeightBall
        (zetaCompletedZeroCenteredHeight ρ))
    hsummand
    hle

/-- The complex norm of a natural zero multiplicity is its real cast. -/
theorem norm_complex_ofNat_zetaZeroMultiplicity
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ =
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) := by
  have hnonneg : 0 ≤ (zetaZeroMultiplicity (ρ : ℂ) : ℝ) :=
    Nat.cast_nonneg (zetaZeroMultiplicity (ρ : ℂ))
  change ‖((zetaZeroMultiplicity (ρ : ℂ) : ℝ) : ℂ)‖ =
    (zetaZeroMultiplicity (ρ : ℂ) : ℝ)
  calc
    ‖((zetaZeroMultiplicity (ρ : ℂ) : ℝ) : ℂ)‖ =
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℝ)‖ := by
      exact Complex.norm_ofReal (zetaZeroMultiplicity (ρ : ℂ) : ℝ)
    _ = (zetaZeroMultiplicity (ρ : ℂ) : ℝ) := by
      exact Real.norm_of_nonneg hnonneg

/-- Completed-zero multiplicities have polynomial growth in centered height, as a local
consequence of multiplicity-aware zero counting. -/
theorem exists_zetaZeroMultiplicityGrowthEnvelope_bound_from_counting :
    ∃ M : ℝ, ∃ d : ℕ,
      0 < M ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ ≤
          M * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) := by
  rcases exists_completedZeroMultiplicityCounting_height_bound with
    ⟨C, d, hCpos, hcount⟩
  refine ⟨C, d, hCpos, ?_⟩
  intro ρ
  have hmult_count :
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤
        completedZeroMultiplicityCountingInCenteredHeightBall
          (zetaCompletedZeroCenteredHeight ρ) :=
    zetaZeroMultiplicity_le_countingFunction_at_height ρ
  have hcount_height :
      completedZeroMultiplicityCountingInCenteredHeightBall
          (zetaCompletedZeroCenteredHeight ρ) ≤
        C * zetaCompletedZeroCenteredHeight ρ ^ d :=
    hcount
      (zetaCompletedZeroCenteredHeight ρ)
      (zetaCompletedZeroCenteredHeight_ge_one ρ)
  have hnat_zpow :
      zetaCompletedZeroCenteredHeight ρ ^ d =
        zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) := by
    exact (zpow_natCast (zetaCompletedZeroCenteredHeight ρ) d).symm
  have hbound_nat :
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤
        C * zetaCompletedZeroCenteredHeight ρ ^ d :=
    le_trans hmult_count hcount_height
  have hbound_zpow :
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤
        C * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) :=
    Eq.subst
      (motive := fun x : ℝ =>
        (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤ C * x)
      hnat_zpow
      hbound_nat
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ C * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ))
    (norm_complex_ofNat_zetaZeroMultiplicity ρ).symm
    hbound_zpow

/-- Every real height at least one belongs to a natural unit shell. -/
theorem exists_nat_unitShell_of_one_le
    {x : ℝ}
    (hx : 1 ≤ x) :
    ∃ m : ℕ, ((m : ℕ) : ℝ) ≤ x ∧ x < ((m + 1 : ℕ) : ℝ) := by
  exact ⟨Nat.floor x,
    Nat.floor_le (le_trans zero_le_one hx),
    Nat.lt_floor_add_one x⟩

/-- Natural unit shells are disjoint. -/
theorem nat_unitShell_index_unique
    {x : ℝ} {m n : ℕ}
    (hm : ((m : ℕ) : ℝ) ≤ x ∧ x < ((m + 1 : ℕ) : ℝ))
    (hn : ((n : ℕ) : ℝ) ≤ x ∧ x < ((n + 1 : ℕ) : ℝ)) :
    m = n := by
  have hmn_real : ((m : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) :=
    lt_of_le_of_lt hm.1 hn.2
  have hnm_real : ((n : ℕ) : ℝ) < ((m + 1 : ℕ) : ℝ) :=
    lt_of_le_of_lt hn.1 hm.2
  have hmn_succ : m < n + 1 :=
    Nat.cast_lt.mp hmn_real
  have hnm_succ : n < m + 1 :=
    Nat.cast_lt.mp hnm_real
  have hmn : m ≤ n :=
    Nat.lt_succ_iff.mp hmn_succ
  have hnm : n ≤ m :=
    Nat.lt_succ_iff.mp hnm_succ
  exact Nat.le_antisymm hmn hnm

/-- The completed-zero shell at integer height `m`, using the centered height
base `1 + |Im|`. -/
def completedZeroCenteredHeightShell
    (m : ℕ) :
    Set {ρ : ℂ // ZetaCompletedZero ρ} :=
  {ρ |
    ((m : ℕ) : ℝ) ≤ zetaCompletedZeroCenteredHeight ρ ∧
      zetaCompletedZeroCenteredHeight ρ < ((m + 1 : ℕ) : ℝ)}

/-- Every completed zero has an integer centered-height shell index. -/
theorem exists_completedZeroCenteredHeightShell_index
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ∃ m : ℕ, ρ ∈ completedZeroCenteredHeightShell m := by
  exact exists_nat_unitShell_of_one_le
    (zetaCompletedZeroCenteredHeight_ge_one ρ)

/-- Centered-height shells are disjoint. -/
theorem completedZeroCenteredHeightShell_index_unique
    {ρ : {ρ : ℂ // ZetaCompletedZero ρ}} {m n : ℕ}
    (hm : ρ ∈ completedZeroCenteredHeightShell m)
    (hn : ρ ∈ completedZeroCenteredHeightShell n) :
    m = n := by
  exact nat_unitShell_index_unique hm hn

/-- A completed-zero shell is contained in the height ball with the next
integer radius. -/
theorem completedZeroCenteredHeightShell_subset_heightBall
    (m : ℕ) :
    completedZeroCenteredHeightShell m ⊆
      completedZerosInCenteredHeightBall ((m + 1 : ℕ) : ℝ) := by
  intro ρ hρ
  exact le_of_lt hρ.2

/-- Completed-zero centered-height shells are finite, by containment in finite
height balls. -/
theorem finite_completedZeroCenteredHeightShell
    (m : ℕ) :
    (completedZeroCenteredHeightShell m).Finite := by
  exact Set.Finite.subset
    (finite_completedZerosInCenteredHeightBall ((m + 1 : ℕ) : ℝ))
    (completedZeroCenteredHeightShell_subset_heightBall m)

/-- A finite set has a finite subtype of its elements. -/
theorem finite_univ_subtype_of_finite_set
    {α : Type*} {s : Set α}
    (hs : s.Finite) :
    (Set.univ : Set s).Finite := by
  classical
  haveI : Fintype s := hs.fintype
  exact Set.finite_univ

/-- The completed-zero shell fiber at integer height `m`. -/
def completedZeroCenteredHeightShellFiber
    (m : ℕ) : Type :=
  {ρ : {ρ : ℂ // ZetaCompletedZero ρ} //
    ρ ∈ completedZeroCenteredHeightShell m}

/-- The sigma type of all completed-zero shell fibers. -/
abbrev CompletedZeroCenteredHeightShellSigma : Type :=
  Sigma completedZeroCenteredHeightShellFiber

/-- Forget a shell-fiber point to its completed zero. -/
def completedZeroCenteredHeightShellSigma_forget
    (x : CompletedZeroCenteredHeightShellSigma) :
    {ρ : ℂ // ZetaCompletedZero ρ} :=
  x.2.1

/-- The shell-fiber forgetful map is surjective onto completed zeros. -/
theorem completedZeroCenteredHeightShellSigma_forget_surjective :
    Function.Surjective completedZeroCenteredHeightShellSigma_forget := by
  intro ρ
  rcases exists_completedZeroCenteredHeightShell_index ρ with ⟨m, hm⟩
  exact ⟨⟨m, ⟨ρ, hm⟩⟩, rfl⟩

/-- The shell-fiber forgetful map is injective; integer height shells are disjoint. -/
theorem completedZeroCenteredHeightShellSigma_forget_injective :
    Function.Injective completedZeroCenteredHeightShellSigma_forget := by
  intro x y hxy
  rcases x with ⟨m, ρm⟩
  rcases y with ⟨n, ρn⟩
  rcases ρm with ⟨ρ, hρm⟩
  rcases ρn with ⟨η, hηn⟩
  have hρη : ρ = η := hxy
  cases hρη
  have hmn : m = n :=
    completedZeroCenteredHeightShell_index_unique hρm hηn
  cases hmn
  rfl

/-- The total decay mass in one centered-height shell. -/
noncomputable def completedZeroCenteredHeightShellDecayMass
    (d k m : ℕ) : ℝ :=
  ∑' x : completedZeroCenteredHeightShellFiber m,
    zetaCompletedZeroCenteredHeight (x : {ρ : ℂ // ZetaCompletedZero ρ}) ^
      (-(d + k + 3 : ℤ))

/-- The polynomial decay restricted to a shell fiber. -/
noncomputable def completedZeroCenteredHeightShellFiberDecay
    (d k : ℕ)
    (x : CompletedZeroCenteredHeightShellSigma) : ℝ :=
  zetaCompletedZeroCenteredHeight
      (completedZeroCenteredHeightShellSigma_forget x) ^
    (-(d + k + 3 : ℤ))

/-- Shell-fiber decay is nonnegative. -/
theorem completedZeroCenteredHeightShellFiberDecay_nonnegative
    (d k : ℕ)
    (x : CompletedZeroCenteredHeightShellSigma) :
    0 ≤ completedZeroCenteredHeightShellFiberDecay d k x := by
  unfold completedZeroCenteredHeightShellFiberDecay
  exact zpow_nonneg
    (le_trans zero_le_one
      (zetaCompletedZeroCenteredHeight_ge_one
        (completedZeroCenteredHeightShellSigma_forget x)))
    (-(d + k + 3 : ℤ))

/-- The shell-fiber `tsum` at height `m` is the shell decay mass. -/
theorem completedZeroCenteredHeightShellFiberDecay_tsum_eq_shellDecayMass
    (d k m : ℕ) :
    (∑' x : completedZeroCenteredHeightShellFiber m,
      zetaCompletedZeroCenteredHeight (x : {ρ : ℂ // ZetaCompletedZero ρ}) ^
        (-(d + k + 3 : ℤ))) =
      completedZeroCenteredHeightShellDecayMass d k m := by
  rfl

/-- Each completed-zero centered-height shell fiber is finite. -/
theorem finite_completedZeroCenteredHeightShellFiber
    (m : ℕ) :
    (Set.univ : Set (completedZeroCenteredHeightShellFiber m)).Finite := by
  exact finite_univ_subtype_of_finite_set
    (finite_completedZeroCenteredHeightShell m)

/-- Decay over a fixed completed-zero centered-height shell fiber is summable. -/
theorem summable_completedZeroCenteredHeightShellFiberDecay_fixed
    (d k m : ℕ) :
    Summable
      (fun x : completedZeroCenteredHeightShellFiber m =>
        completedZeroCenteredHeightShellFiberDecay d k ⟨m, x⟩) := by
  exact summable_of_finite_support_real
    (fun x : completedZeroCenteredHeightShellFiber m =>
      completedZeroCenteredHeightShellFiberDecay d k ⟨m, x⟩)
    Set.univ
    (finite_completedZeroCenteredHeightShellFiber m)
    (fun x hx => False.elim (hx trivial))

/-- Summability over shell masses is equivalent to summability over the sigma
shell decomposition. -/
theorem summable_completedZeroCenteredHeightShellFiberDecay_of_shellMass
    (d k : ℕ)
    (hshell :
      Summable
        (fun m : ℕ =>
          completedZeroCenteredHeightShellDecayMass d k m)) :
    Summable
      (fun x : CompletedZeroCenteredHeightShellSigma =>
        completedZeroCenteredHeightShellFiberDecay d k x) := by
  refine (summable_sigma_of_nonneg ?_).mpr ?_
  · intro x
    exact completedZeroCenteredHeightShellFiberDecay_nonnegative d k x
  · constructor
    · intro m
      exact summable_completedZeroCenteredHeightShellFiberDecay_fixed d k m
    · have hfiberSums :
          (fun m : ℕ =>
            ∑' x : completedZeroCenteredHeightShellFiber m,
              completedZeroCenteredHeightShellFiberDecay d k ⟨m, x⟩) =
            fun m : ℕ =>
              completedZeroCenteredHeightShellDecayMass d k m := by
        funext m
        exact completedZeroCenteredHeightShellFiberDecay_tsum_eq_shellDecayMass
          d k m
      exact Eq.subst
        (motive := fun u : ℕ → ℝ => Summable u)
        hfiberSums.symm
        hshell

/-- Summability transports across a bijective map of index types. -/
theorem summable_of_bijective_index_transport_real
    {α β : Type*} (e : α → β) (u : β → ℝ)
    (hinj : Function.Injective e)
    (hsurj : Function.Surjective e)
    (hsum : Summable (fun a : α => u (e a))) :
    Summable u := by
  let E : α ≃ β := Equiv.ofBijective e ⟨hinj, hsurj⟩
  have hE :
      (fun a : α => u (E a)) = fun a : α => u (e a) := by
    rfl
  exact ((E.symm).summable_iff).mp
    (Eq.subst
      (motive := fun v : α → ℝ => Summable v)
      hE.symm
      hsum)

/-- Shell-fiber decay is the base negative-height decay after forgetting the
shell coordinate. -/
theorem completedZeroCenteredHeightShellFiberDecay_eq_baseDecay
    (d k : ℕ)
    (x : CompletedZeroCenteredHeightShellSigma) :
    completedZeroCenteredHeightShellFiberDecay d k x =
      zetaCompletedZeroCenteredHeight
          (completedZeroCenteredHeightShellSigma_forget x) ^
        (-(d + k + 3 : ℤ)) := by
  rfl

/-- Summability over the sigma shell decomposition transports to summability
over completed zeros. -/
theorem summable_completedZero_centeredHeight_negativePower_of_shellSigma
    (d k : ℕ)
    (hsigma :
      Summable
        (fun x : CompletedZeroCenteredHeightShellSigma =>
          completedZeroCenteredHeightShellFiberDecay d k x)) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) := by
  exact summable_of_bijective_index_transport_real
    completedZeroCenteredHeightShellSigma_forget
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ)))
    completedZeroCenteredHeightShellSigma_forget_injective
    completedZeroCenteredHeightShellSigma_forget_surjective
    (Eq.subst
      (motive := fun u : CompletedZeroCenteredHeightShellSigma → ℝ =>
        Summable u)
      (by
        funext x
        exact completedZeroCenteredHeightShellFiberDecay_eq_baseDecay d k x)
      hsigma)

/-- Summable centered-height shell masses transport to summability over all
completed zeros. -/
theorem summable_completedZero_centeredHeight_negativePower_of_shellMass
    (d k : ℕ)
    (hshell :
      Summable
        (fun m : ℕ =>
          completedZeroCenteredHeightShellDecayMass d k m)) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) := by
  exact summable_completedZero_centeredHeight_negativePower_of_shellSigma
    d
    k
    (summable_completedZeroCenteredHeightShellFiberDecay_of_shellMass
      d k hshell)

end

end LFunctions
end Boundary
