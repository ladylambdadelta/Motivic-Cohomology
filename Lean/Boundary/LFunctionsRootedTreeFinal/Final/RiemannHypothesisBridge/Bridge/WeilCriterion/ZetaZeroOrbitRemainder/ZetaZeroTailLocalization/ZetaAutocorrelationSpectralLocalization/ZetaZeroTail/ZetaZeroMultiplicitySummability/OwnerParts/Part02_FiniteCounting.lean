import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.OwnerParts.Part01_ShellBounds

namespace Boundary
namespace LFunctions

noncomputable section

theorem fintype_univ_card_cast_eq_natCard
    (α : Type*) [Fintype α] :
    ((Finset.univ : Finset α).card : ℝ) = (Nat.card α : ℝ) := by
  have hcard : (Finset.univ : Finset α).card = Nat.card α :=
    Eq.trans Finset.card_univ Fintype.card_eq_nat_card
  exact congrArg Nat.cast hcard

theorem fintype_univ_nsmul_eq_natCard_mul
    (α : Type*) [Fintype α] (B : ℝ) :
    (Finset.univ : Finset α).card • B = (Nat.card α : ℝ) * B := by
  have hsmul :
      (Finset.univ : Finset α).card • B =
        ((Finset.univ : Finset α).card : ℝ) * B :=
    nsmul_eq_mul (Finset.univ : Finset α).card B
  have hcast :
      ((Finset.univ : Finset α).card : ℝ) = (Nat.card α : ℝ) :=
    fintype_univ_card_cast_eq_natCard α
  exact Eq.trans hsmul (congrArg (fun value : ℝ => value * B) hcast)

theorem fintype_sum_one_eq_natCard
    (α : Type*) [Fintype α] :
    (∑ element : α, (1 : ℝ)) = (Nat.card α : ℝ) := by
  have hsum :
      (∑ element : α, (1 : ℝ)) =
        (Finset.univ : Finset α).card • (1 : ℝ) :=
    Finset.sum_const (1 : ℝ)
  have hcardMul :
      (Finset.univ : Finset α).card • (1 : ℝ) =
        (Nat.card α : ℝ) * (1 : ℝ) :=
    fintype_univ_nsmul_eq_natCard_mul α (1 : ℝ)
  have hmul : (Nat.card α : ℝ) * (1 : ℝ) = (Nat.card α : ℝ) :=
    mul_one (Nat.card α : ℝ)
  exact Eq.trans hsum (Eq.trans hcardMul hmul)

theorem real_tsum_le_natCard_mul_of_forall_le
    {α : Type*} [Fintype α]
    (u : α → ℝ) (B : ℝ)
    (hbound : ∀ a : α, u a ≤ B) :
    (∑' a : α, u a) ≤ (Nat.card α : ℝ) * B := by
  have htsum :
      (∑' a : α, u a) = ∑ a : α, u a :=
    tsum_fintype u
  have hsum :
      (∑ a : α, u a) ≤ (Finset.univ : Finset α).card • B :=
    Finset.sum_le_card_nsmul
      (Finset.univ : Finset α)
      u
      B
      (fun a membership =>
        Eq.subst
          (motive := fun evidence : a ∈ (Finset.univ : Finset α) => u a ≤ B)
          (Subsingleton.elim (Finset.mem_univ a) membership)
          (hbound a))
  have htarget :
      (Finset.univ : Finset α).card • B = (Nat.card α : ℝ) * B :=
    fintype_univ_nsmul_eq_natCard_mul α B
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ (Nat.card α : ℝ) * B)
    htsum.symm
    (Eq.subst
      (motive := fun x : ℝ => (∑ a : α, u a) ≤ x)
      htarget
      hsum)

/-- A finite `tsum` whose terms are all at least one dominates the cardinality
of its index type. -/
theorem natCard_le_real_tsum_of_one_le
    {α : Type*} [Fintype α]
    (u : α → ℝ)
    (hone : ∀ a : α, (1 : ℝ) ≤ u a) :
    (Nat.card α : ℝ) ≤ ∑' a : α, u a := by
  have hsum :
      (∑ a : α, (1 : ℝ)) ≤ ∑ a : α, u a :=
    Finset.sum_le_sum
      (fun a membership =>
        Eq.subst
          (motive := fun evidence : a ∈ (Finset.univ : Finset α) =>
            (1 : ℝ) ≤ u a)
          (Subsingleton.elim (Finset.mem_univ a) membership)
          (hone a))
  have hsum_one_natCard :
      (∑ a : α, (1 : ℝ)) = (Nat.card α : ℝ) :=
    fintype_sum_one_eq_natCard α
  have hnatCard_le_sum :
      (Nat.card α : ℝ) ≤ ∑ a : α, u a :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ∑ a : α, u a)
      hsum_one_natCard
      hsum
  have htsum :
      (∑' a : α, u a) = ∑ a : α, u a :=
    tsum_fintype u
  exact Eq.subst
    (motive := fun x : ℝ => (Nat.card α : ℝ) ≤ x)
    htsum.symm
    hnatCard_le_sum

/-- A completed zero in a height ball contributes at least one to the
multiplicity height-ball summand. -/
theorem one_le_completedZeroMultiplicityHeightBallSummand_of_mem
    (T : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∈ completedZerosInCenteredHeightBall T) :
    (1 : ℝ) ≤ completedZeroMultiplicityHeightBallSummand T ρ := by
  have hpos :
      0 < zetaZeroMultiplicity (ρ : ℂ) :=
    zetaZeroMultiplicity_pos_of_completedZero ρ
  have hone_nat :
      1 ≤ zetaZeroMultiplicity (ρ : ℂ) :=
    hpos
  have hone_real :
      (1 : ℝ) ≤ (zetaZeroMultiplicity (ρ : ℂ) : ℝ) :=
    have hcast :
        ((1 : ℕ) : ℝ) ≤ (zetaZeroMultiplicity (ρ : ℂ) : ℝ) :=
      Nat.cast_le.mpr hone_nat
    Eq.subst
      (motive := fun x : ℝ =>
        x ≤ (zetaZeroMultiplicity (ρ : ℂ) : ℝ))
      Nat.cast_one
      hcast
  exact Eq.subst
    (motive := fun x : ℝ => (1 : ℝ) ≤ x)
    (if_pos hρ).symm
    hone_real

def completedZeroCenteredHeightShellFiber_inclusion
    (m : ℕ) :
    completedZeroCenteredHeightShellFiber m →
      {ρ : ℂ // ZetaCompletedZero ρ} :=
  fun ρ => ρ.1

theorem completedZeroCenteredHeightShellFiber_inclusion_injective
    (m : ℕ) :
    Function.Injective (completedZeroCenteredHeightShellFiber_inclusion m) :=
  fun ρ η hρη => Subtype.ext hρη

theorem one_le_heightBallSummand_on_shellFiber
    (m : ℕ) (ρ : completedZeroCenteredHeightShellFiber m) :
    (1 : ℝ) ≤ completedZeroMultiplicityHeightBallSummand
      ((m + 1 : ℕ) : ℝ)
      (completedZeroCenteredHeightShellFiber_inclusion m ρ) := by
  have hmem :
      completedZeroCenteredHeightShellFiber_inclusion m ρ ∈
        completedZerosInCenteredHeightBall ((m + 1 : ℕ) : ℝ) :=
    completedZeroCenteredHeightShell_subset_heightBall m ρ.2
  exact one_le_completedZeroMultiplicityHeightBallSummand_of_mem
    ((m + 1 : ℕ) : ℝ)
    (completedZeroCenteredHeightShellFiber_inclusion m ρ)
    hmem

theorem completedZeroCenteredHeightShellFiber_card_le_shellTsum
    (m : ℕ) [Fintype (completedZeroCenteredHeightShellFiber m)] :
    (Nat.card (completedZeroCenteredHeightShellFiber m) : ℝ) ≤
      ∑' ρ : completedZeroCenteredHeightShellFiber m,
        completedZeroMultiplicityHeightBallSummand ((m + 1 : ℕ) : ℝ)
          (completedZeroCenteredHeightShellFiber_inclusion m ρ) :=
  natCard_le_real_tsum_of_one_le
    (fun ρ : completedZeroCenteredHeightShellFiber m =>
      completedZeroMultiplicityHeightBallSummand ((m + 1 : ℕ) : ℝ)
        (completedZeroCenteredHeightShellFiber_inclusion m ρ))
    (one_le_heightBallSummand_on_shellFiber m)

theorem completedZeroCenteredHeightShellFiber_tsum_le_total
    (m : ℕ) [Fintype (completedZeroCenteredHeightShellFiber m)] :
    (∑' ρ : completedZeroCenteredHeightShellFiber m,
        completedZeroMultiplicityHeightBallSummand ((m + 1 : ℕ) : ℝ)
          (completedZeroCenteredHeightShellFiber_inclusion m ρ)) ≤
      completedZeroMultiplicityCountingInCenteredHeightBall
        ((m + 1 : ℕ) : ℝ) :=
  tsum_comp_le_tsum_of_inj
    (summable_completedZeroMultiplicityHeightBallSummand ((m + 1 : ℕ) : ℝ))
    (completedZeroMultiplicityHeightBallSummand_nonnegative_pointwise
      ((m + 1 : ℕ) : ℝ))
    (completedZeroCenteredHeightShellFiber_inclusion_injective m)

/-- The unweighted shell cardinal is bounded by the multiplicity count in the
containing height ball. -/
theorem completedZeroCenteredHeightShell_unweightedCount_le_multiplicityCounting
    (m : ℕ) :
    (Nat.card (completedZeroCenteredHeightShellFiber m) : ℝ) ≤
      completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) := by
  haveI : Fintype (completedZeroCenteredHeightShellFiber m) :=
    (finite_completedZeroCenteredHeightShell m).fintype
  exact le_trans
    (completedZeroCenteredHeightShellFiber_card_le_shellTsum m)
    (completedZeroCenteredHeightShellFiber_tsum_le_total m)

end

end LFunctions
end Boundary
