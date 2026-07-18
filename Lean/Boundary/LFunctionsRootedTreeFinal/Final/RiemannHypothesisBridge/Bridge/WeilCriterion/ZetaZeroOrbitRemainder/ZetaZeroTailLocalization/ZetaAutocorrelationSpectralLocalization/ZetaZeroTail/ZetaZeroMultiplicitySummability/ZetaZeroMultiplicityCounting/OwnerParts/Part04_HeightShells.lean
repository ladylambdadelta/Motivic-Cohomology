import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.OwnerParts.Part03_MultiplicityGrowth

namespace Boundary
namespace LFunctions

noncomputable section

/-- Every real height at least one belongs to a natural unit shell. -/
theorem exists_nat_unitShell_of_one_le
    {x : ℝ}
    (hx : 1 ≤ x) :
    ∃ m : ℕ, ((m : ℕ) : ℝ) ≤ x ∧ x < ((m + 1 : ℕ) : ℝ) := by
  exact ⟨Nat.floor x,
    Nat.floor_le (le_trans zero_le_one hx),
    have hcast_one : ((1 : ℕ) : ℝ) = 1 :=
      Nat.cast_one
    have hcast_succ :
        (((Nat.floor x + 1 : ℕ) : ℝ)) =
          ((Nat.floor x : ℕ) : ℝ) + 1 :=
      Eq.trans
        (Nat.cast_add (Nat.floor x) 1)
        (congrArg
          (fun y : ℝ => ((Nat.floor x : ℕ) : ℝ) + y)
          hcast_one)
    Eq.subst
      (motive := fun y : ℝ => x < y)
      hcast_succ.symm
      (Nat.lt_floor_add_one x)⟩

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


end

end LFunctions
end Boundary
