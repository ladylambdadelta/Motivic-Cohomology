import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualCrossingRange

/-!
# Discrete collar partition of a dual shifted-correlation block

The continuous derivative-value collar union is pulled back to a natural
integer interval.  The resulting collar and separated index families are
definitionally disjoint and cover the whole block.  This owner proves the exact
finite-sum decomposition, the cardinality bound for the collar contribution,
and principal-level separation for every complementary index.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualShiftCorrelationTerm
    (t : ℝ) (h n : ℕ) : ℂ :=
  Complex.exp
    (Complex.I *
      (Complex.logarithmicPhaseDualShiftedDifference
        t (h : ℝ) (n : ℝ) : ℂ))

def Complex.logarithmicPhaseDualDiscreteCollarModes
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) : Finset ℕ :=
  (Finset.Icc K M).filter
    (fun n : ℕ =>
      ∃ x : ℝ,
        x ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ) ∧
          x ∈ Complex.logarithmicPhaseDualCrossingCollarUnion
            t (h : ℝ) eta (K : ℝ) ((M + 1 : ℕ) : ℝ)
            (Complex.logarithmicPhaseDualCrossingLevels
              t (h : ℝ) eta (K : ℝ)))

def Complex.logarithmicPhaseDualDiscreteSeparatedModes
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) : Finset ℕ :=
  Finset.Icc K M \
    Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M

theorem Complex.mem_logarithmicPhaseDualDiscreteCollarModes_iff
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M n : ℕ) :
    n ∈ Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M ↔
      n ∈ Finset.Icc K M ∧
        ∃ x : ℝ,
          x ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ) ∧
            x ∈ Complex.logarithmicPhaseDualCrossingCollarUnion
              t (h : ℝ) eta (K : ℝ) ((M + 1 : ℕ) : ℝ)
              (Complex.logarithmicPhaseDualCrossingLevels
                t (h : ℝ) eta (K : ℝ)) := by
  exact Finset.mem_filter

theorem Complex.mem_logarithmicPhaseDualDiscreteSeparatedModes_iff
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M n : ℕ) :
    n ∈ Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M ↔
      n ∈ Finset.Icc K M ∧
        n ∉ Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M := by
  exact Finset.mem_sdiff

theorem Complex.logarithmicPhaseDualDiscreteCollarModes_subset_block
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M ⊆
      Finset.Icc K M := by
  exact Finset.filter_subset _ _

theorem Complex.logarithmicPhaseDualDiscreteSeparatedModes_subset_block
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M ⊆
      Finset.Icc K M := by
  exact Finset.sdiff_subset

theorem Complex.logarithmicPhaseDualDiscreteCollar_disjoint_separated
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    Disjoint
      (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M)
      (Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M) := by
  unfold Complex.logarithmicPhaseDualDiscreteSeparatedModes
  exact Finset.disjoint_sdiff_right

theorem Complex.logarithmicPhaseDualDiscreteCollar_union_separated
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M ∪
        Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M =
      Finset.Icc K M := by
  let C := Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M
  let B := Finset.Icc K M
  have hCB : C ⊆ B :=
    Complex.logarithmicPhaseDualDiscreteCollarModes_subset_block
      t h eta K M
  unfold Complex.logarithmicPhaseDualDiscreteSeparatedModes
  exact Finset.union_sdiff_of_subset hCB

theorem Complex.logarithmicPhaseDualShiftCorrelationSum_eq_collar_add_separated
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    (∑ n ∈ Finset.Icc K M,
      Complex.logarithmicPhaseDualShiftCorrelationTerm t h n) =
      (∑ n ∈
        Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M,
        Complex.logarithmicPhaseDualShiftCorrelationTerm t h n) +
      ∑ n ∈
        Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M,
        Complex.logarithmicPhaseDualShiftCorrelationTerm t h n := by
  let C := Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M
  let G := Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M
  have hdisjoint :=
    Complex.logarithmicPhaseDualDiscreteCollar_disjoint_separated
      t h eta K M
  have hunion :=
    Complex.logarithmicPhaseDualDiscreteCollar_union_separated
      t h eta K M
  have hsumUnion := Finset.sum_union hdisjoint
    (f := Complex.logarithmicPhaseDualShiftCorrelationTerm t h)
  exact Eq.trans
    (congrArg
      (fun S : Finset ℕ =>
        ∑ n ∈ S,
          Complex.logarithmicPhaseDualShiftCorrelationTerm t h n)
      hunion.symm)
    hsumUnion

theorem Complex.logarithmicPhaseDualShiftCorrelationTerm_norm
    (t : ℝ) (h n : ℕ) :
    ‖Complex.logarithmicPhaseDualShiftCorrelationTerm t h n‖ = 1 := by
  unfold Complex.logarithmicPhaseDualShiftCorrelationTerm
  exact Complex.norm_exp_ofReal_mul_I
    (Complex.logarithmicPhaseDualShiftedDifference t (h : ℝ) (n : ℝ))

theorem Complex.norm_logarithmicPhaseDualDiscreteCollarSum_le_card
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    ‖∑ n ∈
        Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M,
        Complex.logarithmicPhaseDualShiftCorrelationTerm t h n‖ ≤
      ((Complex.logarithmicPhaseDualDiscreteCollarModes
        t h eta K M).card : ℝ) := by
  have hnormSum := norm_sum_le
    (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M)
    (Complex.logarithmicPhaseDualShiftCorrelationTerm t h)
  have hnorms :
      (∑ n ∈
        Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M,
        ‖Complex.logarithmicPhaseDualShiftCorrelationTerm t h n‖) =
      ∑ n ∈
        Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M,
        (1 : ℝ) := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        Complex.logarithmicPhaseDualShiftCorrelationTerm_norm t h n)
  have hones := Finset.sum_const_zero
    (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M)
    (1 : ℝ)
  exact le_trans hnormSum
    (le_of_eq
      (Eq.trans hnorms
        (Eq.trans hones
          (mul_one
            ((Complex.logarithmicPhaseDualDiscreteCollarModes
              t h eta K M).card : ℝ)))))

theorem Complex.logarithmicPhaseDualDiscreteSeparated_cellwise_gap
    (t : ℝ) {h : ℕ} (hh : 0 < h)
    {eta : ℝ} {K M n : ℕ} (hK : 0 < K)
    (hn : n ∈
      Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M) :
    ∀ x ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ),
      ∀ q ∈ Complex.logarithmicPhaseDualCrossingLevels
          t (h : ℝ) eta (K : ℝ),
        eta <
          | |Complex.logarithmicPhaseDualShiftedDifferenceDerivative
                t (h : ℝ) x| -
              Complex.logarithmicPhaseDualPrincipalLevel q | := by
  intro x hxCell q hq
  have hnMembership :=
    (Complex.mem_logarithmicPhaseDualDiscreteSeparatedModes_iff
      t h eta K M n).mp hn
  have hnNotCollar := hnMembership.2
  have hxInterval : x ∈ Set.Icc (K : ℝ) ((M + 1 : ℕ) : ℝ) := by
    have hnBounds := Finset.mem_Icc.mp hnMembership.1
    have hleft := le_trans (Nat.cast_le.mpr hnBounds.1) hxCell.1
    have hright := le_trans hxCell.2
      (Nat.cast_le.mpr (Nat.add_le_add_right hnBounds.2 1))
    exact And.intro hleft hright
  have hnOutsideUnion :
      x ∉
        Complex.logarithmicPhaseDualCrossingCollarUnion
          t (h : ℝ) eta (K : ℝ) ((M + 1 : ℕ) : ℝ)
          (Complex.logarithmicPhaseDualCrossingLevels
            t (h : ℝ) eta (K : ℝ)) := by
    intro hxUnion
    exact hnNotCollar
      ((Complex.mem_logarithmicPhaseDualDiscreteCollarModes_iff
        t h eta K M n).mpr
        (And.intro hnMembership.1
          (Exists.intro x (And.intro hxCell hxUnion))))
  have hnGap :
      x ∈
        Complex.logarithmicPhaseDualSeparatedGap
          t (h : ℝ) eta (K : ℝ) ((M + 1 : ℕ) : ℝ)
          (Complex.logarithmicPhaseDualCrossingLevels
            t (h : ℝ) eta (K : ℝ)) :=
    And.intro hxInterval hnOutsideUnion
  exact
    ((Complex.mem_logarithmicPhaseDualSeparatedGap_iff
      t (h : ℝ) eta (K : ℝ) ((M + 1 : ℕ) : ℝ)
      (Complex.logarithmicPhaseDualCrossingLevels
        t (h : ℝ) eta (K : ℝ)) x).mp hnGap).2 q hq

theorem Complex.norm_logarithmicPhaseDualShiftCorrelationSum_le_parts
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    ‖∑ n ∈ Finset.Icc K M,
      Complex.logarithmicPhaseDualShiftCorrelationTerm t h n‖ ≤
      ‖∑ n ∈
        Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M,
        Complex.logarithmicPhaseDualShiftCorrelationTerm t h n‖ +
      ‖∑ n ∈
        Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M,
        Complex.logarithmicPhaseDualShiftCorrelationTerm t h n‖ := by
  have hsplit :=
    Complex.logarithmicPhaseDualShiftCorrelationSum_eq_collar_add_separated
      t h eta K M
  exact Eq.subst (motive := fun z : ℂ => ‖z‖ ≤ _)
    hsplit.symm (norm_add_le _ _)

end

end LFunctions
end Boundary
