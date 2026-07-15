import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualContinuousIncrement

/-!
# Midpoint branch cuts for centered reduction

Resonance collars surround `2*pi*ℤ`.  They control cancellation, but centered
reduction to `Ioc(-pi,pi)` changes branch at the distinct midpoint lattice
`(2*q+1)*pi`.  This owner defines the finite midpoint-cut family and marks
every natural unit cell whose continuous increment image meets one of those
cuts.  Deleting these cells in addition to resonance collars makes the reduced
increment branch constant on each surviving run.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualBranchCutLevel
    (q : ℕ) : ℝ :=
  (2 * (q : ℝ) + 1) * Real.pi

def Complex.logarithmicPhaseDualBranchCutUpper
    (t h K : ℝ) : ℕ :=
  ⌊
    |Complex.logarithmicPhaseDualContinuousIncrement t h K| /
      (2 * Real.pi) + 1 / 2
  ⌋₊

def Complex.logarithmicPhaseDualBranchCutLevels
    (t h K : ℝ) : Finset ℕ :=
  Finset.Icc 0 (Complex.logarithmicPhaseDualBranchCutUpper t h K)

def Complex.logarithmicPhaseDualBranchCutCell
    (t : ℝ) (h n q : ℕ) : Prop :=
  ∃ x ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ),
    |Complex.logarithmicPhaseDualContinuousIncrement t (h : ℝ) x| =
      Complex.logarithmicPhaseDualBranchCutLevel q

def Complex.logarithmicPhaseDualDiscreteBranchCutModes
    (t : ℝ) (h K M : ℕ) : Finset ℕ :=
  (Finset.Icc K M).filter
    (fun n : ℕ =>
      ∃ q ∈ Complex.logarithmicPhaseDualBranchCutLevels
          t (h : ℝ) (K : ℝ),
        Complex.logarithmicPhaseDualBranchCutCell t h n q)

def Complex.logarithmicPhaseDualDeletedModes
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) : Finset ℕ :=
  Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M ∪
    Complex.logarithmicPhaseDualDiscreteBranchCutModes t h K M

theorem Complex.mem_logarithmicPhaseDualBranchCutLevels_iff
    (t h K : ℝ) (q : ℕ) :
    q ∈ Complex.logarithmicPhaseDualBranchCutLevels t h K ↔
      0 ≤ q ∧ q ≤ Complex.logarithmicPhaseDualBranchCutUpper t h K := by
  exact Finset.mem_Icc

theorem Complex.logarithmicPhaseDualBranchCutLevels_card
    (t h K : ℝ) :
    (Complex.logarithmicPhaseDualBranchCutLevels t h K).card =
      Complex.logarithmicPhaseDualBranchCutUpper t h K + 1 := by
  unfold Complex.logarithmicPhaseDualBranchCutLevels
  exact Eq.trans (Nat.card_Icc 0 _)
    (Nat.sub_zero _)

theorem Complex.mem_logarithmicPhaseDualDiscreteBranchCutModes_iff
    (t : ℝ) (h K M n : ℕ) :
    n ∈ Complex.logarithmicPhaseDualDiscreteBranchCutModes t h K M ↔
      n ∈ Finset.Icc K M ∧
        ∃ q ∈ Complex.logarithmicPhaseDualBranchCutLevels
            t (h : ℝ) (K : ℝ),
          Complex.logarithmicPhaseDualBranchCutCell t h n q := by
  exact Finset.mem_filter

theorem Complex.logarithmicPhaseDualDiscreteBranchCutModes_subset_block
    (t : ℝ) (h K M : ℕ) :
    Complex.logarithmicPhaseDualDiscreteBranchCutModes t h K M ⊆
      Finset.Icc K M := by
  exact Finset.filter_subset _ _

theorem Complex.logarithmicPhaseDualDeletedModes_subset_block
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualDeletedModes t h eta K M ⊆
      Finset.Icc K M := by
  intro n hn
  match Finset.mem_union.mp hn with
  | Or.inl hcollar =>
      exact Complex.logarithmicPhaseDualDiscreteCollarModes_subset_block
        t h eta K M hcollar
  | Or.inr hcut =>
      exact Complex.logarithmicPhaseDualDiscreteBranchCutModes_subset_block
        t h K M hcut

theorem Complex.logarithmicPhaseDualDiscreteCollarModes_subset_deleted
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M ⊆
      Complex.logarithmicPhaseDualDeletedModes t h eta K M := by
  exact Finset.subset_union_left

theorem Complex.logarithmicPhaseDualDiscreteBranchCutModes_subset_deleted
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualDiscreteBranchCutModes t h K M ⊆
      Complex.logarithmicPhaseDualDeletedModes t h eta K M := by
  exact Finset.subset_union_right

theorem Complex.logarithmicPhaseDualDeletedModes_card_le_add
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    (Complex.logarithmicPhaseDualDeletedModes t h eta K M).card ≤
      (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M).card +
        (Complex.logarithmicPhaseDualDiscreteBranchCutModes t h K M).card := by
  unfold Complex.logarithmicPhaseDualDeletedModes
  exact Finset.card_union_le _ _

theorem Complex.logarithmicPhaseDualBranchCutLevel_pos
    (q : ℕ) :
    0 < Complex.logarithmicPhaseDualBranchCutLevel q := by
  unfold Complex.logarithmicPhaseDualBranchCutLevel
  have hcoefficient : 0 < 2 * (q : ℝ) + 1 :=
    add_pos_of_nonneg_of_pos
      (mul_nonneg (le_of_lt zero_lt_two) (Nat.cast_nonneg q)) zero_lt_one
  exact mul_pos hcoefficient Real.pi_pos

theorem Complex.logarithmicPhaseDualBranchCutLevel_strictMono :
    StrictMono Complex.logarithmicPhaseDualBranchCutLevel := by
  intro q r hqr
  unfold Complex.logarithmicPhaseDualBranchCutLevel
  have hcast : (q : ℝ) < (r : ℝ) := Nat.cast_lt.mpr hqr
  have hscaled := mul_lt_mul_of_pos_left hcast zero_lt_two
  have hadd := add_lt_add_right hscaled 1
  exact mul_lt_mul_of_pos_right hadd Real.pi_pos

theorem Complex.logarithmicPhaseDualBranchCutLevel_succ_gap
    (q : ℕ) :
    Complex.logarithmicPhaseDualBranchCutLevel (q + 1) -
        Complex.logarithmicPhaseDualBranchCutLevel q =
      2 * Real.pi := by
  unfold Complex.logarithmicPhaseDualBranchCutLevel
  have hcastSucc : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := Nat.cast_add q 1
  calc
    (2 * ((q + 1 : ℕ) : ℝ) + 1) * Real.pi -
        (2 * (q : ℝ) + 1) * Real.pi =
      ((2 * ((q + 1 : ℕ) : ℝ) + 1) - (2 * (q : ℝ) + 1)) * Real.pi := by
        exact (sub_mul _ _ Real.pi).symm
    _ = ((2 * ((q : ℝ) + 1) + 1) - (2 * (q : ℝ) + 1)) * Real.pi := by
      exact congrArg
        (fun z : ℝ => ((2 * z + 1) - (2 * (q : ℝ) + 1)) * Real.pi)
        hcastSucc
    _ = 2 * Real.pi := by exact rfl

end

end LFunctions
end Boundary
