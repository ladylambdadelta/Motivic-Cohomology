import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualIncrementLattice

/-!
# Separation from unrepresented dual lattice levels

Levels beyond the canonical represented range exceed the left-end derivative
by more than the collar width.  Every increment on the block is a derivative
value from a cell to the right of that endpoint, so its absolute value is no
larger than the left-end value.  Thus unrepresented negative lattice levels
are automatically separated.  Together with represented-level separation this
gives the full integer-lattice statement.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseDualShiftedIncrement_abs_le_leftDerivative
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M n : ℕ} (hh : 0 < h) (hK : 0 < K)
    (hnBlock : n ∈ Finset.Icc K M) :
    |Complex.logarithmicPhaseDualShiftedIncrement t h n| ≤
      |Complex.logarithmicPhaseDualShiftedDifferenceDerivative
        t (h : ℝ) (K : ℝ)| := by
  have hnPos := lt_of_lt_of_le hK (Finset.mem_Icc.mp hnBlock).1
  rcases Complex.exists_dualShiftDerivative_eq_increment t ht hh hnPos with
    ⟨c, hc, hderiv⟩
  have hKReal : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  have hcPos := lt_of_lt_of_le (Nat.cast_pos.mpr hnPos) (le_of_lt hc.1)
  have hKc : (K : ℝ) ≤ c := le_trans
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hnBlock).1)
    (le_of_lt hc.1)
  have hanti :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_antitoneOn
      t (le_of_lt (Nat.cast_pos.mpr hh)) hKReal hcPos hKc
  exact Eq.subst (motive := fun z : ℝ => |z| ≤ _)
    hderiv hanti

theorem Complex.logarithmicPhaseDual_unrepresented_level_gt_leftDerivative_add_eta
    (t : ℝ) {h eta L : ℝ} (heta : 0 ≤ eta)
    {q : ℕ}
    (hq : q ∉ Complex.logarithmicPhaseDualCrossingLevels t h eta L) :
    |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h L| + eta <
      Complex.logarithmicPhaseDualPrincipalLevel q := by
  have hqUpper :
      Complex.logarithmicPhaseDualCrossingLevelUpper t h eta L < q := by
    have hnotBounds : ¬ q ≤
        Complex.logarithmicPhaseDualCrossingLevelUpper t h eta L := by
      intro hqLe
      exact hq
        ((Complex.mem_logarithmicPhaseDualCrossingLevels_iff
          t h eta L q).mpr (And.intro (Nat.zero_le q) hqLe))
    exact Nat.lt_of_not_ge hnotBounds
  have hfloorRatio :=
    Complex.logarithmicPhaseDualCrossingLevelUpper_ratio_lt_succ
      t h eta L
  have hsuccLeQ :
      Complex.logarithmicPhaseDualCrossingLevelUpper t h eta L + 1 ≤ q :=
    Nat.succ_le_of_lt hqUpper
  have hratioQ :
      (|Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h L| + eta) /
          (2 * Real.pi) < (q : ℝ) :=
    lt_of_lt_of_le hfloorRatio (Nat.cast_le.mpr hsuccLeQ)
  have htwoPi := Complex.two_mul_pi_pos
  have hscaled := (div_lt_iff₀ htwoPi).mp hratioQ
  unfold Complex.logarithmicPhaseDualPrincipalLevel
  exact Eq.subst (motive := fun z : ℝ => _ < z)
    (mul_comm (q : ℝ) (2 * Real.pi)) hscaled

theorem Real.abs_difference_level_eq_level_sub_abs_of_le
    {x level : ℝ} (hx : x ≤ level) :
    |x - level| = level - x := by
  exact Eq.trans (abs_of_nonpos (sub_nonpos.mpr hx))
    (neg_sub x level)

theorem Complex.logarithmicPhaseDualSeparated_increment_gap_unrepresented
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M n : ℕ} (hh : 0 < h) (hK : 0 < K)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hn : n ∈
      Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M)
    {q : ℕ}
    (hq : q ∉ Complex.logarithmicPhaseDualCrossingLevels
      t (h : ℝ) eta (K : ℝ)) :
    eta <
      | |Complex.logarithmicPhaseDualShiftedIncrement t h n| -
          Complex.logarithmicPhaseDualPrincipalLevel q | := by
  have hnMembership :=
    (Complex.mem_logarithmicPhaseDualDiscreteSeparatedModes_iff
      t h eta K M n).mp hn
  have hincLe :=
    Complex.logarithmicPhaseDualShiftedIncrement_abs_le_leftDerivative
      t ht hh hK hnMembership.1
  have hlevel :=
    Complex.logarithmicPhaseDual_unrepresented_level_gt_leftDerivative_add_eta
      t heta hq
  have hincEta :
      |Complex.logarithmicPhaseDualShiftedIncrement t h n| + eta <
        Complex.logarithmicPhaseDualPrincipalLevel q :=
    lt_of_le_of_lt (add_le_add_right hincLe eta) hlevel
  have hincLevel :
      |Complex.logarithmicPhaseDualShiftedIncrement t h n| ≤
        Complex.logarithmicPhaseDualPrincipalLevel q :=
    le_trans (le_add_of_nonneg_right heta) (le_of_lt hincEta)
  have hdifference :
      | |Complex.logarithmicPhaseDualShiftedIncrement t h n| -
          Complex.logarithmicPhaseDualPrincipalLevel q | =
        Complex.logarithmicPhaseDualPrincipalLevel q -
          |Complex.logarithmicPhaseDualShiftedIncrement t h n| :=
    Real.abs_difference_level_eq_level_sub_abs_of_le hincLevel
  have hetaGap :
      eta < Complex.logarithmicPhaseDualPrincipalLevel q -
        |Complex.logarithmicPhaseDualShiftedIncrement t h n| :=
    sub_lt_iff_lt_add.mpr
      (Eq.subst (motive := fun z : ℝ => _ < z)
        (add_comm
          |Complex.logarithmicPhaseDualShiftedIncrement t h n| eta)
        hincEta)
  exact Eq.subst (motive := fun z : ℝ => eta < z)
    hdifference.symm hetaGap

theorem Complex.logarithmicPhaseDualSeparated_increment_gap_allNatLevels
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M n : ℕ} (hh : 0 < h) (hK : 0 < K)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hn : n ∈
      Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M)
    (q : ℕ) :
    eta <
      | |Complex.logarithmicPhaseDualShiftedIncrement t h n| -
          Complex.logarithmicPhaseDualPrincipalLevel q | := by
  match Classical.em
    (q ∈ Complex.logarithmicPhaseDualCrossingLevels
      t (h : ℝ) eta (K : ℝ)) with
  | Or.inl hq =>
      exact Complex.logarithmicPhaseDualSeparated_increment_gap
        t ht hh hK hn q hq
  | Or.inr hq =>
      exact Complex.logarithmicPhaseDualSeparated_increment_gap_unrepresented
        t ht hh hK heta hn hq

theorem Complex.logarithmicPhaseDualSeparated_increment_distance_allIntModes
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M n : ℕ} (hh : 0 < h) (hK : 0 < K)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hn : n ∈
      Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M)
    (k : ℤ) :
    eta <
      |Complex.logarithmicPhaseDualShiftedIncrement t h n -
        2 * Real.pi * (k : ℝ)| := by
  have hnMembership :=
    (Complex.mem_logarithmicPhaseDualDiscreteSeparatedModes_iff
      t h eta K M n).mp hn
  have hnPos := lt_of_lt_of_le hK (Finset.mem_Icc.mp hnMembership.1).1
  match k with
  | ofNat q =>
      have hzeroGap :=
        Complex.logarithmicPhaseDualSeparated_increment_gap_allNatLevels
          t ht hh hK heta hn 0
      have hzeroLevel : Complex.logarithmicPhaseDualPrincipalLevel 0 = 0 := by
        rfl
      have hbase : eta <
          |Complex.logarithmicPhaseDualShiftedIncrement t h n| := by
        exact Eq.subst (motive := fun z : ℝ => eta < z)
          (Eq.trans
            (congrArg abs
              (Eq.trans
                (congrArg
                  (fun level : ℝ =>
                    |Complex.logarithmicPhaseDualShiftedIncrement t h n| - level)
                  hzeroLevel)
                (sub_zero _)))
            (abs_abs _)).symm hzeroGap
      exact lt_of_lt_of_le hbase
        (Complex.logarithmicPhaseDualShiftedIncrement_distance_nonnegativeMode
          t ht hh hnPos q)
  | negSucc q =>
      let r := q + 1
      have hgap :=
        Complex.logarithmicPhaseDualSeparated_increment_gap_allNatLevels
          t ht hh hK heta hn r
      have hcast : ((Int.negSucc q : ℤ) : ℝ) = -(r : ℝ) :=
        Int.cast_negSucc q
      exact Eq.subst
        (motive := fun value : ℝ =>
          eta <
            |Complex.logarithmicPhaseDualShiftedIncrement t h n -
              2 * Real.pi * value|)
        hcast.symm
        (Eq.subst (motive := fun z : ℝ => eta < z)
          (Complex.logarithmicPhaseDualShiftedIncrement_distance_negativeMode_eq
            t h n r
            (Complex.logarithmicPhaseDualShiftedIncrement_neg t ht hh hnPos)).symm
          hgap)

end

end LFunctions
end Boundary
