import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualIncrementSeparation

/-!
# Full lattice separation for dual shifted increments

The dual shifted derivative is negative, hence every shifted increment is
negative by the mean-value theorem.  Separation from the absolute principal
levels `2*pi*q` therefore gives separation from all negative lattice points.
Nonnegative lattice points are farther away than zero.  This owner packages
the complete integer-lattice statement consumed by the first-derivative bound.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseDualShiftedIncrement_neg
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h n : ℕ} (hh : 0 < h) (hn : 0 < n) :
    Complex.logarithmicPhaseDualShiftedIncrement t h n < 0 := by
  rcases Complex.exists_dualShiftDerivative_eq_increment t ht hh hn with
    ⟨c, hc, hderiv⟩
  have hcPos := lt_of_lt_of_le (Nat.cast_pos.mpr hn) (le_of_lt hc.1)
  have hnegative :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_neg
      t ht (Nat.cast_pos.mpr hh) hcPos
  exact Eq.subst (motive := fun z : ℝ => z < 0) hderiv hnegative

theorem Real.abs_sub_nonnegative_level_ge_abs_of_neg
    {x level : ℝ} (hx : x < 0) (hlevel : 0 ≤ level) :
    |x| ≤ |x - level| := by
  have hxAbs : |x| = -x := abs_of_neg hx
  have hdiffNeg : x - level < 0 :=
    lt_of_lt_of_le hx (sub_nonpos.mpr hlevel)
  have hdiffAbs : |x - level| = -(x - level) := abs_of_neg hdiffNeg
  have hnegLe : -x ≤ -(x - level) := by
    exact neg_le_neg (sub_le_self x hlevel)
  exact Eq.subst (motive := fun z : ℝ => z ≤ |x - level|)
    hxAbs.symm
    (Eq.subst (motive := fun z : ℝ => -x ≤ z) hdiffAbs.symm hnegLe)

theorem Real.abs_neg_sub_neg_level
    (x level : ℝ) :
    |(-x) - (-level)| = |x - level| := by
  have hneg : (-x) - (-level) = -(x - level) := by
    exact Eq.trans (sub_neg_eq_add (-x) level)
      (Eq.trans (add_comm (-x) level)
        (sub_eq_add_neg level x).symm)
  exact Eq.trans (congrArg abs hneg) (abs_neg (x - level))

theorem Complex.logarithmicPhaseDualShiftedIncrement_distance_nonnegativeMode
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (q : ℕ) :
    |Complex.logarithmicPhaseDualShiftedIncrement t h n| ≤
      |Complex.logarithmicPhaseDualShiftedIncrement t h n -
        2 * Real.pi * (q : ℝ)| := by
  exact Real.abs_sub_nonnegative_level_ge_abs_of_neg
    (Complex.logarithmicPhaseDualShiftedIncrement_neg t ht hh hn)
    (mul_nonneg (le_of_lt Complex.two_mul_pi_pos) (Nat.cast_nonneg q))

theorem Complex.logarithmicPhaseDualShiftedIncrement_distance_negativeMode_eq
    (t : ℝ) (h n q : ℕ)
    (hnegative : Complex.logarithmicPhaseDualShiftedIncrement t h n < 0) :
    |Complex.logarithmicPhaseDualShiftedIncrement t h n -
        2 * Real.pi * (-(q : ℝ))| =
      | |Complex.logarithmicPhaseDualShiftedIncrement t h n| -
          2 * Real.pi * (q : ℝ)| := by
  let increment := Complex.logarithmicPhaseDualShiftedIncrement t h n
  let level := 2 * Real.pi * (q : ℝ)
  have hlevelNeg : 2 * Real.pi * (-(q : ℝ)) = -level := by
    exact Eq.trans (mul_neg (2 * Real.pi) (q : ℝ)) rfl
  have hincrementAbs : |increment| = -increment := abs_of_neg hnegative
  exact Eq.trans
    (congrArg (fun z : ℝ => |increment - z|) hlevelNeg)
    (Eq.trans
      (Real.abs_neg_sub_neg_level increment level).symm
      (congrArg (fun z : ℝ => |z - level|) hincrementAbs.symm))

theorem Complex.logarithmicPhaseDualCrossingLevels_downward_closed
    (t h eta L : ℝ) {q r : ℕ}
    (hq : q ∈ Complex.logarithmicPhaseDualCrossingLevels t h eta L)
    (hrq : r ≤ q) :
    r ∈ Complex.logarithmicPhaseDualCrossingLevels t h eta L := by
  have hqBounds :=
    (Complex.mem_logarithmicPhaseDualCrossingLevels_iff t h eta L q).mp hq
  exact
    (Complex.mem_logarithmicPhaseDualCrossingLevels_iff t h eta L r).mpr
      (And.intro (Nat.zero_le r) (le_trans hrq hqBounds.2))

theorem Complex.logarithmicPhaseDualCrossingLevel_zero_mem
    (t h eta L : ℝ) :
    0 ∈ Complex.logarithmicPhaseDualCrossingLevels t h eta L := by
  exact
    (Complex.mem_logarithmicPhaseDualCrossingLevels_iff t h eta L 0).mpr
      (And.intro (Nat.zero_le 0) (Nat.zero_le _))

theorem Complex.logarithmicPhaseDualSeparated_increment_distance_intMode
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M n : ℕ} (hh : 0 < h) (hK : 0 < K)
    {eta : ℝ}
    (hn : n ∈
      Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M)
    (k : ℤ)
    (hkRepresented :
      k.natAbs ∈ Complex.logarithmicPhaseDualCrossingLevels
        t (h : ℝ) eta (K : ℝ)) :
    eta <
      |Complex.logarithmicPhaseDualShiftedIncrement t h n -
        2 * Real.pi * (k : ℝ)| := by
  have hnBlock :=
    (Complex.mem_logarithmicPhaseDualDiscreteSeparatedModes_iff
      t h eta K M n).mp hn
  have hnPos := lt_of_lt_of_le hK (Finset.mem_Icc.mp hnBlock.1).1
  match k with
  | ofNat q =>
      have hzero := Complex.logarithmicPhaseDualCrossingLevel_zero_mem
        t (h : ℝ) eta (K : ℝ)
      have hbase :=
        Complex.logarithmicPhaseDualSeparated_increment_abs_ge_eta
          t ht hh hK hn hzero
      exact lt_of_lt_of_le hbase
        (Complex.logarithmicPhaseDualShiftedIncrement_distance_nonnegativeMode
          t ht hh hnPos q)
  | negSucc q =>
      let r := q + 1
      have hrNatAbs : Int.natAbs (Int.negSucc q) = r := rfl
      have hrRepresented :
          r ∈ Complex.logarithmicPhaseDualCrossingLevels
            t (h : ℝ) eta (K : ℝ) :=
        Eq.subst
          (motive := fun z : ℕ =>
            z ∈ Complex.logarithmicPhaseDualCrossingLevels
              t (h : ℝ) eta (K : ℝ))
          hrNatAbs hkRepresented
      have hgap :=
        Complex.logarithmicPhaseDualSeparated_increment_gap
          t ht hh hK hn r hrRepresented
      have hcast : ((Int.negSucc q : ℤ) : ℝ) = -(r : ℝ) := by
        exact Int.cast_negSucc q
      exact Eq.subst
        (motive := fun value : ℝ =>
          eta <
            |Complex.logarithmicPhaseDualShiftedIncrement t h n -
              2 * Real.pi * value|)
        hcast.symm
        (Eq.subst (motive := fun z : ℝ => eta < z)
          (Complex.logarithmicPhaseDualShiftedIncrement_distance_negativeMode_eq
            t h n r
            (Complex.logarithmicPhaseDualShiftedIncrement_neg t ht hh hnPos)).symm hgap)

end

end LFunctions
end Boundary
