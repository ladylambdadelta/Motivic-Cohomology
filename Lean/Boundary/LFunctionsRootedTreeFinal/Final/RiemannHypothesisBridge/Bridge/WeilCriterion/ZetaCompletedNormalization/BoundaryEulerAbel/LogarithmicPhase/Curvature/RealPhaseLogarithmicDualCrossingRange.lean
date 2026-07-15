import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualCollarLength

/-!
# Finite represented principal-level range

The absolute dual shifted derivative is antitone on the positive half-line.
Consequently every principal collar meeting `[L,U]` has level at most the
left-end derivative plus the collar width.  Dividing by `2*pi` and taking the
natural floor gives a canonical finite range of all represented positive
levels.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualCrossingLevelUpper
    (t h eta L : ℝ) : ℕ :=
  ⌊
    (|Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h L| + eta) /
      (2 * Real.pi)
  ⌋₊

def Complex.logarithmicPhaseDualCrossingLevels
    (t h eta L : ℝ) : Finset ℕ :=
  Finset.Icc 0
    (Complex.logarithmicPhaseDualCrossingLevelUpper t h eta L)

theorem Complex.mem_logarithmicPhaseDualCrossingLevels_iff
    (t h eta L : ℝ) (q : ℕ) :
    q ∈ Complex.logarithmicPhaseDualCrossingLevels t h eta L ↔
      0 ≤ q ∧
        q ≤ Complex.logarithmicPhaseDualCrossingLevelUpper t h eta L := by
  exact Finset.mem_Icc

theorem Complex.logarithmicPhaseDualCrossingLevels_card
    (t h eta L : ℝ) :
    (Complex.logarithmicPhaseDualCrossingLevels t h eta L).card =
      Complex.logarithmicPhaseDualCrossingLevelUpper t h eta L + 1 := by
  unfold Complex.logarithmicPhaseDualCrossingLevels
  have hcard := Nat.card_Icc 0
    (Complex.logarithmicPhaseDualCrossingLevelUpper t h eta L)
  have hnormalize :
      Complex.logarithmicPhaseDualCrossingLevelUpper t h eta L + 1 - 0 =
        Complex.logarithmicPhaseDualCrossingLevelUpper t h eta L + 1 :=
    Nat.sub_zero _
  exact Eq.trans hcard hnormalize

theorem Complex.logarithmicPhaseDualCrossingLevelUpper_cast_le_ratio
    (t h eta L : ℝ)
    (hratio :
      0 ≤
        (|Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h L| + eta) /
          (2 * Real.pi)) :
    ((Complex.logarithmicPhaseDualCrossingLevelUpper t h eta L : ℕ) : ℝ) ≤
      (|Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h L| + eta) /
        (2 * Real.pi) := by
  unfold Complex.logarithmicPhaseDualCrossingLevelUpper
  exact Nat.floor_le hratio

theorem Complex.logarithmicPhaseDualCrossingLevelUpper_ratio_lt_succ
    (t h eta L : ℝ) :
    (|Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h L| + eta) /
        (2 * Real.pi) <
      ((Complex.logarithmicPhaseDualCrossingLevelUpper t h eta L : ℕ) : ℝ) + 1 := by
  unfold Complex.logarithmicPhaseDualCrossingLevelUpper
  exact Nat.lt_floor_add_one _

theorem Complex.logarithmicPhaseDualCrossingLevels_card_real_le_ratio
    (t h eta L : ℝ)
    (heta : 0 ≤ eta) :
    ((Complex.logarithmicPhaseDualCrossingLevels t h eta L).card : ℝ) ≤
      (|Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h L| + eta) /
        (2 * Real.pi) + 1 := by
  have hratio :
      0 ≤
        (|Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h L| + eta) /
          (2 * Real.pi) := by
    exact div_nonneg
      (add_nonneg (abs_nonneg _) heta)
      (le_of_lt Complex.two_mul_pi_pos)
  have hupper :=
    Complex.logarithmicPhaseDualCrossingLevelUpper_cast_le_ratio
      t h eta L hratio
  have hupperAdd := add_le_add_right hupper 1
  have hcastSucc :
      (((Complex.logarithmicPhaseDualCrossingLevelUpper t h eta L + 1 : ℕ) : ℝ)) =
        ((Complex.logarithmicPhaseDualCrossingLevelUpper t h eta L : ℕ) : ℝ) + 1 :=
    Nat.cast_add _ 1
  exact Eq.subst (motive := fun z : ℝ => z ≤ _)
    (Eq.trans
      (congrArg (fun n : ℕ => (n : ℝ))
        (Complex.logarithmicPhaseDualCrossingLevels_card t h eta L))
      hcastSucc).symm hupperAdd

theorem Complex.logarithmicPhaseDual_level_le_leftDerivative_add_eta_of_collar
    (t : ℝ) {h eta L U x : ℝ} {q : ℕ}
    (hh : 0 ≤ h) (hL : 0 < L)
    (hx : x ∈
      Complex.logarithmicPhaseDualCrossingCollar t h eta L U q) :
    Complex.logarithmicPhaseDualPrincipalLevel q ≤
      |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h L| + eta := by
  have hxPos : 0 < x := lt_of_lt_of_le hL hx.1.1
  have hanti :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_antitoneOn
      t hh hL hxPos hx.1.1
  have hcollarLower :
      Complex.logarithmicPhaseDualPrincipalLevel q -
          |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x| ≤
        eta := by
    have habs := neg_le_of_abs_le hx.2
    exact Eq.subst (motive := fun z : ℝ => z ≤ eta)
      (neg_sub
        |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x|
        (Complex.logarithmicPhaseDualPrincipalLevel q)).symm habs
  have hlevelX :
      Complex.logarithmicPhaseDualPrincipalLevel q ≤
        |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x| + eta := by
    exact sub_le_iff_le_add.mp hcollarLower
  exact le_trans hlevelX (add_le_add_right hanti eta)

theorem Complex.logarithmicPhaseDual_levelRatio_le_upperRatio_of_collar
    (t : ℝ) {h eta L U x : ℝ} {q : ℕ}
    (hh : 0 ≤ h) (hL : 0 < L)
    (hx : x ∈
      Complex.logarithmicPhaseDualCrossingCollar t h eta L U q) :
    (q : ℝ) ≤
      (|Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h L| + eta) /
        (2 * Real.pi) := by
  have hlevel :=
    Complex.logarithmicPhaseDual_level_le_leftDerivative_add_eta_of_collar
      t hh hL hx
  have htwoPi := Complex.two_mul_pi_pos
  unfold Complex.logarithmicPhaseDualPrincipalLevel at hlevel
  exact (le_div_iff₀ htwoPi).mpr
    (Eq.subst (motive := fun z : ℝ => z ≤ _)
      (mul_comm (q : ℝ) (2 * Real.pi)) hlevel)

theorem Complex.logarithmicPhaseDual_crossingLevel_mem_range_of_collar
    (t : ℝ) {h eta L U x : ℝ} {q : ℕ}
    (hh : 0 ≤ h) (hL : 0 < L)
    (hx : x ∈
      Complex.logarithmicPhaseDualCrossingCollar t h eta L U q) :
    q ∈ Complex.logarithmicPhaseDualCrossingLevels t h eta L := by
  have hratio :=
    Complex.logarithmicPhaseDual_levelRatio_le_upperRatio_of_collar
      t hh hL hx
  have hratioNonneg :
      0 ≤
        (|Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h L| + eta) /
          (2 * Real.pi) :=
    le_trans (Nat.cast_nonneg q) hratio
  have hfloor :
      q ≤ Complex.logarithmicPhaseDualCrossingLevelUpper t h eta L := by
    unfold Complex.logarithmicPhaseDualCrossingLevelUpper
    exact (Nat.le_floor_iff hratioNonneg).mpr hratio
  exact
    (Complex.mem_logarithmicPhaseDualCrossingLevels_iff
      t h eta L q).mpr
      (And.intro (Nat.zero_le q) hfloor)

theorem Complex.logarithmicPhaseDual_positiveCrossingCollar_subset_canonicalUnion
    (t : ℝ) {h eta L U : ℝ}
    (hh : 0 ≤ h) (hL : 0 < L) {q : ℕ} :
    Complex.logarithmicPhaseDualCrossingCollar t h eta L U q ⊆
      Complex.logarithmicPhaseDualCrossingCollarUnion t h eta L U
        (Complex.logarithmicPhaseDualCrossingLevels t h eta L) := by
  intro x hx
  have hqRange :=
    Complex.logarithmicPhaseDual_crossingLevel_mem_range_of_collar
      t hh hL hx
  exact
    (Complex.mem_logarithmicPhaseDualCrossingCollarUnion_iff
      t h eta L U
      (Complex.logarithmicPhaseDualCrossingLevels t h eta L) x).mpr
      (Exists.intro q (And.intro hqRange hx))

theorem Complex.logarithmicPhaseDualCrossingLevels_card_real_le_leftDerivative
    (t : ℝ) {h eta L : ℝ}
    (hh : 0 ≤ h) (hL : 0 < L) (heta : 0 ≤ eta) :
    ((Complex.logarithmicPhaseDualCrossingLevels t h eta L).card : ℝ) ≤
      (‖t‖ * h / (L * (L + h)) + eta) /
        (2 * Real.pi) + 1 := by
  have hcard :=
    Complex.logarithmicPhaseDualCrossingLevels_card_real_le_ratio
      t h eta L heta
  have hformula :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_eq
      t hh hL
  exact le_trans hcard
    (le_of_eq
      (congrArg
        (fun z : ℝ => (z + eta) / (2 * Real.pi) + 1) hformula))

end

end LFunctions
end Boundary
