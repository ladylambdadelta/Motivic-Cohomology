import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseIntegerJumpTelescoping

/-!
# Endpoint variation of the base dual branch quotient

The canonical `toIocDiv` quotient is antitone along the positive integer
samples of the base dual action.  Its jump count is therefore controlled by
its endpoint drop.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseDualBaseBranchIndex_eq_neg_floor
    (t : ℝ) (n : ℕ) :
    Complex.logarithmicPhaseDualBaseBranchIndex t n =
      -⌊(Real.pi - Complex.logarithmicPhaseDualBaseIncrementNat t n) /
          (2 * Real.pi)⌋ := by
  unfold Complex.logarithmicPhaseDualBaseBranchIndex
  have hformula := toIocDiv_eq_neg_floor Real.two_pi_pos
    (-Real.pi) (Complex.logarithmicPhaseDualBaseIncrementNat t n)
  have hnumerator :
      -Real.pi + 2 * Real.pi -
          Complex.logarithmicPhaseDualBaseIncrementNat t n =
        Real.pi - Complex.logarithmicPhaseDualBaseIncrementNat t n := by
    have hbase : -Real.pi + 2 * Real.pi = Real.pi := by
      exact Eq.trans
        (congrArg (fun z : ℝ => -Real.pi + z) (two_mul Real.pi).symm)
        (neg_add_cancel_left Real.pi Real.pi)
    exact congrArg
      (fun z : ℝ => z - Complex.logarithmicPhaseDualBaseIncrementNat t n)
      hbase
  exact Eq.trans hformula
    (congrArg (fun z : ℝ => -⌊z / (2 * Real.pi)⌋) hnumerator)

theorem Complex.logarithmicPhaseDualBaseBranchIndex_antitone
    (t : ℝ) (ht : 1 ≤ ‖t‖) {n m : ℕ}
    (hn : 0 < n) (hnm : n ≤ m) :
    Complex.logarithmicPhaseDualBaseBranchIndex t m ≤
      Complex.logarithmicPhaseDualBaseBranchIndex t n := by
  have hinc := Complex.logarithmicPhaseDualBaseIncrementNat_antitone
    t ht hn hnm
  have hnumerator :
      Real.pi - Complex.logarithmicPhaseDualBaseIncrementNat t n ≤
        Real.pi - Complex.logarithmicPhaseDualBaseIncrementNat t m :=
    sub_le_sub_left hinc Real.pi
  have hratio := div_le_div_of_nonneg_right hnumerator
    (le_of_lt Complex.two_mul_pi_pos)
  have hfloor := Int.floor_mono hratio
  have hneg := neg_le_neg hfloor
  exact Eq.subst (motive := fun z : ℤ => z ≤ _)
    (Complex.logarithmicPhaseDualBaseBranchIndex_eq_neg_floor t m).symm
    (Eq.subst (motive := fun z : ℤ => _ ≤ z)
      (Complex.logarithmicPhaseDualBaseBranchIndex_eq_neg_floor t n).symm
      hneg)

theorem Complex.logarithmicPhaseDualBaseBranchIndex_forward_antitone
    (t : ℝ) (ht : 1 ≤ ‖t‖) {K N : ℕ} (hK : 0 < K) :
    ∀ j < N,
      Complex.logarithmicPhaseDualBaseBranchIndex t (K + j + 1) ≤
        Complex.logarithmicPhaseDualBaseBranchIndex t (K + j) := by
  intro j hj
  have hKj : 0 < K + j := lt_of_lt_of_le hK (Nat.le_add_right K j)
  exact Complex.logarithmicPhaseDualBaseBranchIndex_antitone
    t ht hKj (Nat.le_add_right (K + j) 1)

theorem Complex.logarithmicPhaseDualBaseBranchJumpCount_le_endpointDrop
    (t : ℝ) (ht : 1 ≤ ‖t‖) (K N : ℕ) (hK : 0 < K) :
    Int.forwardJumpCount
        (Complex.logarithmicPhaseDualBaseBranchIndex t) K N ≤
      Complex.logarithmicPhaseDualBaseBranchIndex t K -
        Complex.logarithmicPhaseDualBaseBranchIndex t (K + N) := by
  exact Int.forwardJumpCount_le_endpointDrop
    (Complex.logarithmicPhaseDualBaseBranchIndex t) K N
    (Complex.logarithmicPhaseDualBaseBranchIndex_forward_antitone
      t ht hK)

theorem Complex.logarithmicPhaseDualBaseBranchEndpointDrop_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (K N : ℕ) (hK : 0 < K) :
    0 ≤ Complex.logarithmicPhaseDualBaseBranchIndex t K -
      Complex.logarithmicPhaseDualBaseBranchIndex t (K + N) := by
  exact sub_nonneg.mpr
    (Complex.logarithmicPhaseDualBaseBranchIndex_antitone
      t ht hK (Nat.le_add_right K N))

theorem Complex.logarithmicPhaseDualBaseBranchBoundaryModes_card_cast_eq_indicator_sum
    (t : ℝ) (K M : ℕ) :
    ((Complex.logarithmicPhaseDualBaseBranchBoundaryModes t K M).card : ℤ) =
      ∑ n ∈ Finset.Icc K M,
        Int.forwardJumpIndicator
          (Complex.logarithmicPhaseDualBaseBranchIndex t) n := by
  unfold Complex.logarithmicPhaseDualBaseBranchBoundaryModes
  have hcard := Finset.natCast_card_filter
    (fun n : ℕ =>
      Complex.logarithmicPhaseDualBaseBranchIndex t n ≠
        Complex.logarithmicPhaseDualBaseBranchIndex t (n + 1))
    (Finset.Icc K M)
  have hindicator :
      (∑ n ∈ Finset.Icc K M,
        if Complex.logarithmicPhaseDualBaseBranchIndex t n ≠
            Complex.logarithmicPhaseDualBaseBranchIndex t (n + 1)
        then (1 : ℤ) else 0) =
      ∑ n ∈ Finset.Icc K M,
        Int.forwardJumpIndicator
          (Complex.logarithmicPhaseDualBaseBranchIndex t) n := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        by_cases h :
            Complex.logarithmicPhaseDualBaseBranchIndex t n =
              Complex.logarithmicPhaseDualBaseBranchIndex t (n + 1)
        · exact Eq.trans (if_neg (not_not.mpr h))
            (Int.forwardJumpIndicator_eq_zero_of_eq _ _ h).symm
        · exact Eq.trans (if_pos h)
            (Int.forwardJumpIndicator_eq_one_of_ne _ _ h).symm)
  exact Eq.trans hcard hindicator

theorem Nat.start_add_closedIntervalLength
    {K M : ℕ} (hKM : K ≤ M) :
    K + (M - K + 1) = M + 1 := by
  exact Eq.trans
    (Nat.add_assoc K (M - K) 1).symm
    (congrArg (fun z : ℕ => z + 1) (Nat.add_sub_of_le hKM))

theorem Finset.Icc_eq_map_range_closedIntervalLength
    {K M : ℕ} (hKM : K ≤ M) :
    Finset.Icc K M =
      (Finset.range (M - K + 1)).map
        ⟨fun j : ℕ => K + j,
          fun x y hxy => Nat.add_left_cancel hxy⟩ := by
  have hIccIco : Finset.Icc K M = Finset.Ico K (M + 1) := by
    exact Finset.ext (fun n =>
      Iff.intro
        (fun hn =>
          have hdata := Finset.mem_Icc.mp hn
          Finset.mem_Ico.mpr
            (And.intro hdata.1 (Nat.lt_succ_of_le hdata.2)))
        (fun hn =>
          have hdata := Finset.mem_Ico.mp hn
          Finset.mem_Icc.mpr
            (And.intro hdata.1 (Nat.le_of_lt_succ hdata.2))))
  have hlength := Nat.start_add_closedIntervalLength hKM
  exact Eq.trans hIccIco
    (Eq.trans
      (congrArg (Finset.Ico K) hlength.symm)
      (Finset.Ico_eq_map_range K (M - K + 1)))

theorem Complex.logarithmicPhaseDualBaseBranchBoundary_indicator_sum_eq_jumpCount
    (t : ℝ) {K M : ℕ} (hKM : K ≤ M) :
    (∑ n ∈ Finset.Icc K M,
      Int.forwardJumpIndicator
        (Complex.logarithmicPhaseDualBaseBranchIndex t) n) =
      Int.forwardJumpCount
        (Complex.logarithmicPhaseDualBaseBranchIndex t)
        K (M - K + 1) := by
  unfold Int.forwardJumpCount
  have hmap := Finset.Icc_eq_map_range_closedIntervalLength hKM
  exact Eq.trans
    (congrArg
      (fun S : Finset ℕ =>
        ∑ n ∈ S,
          Int.forwardJumpIndicator
            (Complex.logarithmicPhaseDualBaseBranchIndex t) n)
      hmap)
    (Finset.sum_map
      (Finset.range (M - K + 1))
      ⟨fun j : ℕ => K + j,
        fun x y hxy => Nat.add_left_cancel hxy⟩
      (fun n : ℕ =>
        Int.forwardJumpIndicator
          (Complex.logarithmicPhaseDualBaseBranchIndex t) n))

theorem Complex.logarithmicPhaseDualBaseBranchBoundaryModes_card_cast_le_endpointDrop
    (t : ℝ) (ht : 1 ≤ ‖t‖) {K M : ℕ}
    (hK : 0 < K) (hKM : K ≤ M) :
    ((Complex.logarithmicPhaseDualBaseBranchBoundaryModes t K M).card : ℤ) ≤
      Complex.logarithmicPhaseDualBaseBranchIndex t K -
        Complex.logarithmicPhaseDualBaseBranchIndex t (M + 1) := by
  have hcard :=
    Complex.logarithmicPhaseDualBaseBranchBoundaryModes_card_cast_eq_indicator_sum
      t K M
  have hsum :=
    Complex.logarithmicPhaseDualBaseBranchBoundary_indicator_sum_eq_jumpCount
      t hKM
  have hjump :=
    Complex.logarithmicPhaseDualBaseBranchJumpCount_le_endpointDrop
      t ht K (M - K + 1) hK
  have hendpoint := Nat.start_add_closedIntervalLength hKM
  exact Eq.subst (motive := fun z : ℤ => z ≤ _)
    hcard.symm
    (Eq.subst (motive := fun z : ℤ => z ≤ _)
      hsum.symm
      (Eq.subst
        (motive := fun endpoint : ℕ =>
          Int.forwardJumpCount
              (Complex.logarithmicPhaseDualBaseBranchIndex t)
              K (M - K + 1) ≤
            Complex.logarithmicPhaseDualBaseBranchIndex t K -
              Complex.logarithmicPhaseDualBaseBranchIndex t endpoint)
        hendpoint hjump))

theorem Int.cast_floor_sub_floor_lt_sub_add_one
    (x y : ℝ) :
    ((⌊y⌋ - ⌊x⌋ : ℤ) : ℝ) < y - x + 1 := by
  have hyFloor : ((⌊y⌋ : ℤ) : ℝ) ≤ y := Int.floor_le y
  have hxFloor : x < ((⌊x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x
  have hnegX : -((⌊x⌋ : ℤ) : ℝ) < 1 - x := by
    exact (neg_lt_sub_iff_lt_add).mpr hxFloor
  have hadd := add_lt_add_of_le_of_lt hyFloor hnegX
  have hcast :
      ((⌊y⌋ - ⌊x⌋ : ℤ) : ℝ) =
        ((⌊y⌋ : ℤ) : ℝ) - ((⌊x⌋ : ℤ) : ℝ) :=
    Int.cast_sub ⌊y⌋ ⌊x⌋
  have hright : y + (1 - x) = y - x + 1 := by
    exact Eq.trans (add_sub_assoc y 1 x)
      (Eq.trans
        (congrArg (fun z : ℝ => z - x) (add_comm y 1))
        (sub_add_eq_add_sub 1 x y))
  exact Eq.subst (motive := fun z : ℝ => z < _)
    hcast.symm
    (Eq.subst (motive := fun z : ℝ => _ < z) hright hadd)

theorem Int.cast_floor_sub_floor_le_sub_add_one
    (x y : ℝ) :
    ((⌊y⌋ - ⌊x⌋ : ℤ) : ℝ) ≤ y - x + 1 := by
  exact le_of_lt (Int.cast_floor_sub_floor_lt_sub_add_one x y)

theorem Complex.logarithmicPhaseDualBaseBranchBoundaryModes_card_real_le_incrementVariation
    (t : ℝ) (ht : 1 ≤ ‖t‖) {K M : ℕ}
    (hK : 0 < K) (hKM : K ≤ M) :
    ((Complex.logarithmicPhaseDualBaseBranchBoundaryModes t K M).card : ℝ) ≤
      (Complex.logarithmicPhaseDualBaseIncrementNat t K -
          Complex.logarithmicPhaseDualBaseIncrementNat t (M + 1)) /
        (2 * Real.pi) + 1 := by
  let x :=
    (Real.pi - Complex.logarithmicPhaseDualBaseIncrementNat t K) /
      (2 * Real.pi)
  let y :=
    (Real.pi - Complex.logarithmicPhaseDualBaseIncrementNat t (M + 1)) /
      (2 * Real.pi)
  have hcardInt :=
    Complex.logarithmicPhaseDualBaseBranchBoundaryModes_card_cast_le_endpointDrop
      t ht hK hKM
  have hendpoint :
      Complex.logarithmicPhaseDualBaseBranchIndex t K -
          Complex.logarithmicPhaseDualBaseBranchIndex t (M + 1) =
        ⌊y⌋ - ⌊x⌋ := by
    exact Eq.trans
      (congrArg₂ (fun a b : ℤ => a - b)
        (Complex.logarithmicPhaseDualBaseBranchIndex_eq_neg_floor t K)
        (Complex.logarithmicPhaseDualBaseBranchIndex_eq_neg_floor t (M + 1)))
      (neg_sub_neg ⌊x⌋ ⌊y⌋)
  have hcastInt :
      (((Complex.logarithmicPhaseDualBaseBranchBoundaryModes t K M).card : ℤ) : ℝ) ≤
        ((⌊y⌋ - ⌊x⌋ : ℤ) : ℝ) := by
    exact Int.cast_le.mpr
      (Eq.subst (motive := fun z : ℤ => _ ≤ z) hendpoint hcardInt)
  have hfloor := Int.cast_floor_sub_floor_le_sub_add_one x y
  have hvariation :
      y - x + 1 =
        (Complex.logarithmicPhaseDualBaseIncrementNat t K -
            Complex.logarithmicPhaseDualBaseIncrementNat t (M + 1)) /
          (2 * Real.pi) + 1 := by
    unfold x y
    have hsubDiv := sub_div
      (Real.pi - Complex.logarithmicPhaseDualBaseIncrementNat t (M + 1))
      (Real.pi - Complex.logarithmicPhaseDualBaseIncrementNat t K)
      (2 * Real.pi)
    have hnumerator :
        (Real.pi - Complex.logarithmicPhaseDualBaseIncrementNat t (M + 1)) -
            (Real.pi - Complex.logarithmicPhaseDualBaseIncrementNat t K) =
          Complex.logarithmicPhaseDualBaseIncrementNat t K -
            Complex.logarithmicPhaseDualBaseIncrementNat t (M + 1) := by
      exact sub_sub_sub_cancel_right Real.pi
        (Complex.logarithmicPhaseDualBaseIncrementNat t (M + 1))
        (Complex.logarithmicPhaseDualBaseIncrementNat t K)
    exact congrArg (fun z : ℝ => z + 1)
      (Eq.trans hsubDiv.symm
        (congrArg (fun z : ℝ => z / (2 * Real.pi)) hnumerator))
  have hcombined := le_trans hcastInt (le_trans hfloor (le_of_eq hvariation))
  have hcardCast :
      (((Complex.logarithmicPhaseDualBaseBranchBoundaryModes t K M).card : ℤ) : ℝ) =
        ((Complex.logarithmicPhaseDualBaseBranchBoundaryModes t K M).card : ℝ) := by
    exact Int.cast_natCast _
  exact Eq.subst (motive := fun z : ℝ => z ≤ _)
    hcardCast.symm hcombined

end

end LFunctions
end Boundary
