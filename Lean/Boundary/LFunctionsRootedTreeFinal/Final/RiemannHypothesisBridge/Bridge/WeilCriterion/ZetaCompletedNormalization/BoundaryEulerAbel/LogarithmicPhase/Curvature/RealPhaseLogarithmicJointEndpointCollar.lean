import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicSharpBudgetLedger

/-!
# Joint active/inactive endpoint collars

Active endpoint packets and near finite-inactive packets meet along the same
two support boundaries.  This owner forms their sidewise unions, proves the
exact disjoint decompositions, and exposes the combined crossing and
stationary budgets so duplicated endpoint charges can be removed upstream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhasePoissonBProcessLeftEndpointModes_subset_endpoint
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonBProcessLeftEndpointModes t a b ⊆
      Complex.logarithmicPhasePoissonBProcessEndpointModes t a b := by
  exact fun m hm =>
    have hcases :=
      (Complex.mem_logarithmicPhasePoissonBProcessLeftEndpointModes_iff
        t a b m).mp hm
    match hcases with
    | Or.inl houtside =>
        exact ((Complex.mem_logarithmicPhasePoissonBProcessLeftOutsideModes_iff
          t a b m).mp houtside).1
    | Or.inr hclipped =>
        exact ((Complex.mem_logarithmicPhasePoissonBProcessLeftClippedModes_iff
          t a b m).mp hclipped).1

theorem Complex.logarithmicPhasePoissonBProcessRightEndpointModes_subset_endpoint
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonBProcessRightEndpointModes t a b ⊆
      Complex.logarithmicPhasePoissonBProcessEndpointModes t a b := by
  exact fun m hm =>
    have hcases :=
      (Complex.mem_logarithmicPhasePoissonBProcessRightEndpointModes_iff
        t a b m).mp hm
    match hcases with
    | Or.inl houtside =>
        exact ((Complex.mem_logarithmicPhasePoissonBProcessRightOutsideModes_iff
          t a b m).mp houtside).1
    | Or.inr hclipped =>
        exact ((Complex.mem_logarithmicPhasePoissonBProcessRightClippedModes_iff
          t a b m).mp hclipped).1

theorem Complex.logarithmicPhasePoissonBProcessSideUnion_subset_endpoint
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonBProcessLeftEndpointModes t a b ∪
        Complex.logarithmicPhasePoissonBProcessRightEndpointModes t a b ⊆
      Complex.logarithmicPhasePoissonBProcessEndpointModes t a b := by
  exact fun m hm =>
    match Finset.mem_union.mp hm with
    | Or.inl hleft =>
        exact
          Complex.logarithmicPhasePoissonBProcessLeftEndpointModes_subset_endpoint
            t a b hleft
    | Or.inr hright =>
        exact
          Complex.logarithmicPhasePoissonBProcessRightEndpointModes_subset_endpoint
            t a b hright

theorem Complex.logarithmicPhasePoissonBProcessEndpointModes_eq_sideUnion
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonBProcessEndpointModes t a b =
      Complex.logarithmicPhasePoissonBProcessLeftEndpointModes t a b ∪
        Complex.logarithmicPhasePoissonBProcessRightEndpointModes t a b := by
  exact Finset.Subset.antisymm
    (Complex.logarithmicPhasePoissonBProcessEndpointModes_subset_sideUnion
      t a b)
    (Complex.logarithmicPhasePoissonBProcessSideUnion_subset_endpoint
      t a b)

theorem Complex.logarithmicPhasePoissonBProcessEndpointModes_subset_active
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonBProcessEndpointModes t a b ⊆
      Complex.logarithmicPhasePoissonActiveModes t a b := by
  exact fun _m hm => (Finset.mem_sdiff.mp hm).1

theorem Complex.logarithmicPhasePoissonBProcessLeftEndpointModes_card_le_one
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhasePoissonBProcessLeftEndpointModes
      t (a : ℤ) (b : ℤ)).card ≤ 1 := by
  have ha : (1 : ℤ) ≤ (a : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  exact Complex.integerModeFamily_card_le_one_of_center_bounds
    t (Complex.logarithmicPhasePoissonBProcessLeftEndpointModes
      t (a : ℤ) (b : ℤ))
    (Complex.integerBlockCutoffSupportLeftEndpoint_pos ha)
    (le_trans
      (sub_le_self (a : ℝ)
        (div_nonneg (OfNat.zero_le 2) (OfNat.zero_le 3)))
      (Complex.logarithmicPhaseBProcessLeftClipped_a_lt_centerUpper
        t ht ha).le)
    (Complex.leftEndpoint_angular_width ht hgeometry)
    (fun m hm =>
      Complex.logarithmicPhaseBProcessLeftEndpoint_negModeCast_bounds
        t ht (a : ℤ) (b : ℤ) ha hm)

theorem Complex.logarithmicPhasePoissonBProcessRightEndpointModes_card_le_one
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhasePoissonBProcessRightEndpointModes
      t (a : ℤ) (b : ℤ)).card ≤ 1 := by
  have hb : (1 : ℤ) ≤ (b : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry)
  exact Complex.integerModeFamily_card_le_one_of_center_bounds
    t (Complex.logarithmicPhasePoissonBProcessRightEndpointModes
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhaseBProcessRightClipped_lower_pos t hb)
    (le_trans
      (Complex.logarithmicPhaseBProcessRightClipped_centerLower_lt_b
        t hb).le
      (le_add_of_nonneg_right
        (div_nonneg (OfNat.zero_le 2) (OfNat.zero_le 3))))
    (Complex.rightEndpoint_angular_width ht hgeometry)
    (fun m hm =>
      Complex.logarithmicPhaseBProcessRightEndpoint_negModeCast_bounds
        t ht (a : ℤ) (b : ℤ) hb hm)

def Complex.logarithmicPhaseBProcessLeftEndpointBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonBProcessLeftEndpointModes t a b,
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m

def Complex.logarithmicPhaseBProcessRightEndpointBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonBProcessRightEndpointModes t a b,
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m

def Complex.logarithmicPhaseBProcessSideUnionEndpointBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈
      Complex.logarithmicPhasePoissonBProcessLeftEndpointModes t a b ∪
        Complex.logarithmicPhasePoissonBProcessRightEndpointModes t a b,
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m

theorem Complex.logarithmicPhaseBProcessUniversalEndpointBudget_eq_sideUnionBudget
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget t a b =
      Complex.logarithmicPhaseBProcessSideUnionEndpointBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointBudget
  unfold Complex.logarithmicPhaseBProcessSideUnionEndpointBudget
  exact congrArg
    (fun modes : Finset ℤ =>
      ∑ m ∈ modes,
        Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
          t a b m)
    (Complex.logarithmicPhasePoissonBProcessEndpointModes_eq_sideUnion
      t a b)

theorem Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_nonneg_of_negative
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b m : ℤ) (hm : m < 0) :
    0 ≤ Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
      t a b m := by
  have hcrossing : (0 : ℝ) ≤ 4 / 3 :=
    div_nonneg (OfNat.zero_le 4) (OfNat.zero_le 3)
  have hleft :=
    Complex.logarithmicPhaseBProcessClippedLeftTailBudget_nonneg
      t ht a m hm
  have hradius :=
    Complex.logarithmicPhaseBProcessRadius_nonneg t ht hm
  have htwiceRadius :
      0 ≤ 2 * Complex.logarithmicPhaseBProcessRadius t m :=
    mul_nonneg (OfNat.zero_le 2) hradius
  have hright :=
    Complex.logarithmicPhaseBProcessClippedRightTailBudget_nonneg
      t ht b m hm
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
  exact add_nonneg (add_nonneg (add_nonneg hcrossing hleft) htwiceRadius)
    hright

theorem Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget_nonneg_of_negative
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b m : ℤ) (hm : m < 0) :
    0 ≤ Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
      t a b m := by
  have hcrossing : (0 : ℝ) ≤ 2 / 3 :=
    div_nonneg (OfNat.zero_le 2) (OfNat.zero_le 3)
  have hleft :=
    Complex.logarithmicPhaseBProcessClippedLeftTailBudget_nonneg
      t ht a m hm
  have hradius :=
    Complex.logarithmicPhaseBProcessRadius_nonneg t ht hm
  have htwiceRadius :
      0 ≤ 2 * Complex.logarithmicPhaseBProcessRadius t m :=
    mul_nonneg (OfNat.zero_le 2) hradius
  have hright :=
    Complex.logarithmicPhaseBProcessClippedRightTailBudget_nonneg
      t ht b m hm
  unfold Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
  exact add_nonneg (add_nonneg (add_nonneg hcrossing hleft) htwiceRadius)
    hright

theorem Complex.logarithmicPhaseBProcessSideUnionEndpointBudget_le_sideBudgets
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) :
    Complex.logarithmicPhaseBProcessSideUnionEndpointBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseBProcessLeftEndpointBudget
          t (a : ℤ) (b : ℤ) +
        Complex.logarithmicPhaseBProcessRightEndpointBudget
          t (a : ℤ) (b : ℤ) := by
  let left := Complex.logarithmicPhasePoissonBProcessLeftEndpointModes
    t (a : ℤ) (b : ℤ)
  let right := Complex.logarithmicPhasePoissonBProcessRightEndpointModes
    t (a : ℤ) (b : ℤ)
  let budget := Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
    t (a : ℤ) (b : ℤ)
  have hunionRemainder : left ∪ (right \ left) = left ∪ right :=
    Finset.union_sdiff_self_eq_union
  have hdisjoint : Disjoint left (right \ left) := Finset.disjoint_sdiff
  have hsumDecomposition :
      (∑ m ∈ left ∪ (right \ left), budget m) =
        (∑ m ∈ left, budget m) + ∑ m ∈ right \ left, budget m :=
    Finset.sum_union hdisjoint
  have hsumUnion :
      (∑ m ∈ left ∪ right, budget m) =
        (∑ m ∈ left, budget m) + ∑ m ∈ right \ left, budget m :=
    Eq.trans
      (congrArg (fun modes : Finset ℤ => ∑ m ∈ modes, budget m)
        hunionRemainder.symm)
      hsumDecomposition
  have hrightRemainder :
      (∑ m ∈ right \ left, budget m) ≤ ∑ m ∈ right, budget m :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun m hmRight _hmNotRemainder =>
        have hendpoint :=
          Complex.logarithmicPhasePoissonBProcessRightEndpointModes_subset_endpoint
            t (a : ℤ) (b : ℤ) hmRight
        have hmNeg :=
          Complex.logarithmicPhaseBProcessEndpointMode_negative_nat hendpoint
        Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_nonneg_of_negative
          t ht (a : ℤ) (b : ℤ) m hmNeg)
  have hsumBound := add_le_add_left hrightRemainder
    (∑ m ∈ left, budget m)
  unfold Complex.logarithmicPhaseBProcessSideUnionEndpointBudget
  unfold Complex.logarithmicPhaseBProcessLeftEndpointBudget
  unfold Complex.logarithmicPhaseBProcessRightEndpointBudget
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hsumUnion.symm hsumBound

theorem Complex.logarithmicPhaseBProcessLeftEndpointBudget_nonneg
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) :
    0 ≤ Complex.logarithmicPhaseBProcessLeftEndpointBudget
      t (a : ℤ) (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessLeftEndpointBudget
  exact Finset.sum_nonneg (fun m hm =>
    have hendpoint :=
      Complex.logarithmicPhasePoissonBProcessLeftEndpointModes_subset_endpoint
        t (a : ℤ) (b : ℤ) hm
    have hmNeg :=
      Complex.logarithmicPhaseBProcessEndpointMode_negative_nat hendpoint
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_nonneg_of_negative
      t ht (a : ℤ) (b : ℤ) m hmNeg)

theorem Complex.logarithmicPhaseBProcessRightEndpointBudget_nonneg
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) :
    0 ≤ Complex.logarithmicPhaseBProcessRightEndpointBudget
      t (a : ℤ) (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessRightEndpointBudget
  exact Finset.sum_nonneg (fun m hm =>
    have hendpoint :=
      Complex.logarithmicPhasePoissonBProcessRightEndpointModes_subset_endpoint
        t (a : ℤ) (b : ℤ) hm
    have hmNeg :=
      Complex.logarithmicPhaseBProcessEndpointMode_negative_nat hendpoint
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_nonneg_of_negative
      t ht (a : ℤ) (b : ℤ) m hmNeg)

theorem Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget_nonneg
    {t : ℝ} {a b : ℕ} (ht : 1 ≤ ‖t‖) :
    0 ≤ Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
      t (a : ℤ) (b : ℤ) := by
  unfold Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
  exact Finset.sum_nonneg (fun m hm =>
    have hnear :=
      (Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
        t (a : ℤ) (b : ℤ) m).mp hm
    have hinactive :=
      (Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
        t (a : ℤ) (b : ℤ) m).mp hnear.1
    Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget_nonneg_of_negative
      t ht (a : ℤ) (b : ℤ) m hinactive.2.1)

theorem Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget_nonneg
    {t : ℝ} {a b : ℕ} (ht : 1 ≤ ‖t‖) :
    0 ≤ Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
      t (a : ℤ) (b : ℤ) := by
  unfold Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
  exact Finset.sum_nonneg (fun m hm =>
    have hnear :=
      (Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
        t (a : ℤ) (b : ℤ) m).mp hm
    have hinactive :=
      (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
        t (a : ℤ) (b : ℤ) m).mp hnear.1
    Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget_nonneg_of_negative
      t ht (a : ℤ) (b : ℤ) m hinactive.2.1)

def Complex.logarithmicPhaseJointLeftEndpointCollarModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  Complex.logarithmicPhasePoissonBProcessLeftEndpointModes t a b ∪
    Complex.logarithmicPhaseFiniteLeftNearEndpointModes t a b

def Complex.logarithmicPhaseJointRightEndpointCollarModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  Complex.logarithmicPhasePoissonBProcessRightEndpointModes t a b ∪
    Complex.logarithmicPhaseFiniteRightNearEndpointModes t a b

def Complex.logarithmicPhaseJointEndpointCollarModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  Complex.logarithmicPhaseJointLeftEndpointCollarModes t a b ∪
    Complex.logarithmicPhaseJointRightEndpointCollarModes t a b

theorem Complex.logarithmicPhaseLeftActiveEndpoint_disjoint_leftInactiveNear
    (t : ℝ) (a b : ℤ) :
    Disjoint
      (Complex.logarithmicPhasePoissonBProcessLeftEndpointModes t a b)
      (Complex.logarithmicPhaseFiniteLeftNearEndpointModes t a b) := by
  exact Finset.disjoint_left.mpr (fun m hactive hinactive =>
    have hactiveBase :=
      Complex.logarithmicPhasePoissonBProcessLeftEndpointModes_subset_endpoint
        t a b hactive
    have hactiveMode :=
      Complex.logarithmicPhasePoissonBProcessEndpointModes_subset_active
        t a b hactiveBase
    have hinactiveBase :=
      ((Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
        t a b m).mp hinactive).1
    have hinactiveMode :=
      ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
        t a b m).mp hinactiveBase).1
    have hsdiff := Finset.mem_sdiff.mp hinactiveMode
    hsdiff.2 hactiveMode)

theorem Complex.logarithmicPhaseRightActiveEndpoint_disjoint_rightInactiveNear
    (t : ℝ) (a b : ℤ) :
    Disjoint
      (Complex.logarithmicPhasePoissonBProcessRightEndpointModes t a b)
      (Complex.logarithmicPhaseFiniteRightNearEndpointModes t a b) := by
  exact Finset.disjoint_left.mpr (fun m hactive hinactive =>
    have hactiveBase :=
      Complex.logarithmicPhasePoissonBProcessRightEndpointModes_subset_endpoint
        t a b hactive
    have hactiveMode :=
      Complex.logarithmicPhasePoissonBProcessEndpointModes_subset_active
        t a b hactiveBase
    have hinactiveBase :=
      ((Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
        t a b m).mp hinactive).1
    have hinactiveMode :=
      ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
        t a b m).mp hinactiveBase).1
    have hsdiff := Finset.mem_sdiff.mp hinactiveMode
    hsdiff.2 hactiveMode)

theorem Complex.logarithmicPhaseJointLeftEndpointCollar_card_eq_sum
    (t : ℝ) (a b : ℤ) :
    (Complex.logarithmicPhaseJointLeftEndpointCollarModes t a b).card =
      (Complex.logarithmicPhasePoissonBProcessLeftEndpointModes t a b).card +
        (Complex.logarithmicPhaseFiniteLeftNearEndpointModes t a b).card := by
  unfold Complex.logarithmicPhaseJointLeftEndpointCollarModes
  exact Finset.card_union_of_disjoint
    (Complex.logarithmicPhaseLeftActiveEndpoint_disjoint_leftInactiveNear
      t a b)

theorem Complex.logarithmicPhaseJointRightEndpointCollar_card_eq_sum
    (t : ℝ) (a b : ℤ) :
    (Complex.logarithmicPhaseJointRightEndpointCollarModes t a b).card =
      (Complex.logarithmicPhasePoissonBProcessRightEndpointModes t a b).card +
        (Complex.logarithmicPhaseFiniteRightNearEndpointModes t a b).card := by
  unfold Complex.logarithmicPhaseJointRightEndpointCollarModes
  exact Finset.card_union_of_disjoint
    (Complex.logarithmicPhaseRightActiveEndpoint_disjoint_rightInactiveNear
      t a b)

theorem Complex.logarithmicPhaseJointLeftEndpointCollar_card_le_two
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhaseJointLeftEndpointCollarModes
      t (a : ℤ) (b : ℤ)).card ≤ 2 := by
  have hactive :=
    Complex.logarithmicPhasePoissonBProcessLeftEndpointModes_card_le_one
      ht hgeometry
  have hinactive :=
    Complex.logarithmicPhaseFiniteLeftNear_card_le_one ht hgeometry
  have hadd := Nat.add_le_add hactive hinactive
  exact Eq.subst (motive := fun value : ℕ => value ≤ 2)
    (Complex.logarithmicPhaseJointLeftEndpointCollar_card_eq_sum
      t (a : ℤ) (b : ℤ)).symm hadd

theorem Complex.logarithmicPhaseJointRightEndpointCollar_card_le_two
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhaseJointRightEndpointCollarModes
      t (a : ℤ) (b : ℤ)).card ≤ 2 := by
  have hactive :=
    Complex.logarithmicPhasePoissonBProcessRightEndpointModes_card_le_one
      ht hgeometry
  have hinactive :=
    Complex.logarithmicPhaseFiniteRightNear_card_le_one ht hgeometry
  have hadd := Nat.add_le_add hactive hinactive
  exact Eq.subst (motive := fun value : ℕ => value ≤ 2)
    (Complex.logarithmicPhaseJointRightEndpointCollar_card_eq_sum
      t (a : ℤ) (b : ℤ)).symm hadd

def Complex.logarithmicPhaseJointLeftEndpointCollarBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseBProcessLeftEndpointBudget t a b +
    Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget t a b

def Complex.logarithmicPhaseJointRightEndpointCollarBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseBProcessRightEndpointBudget t a b +
    Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget t a b

def Complex.logarithmicPhaseJointEndpointCollarBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseJointLeftEndpointCollarBudget t a b +
    Complex.logarithmicPhaseJointRightEndpointCollarBudget t a b

def Complex.logarithmicPhaseJointEndpointCollarCrossingBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ _m ∈ Complex.logarithmicPhaseJointEndpointCollarModes t a b,
    (2 / 3 : ℝ)

theorem Complex.logarithmicPhaseJointEndpointCollarCrossingBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseJointEndpointCollarCrossingBudget t a b := by
  unfold Complex.logarithmicPhaseJointEndpointCollarCrossingBudget
  exact Finset.sum_nonneg (fun m hm =>
    div_nonneg (OfNat.zero_le 2) (OfNat.zero_le 3))

theorem Complex.logarithmicPhaseJointLeftEndpointCollarBudget_nonneg
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) :
    0 ≤ Complex.logarithmicPhaseJointLeftEndpointCollarBudget
      t (a : ℤ) (b : ℤ) := by
  unfold Complex.logarithmicPhaseJointLeftEndpointCollarBudget
  exact add_nonneg
    (Complex.logarithmicPhaseBProcessLeftEndpointBudget_nonneg
      ht)
    (Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget_nonneg ht)

theorem Complex.logarithmicPhaseJointRightEndpointCollarBudget_nonneg
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) :
    0 ≤ Complex.logarithmicPhaseJointRightEndpointCollarBudget
      t (a : ℤ) (b : ℤ) := by
  unfold Complex.logarithmicPhaseJointRightEndpointCollarBudget
  exact add_nonneg
    (Complex.logarithmicPhaseBProcessRightEndpointBudget_nonneg
      ht)
    (Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget_nonneg ht)

theorem Complex.logarithmicPhaseJointEndpointCollarBudget_nonneg
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) :
    0 ≤ Complex.logarithmicPhaseJointEndpointCollarBudget
      t (a : ℤ) (b : ℤ) := by
  unfold Complex.logarithmicPhaseJointEndpointCollarBudget
  exact add_nonneg
    (Complex.logarithmicPhaseJointLeftEndpointCollarBudget_nonneg
      ht)
    (Complex.logarithmicPhaseJointRightEndpointCollarBudget_nonneg
      ht)

end

end LFunctions
end Boundary
