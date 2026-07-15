import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.BProcessStationaryPacket

/-!
# Balanced logarithmic B-process active budget

This owner sums the balanced stationary-packet majorant over all B-process
interior modes.  It retains four separately named components so the curvature
arithmetic can normalize cardinality, central width, and reciprocal tails by
independent explicit inequalities.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseBProcessInteriorCrossingBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ _m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
    (4 / 3 : ℝ)

def Complex.logarithmicPhaseBProcessInteriorLeftTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
    Complex.logarithmicPhaseBProcessLeftTailBudget t m

def Complex.logarithmicPhaseBProcessInteriorCentralBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
    Complex.logarithmicPhaseBProcessWindowWidth t m

def Complex.logarithmicPhaseBProcessInteriorRightTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
    Complex.logarithmicPhaseBProcessRightTailBudget t m

def Complex.logarithmicPhaseBProcessInteriorBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseBProcessInteriorCrossingBudget t a b +
    Complex.logarithmicPhaseBProcessInteriorLeftTailBudget t a b +
      Complex.logarithmicPhaseBProcessInteriorCentralBudget t a b +
        Complex.logarithmicPhaseBProcessInteriorRightTailBudget t a b

theorem Complex.logarithmicPhaseBProcessInteriorCrossingBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseBProcessInteriorCrossingBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessInteriorCrossingBudget
  have hfour : (0 : ℝ) ≤ 4 := zero_le_four
  have hthree : (0 : ℝ) ≤ 3 := zero_le_three
  have hcrossing : (0 : ℝ) ≤ 4 / 3 :=
    div_nonneg hfour hthree
  exact Finset.sum_nonneg
    (fun _m _hm => hcrossing)

theorem Complex.logarithmicPhaseBProcessInteriorCentralBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseBProcessInteriorCentralBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessInteriorCentralBudget
  exact Finset.sum_nonneg (fun m hm => by
    have hmem :=
      (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
        t a b m).mp hm
    have hradius :=
      Complex.logarithmicPhaseBProcessRadius_nonneg t ht hmem.2.1
    have htwo : (0 : ℝ) ≤ 2 := zero_le_two
    have htwiceRadius :
        0 ≤ 2 * Complex.logarithmicPhaseBProcessRadius t m :=
      mul_nonneg htwo hradius
    exact Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (Complex.logarithmicPhaseBProcessWindowWidth_eq_two_mul_radius
        t m).symm
      htwiceRadius)

theorem Complex.logarithmicPhaseBProcessInteriorLeftTailBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (ha : 1 ≤ a) :
    0 ≤ Complex.logarithmicPhaseBProcessInteriorLeftTailBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessInteriorLeftTailBudget
  exact Finset.sum_nonneg (fun m hm => by
    have hmem :=
      (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
        t a b m).mp hm
    have hleftPos :=
      Complex.logarithmicPhaseBProcessWindowLeft_pos_of_mem
        t a b m ha hm
    have hcenter :=
      Complex.logarithmicPhaseBProcessWindowLeft_lt_center
        t ht hmem.2.1
    have hcoefficient :=
      Complex.logarithmicPhaseLeftReciprocalGap_eq_coefficientNorm
        t ht m hmem.2.1 hleftPos hcenter
    have hterm :
        0 ≤ Complex.logarithmicPhaseLeftReciprocalGap t m
          (Complex.logarithmicPhaseBProcessWindowLeft t m) :=
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        hcoefficient.symm
        (norm_nonneg _)
    exact add_nonneg hterm hterm)

theorem Complex.logarithmicPhaseBProcessInteriorRightTailBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseBProcessInteriorRightTailBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessInteriorRightTailBudget
  exact Finset.sum_nonneg (fun m hm => by
    have hmem :=
      (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
        t a b m).mp hm
    have hcenterPos :=
      Complex.logarithmicPhaseFourierStationaryPoint_pos
        t ht hmem.2.1
    have hrightPos :=
      lt_of_lt_of_le hcenterPos
        (Complex.logarithmicPhaseBProcess_center_lt_WindowRight
          t ht hmem.2.1).le
    have hcenter :=
      Complex.logarithmicPhaseBProcess_center_lt_WindowRight
        t ht hmem.2.1
    have hcoefficient :=
      Complex.logarithmicPhaseRightReciprocalGap_eq_coefficientNorm
        t ht m hmem.2.1 hrightPos hcenter
    have hterm :
        0 ≤ Complex.logarithmicPhaseRightReciprocalGap t m
          (Complex.logarithmicPhaseBProcessWindowRight t m) :=
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        hcoefficient.symm
        (norm_nonneg _)
    exact add_nonneg hterm hterm)

theorem Complex.logarithmicPhaseBProcessInteriorBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (ha : 1 ≤ a) :
    0 ≤ Complex.logarithmicPhaseBProcessInteriorBudget t a b := by
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (Complex.logarithmicPhaseBProcessInteriorCrossingBudget_nonneg
          t a b)
        (Complex.logarithmicPhaseBProcessInteriorLeftTailBudget_nonneg
          t ht a b ha))
      (Complex.logarithmicPhaseBProcessInteriorCentralBudget_nonneg
        t ht a b))
    (Complex.logarithmicPhaseBProcessInteriorRightTailBudget_nonneg
      t ht a b)

theorem Complex.sum_logarithmicPhaseBProcessStationaryPacketMajorant_eq_budget
    (t : ℝ) (a b : ℤ) :
    (∑ m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
      Complex.logarithmicPhaseBProcessStationaryPacketMajorant t m) =
      Complex.logarithmicPhaseBProcessInteriorBudget t a b := by
  let modes :=
    Complex.logarithmicPhasePoissonBProcessInteriorModes t a b
  let crossing : ℤ → ℝ := fun _m => 4 / 3
  let leftTail : ℤ → ℝ := fun m =>
    Complex.logarithmicPhaseBProcessLeftTailBudget t m
  let central : ℤ → ℝ := fun m =>
    Complex.logarithmicPhaseBProcessWindowWidth t m
  let rightTail : ℤ → ℝ := fun m =>
    Complex.logarithmicPhaseBProcessRightTailBudget t m
  have hrightSplit :
      modes.sum (fun m =>
        crossing m + leftTail m + central m + rightTail m) =
        modes.sum (fun m => crossing m + leftTail m + central m) +
          modes.sum rightTail :=
    Finset.sum_add_distrib
  have hcentralSplit :
      modes.sum (fun m => crossing m + leftTail m + central m) =
        modes.sum (fun m => crossing m + leftTail m) +
          modes.sum central :=
    Finset.sum_add_distrib
  have hleftSplit :
      modes.sum (fun m => crossing m + leftTail m) =
        modes.sum crossing + modes.sum leftTail :=
    Finset.sum_add_distrib
  calc
    (∑ m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
      Complex.logarithmicPhaseBProcessStationaryPacketMajorant t m) =
        modes.sum (fun m =>
          crossing m + leftTail m + central m + rightTail m) := by
      rfl
    _ =
        modes.sum (fun m => crossing m + leftTail m + central m) +
          modes.sum rightTail := hrightSplit
    _ =
        (modes.sum (fun m => crossing m + leftTail m) +
          modes.sum central) + modes.sum rightTail := by
      exact congrArg
        (fun value : ℝ => value + modes.sum rightTail)
        hcentralSplit
    _ =
        ((modes.sum crossing + modes.sum leftTail) +
          modes.sum central) + modes.sum rightTail := by
      exact congrArg
        (fun value : ℝ =>
          (value + modes.sum central) + modes.sum rightTail)
        hleftSplit
    _ = Complex.logarithmicPhaseBProcessInteriorBudget t a b := by
      rfl

theorem Complex.logarithmicPhaseBProcessInteriorNormSum_le_budget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
      ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖) ≤
      Complex.logarithmicPhaseBProcessInteriorBudget t a b := by
  have hpointwise := Finset.sum_le_sum (fun m hm =>
    Complex.norm_integerBlockFourierPacket_le_BProcessStationaryMajorant
      t ht ht_nonneg a b m ha hab hm)
  exact le_trans hpointwise
    (le_of_eq
      (Complex.sum_logarithmicPhaseBProcessStationaryPacketMajorant_eq_budget
        t a b))

theorem Complex.norm_logarithmicPhaseBProcessInterior_packet_tsum_le_budget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      Complex.logarithmicPhaseBProcessInteriorBudget t a b := by
  let modes := Complex.logarithmicPhasePoissonBProcessInteriorModes t a b
  let packet : ℤ → ℂ := fun m =>
    Complex.integerBlockFourierPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m
  have hfinite :
      (∑' m : {m : ℤ // m ∈ modes}, packet m) =
        ∑ m ∈ modes, packet m :=
    modes.tsum_subtype packet
  have htriangle :
      ‖∑ m ∈ modes, packet m‖ ≤
        ∑ m ∈ modes, ‖packet m‖ :=
    norm_sum_le _ _
  have hbudget :=
    Complex.logarithmicPhaseBProcessInteriorNormSum_le_budget
      t ht ht_nonneg a b ha hab
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤ Complex.logarithmicPhaseBProcessInteriorBudget t a b)
    hfinite.symm
    (le_trans htriangle hbudget)

theorem Complex.logarithmicPhaseBProcessInteriorCrossingBudget_eq_card_mul
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseBProcessInteriorCrossingBudget t a b =
      ((Complex.logarithmicPhasePoissonBProcessInteriorModes t a b).card : ℝ) *
        (4 / 3 : ℝ) := by
  unfold Complex.logarithmicPhaseBProcessInteriorCrossingBudget
  exact Finset.sum_const_real_eq_card_mul
    (Complex.logarithmicPhasePoissonBProcessInteriorModes t a b)
    (4 / 3)

end

end LFunctions
end Boundary
