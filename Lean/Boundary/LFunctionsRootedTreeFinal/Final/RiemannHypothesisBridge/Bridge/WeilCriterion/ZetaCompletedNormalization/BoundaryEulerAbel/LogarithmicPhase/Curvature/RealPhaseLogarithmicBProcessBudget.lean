import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicQuantitativeActiveBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedComplementAssembly

/-!
# Exact logarithmic B-process budget

The quantitative Poisson sum is partitioned into the balanced active family,
the finite in-range inactive family, and the two summable outside tails.  This
owner records both the four analytic packet classes and the public
three-component presentation used by arithmetic closure.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseBProcessActiveWindowPacketBudget
    (t : ℝ) (a b m : ℤ) : ℝ :=
  if m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b then
    Complex.logarithmicPhaseBProcessLeftTailBudget t m +
      Complex.logarithmicPhaseBProcessWindowWidth t m +
        Complex.logarithmicPhaseBProcessRightTailBudget t m
  else
    Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
      2 * Complex.logarithmicPhaseBProcessRadius t m +
        Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m

def Complex.logarithmicPhaseBProcessActiveWindowBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonActiveModes t a b,
    Complex.logarithmicPhaseBProcessActiveWindowPacketBudget t a b m

def Complex.logarithmicPhaseBProcessCrossingBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ _m ∈ Complex.logarithmicPhasePoissonActiveModes t a b, (2 / 3 : ℝ)

def Complex.logarithmicPhaseBProcessComplementTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseAdaptedComplementBudget t a b

def Complex.logarithmicPhaseBProcessThreeComponentBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseBProcessActiveWindowBudget t a b +
    Complex.logarithmicPhaseBProcessCrossingBudget t a b +
      Complex.logarithmicPhaseBProcessComplementTailBudget t a b

def Complex.logarithmicPhaseBProcessFourClassBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseBProcessActiveWindowBudget t a b +
    Complex.logarithmicPhaseBProcessCrossingBudget t a b +
    Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b +
      Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b +
        Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b

theorem Complex.logarithmicPhaseBProcessLeftTailBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    0 ≤ Complex.logarithmicPhaseBProcessLeftTailBudget t m := by
  have hwindow := Complex.logarithmicPhaseBProcessWindowLeft_nonneg t ht hm
  have hproduct := mul_nonneg hwindow
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have hquotient := div_nonneg hproduct (norm_nonneg t)
  have htwice := mul_nonneg (Nat.cast_nonneg 2) hquotient
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (Complex.logarithmicPhaseBProcessLeftTailBudget_eq t ht hm).symm
    htwice

theorem Complex.logarithmicPhaseBProcessRightTailBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    0 ≤ Complex.logarithmicPhaseBProcessRightTailBudget t m := by
  have hcenterPos :=
    Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm
  have hwindowPos := lt_of_lt_of_le hcenterPos
    (Complex.logarithmicPhaseBProcess_center_lt_WindowRight t ht hm).le
  have hproduct := mul_nonneg hwindowPos.le
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have hquotient := div_nonneg hproduct (norm_nonneg t)
  have htwice := mul_nonneg (Nat.cast_nonneg 2) hquotient
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (Complex.logarithmicPhaseBProcessRightTailBudget_eq t ht hm).symm
    htwice

theorem Complex.logarithmicPhaseBProcessWindowWidth_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    0 ≤ Complex.logarithmicPhaseBProcessWindowWidth t m := by
  have hradius := Complex.logarithmicPhaseBProcessRadius_nonneg t ht hm
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (Complex.logarithmicPhaseBProcessWindowWidth_eq_two_mul_radius t m).symm
    (mul_nonneg (Nat.cast_nonneg 2) hradius)

theorem Complex.logarithmicPhaseBProcessClippedLeftTailBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a m : ℤ) (hm : m < 0) :
    0 ≤ Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m := by
  match Classical.em
      ((a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m) with
  | Or.inl hraw =>
      have hvalue :
          Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m =
            Complex.logarithmicPhaseBProcessLeftTailBudget t m := by
        unfold Complex.logarithmicPhaseBProcessClippedLeftTailBudget
        exact if_pos hraw
      have hnonneg :=
        Complex.logarithmicPhaseBProcessLeftTailBudget_nonneg t ht hm
      exact Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        hvalue.symm hnonneg
  | Or.inr hraw =>
      have hvalue :
          Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m = 0 := by
        unfold Complex.logarithmicPhaseBProcessClippedLeftTailBudget
        exact if_neg hraw
      exact Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        hvalue.symm le_rfl

theorem Complex.logarithmicPhaseBProcessClippedRightTailBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (b m : ℤ) (hm : m < 0) :
    0 ≤ Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m := by
  match Classical.em
      (Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ)) with
  | Or.inl hraw =>
      have hvalue :
          Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m =
            Complex.logarithmicPhaseBProcessRightTailBudget t m := by
        unfold Complex.logarithmicPhaseBProcessClippedRightTailBudget
        exact if_pos hraw
      have hnonneg :=
        Complex.logarithmicPhaseBProcessRightTailBudget_nonneg t ht hm
      exact Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        hvalue.symm hnonneg
  | Or.inr hraw =>
      have hvalue :
          Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m = 0 := by
        unfold Complex.logarithmicPhaseBProcessClippedRightTailBudget
        exact if_neg hraw
      exact Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        hvalue.symm le_rfl

theorem Complex.logarithmicPhaseBProcessActiveWindowPacketBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b m : ℤ)
    (hm : m ∈ Complex.logarithmicPhasePoissonActiveModes t a b) :
    0 ≤ Complex.logarithmicPhaseBProcessActiveWindowPacketBudget t a b m := by
  match Classical.em
      (m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) with
  | Or.inl hinterior =>
      have hmNeg :=
        ((Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
          t a b m).mp hinterior).2.1
      have hnonneg := add_nonneg
        (add_nonneg
          (Complex.logarithmicPhaseBProcessLeftTailBudget_nonneg t ht hmNeg)
          (Complex.logarithmicPhaseBProcessWindowWidth_nonneg t ht hmNeg))
        (Complex.logarithmicPhaseBProcessRightTailBudget_nonneg t ht hmNeg)
      have hvalue :
          Complex.logarithmicPhaseBProcessActiveWindowPacketBudget t a b m =
            Complex.logarithmicPhaseBProcessLeftTailBudget t m +
              Complex.logarithmicPhaseBProcessWindowWidth t m +
                Complex.logarithmicPhaseBProcessRightTailBudget t m := by
        unfold Complex.logarithmicPhaseBProcessActiveWindowPacketBudget
        exact if_pos hinterior
      exact Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        hvalue.symm hnonneg
  | Or.inr hnotInterior =>
      have hendpoint :
          m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b := by
        unfold Complex.logarithmicPhasePoissonBProcessEndpointModes
        exact Finset.mem_sdiff.mpr (And.intro hm hnotInterior)
      have hmNeg :=
        Complex.logarithmicPhasePoissonBProcessEndpointMode_negative
          t a b hendpoint
      have hradius := Complex.logarithmicPhaseBProcessRadius_nonneg t ht hmNeg
      have hnonneg := add_nonneg
        (add_nonneg
          (Complex.logarithmicPhaseBProcessClippedLeftTailBudget_nonneg
            t ht a m hmNeg)
          (mul_nonneg (Nat.cast_nonneg 2) hradius))
        (Complex.logarithmicPhaseBProcessClippedRightTailBudget_nonneg
          t ht b m hmNeg)
      have hvalue :
          Complex.logarithmicPhaseBProcessActiveWindowPacketBudget t a b m =
            Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
              2 * Complex.logarithmicPhaseBProcessRadius t m +
                Complex.logarithmicPhaseBProcessClippedRightTailBudget
                  t b m := by
        unfold Complex.logarithmicPhaseBProcessActiveWindowPacketBudget
        exact if_neg hnotInterior
      exact Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        hvalue.symm hnonneg

theorem Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget_eq_crossing_add_window
    (t : ℝ) (a b m : ℤ) :
    Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget t a b m =
      2 / 3 +
        Complex.logarithmicPhaseBProcessActiveWindowPacketBudget t a b m := by
  match Classical.em
      (m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) with
  | Or.inl hinterior =>
      let crossing : ℝ := 2 / 3
      let left := Complex.logarithmicPhaseBProcessLeftTailBudget t m
      let middle := Complex.logarithmicPhaseBProcessWindowWidth t m
      let right := Complex.logarithmicPhaseBProcessRightTailBudget t m
      have hquantitative :
          Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget
              t a b m =
            crossing + left + middle + right := by
        unfold Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget
        unfold Complex.logarithmicPhaseBProcessQuantitativeInteriorPacketBudget
        exact if_pos hinterior
      have hwindow :
          Complex.logarithmicPhaseBProcessActiveWindowPacketBudget t a b m =
            left + middle + right := by
        unfold Complex.logarithmicPhaseBProcessActiveWindowPacketBudget
        exact if_pos hinterior
      have hassociate :
          crossing + left + middle + right =
            crossing + (left + middle + right) :=
        Eq.trans
          (congrArg (fun value : ℝ => value + right)
            (add_assoc crossing left middle))
          (add_assoc crossing (left + middle) right)
      exact hquantitative.trans
        (hassociate.trans
          (congrArg (fun value : ℝ => crossing + value) hwindow.symm))
  | Or.inr hnotInterior =>
      let crossing : ℝ := 2 / 3
      let left :=
        Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m
      let middle := 2 * Complex.logarithmicPhaseBProcessRadius t m
      let right :=
        Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m
      have hquantitative :
          Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget
              t a b m =
            crossing + left + middle + right := by
        unfold Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget
        unfold Complex.logarithmicPhaseBProcessQuantitativeEndpointPacketBudget
        exact if_neg hnotInterior
      have hwindow :
          Complex.logarithmicPhaseBProcessActiveWindowPacketBudget t a b m =
            left + middle + right := by
        unfold Complex.logarithmicPhaseBProcessActiveWindowPacketBudget
        exact if_neg hnotInterior
      have hassociate :
          crossing + left + middle + right =
            crossing + (left + middle + right) :=
        Eq.trans
          (congrArg (fun value : ℝ => value + right)
            (add_assoc crossing left middle))
          (add_assoc crossing (left + middle) right)
      exact hquantitative.trans
        (hassociate.trans
          (congrArg (fun value : ℝ => crossing + value) hwindow.symm))

theorem Complex.logarithmicPhaseBProcessQuantitativeActiveBudget_eq_crossing_add_window
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseBProcessQuantitativeActiveBudget t a b =
      Complex.logarithmicPhaseBProcessCrossingBudget t a b +
        Complex.logarithmicPhaseBProcessActiveWindowBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeActiveBudget
  unfold Complex.logarithmicPhaseBProcessCrossingBudget
  unfold Complex.logarithmicPhaseBProcessActiveWindowBudget
  have hpoint :
      (∑ m ∈ Complex.logarithmicPhasePoissonActiveModes t a b,
          Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget
            t a b m) =
        ∑ m ∈ Complex.logarithmicPhasePoissonActiveModes t a b,
          ((2 / 3 : ℝ) +
            Complex.logarithmicPhaseBProcessActiveWindowPacketBudget t a b m) :=
    Finset.sum_congr
      (Eq.refl (Complex.logarithmicPhasePoissonActiveModes t a b))
      (fun m hm =>
        Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget_eq_crossing_add_window
          t a b m)
  have hsplit := Finset.sum_add_distrib
    (s := Complex.logarithmicPhasePoissonActiveModes t a b)
    (f := fun _m : ℤ => (2 / 3 : ℝ))
    (g := Complex.logarithmicPhaseBProcessActiveWindowPacketBudget t a b)
  exact hpoint.trans hsplit

theorem Complex.logarithmicPhaseBProcessActiveWindowBudget_nonneg
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    0 ≤ Complex.logarithmicPhaseBProcessActiveWindowBudget
      t (a : ℤ) (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessActiveWindowBudget
  exact Finset.sum_nonneg (fun m hm =>
    Complex.logarithmicPhaseBProcessActiveWindowPacketBudget_nonneg
      t ht (a : ℤ) (b : ℤ) m hm)

theorem Complex.logarithmicPhaseBProcessCrossingBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseBProcessCrossingBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessCrossingBudget
  exact Finset.sum_nonneg (fun m hm =>
    div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))

theorem Complex.logarithmicPhaseBProcessComplementTailBudget_nonneg
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseBProcessComplementTailBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessComplementTailBudget
  exact Complex.logarithmicPhaseAdaptedComplementBudget_nonneg
    t a b ha hab

theorem Complex.logarithmicPhaseBProcessThreeComponentBudget_nonneg
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    0 ≤ Complex.logarithmicPhaseBProcessThreeComponentBudget
      t (a : ℤ) (b : ℤ) := by
  have hactive :=
    Complex.logarithmicPhaseBProcessActiveWindowBudget_nonneg
      ht ht_nonneg hgeometry
  have hcrossing :=
    Complex.logarithmicPhaseBProcessCrossingBudget_nonneg
      t (a : ℤ) (b : ℤ)
  have hcomplement :=
    Complex.logarithmicPhaseBProcessComplementTailBudget_nonneg
      t (a : ℤ) (b : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_order hgeometry))
  exact add_nonneg (add_nonneg hactive hcrossing) hcomplement

theorem Complex.logarithmicPhaseBProcessThreeComponentBudget_eq_fourClassBudget
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseBProcessThreeComponentBudget t a b =
      Complex.logarithmicPhaseBProcessFourClassBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessThreeComponentBudget
  unfold Complex.logarithmicPhaseBProcessComplementTailBudget
  unfold Complex.logarithmicPhaseBProcessFourClassBudget
  have hcomplement :=
    Complex.logarithmicPhaseAdaptedComplementBudget_eq_finite_add_tails
      t a b
  let A := Complex.logarithmicPhaseBProcessActiveWindowBudget t a b
  let C := Complex.logarithmicPhaseBProcessCrossingBudget t a b
  let I := Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b
  let N := Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b
  let P := Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b
  calc
    A + C + Complex.logarithmicPhaseAdaptedComplementBudget t a b =
        A + C + (I + N + P) := by
      exact congrArg (fun value : ℝ => A + C + value) hcomplement
    _ = ((A + C) + I) + N + P := by
      exact Eq.trans
        (add_assoc (A + C) (I + N) P).symm
        (congrArg (fun value : ℝ => value + P)
          (add_assoc (A + C) I N).symm)

theorem Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_BProcessThreeComponentBudget
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          t (a : ℤ) (b : ℤ) m‖ ≤
      Complex.logarithmicPhaseBProcessThreeComponentBudget
        t (a : ℤ) (b : ℤ) := by
  have ha : (1 : ℤ) ≤ (a : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hab : (a : ℤ) ≤ (b : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hglobalAtNorm :=
    Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_active_add_adaptedComplement
      t (a : ℤ) (b : ℤ) ha hab
  have hnorm : ‖t‖ = t := Real.norm_of_nonneg ht_nonneg
  have hglobal :
      ‖∑' m : ℤ,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket
            t (a : ℤ) (b : ℤ) m‖ ≤
        ‖∑' m : {m : ℤ //
            m ∈ Complex.logarithmicPhasePoissonActiveModes
              t (a : ℤ) (b : ℤ)},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket
            t (a : ℤ) (b : ℤ) m‖ +
          Complex.logarithmicPhaseAdaptedComplementBudget
            t (a : ℤ) (b : ℤ) :=
    Eq.subst
      (motive := fun packetParameter : ℝ =>
        ‖∑' m : ℤ,
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket
              packetParameter (a : ℤ) (b : ℤ) m‖ ≤
          ‖∑' m : {m : ℤ //
              m ∈ Complex.logarithmicPhasePoissonActiveModes
                t (a : ℤ) (b : ℤ)},
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket
              packetParameter (a : ℤ) (b : ℤ) m‖ +
            Complex.logarithmicPhaseAdaptedComplementBudget
              t (a : ℤ) (b : ℤ))
      hnorm hglobalAtNorm
  have hactive :=
    Complex.norm_logarithmicPhaseQuantitativeActive_tsum_le_BProcessBudget
      ht ht_nonneg hgeometry
  have hcombined := add_le_add_right hactive
    (Complex.logarithmicPhaseAdaptedComplementBudget
      t (a : ℤ) (b : ℤ))
  have hactiveSplit :=
    Complex.logarithmicPhaseBProcessQuantitativeActiveBudget_eq_crossing_add_window
      t (a : ℤ) (b : ℤ)
  have htarget :
      Complex.logarithmicPhaseBProcessQuantitativeActiveBudget
          t (a : ℤ) (b : ℤ) +
        Complex.logarithmicPhaseAdaptedComplementBudget
          t (a : ℤ) (b : ℤ) =
      Complex.logarithmicPhaseBProcessThreeComponentBudget
          t (a : ℤ) (b : ℤ) := by
    unfold Complex.logarithmicPhaseBProcessThreeComponentBudget
    unfold Complex.logarithmicPhaseBProcessComplementTailBudget
    exact (congrArg
      (fun value : ℝ => value +
        Complex.logarithmicPhaseAdaptedComplementBudget
          t (a : ℤ) (b : ℤ)) hactiveSplit).trans
      (congrArg
        (fun value : ℝ => value +
          Complex.logarithmicPhaseAdaptedComplementBudget
            t (a : ℤ) (b : ℤ))
        (add_comm
          (Complex.logarithmicPhaseBProcessCrossingBudget
            t (a : ℤ) (b : ℤ))
          (Complex.logarithmicPhaseBProcessActiveWindowBudget
            t (a : ℤ) (b : ℤ))))
  exact le_trans hglobal
    (le_trans hcombined (le_of_eq htarget))

theorem Complex.logarithmicPhaseBProcessComplementTailBudget_eq_finite_add_tails
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseBProcessComplementTailBudget t a b =
      Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b +
        Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b +
          Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessComplementTailBudget
  exact Complex.logarithmicPhaseAdaptedComplementBudget_eq_finite_add_tails
    t a b

end

end LFunctions
end Boundary
