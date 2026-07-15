import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicEndpointAngularCompletion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedComplementAssembly

/-!
# Balanced active budget for the quantitative Poisson packet

The exact reconstruction uses `logarithmicPhaseQuantitativeBlockFourierPacket`.
Its principal oscillation is the one already controlled by the balanced
B-process.  Only the cutoff crossing contribution changes, from `4/3` to
`2/3`.  This owner transports both interior and universal endpoint estimates
to the quantitative packet and assembles their disjoint active sum.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseBProcessQuantitativeInteriorPacketBudget
    (t : ℝ) (m : ℤ) : ℝ :=
  2 / 3 +
    Complex.logarithmicPhaseBProcessLeftTailBudget t m +
      Complex.logarithmicPhaseBProcessWindowWidth t m +
        Complex.logarithmicPhaseBProcessRightTailBudget t m

def Complex.logarithmicPhaseBProcessQuantitativeEndpointPacketBudget
    (t : ℝ) (a b m : ℤ) : ℝ :=
  2 / 3 +
    Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
      2 * Complex.logarithmicPhaseBProcessRadius t m +
        Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m

def Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget
    (t : ℝ) (a b m : ℤ) : ℝ :=
  if m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b then
    Complex.logarithmicPhaseBProcessQuantitativeInteriorPacketBudget t m
  else
    Complex.logarithmicPhaseBProcessQuantitativeEndpointPacketBudget t a b m

def Complex.logarithmicPhaseBProcessQuantitativeActiveBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonActiveModes t a b,
    Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget t a b m

theorem Complex.logarithmicPhaseBProcessQuantitativeInteriorPacketBudget_eq
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhaseBProcessQuantitativeInteriorPacketBudget t m =
      2 / 3 +
        (Complex.logarithmicPhaseBProcessLeftTailBudget t m +
          Complex.logarithmicPhaseBProcessWindowWidth t m +
            Complex.logarithmicPhaseBProcessRightTailBudget t m) := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeInteriorPacketBudget
  calc
    (2 / 3 + Complex.logarithmicPhaseBProcessLeftTailBudget t m) +
          Complex.logarithmicPhaseBProcessWindowWidth t m +
        Complex.logarithmicPhaseBProcessRightTailBudget t m =
      (2 / 3 +
          (Complex.logarithmicPhaseBProcessLeftTailBudget t m +
            Complex.logarithmicPhaseBProcessWindowWidth t m)) +
        Complex.logarithmicPhaseBProcessRightTailBudget t m := by
      exact congrArg
        (fun value : ℝ => value +
          Complex.logarithmicPhaseBProcessRightTailBudget t m)
        (add_assoc _ _ _)
    _ = 2 / 3 +
        (Complex.logarithmicPhaseBProcessLeftTailBudget t m +
          Complex.logarithmicPhaseBProcessWindowWidth t m +
            Complex.logarithmicPhaseBProcessRightTailBudget t m) :=
      add_assoc _ _ _

theorem Complex.logarithmicPhaseBProcessQuantitativeEndpointPacketBudget_eq
    (t : ℝ) (a b m : ℤ) :
    Complex.logarithmicPhaseBProcessQuantitativeEndpointPacketBudget t a b m =
      2 / 3 +
        (Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
          2 * Complex.logarithmicPhaseBProcessRadius t m +
            Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m) := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeEndpointPacketBudget
  calc
    (2 / 3 + Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m) +
          2 * Complex.logarithmicPhaseBProcessRadius t m +
        Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m =
      (2 / 3 +
          (Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
            2 * Complex.logarithmicPhaseBProcessRadius t m)) +
        Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m := by
      exact congrArg
        (fun value : ℝ => value +
          Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m)
        (add_assoc _ _ _)
    _ = 2 / 3 +
        (Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
          2 * Complex.logarithmicPhaseBProcessRadius t m +
            Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m) :=
      add_assoc _ _ _

theorem Complex.logarithmicPhaseBProcessStationaryPacketMajorant_eq_crossing_add
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhaseBProcessStationaryPacketMajorant t m =
      4 / 3 +
        (Complex.logarithmicPhaseBProcessLeftTailBudget t m +
          Complex.logarithmicPhaseBProcessWindowWidth t m +
            Complex.logarithmicPhaseBProcessRightTailBudget t m) := by
  unfold Complex.logarithmicPhaseBProcessStationaryPacketMajorant
  calc
    (4 / 3 + Complex.logarithmicPhaseBProcessLeftTailBudget t m) +
          Complex.logarithmicPhaseBProcessWindowWidth t m +
        Complex.logarithmicPhaseBProcessRightTailBudget t m =
      (4 / 3 +
          (Complex.logarithmicPhaseBProcessLeftTailBudget t m +
            Complex.logarithmicPhaseBProcessWindowWidth t m)) +
        Complex.logarithmicPhaseBProcessRightTailBudget t m := by
      exact congrArg
        (fun value : ℝ => value +
          Complex.logarithmicPhaseBProcessRightTailBudget t m)
        (add_assoc _ _ _)
    _ = 4 / 3 +
        (Complex.logarithmicPhaseBProcessLeftTailBudget t m +
          Complex.logarithmicPhaseBProcessWindowWidth t m +
            Complex.logarithmicPhaseBProcessRightTailBudget t m) :=
      add_assoc _ _ _

theorem Complex.norm_logarithmicPhaseBProcessInteriorPrincipal_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    ‖∫ x in (a : ℝ)..(b : ℝ),
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x‖ ≤
      Complex.logarithmicPhaseBProcessLeftTailBudget t m +
        Complex.logarithmicPhaseBProcessWindowWidth t m +
          Complex.logarithmicPhaseBProcessRightTailBudget t m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mp hm
  have hbounds :=
    Complex.logarithmicPhaseBProcessWindow_bounds_of_mem t a b m hm
  have horder :
      Complex.logarithmicPhaseBProcessWindowLeft t m ≤
        Complex.logarithmicPhaseBProcessWindowRight t m :=
    le_trans
      (Complex.logarithmicPhaseBProcessWindowLeft_lt_center
        t ht hmem.2.1).le
      (Complex.logarithmicPhaseBProcess_center_lt_WindowRight
        t ht hmem.2.1).le
  have hleft :=
    Complex.norm_logarithmicPhaseBProcessLeftTail_le
      t ht ht_nonneg a b m ha hm
  have hright :=
    Complex.norm_logarithmicPhaseBProcessRightTail_le
      t ht ht_nonneg a b m ha hm
  have hcentral :=
    Complex.norm_logarithmicPhaseBProcessCentralIntegral_le_width
      t ht a b m hm
  have hwidth :=
    Complex.logarithmicPhaseBProcessWindowWidth_eq_two_mul_radius t m
  have hcentralTwo :
      ‖∫ x in Complex.logarithmicPhaseBProcessWindowLeft t m..
          Complex.logarithmicPhaseBProcessWindowRight t m,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤
        2 * Complex.logarithmicPhaseBProcessRadius t m :=
    Eq.subst
      (motive := fun value : ℝ =>
        ‖∫ x in Complex.logarithmicPhaseBProcessWindowLeft t m..
            Complex.logarithmicPhaseBProcessWindowRight t m,
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m) x‖ ≤ value)
      hwidth hcentral
  have hprincipal :=
    Complex.norm_logarithmicPhaseQuantitativeEndpoint_principal_le
      t ht_nonneg a b m
      (Complex.logarithmicPhaseBProcessWindowLeft t m)
      (Complex.logarithmicPhaseBProcessWindowRight t m)
      (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessRadius t m)
      ha hbounds.1 horder hbounds.2 hleft hright hcentralTwo
  exact Eq.subst
    (motive := fun value : ℝ =>
      ‖∫ x in (a : ℝ)..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤
        Complex.logarithmicPhaseBProcessLeftTailBudget t m + value +
          Complex.logarithmicPhaseBProcessRightTailBudget t m)
    hwidth.symm hprincipal

theorem Complex.norm_logarithmicPhaseQuantitativeInteriorPacket_le_BProcessBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseBProcessQuantitativeInteriorPacketBudget t m := by
  have hprincipal :=
    Complex.norm_logarithmicPhaseBProcessInteriorPrincipal_le
      t ht ht_nonneg a b m ha hab hm
  have hpacket :=
    Complex.norm_logarithmicPhaseQuantitativePacket_le_crossings_add_principal
      t a b m ha hab hprincipal
  exact Eq.subst
    (motive := fun value : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤ value)
    (Complex.logarithmicPhaseBProcessQuantitativeInteriorPacketBudget_eq t m).symm
    hpacket

theorem Complex.norm_logarithmicPhaseQuantitativeEndpointPacket_le_BProcessBudget
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
        t (a : ℤ) (b : ℤ) m‖ ≤
      Complex.logarithmicPhaseBProcessQuantitativeEndpointPacketBudget
        t (a : ℤ) (b : ℤ) m := by
  have ha : (1 : ℤ) ≤ (a : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hab : (a : ℤ) ≤ (b : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hmNeg :=
    Complex.logarithmicPhaseBProcessEndpointMode_negative_nat hm
  have horder :=
    Complex.logarithmicPhaseBProcessEndpointMode_clippedWindow_order
      hgeometry hm
  have hprincipal :=
    Complex.norm_logarithmicPhaseBProcessUniversalPrincipal_le
      t ht ht_nonneg (a : ℤ) (b : ℤ) m ha hab hmNeg horder
  have hpacket :=
    Complex.norm_logarithmicPhaseQuantitativePacket_le_crossings_add_principal
      t (a : ℤ) (b : ℤ) m ha hab hprincipal
  exact Eq.subst
    (motive := fun value : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
        t (a : ℤ) (b : ℤ) m‖ ≤ value)
    (Complex.logarithmicPhaseBProcessQuantitativeEndpointPacketBudget_eq
      t (a : ℤ) (b : ℤ) m).symm
    hpacket

theorem Complex.norm_logarithmicPhaseQuantitativeActivePacket_le_BProcessBudget
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonActiveModes
      t (a : ℤ) (b : ℤ)) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
        t (a : ℤ) (b : ℤ) m‖ ≤
      Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget
        t (a : ℤ) (b : ℤ) m := by
  have hpartition :=
    Complex.logarithmicPhasePoissonActiveMode_mem_interior_or_endpoint
      t ht (a : ℤ) (b : ℤ) hm
  match hpartition with
  | Or.inl hinterior =>
      have ha : (1 : ℤ) ≤ (a : ℤ) := Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
      have hab : (a : ℤ) ≤ (b : ℤ) := Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
      have hpacket :=
        Complex.norm_logarithmicPhaseQuantitativeInteriorPacket_le_BProcessBudget
          t ht ht_nonneg (a : ℤ) (b : ℤ) m ha hab hinterior
      unfold Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget
      exact hpacket.trans_eq (if_pos hinterior).symm
  | Or.inr hendpoint =>
      have hpacket :=
        Complex.norm_logarithmicPhaseQuantitativeEndpointPacket_le_BProcessBudget
          ht ht_nonneg hgeometry hendpoint
      have hnotInterior :=
        Complex.logarithmicPhasePoissonEndpointMode_not_interior
          t (a : ℤ) (b : ℤ) hendpoint
      unfold Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget
      exact hpacket.trans_eq (if_neg hnotInterior).symm

theorem Complex.norm_logarithmicPhaseQuantitativeActive_tsum_le_BProcessBudget
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonActiveModes
          t (a : ℤ) (b : ℤ)},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          t (a : ℤ) (b : ℤ) m‖ ≤
      Complex.logarithmicPhaseBProcessQuantitativeActiveBudget
        t (a : ℤ) (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeActiveBudget
  have hpoint :
      ∀ m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes
            t (a : ℤ) (b : ℤ)},
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          t (a : ℤ) (b : ℤ) m‖ ≤
          Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget
            t (a : ℤ) (b : ℤ) m :=
    fun m =>
      Complex.norm_logarithmicPhaseQuantitativeActivePacket_le_BProcessBudget
        ht ht_nonneg hgeometry m.property
  exact
    Complex.norm_logarithmicPhaseQuantitative_selectedPacket_tsum_le_finset_majorant_sum
      t (a : ℤ) (b : ℤ)
      (Complex.logarithmicPhasePoissonActiveModes
        t (a : ℤ) (b : ℤ))
      (Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget
        t (a : ℤ) (b : ℤ))
      (fun m hm => hpoint ⟨m, hm⟩)

theorem Complex.logarithmicPhaseBProcessQuantitativeActiveBudget_le_completeActiveBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) :
    Complex.logarithmicPhaseBProcessQuantitativeActiveBudget t a b ≤
      Complex.logarithmicPhaseBProcessCompleteActiveBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeActiveBudget
  have hpoint :
      ∀ m ∈ Complex.logarithmicPhasePoissonActiveModes t a b,
        Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget t a b m ≤
          Complex.logarithmicPhaseBProcessCompleteActivePacketBudget t a b m := by
    intro m hm
    unfold Complex.logarithmicPhaseBProcessQuantitativeActivePacketBudget
    unfold Complex.logarithmicPhaseBProcessCompleteActivePacketBudget
    match Classical.em
        (m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) with
    | Or.inl hinterior =>
        have htwoAddTwo : (2 : ℝ) + 2 = 4 :=
          Real.endpoint_nat_cast_add 2 2 4 rfl
        have htwoLeFour : (2 : ℝ) ≤ 4 := Eq.subst
          (motive := fun value : ℝ => (2 : ℝ) ≤ value)
          htwoAddTwo
          (le_add_of_nonneg_right (Nat.cast_nonneg 2))
        have hconstant : (2 / 3 : ℝ) ≤ 4 / 3 := by
          exact div_le_div_of_nonneg_right
            htwoLeFour
            (Nat.cast_nonneg 3)
        have hraw := add_le_add_right hconstant
          (Complex.logarithmicPhaseBProcessLeftTailBudget t m +
            Complex.logarithmicPhaseBProcessWindowWidth t m +
              Complex.logarithmicPhaseBProcessRightTailBudget t m)
        have hbranch :
            Complex.logarithmicPhaseBProcessQuantitativeInteriorPacketBudget t m ≤
              Complex.logarithmicPhaseBProcessStationaryPacketMajorant t m :=
          Eq.subst
            (motive := fun value : ℝ => value ≤
              Complex.logarithmicPhaseBProcessStationaryPacketMajorant t m)
            (Complex.logarithmicPhaseBProcessQuantitativeInteriorPacketBudget_eq
              t m).symm
            (Eq.subst
              (motive := fun value : ℝ =>
                2 / 3 +
                    (Complex.logarithmicPhaseBProcessLeftTailBudget t m +
                      Complex.logarithmicPhaseBProcessWindowWidth t m +
                        Complex.logarithmicPhaseBProcessRightTailBudget t m) ≤ value)
              (Complex.logarithmicPhaseBProcessStationaryPacketMajorant_eq_crossing_add
                t m).symm
              hraw)
        have hsource :
            (if m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b then
                Complex.logarithmicPhaseBProcessQuantitativeInteriorPacketBudget t m
              else Complex.logarithmicPhaseBProcessQuantitativeEndpointPacketBudget t a b m) =
              Complex.logarithmicPhaseBProcessQuantitativeInteriorPacketBudget t m :=
          if_pos hinterior
        have htarget :
            (if m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b then
                Complex.logarithmicPhaseBProcessStationaryPacketMajorant t m
              else Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m) =
              Complex.logarithmicPhaseBProcessStationaryPacketMajorant t m :=
          if_pos hinterior
        exact Eq.subst (motive := fun value : ℝ => value ≤ _)
          hsource.symm
          (Eq.subst (motive := fun value : ℝ => _ ≤ value)
            htarget.symm hbranch)
    | Or.inr hnotInterior =>
        have htwoAddTwo : (2 : ℝ) + 2 = 4 :=
          Real.endpoint_nat_cast_add 2 2 4 rfl
        have htwoLeFour : (2 : ℝ) ≤ 4 := Eq.subst
          (motive := fun value : ℝ => (2 : ℝ) ≤ value)
          htwoAddTwo
          (le_add_of_nonneg_right (Nat.cast_nonneg 2))
        have hconstant : (2 / 3 : ℝ) ≤ 4 / 3 := by
          exact div_le_div_of_nonneg_right
            htwoLeFour
            (Nat.cast_nonneg 3)
        have hraw := add_le_add_right hconstant
          (Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
            2 * Complex.logarithmicPhaseBProcessRadius t m +
              Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m)
        have hbranch :
            Complex.logarithmicPhaseBProcessQuantitativeEndpointPacketBudget t a b m ≤
              Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m :=
          Eq.subst
            (motive := fun value : ℝ => value ≤
              Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m)
            (Complex.logarithmicPhaseBProcessQuantitativeEndpointPacketBudget_eq
              t a b m).symm
            (Eq.subst
              (motive := fun value : ℝ =>
                2 / 3 +
                    (Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
                      2 * Complex.logarithmicPhaseBProcessRadius t m +
                        Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m) ≤ value)
              (Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_eq_crossing_add
                t a b m).symm
              hraw)
        have hsource :
            (if m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b then
                Complex.logarithmicPhaseBProcessQuantitativeInteriorPacketBudget t m
              else Complex.logarithmicPhaseBProcessQuantitativeEndpointPacketBudget t a b m) =
              Complex.logarithmicPhaseBProcessQuantitativeEndpointPacketBudget t a b m :=
          if_neg hnotInterior
        have htarget :
            (if m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b then
                Complex.logarithmicPhaseBProcessStationaryPacketMajorant t m
              else Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m) =
              Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m :=
          if_neg hnotInterior
        exact Eq.subst (motive := fun value : ℝ => value ≤ _)
          hsource.symm
          (Eq.subst (motive := fun value : ℝ => _ ≤ value)
            htarget.symm hbranch)
  have hsum := Finset.sum_le_sum hpoint
  exact hsum.trans_eq
    (Complex.sum_completeActivePacketBudget_eq_completeActiveBudget
      t ht a b)

end

end LFunctions
end Boundary
