import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CanonicalWindows

/-!
# Active Poisson budget with canonical stationary windows

The active family is split using the genuine mode-dependent stationary radius.
The finite endpoint remainder is retained explicitly, while the canonical
interior family is controlled by the stationary packet owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhasePoissonCanonicalEndpointModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  Complex.logarithmicPhasePoissonActiveModes t a b \
    Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b

theorem Complex.logarithmicPhasePoissonCanonicalInteriorModes_subset_activeModes
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b ⊆
      Complex.logarithmicPhasePoissonActiveModes t a b := by
  intro m hm
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
      t a b m).mp hm
  have hradius_nonneg :
      0 ≤ Complex.logarithmicPhasePoissonCanonicalRadius t m :=
    Complex.logarithmicPhasePoissonCanonicalRadius_nonneg t m
  have htwo_nonneg : 0 ≤ (2 / 3 : ℝ) := by
    exact div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3)
  have ha_center : (a : ℝ) ≤
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
    have hsub :
        Complex.logarithmicPhaseFourierStationaryPoint t m -
            Complex.logarithmicPhasePoissonCanonicalRadius t m ≤
          Complex.logarithmicPhaseFourierStationaryPoint t m :=
      sub_le_self _ hradius_nonneg
    exact le_trans hmem.2.2.1 hsub
  have hcenter_b :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤ (b : ℝ) := by
    have hadd :
        Complex.logarithmicPhaseFourierStationaryPoint t m ≤
          Complex.logarithmicPhaseFourierStationaryPoint t m +
            Complex.logarithmicPhasePoissonCanonicalRadius t m :=
      le_add_of_nonneg_right hradius_nonneg
    exact le_trans hadd hmem.2.2.2
  have hleft :
      Real.integerBlockCutoffSupportLeftEndpoint a ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m := by
    unfold Real.integerBlockCutoffSupportLeftEndpoint
    exact
      le_trans
        (sub_le_self (a : ℝ) htwo_nonneg)
        ha_center
  have hright :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤
        (b : ℝ) + 2 / 3 := by
    exact
      le_trans hcenter_b
        (le_add_of_nonneg_right htwo_nonneg)
  exact
    (Complex.mem_logarithmicPhasePoissonActiveModes_iff t a b m).mpr
      ⟨hmem.1, hmem.2.1, ⟨hleft, hright⟩⟩

theorem Complex.logarithmicPhasePoissonCanonicalInterior_union_endpoint_eq_active
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b ∪
        Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b =
      Complex.logarithmicPhasePoissonActiveModes t a b := by
  unfold Complex.logarithmicPhasePoissonCanonicalEndpointModes
  exact
    (Finset.union_comm _ _).trans
      (Finset.sdiff_union_of_subset
        (Complex.logarithmicPhasePoissonCanonicalInteriorModes_subset_activeModes
          t a b))

theorem Complex.logarithmicPhasePoissonCanonicalInterior_disjoint_endpoint
    (t : ℝ) (a b : ℤ) :
    Disjoint
      (Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b)
      (Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b) := by
  unfold Complex.logarithmicPhasePoissonCanonicalEndpointModes
  exact Finset.disjoint_sdiff

theorem Complex.logarithmicPhasePoissonCanonicalEndpointModes_card_le_activeModes_card
    (t : ℝ) (a b : ℤ) :
    (Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b).card ≤
      (Complex.logarithmicPhasePoissonActiveModes t a b).card := by
  unfold Complex.logarithmicPhasePoissonCanonicalEndpointModes
  exact Finset.card_le_card (Finset.sdiff_subset)

theorem Complex.logarithmicPhasePoissonCanonicalEndpointModes_card_le_modeRange_card
    (t : ℝ) (a b : ℤ) :
    (Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b).card ≤
      (Complex.logarithmicPhasePoissonModeRange t a).card := by
  exact
    le_trans
      (Complex.logarithmicPhasePoissonCanonicalEndpointModes_card_le_activeModes_card
        t a b)
      (Complex.logarithmicPhasePoissonActiveModes_card_le_modeRange_card
        t a b)

def Complex.logarithmicPhasePoissonCanonicalEndpointBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b,
    ‖Complex.integerBlockFourierPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖

theorem Complex.logarithmicPhasePoissonCanonicalEndpointBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhasePoissonCanonicalEndpointBudget t a b := by
  unfold Complex.logarithmicPhasePoissonCanonicalEndpointBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhasePoissonCanonicalEndpoint_packet_tsum_le_budget
    (t : ℝ) (a b : ℤ) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalEndpointBudget t a b := by
  let modes := Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b
  let bound : ℤ → ℝ := fun m =>
    ‖Complex.integerBlockFourierPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖
  exact
    Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_majorant_sum
      t a b modes bound
      (fun m hm => le_rfl)

theorem Complex.logarithmicPhasePoissonCanonicalEndpointBudget_upper_of_pointwise_bound
    (t : ℝ) (a b : ℤ) (C : ℝ)
    (hbound :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b →
          ‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤ C) :
    Complex.logarithmicPhasePoissonCanonicalEndpointBudget t a b ≤
      ((Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b).card : ℝ) * C := by
  unfold Complex.logarithmicPhasePoissonCanonicalEndpointBudget
  have hpointwise :=
    Finset.sum_le_sum
      (fun m hm => hbound m hm)
  have hconstant :
      (∑ m ∈ Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b,
        C) =
        ((Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b).card : ℝ) * C := by
    exact
      Finset.sum_const_real_eq_card_mul
        (Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b) C
  exact hpointwise.trans_eq hconstant

theorem Complex.logarithmicPhasePoissonCanonicalEndpointBudget_le_modeRange_card_mul
    (t : ℝ) (a b : ℤ) (C : ℝ) (hC : 0 ≤ C)
    (hbound :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b →
          ‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤ C) :
    Complex.logarithmicPhasePoissonCanonicalEndpointBudget t a b ≤
      ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) * C := by
  have hbudget :=
    Complex.logarithmicPhasePoissonCanonicalEndpointBudget_upper_of_pointwise_bound
      t a b C hbound
  have hcard :
      ((Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b).card : ℝ) ≤
        ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) :=
    Nat.cast_le.mpr
      (Complex.logarithmicPhasePoissonCanonicalEndpointModes_card_le_modeRange_card
        t a b)
  exact le_trans hbudget (mul_le_mul_of_nonneg_right hcard hC)

theorem Complex.logarithmicPhasePoissonCanonicalActive_packet_tsum_le_interior_add_endpoint
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalInteriorBudget t a b +
        Complex.logarithmicPhasePoissonCanonicalEndpointBudget t a b := by
  let active := Complex.logarithmicPhasePoissonActiveModes t a b
  let interior := Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b
  let endpoint := Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b
  let packet : ℤ → ℂ := fun m =>
    Complex.integerBlockFourierPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m
  have hunion : interior ∪ endpoint = active := by
    exact
      Complex.logarithmicPhasePoissonCanonicalInterior_union_endpoint_eq_active
        t a b
  have hdisjoint : Disjoint interior endpoint := by
    exact
      Complex.logarithmicPhasePoissonCanonicalInterior_disjoint_endpoint
        t a b
  have hactive_tsum := active.tsum_subtype packet
  have hinterior_tsum := interior.tsum_subtype packet
  have hendpoint_tsum := endpoint.tsum_subtype packet
  have hsum_union :
      (∑ m ∈ active, packet m) =
        (∑ m ∈ interior, packet m) + ∑ m ∈ endpoint, packet m := by
    exact
      Eq.trans
        (congrArg (fun modes : Finset ℤ => ∑ m ∈ modes, packet m)
          hunion.symm)
        (Finset.sum_union hdisjoint)
  have hdecomp :
      (∑' m : {m : ℤ // m ∈ active}, packet m) =
        (∑' m : {m : ℤ // m ∈ interior}, packet m) +
          ∑' m : {m : ℤ // m ∈ endpoint}, packet m := by
    exact
      Eq.trans
        (hactive_tsum.trans hsum_union)
        (congrArg₂ (fun left right : ℂ => left + right)
          hinterior_tsum.symm hendpoint_tsum.symm)
  have hinterior :=
    Complex.norm_logarithmicPhasePoissonCanonicalInterior_packet_tsum_le_budget
      t ht ht_nonneg a b ha hab
  have hendpoint :=
    Complex.logarithmicPhasePoissonCanonicalEndpoint_packet_tsum_le_budget
      t a b
  calc
    ‖∑' m : {m : ℤ // m ∈ active}, packet m‖ =
        ‖(∑' m : {m : ℤ // m ∈ interior}, packet m) +
          ∑' m : {m : ℤ // m ∈ endpoint}, packet m‖ :=
      congrArg norm hdecomp
    _ ≤
        ‖∑' m : {m : ℤ // m ∈ interior}, packet m‖ +
          ‖∑' m : {m : ℤ // m ∈ endpoint}, packet m‖ :=
      norm_add_le _ _
    _ ≤
        Complex.logarithmicPhasePoissonCanonicalInteriorBudget t a b +
          Complex.logarithmicPhasePoissonCanonicalEndpointBudget t a b :=
      add_le_add hinterior hendpoint

end
end LFunctions
end Boundary
