import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.Reconstruction
namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff FourierTransform Interval
open MeasureTheory

theorem Complex.norm_summable_logarithmicPhase_integerBlockFourierPacket_sequence
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Summable (fun m : ℤ => ‖
      Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖) := by
  exact
    (Complex.summable_logarithmicPhase_integerBlockFourierPacket_sequence
      t a b ha hab).norm

theorem Complex.logarithmicPhase_integerBlockFourierPacket_tsum_eq_selected_add_complement
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (selected : Set ℤ) :
    (∑' m : ℤ,
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m) =
      (∑' m : selected,
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m) +
      (∑' m : (selectedᶜ : Set ℤ),
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m) := by
  have htotal :
      Summable (fun m : ℤ =>
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m) :=
    Complex.summable_logarithmicPhase_integerBlockFourierPacket_sequence
      t a b ha hab
  have hsplit :=
    tsum_subtype_add_tsum_subtype_compl htotal selected
  exact hsplit.symm

theorem Complex.norm_logarithmicPhase_integerBlockFourierPacket_tsum_norm_le_selected_add_complement
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (selected : Set ℤ) :
    ‖∑' m : ℤ,
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ‖∑' m : selected,
          Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ +
      ‖∑' m : (selectedᶜ : Set ℤ),
          Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ := by
  have hsplit :=
    Complex.logarithmicPhase_integerBlockFourierPacket_tsum_eq_selected_add_complement
      t a b ha hab selected
  calc
    ‖∑' m : ℤ,
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ =
        ‖(∑' m : selected,
            Complex.integerBlockFourierPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m) +
          (∑' m : (selectedᶜ : Set ℤ),
            Complex.integerBlockFourierPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m)‖ :=
      congrArg norm hsplit
    _ ≤ _ := norm_add_le _ _

theorem Complex.norm_logarithmicPhase_integerBlockFourierPacket_tsum_norm_le_selected_add_complement_tsum_norm
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (selected : Set ℤ) :
    ‖∑' m : ℤ,
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ‖∑' m : selected,
          Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ +
      ∑' m : (selectedᶜ : Set ℤ),
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ := by
  have hsplit :=
    Complex.logarithmicPhase_integerBlockFourierPacket_tsum_eq_selected_add_complement
      t a b ha hab selected
  have hcomplement_summable :
      Summable (fun m : (selectedᶜ : Set ℤ) =>
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖) := by
    exact
      (Complex.norm_summable_logarithmicPhase_integerBlockFourierPacket_sequence
        t a b ha hab).subtype (selectedᶜ : Set ℤ)
  have hcomplement_norm :
      ‖∑' m : (selectedᶜ : Set ℤ),
          Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤
        ∑' m : (selectedᶜ : Set ℤ),
          ‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ :=
    norm_tsum_le_tsum_norm hcomplement_summable
  calc
    ‖∑' m : ℤ,
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ =
        ‖(∑' m : selected,
            Complex.integerBlockFourierPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m) +
          (∑' m : (selectedᶜ : Set ℤ),
            Complex.integerBlockFourierPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m)‖ :=
      congrArg norm hsplit
    _ ≤
        ‖∑' m : selected,
            Complex.integerBlockFourierPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m‖ +
          ‖∑' m : (selectedᶜ : Set ℤ),
            Complex.integerBlockFourierPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m‖ := norm_add_le _ _
    _ ≤
        ‖∑' m : selected,
            Complex.integerBlockFourierPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m‖ +
          ∑' m : (selectedᶜ : Set ℤ),
            ‖Complex.integerBlockFourierPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m‖ :=
      add_le_add_left hcomplement_norm _

theorem Complex.norm_logarithmicPhase_integerBlockFourierPacket_tsum_norm_le_active_add_nonactive_tsum_norm
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : ℤ,
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ‖∑' m : {m : ℤ // m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
          Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ +
      ∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonActiveModes t a b},
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ := by
  exact
    Complex.norm_logarithmicPhase_integerBlockFourierPacket_tsum_norm_le_selected_add_complement_tsum_norm
      t a b ha hab (Complex.logarithmicPhasePoissonActiveModes t a b : Set ℤ)

theorem Complex.norm_logarithmicPhase_integerBlockFourierPacket_tsum_norm_le_modeRange_add_outsideRange_tsum_norm
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : ℤ,
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ‖∑' m : {m : ℤ // m ∈ Complex.logarithmicPhasePoissonModeRange t a},
          Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ +
      ∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a},
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ := by
  exact
    Complex.norm_logarithmicPhase_integerBlockFourierPacket_tsum_norm_le_selected_add_complement_tsum_norm
      t a b ha hab (Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)

theorem Complex.norm_logarithmicPhase_outsideRange_packet_tsum_le_global_packet_norm_tsum
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ // m ∈
        (Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)ᶜ},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ∑' m : ℤ,
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ := by
  have hnorm_summable :=
    Complex.norm_summable_logarithmicPhase_integerBlockFourierPacket_sequence
      t a b ha hab
  have houtside_summable :=
    hnorm_summable.subtype
      ((Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)ᶜ)
  have houtside_norm := norm_tsum_le_tsum_norm houtside_summable
  have hsplit :=
    tsum_subtype_add_tsum_subtype_compl hnorm_summable
      (Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)
  have hselected_nonneg :
      0 ≤ ∑' m : {m : ℤ // m ∈
        (Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)},
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ := by
    exact tsum_nonneg (fun m => norm_nonneg _)
  have houtside_le_global :
      (∑' m : {m : ℤ // m ∈
        (Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)ᶜ},
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖) ≤
        ∑' m : ℤ,
          ‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ := by
    calc
      (∑' m : {m : ℤ // m ∈
        (Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)ᶜ},
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖) ≤
          (∑' m : {m : ℤ // m ∈
            (Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)},
            ‖Complex.integerBlockFourierPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m‖) +
            (∑' m : {m : ℤ // m ∈
              (Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)ᶜ},
              ‖Complex.integerBlockFourierPacket
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                a b m‖) :=
        le_add_of_nonneg_left hselected_nonneg
      _ = ∑' m : ℤ,
          ‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ := hsplit
  exact houtside_norm.trans houtside_le_global

theorem Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_norm_sum
    (t : ℝ) (a b : ℤ) (modes : Finset ℤ) :
    ‖∑' m : {m : ℤ // m ∈ modes},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ∑ m ∈ modes,
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ := by
  have hfinite :=
    modes.tsum_subtype
      (fun m : ℤ =>
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m)
  exact
    Eq.subst
      (motive := fun value : ℂ => ‖value‖ ≤
        ∑ m ∈ modes,
          ‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖)
      hfinite.symm
      (norm_sum_le modes
        (fun m : ℤ =>
          Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m))

theorem Complex.logarithmicPhaseEndpointActiveModes_card_le_activeModes_card
    (t : ℝ) (a b : ℤ) (radius : ℝ) :
    (Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius).card ≤
      (Complex.logarithmicPhasePoissonActiveModes t a b).card := by
  exact Finset.card_le_card (Finset.sdiff_subset)

theorem Complex.norm_logarithmicPhaseEndpointActiveModes_packet_tsum_le_finset_norm_sum
    (t : ℝ) (a b : ℤ) (radius : ℝ) :
    ‖∑' m :
        {m : ℤ // m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ∑ m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius,
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ := by
  exact
    Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_norm_sum
      t a b (Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius)

theorem Complex.norm_logarithmicPhaseInRangeInactiveModes_packet_tsum_le_finset_norm_sum
    (t : ℝ) (a b : ℤ) :
    ‖∑' m :
        {m : ℤ // m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ∑ m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b,
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ := by
  exact
    Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_norm_sum
      t a b (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b)

theorem Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_majorant_sum
    (t : ℝ) (a b : ℤ) (modes : Finset ℤ)
    (bound : ℤ → ℝ)
    (hbound : ∀ m ∈ modes,
      ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ bound m) :
    ‖∑' m : {m : ℤ // m ∈ modes},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ∑ m ∈ modes, bound m := by
  have hnorm :=
    Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_norm_sum
      t a b modes
  have hsum_norm :
      (∑ m ∈ modes,
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖) ≤
        ∑ m ∈ modes, bound m := by
    exact Finset.sum_le_sum (fun m hm => hbound m hm)
  exact le_trans hnorm hsum_norm

theorem Complex.norm_integerBlockFourierPacket_le_crossing_add_principal
    (t : ℝ) (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    {P : ℝ}
    (hprincipal :
      ‖∫ x in (a : ℝ)..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤ P) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤ 4 / 3 + P := by
  let leftPart : ℂ :=
    ∫ x in ((a : ℝ) - 2 / 3)..(a : ℝ),
      Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.integerBlockCutoff a b) m x
  let principalPart : ℂ :=
    ∫ x in (a : ℝ)..(b : ℝ),
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x
  let rightPart : ℂ :=
    ∫ x in (b : ℝ)..((b : ℝ) + 2 / 3),
      Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.integerBlockCutoff a b) m x
  have hsplit :
      Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m = leftPart + principalPart + rightPart := by
    exact
      Complex.integral_logarithmicPhase_integerBlockCutoffFrequencyTwist_eq_three_parts
        t a b m ha hab
  have hassoc :
      leftPart + principalPart + rightPart = (leftPart + rightPart) + principalPart := by
    calc
      leftPart + principalPart + rightPart = leftPart + (principalPart + rightPart) :=
        add_assoc _ _ _
      _ = leftPart + (rightPart + principalPart) :=
        congrArg (fun value : ℂ => leftPart + value) (add_comm _ _)
      _ = (leftPart + rightPart) + principalPart :=
        (add_assoc _ _ _).symm
  have hdecomp :
      Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m = (leftPart + rightPart) + principalPart :=
    hsplit.trans hassoc
  have hcrossing : ‖leftPart + rightPart‖ ≤ 4 / 3 := by
    exact Complex.norm_logarithmicPhase_cutoffCrossingSum_le t a b m
  have htriangle :
      ‖(leftPart + rightPart) + principalPart‖ ≤
        ‖leftPart + rightPart‖ + ‖principalPart‖ :=
    norm_add_le _ _
  have hprincipal' : ‖principalPart‖ ≤ P := hprincipal
  have hsum :
      ‖leftPart + rightPart‖ + ‖principalPart‖ ≤ 4 / 3 + P :=
    add_le_add hcrossing hprincipal'
  exact
    Eq.subst
      (motive := fun value : ℂ => ‖value‖ ≤ 4 / 3 + P)
      hdecomp.symm
      (le_trans htriangle hsum)

theorem Complex.norm_integerBlockFourierPacket_le_active_three_piece
    (t : ℝ) (ht_nonneg : 0 ≤ t) (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (center radius : ℝ)
    (hleft_center : (a : ℝ) ≤ center - radius)
    (hcenter_right : center - radius ≤ center + radius)
    (hright : center + radius ≤ (b : ℝ))
    {leftBound rightBound : ℝ}
    (hleft_bound :
      ‖∫ x in (a : ℝ)..center - radius,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤ leftBound)
    (hright_bound :
      ‖∫ x in center + radius..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤ rightBound)
    (_hradius : 0 ≤ radius) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤
      4 / 3 + leftBound + ((center + radius) - (center - radius)) + rightBound := by
  have hcentral_cutoff :=
    Complex.norm_intervalIntegral_logarithmicPhase_packet_centralWindow_le_two_radius
      t a b m center radius hleft_center hright (by exact _hradius)
  have hcentral_eq :=
    Complex.integral_logarithmicPhase_packet_eq_integral_realPhaseOscillation_on_subinterval
      t a b m (center - radius) (center + radius)
      hleft_center hright hcenter_right
  have hcentral_bound :
      ‖∫ x in center - radius..center + radius,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤ (center + radius) - (center - radius) := by
    exact
      Eq.subst
        (motive := fun value : ℂ => ‖value‖ ≤
          (center + radius) - (center - radius))
        hcentral_eq
        hcentral_cutoff
  have ha_real : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hleft_integrable :=
    Complex.intervalIntegrable_logarithmicPhase_oscillation
      t ht_nonneg m (a : ℝ) (center - radius)
      ha_real
      hleft_center
  have hcentral_integrable :=
    Complex.intervalIntegrable_logarithmicPhase_oscillation
      t ht_nonneg m (center - radius) (center + radius)
      (lt_of_lt_of_le ha_real hleft_center)
      hcenter_right
  have hright_integrable :=
    Complex.intervalIntegrable_logarithmicPhase_oscillation
      t ht_nonneg m (center + radius) (b : ℝ)
      (lt_of_lt_of_le (lt_of_lt_of_le ha_real hleft_center) hcenter_right)
      hright
  have hprincipal :=
    Complex.norm_intervalIntegral_logarithmicPhase_principal_three_piece_bound
      t m (a : ℝ) center radius (b : ℝ)
      hleft_center hcenter_right hright
      hleft_integrable hcentral_integrable hright_integrable
      hleft_bound hcentral_bound hright_bound
  have hpacket :=
    Complex.norm_integerBlockFourierPacket_le_crossing_add_principal
      t a b m ha hab hprincipal
  exact
    hpacket.trans_eq
      ((add_assoc (4 / 3 : ℝ)
          (leftBound + (center + radius - (center - radius))) rightBound).symm.trans
        (congrArg (fun value : ℝ => value + rightBound)
          (add_assoc (4 / 3 : ℝ) leftBound
            (center + radius - (center - radius))).symm))

theorem Complex.norm_integerBlockFourierPacket_le_left_inactive_explicit
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : m < 0)
    (hcenter : Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ)) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤
      4 / 3 +
        2 * ((2 * Real.pi * (-(m : ℝ))) *
          ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
            (b : ℝ))⁻¹ +
        ((b : ℝ) - (a : ℝ)) •
          ((‖t‖ / (a : ℝ) ^ 2) /
            ((2 * Real.pi * (-(m : ℝ))) *
              ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
                (b : ℝ)) ^ 2) := by
  have ha_real : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hab_real : (a : ℝ) ≤ (b : ℝ) :=
    Int.cast_le.mpr hab
  have hprincipal :=
    Complex.norm_intervalIntegral_logarithmicPhase_realOscillation_le_right_nonstationary_tail_explicit
      t ht ht_nonneg a b m (a : ℝ) (b : ℝ) ha_real le_rfl le_rfl hab_real hcenter hm
  have hpacket :=
    Complex.norm_integerBlockFourierPacket_le_crossing_add_principal
      t a b m ha hab hprincipal
  exact
    hpacket.trans_eq
      (add_assoc (4 / 3 : ℝ)
        (2 * ((2 * Real.pi * (-(m : ℝ))) *
          ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
            (b : ℝ))⁻¹)
        (((b : ℝ) - (a : ℝ)) •
          ((‖t‖ / (a : ℝ) ^ 2) /
            ((2 * Real.pi * (-(m : ℝ))) *
              ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
                (b : ℝ)) ^ 2))).symm

theorem Complex.norm_integerBlockFourierPacket_le_right_inactive_explicit
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : m < 0)
    (hcenter : (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤
      4 / 3 +
        2 * ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
            (b : ℝ))⁻¹ +
        ((b : ℝ) - (a : ℝ)) •
          ((‖t‖ / (a : ℝ) ^ 2) /
            ((2 * Real.pi * (-(m : ℝ))) *
              (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
                (b : ℝ)) ^ 2) := by
  have ha_real : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hab_real : (a : ℝ) ≤ (b : ℝ) :=
    Int.cast_le.mpr hab
  have hprincipal :=
    Complex.norm_intervalIntegral_logarithmicPhase_realOscillation_le_left_nonstationary_tail_explicit
      t ht ht_nonneg a b m (a : ℝ) (b : ℝ) ha_real le_rfl le_rfl hab_real hcenter hm
  have hpacket :=
    Complex.norm_integerBlockFourierPacket_le_crossing_add_principal
      t a b m ha hab hprincipal
  exact
    hpacket.trans_eq
      (add_assoc (4 / 3 : ℝ)
        (2 * ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
            (b : ℝ))⁻¹)
      (((b : ℝ) - (a : ℝ)) •
          ((‖t‖ / (a : ℝ) ^ 2) /
            ((2 * Real.pi * (-(m : ℝ))) *
              (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
                (b : ℝ)) ^ 2))).symm

theorem Complex.norm_logarithmicPhase_leftInactive_packet_tsum_le_explicit_sum
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (modes : Finset ℤ)
    (hleft : ∀ m ∈ modes,
      m < 0 ∧
        Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ)) :
    ‖∑' m : {m : ℤ // m ∈ modes},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ∑ m ∈ modes,
        (4 / 3 +
          2 * ((2 * Real.pi * (-(m : ℝ))) *
            ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
              (b : ℝ))⁻¹ +
          ((b : ℝ) - (a : ℝ)) •
            ((‖t‖ / (a : ℝ) ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
                ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
                  (b : ℝ)) ^ 2)) := by
  let bound : ℤ → ℝ := fun m =>
    4 / 3 +
      2 * ((2 * Real.pi * (-(m : ℝ))) *
        ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
          (b : ℝ))⁻¹ +
      ((b : ℝ) - (a : ℝ)) •
        ((‖t‖ / (a : ℝ) ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
              (b : ℝ)) ^ 2)
  have hbound : ∀ m ∈ modes,
      ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ bound m := by
    intro m hm
    exact
      Complex.norm_integerBlockFourierPacket_le_left_inactive_explicit
        t ht ht_nonneg a b m ha hab (hleft m hm).1 (hleft m hm).2
  have hsum :=
    Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_majorant_sum
      t a b modes bound hbound
  exact hsum

theorem Complex.norm_logarithmicPhase_rightInactive_packet_tsum_le_explicit_sum
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (modes : Finset ℤ)
    (hright : ∀ m ∈ modes,
      m < 0 ∧
        (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    ‖∑' m : {m : ℤ // m ∈ modes},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ∑ m ∈ modes,
        (4 / 3 +
          2 * ((2 * Real.pi * (-(m : ℝ))) *
            (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
              (b : ℝ))⁻¹ +
          ((b : ℝ) - (a : ℝ)) •
            ((‖t‖ / (a : ℝ) ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
                (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
                  (b : ℝ)) ^ 2)) := by
  let bound : ℤ → ℝ := fun m =>
    4 / 3 +
      2 * ((2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
          (b : ℝ))⁻¹ +
      ((b : ℝ) - (a : ℝ)) •
        ((‖t‖ / (a : ℝ) ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
              (b : ℝ)) ^ 2)
  have hbound : ∀ m ∈ modes,
      ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ bound m := by
    intro m hm
    exact
      Complex.norm_integerBlockFourierPacket_le_right_inactive_explicit
        t ht ht_nonneg a b m ha hab (hright m hm).1 (hright m hm).2
  have hsum :=
    Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_majorant_sum
      t a b modes bound hbound
  exact hsum

theorem Complex.norm_logarithmicPhase_packet_subtype_tsum_le_subtype_bound
    (t : ℝ) (a b : ℤ)
    (selected : Set ℤ) (bound : ℤ → ℝ)
    (hbound : ∀ m : selected,
      ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ bound m)
    (hsummable : Summable (fun m : selected => bound m)) :
    ‖∑' m : selected,
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ∑' m : selected, bound m := by
  exact tsum_of_norm_bounded hsummable.hasSum hbound

def Complex.logarithmicPhaseInteriorStationaryPacketBound
    (t : ℝ) (a b m : ℤ) (radius : ℝ) : ℝ :=
  4 / 3 +
    (2 * ((2 * Real.pi * (-(m : ℝ))) *
      (Complex.logarithmicPhaseFourierStationaryPoint t m -
        (Complex.logarithmicPhaseFourierStationaryPoint t m - radius)) /
        (Complex.logarithmicPhaseFourierStationaryPoint t m - radius))⁻¹ +
      ((Complex.logarithmicPhaseFourierStationaryPoint t m - radius) - (a : ℝ)) •
        ((‖t‖ / (a : ℝ) ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            (Complex.logarithmicPhaseFourierStationaryPoint t m -
              (Complex.logarithmicPhaseFourierStationaryPoint t m - radius)) /
              (Complex.logarithmicPhaseFourierStationaryPoint t m - radius)) ^ 2)) +
    ((Complex.logarithmicPhaseFourierStationaryPoint t m + radius) -
      (Complex.logarithmicPhaseFourierStationaryPoint t m - radius)) +
    (2 * ((2 * Real.pi * (-(m : ℝ))) *
      ((Complex.logarithmicPhaseFourierStationaryPoint t m + radius) -
        Complex.logarithmicPhaseFourierStationaryPoint t m) /
        (b : ℝ))⁻¹ +
      ((b : ℝ) - (Complex.logarithmicPhaseFourierStationaryPoint t m + radius)) •
        ((‖t‖ / (Complex.logarithmicPhaseFourierStationaryPoint t m + radius) ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            ((Complex.logarithmicPhaseFourierStationaryPoint t m + radius) -
              Complex.logarithmicPhaseFourierStationaryPoint t m) /
              (b : ℝ)) ^ 2))

theorem Complex.norm_integerBlockFourierPacket_le_active_stationary_explicit
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : m < 0)
    (center radius : ℝ)
    (hcenter : center = Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hradius : 0 < radius)
    (hleft_center : (a : ℝ) ≤ center - radius)
    (hright : center + radius ≤ (b : ℝ)) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤
      4 / 3 +
        (2 * ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m - (center - radius)) /
            (center - radius))⁻¹ +
          ((center - radius) - (a : ℝ)) •
            ((‖t‖ / (a : ℝ) ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
              (Complex.logarithmicPhaseFourierStationaryPoint t m - (center - radius)) /
                (center - radius)) ^ 2)) +
        ((center + radius) - (center - radius)) +
        (2 * ((2 * Real.pi * (-(m : ℝ))) *
          ((center + radius) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
            (b : ℝ))⁻¹ +
          ((b : ℝ) - (center + radius)) •
            ((‖t‖ / (center + radius) ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
              ((center + radius) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
                (b : ℝ)) ^ 2)) := by
  have ha_real : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hcenter_left : center - radius <
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
    exact hcenter ▸ sub_lt_self _ hradius
  have hcenter_right :
      Complex.logarithmicPhaseFourierStationaryPoint t m < center + radius := by
    exact hcenter ▸ lt_add_of_pos_right _ hradius
  have hwindow_order : center - radius ≤ center + radius := by
    have hraw : center - radius ≤ center - -radius := by
      exact (sub_le_sub_iff_left center).mpr
        (le_trans (neg_nonpos.mpr (le_of_lt hradius)) (le_of_lt hradius))
    exact hraw.trans_eq (sub_neg_eq_add center radius)
  have hleft_bound :=
    Complex.norm_intervalIntegral_logarithmicPhase_realOscillation_le_left_nonstationary_tail_explicit
      t ht ht_nonneg a b m (a : ℝ) (center - radius) ha_real le_rfl
      (le_trans hwindow_order hright)
      hleft_center hcenter_left hm
  have hright_bound :=
    Complex.norm_intervalIntegral_logarithmicPhase_realOscillation_le_right_nonstationary_tail_explicit
      t ht ht_nonneg a b m (center + radius) (b : ℝ)
      (lt_of_lt_of_le (lt_of_lt_of_le ha_real hleft_center) hwindow_order)
      (le_trans hleft_center hwindow_order) le_rfl hright hcenter_right hm
  have hpacket :=
    Complex.norm_integerBlockFourierPacket_le_active_three_piece
      t ht_nonneg a b m ha hab center radius hleft_center
      hwindow_order hright
      hleft_bound hright_bound (le_of_lt hradius)
  exact hpacket

theorem Complex.norm_logarithmicPhase_interiorActive_packet_tsum_le_explicit_sum
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (radius : ℝ) (hradius : 0 < radius) :
    ‖∑' m :
        {m : ℤ // m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ∑ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
        Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m radius := by
  let modes := Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius
  have hbound : ∀ m ∈ modes,
      ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m radius := by
    intro m hm
    have hmem :=
      (Complex.mem_logarithmicPhasePoissonInteriorActiveModes_iff
        t a b m radius).mp hm
    exact
      Complex.norm_integerBlockFourierPacket_le_active_stationary_explicit
        t ht ht_nonneg a b m ha hab hmem.2.1
        (Complex.logarithmicPhaseFourierStationaryPoint t m) radius rfl hradius
        hmem.2.2.1 hmem.2.2.2
  exact
    Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_majorant_sum
      t a b modes
      (fun m : ℤ => Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m radius)
      hbound

theorem Complex.norm_logarithmicPhase_active_packet_tsum_le_interior_add_endpoint
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (radius : ℝ) (hradius : 0 < radius) :
    ‖∑' m : {m : ℤ // m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ∑ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
        Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m radius +
      ∑ m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius,
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ := by
  let active := Complex.logarithmicPhasePoissonActiveModes t a b
  let interior := Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius
  let endpoint := Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius
  have hsubset : (interior : Set ℤ) ⊆ (active : Set ℤ) := by
    exact
      Complex.logarithmicPhasePoissonInteriorActiveModes_subset_activeModes
        t a b radius (le_of_lt hradius)
  have hfinset_union : interior ∪ endpoint = active := by
    change
      Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius ∪
          Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius =
        Complex.logarithmicPhasePoissonActiveModes t a b
    exact
      Complex.logarithmicPhasePoissonInterior_union_endpoint_eq_active
        t a b radius hsubset
  have hdisjoint : Disjoint interior endpoint := by
    exact Finset.disjoint_sdiff
  let packet : ℤ → ℂ := fun m =>
    Complex.integerBlockFourierPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m
  have hactive_tsum := active.tsum_subtype packet
  have hinterior_tsum := interior.tsum_subtype packet
  have hendpoint_tsum := endpoint.tsum_subtype packet
  have hsum_union :
      (∑ m ∈ active, packet m) =
        (∑ m ∈ interior, packet m) + ∑ m ∈ endpoint, packet m := by
    exact
      Eq.trans
        (congrArg (fun modes : Finset ℤ => ∑ m ∈ modes, packet m)
          hfinset_union.symm)
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
  have hinterior_bound :=
    Complex.norm_logarithmicPhase_interiorActive_packet_tsum_le_explicit_sum
      t ht ht_nonneg a b ha hab radius hradius
  have hendpoint_bound :=
    Complex.norm_logarithmicPhaseEndpointActiveModes_packet_tsum_le_finset_norm_sum
      t a b radius
  calc
    ‖∑' m : {m : ℤ // m ∈ active}, packet m‖ =
        ‖(∑' m : {m : ℤ // m ∈ interior}, packet m) +
          ∑' m : {m : ℤ // m ∈ endpoint}, packet m‖ :=
      congrArg norm hdecomp
    _ ≤
        ‖∑' m : {m : ℤ // m ∈ interior}, packet m‖ +
          ‖∑' m : {m : ℤ // m ∈ endpoint}, packet m‖ := norm_add_le _ _
    _ ≤
        (∑ m ∈ interior,
          Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m radius) +
          ∑ m ∈ endpoint,
            ‖Complex.integerBlockFourierPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m‖ :=
      add_le_add hinterior_bound hendpoint_bound

theorem Complex.norm_logarithmicPhase_integerBlockFourierPacket_tsum_norm_le_three_component_budget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (radius : ℝ) (hradius : 0 < radius) :
    ‖∑' m : ℤ,
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      (∑ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
        Complex.logarithmicPhaseInteriorStationaryPacketBound t a b m radius) +
      (∑ m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius,
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖) +
      ∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonActiveModes t a b},
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ := by
  have hsplit :=
    Complex.norm_logarithmicPhase_integerBlockFourierPacket_tsum_norm_le_active_add_nonactive_tsum_norm
      t a b ha hab
  have hactive :=
    Complex.norm_logarithmicPhase_active_packet_tsum_le_interior_add_endpoint
      t ht ht_nonneg a b ha hab radius hradius
  exact
    le_trans hsplit
      (add_le_add_right hactive
        (∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonActiveModes t a b},
          ‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖))

theorem Complex.norm_tsum_integerBlockFourierPacket_le_tsum_bound
    (phase : ℝ → ℝ)
    (a b : ℤ)
    (bound : ℤ → ℝ)
    (hbound : ∀ m : ℤ,
      ‖Complex.integerBlockFourierPacket phase a b m‖ ≤ bound m)
    (hsummable : Summable bound) :
    ‖∑' m : ℤ, Complex.integerBlockFourierPacket phase a b m‖ ≤
      ∑' m : ℤ, bound m := by
  exact
    tsum_of_norm_bounded hsummable.hasSum hbound

theorem Complex.norm_tsum_logarithmicPhase_integerBlockFourierPacket_sequence_le_tsum_norm
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : ℤ,
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ∑' m : ℤ,
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ := by
  exact
    Complex.norm_tsum_integerBlockFourierPacket_le_tsum_bound
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b
      (fun m : ℤ => ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖)
      (fun m : ℤ => le_rfl)
      (Complex.norm_summable_logarithmicPhase_integerBlockFourierPacket_sequence
        t a b ha hab)

theorem Complex.norm_logarithmicPhase_integerBlock_sum_le_packet_tsum_norm
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      ∑' m : ℤ,
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ := by
  have hreconstruction :=
    Complex.logarithmicPhase_integerBlock_poisson_packet_reconstruction
      t a b ha hab
  have hpacket :=
    Complex.norm_tsum_logarithmicPhase_integerBlockFourierPacket_sequence_le_tsum_norm
      t a b ha hab
  exact
    Eq.subst
      (motive := fun value : ℂ => ‖value‖ ≤
        ∑' m : ℤ,
          ‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖)
      hreconstruction.symm
      hpacket

end

end LFunctions
end Boundary
