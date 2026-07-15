import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeZeroMode

/-!
# Principal-to-packet transport for the quantitative cutoff

Every nonzero-frequency estimate is first an estimate for the uncut principal
oscillation.  The fixed-collar cutoff contributes only the proved `2 / 3`
crossing budget, so this file owns the uniform transport from principal bounds
to quantitative packet bounds.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff FourierTransform Interval
open MeasureTheory

theorem Real.add_reassociate_four
    (a b c d : ℝ) :
    a + ((b + c) + d) = (a + b) + (c + d) := by
  exact
    (congrArg (fun value : ℝ => a + value) (add_assoc b c d)).trans
      (add_assoc a b (c + d)).symm

theorem Real.add_reassociate_four_left
    (a b c d : ℝ) :
    a + ((b + c) + d) = ((a + b) + c) + d := by
  have houter :
      a + ((b + c) + d) = (a + (b + c)) + d :=
    (add_assoc a (b + c) d).symm
  have hinner :
      (a + (b + c)) + d = ((a + b) + c) + d :=
    congrArg (fun value : ℝ => value + d) (add_assoc a b c).symm
  exact houter.trans hinner

theorem Complex.norm_logarithmicPhaseQuantitativePacket_le_crossings_add_principal
    (t : ℝ)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    {P : ℝ}
    (hprincipal :
      ‖∫ x in (a : ℝ)..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤ P) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      2 / 3 + P := by
  let leftPart : ℂ :=
    ∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
      Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.quantitativeLogarithmicBlockCutoff a b) m x
  let principalPart : ℂ :=
    ∫ x in (a : ℝ)..(b : ℝ),
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x
  let rightPart : ℂ :=
    ∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
      Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.quantitativeLogarithmicBlockCutoff a b) m x
  have hsplit :
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m =
        leftPart + principalPart + rightPart := by
    exact
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_three_parts
        t a b m ha hab
  have hassoc :
      leftPart + principalPart + rightPart = (leftPart + rightPart) + principalPart := by
    calc
      leftPart + principalPart + rightPart = leftPart + (principalPart + rightPart) :=
        add_assoc _ _ _
      _ = leftPart + (rightPart + principalPart) :=
        congrArg (fun value : ℂ => leftPart + value) (add_comm _ _)
      _ = (leftPart + rightPart) + principalPart := (add_assoc _ _ _).symm
  have hdecomposition :
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m =
        (leftPart + rightPart) + principalPart :=
    hsplit.trans hassoc
  have hcrossings : ‖leftPart + rightPart‖ ≤ 2 / 3 := by
    have htriangle : ‖leftPart + rightPart‖ ≤ ‖leftPart‖ + ‖rightPart‖ :=
      norm_add_le leftPart rightPart
    have hbudget : ‖leftPart‖ + ‖rightPart‖ ≤ 2 / 3 :=
      Complex.norm_quantitativeLogarithmic_crossings_le_two_div_three t a b m
    exact le_trans htriangle hbudget
  have htriangle :
      ‖(leftPart + rightPart) + principalPart‖ ≤
        ‖leftPart + rightPart‖ + ‖principalPart‖ :=
    norm_add_le _ _
  have hprincipal_part : ‖principalPart‖ ≤ P := hprincipal
  have hsum : ‖leftPart + rightPart‖ + ‖principalPart‖ ≤ 2 / 3 + P :=
    add_le_add hcrossings hprincipal_part
  exact
    Eq.subst
      (motive := fun value : ℂ => ‖value‖ ≤ 2 / 3 + P)
      hdecomposition.symm
      (le_trans htriangle hsum)

theorem Complex.norm_logarithmicPhaseQuantitativePacket_le_leftInactive_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hm : m < 0)
    (hcenter : Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ)) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      2 / 3 +
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
  have hab_real : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  have hprincipal :=
    Complex.norm_intervalIntegral_logarithmicPhase_realOscillation_le_right_nonstationary_tail_explicit
      t ht ht_nonneg a b m (a : ℝ) (b : ℝ) ha_real le_rfl le_rfl hab_real hcenter hm
  have hbound :=
    Complex.norm_logarithmicPhaseQuantitativePacket_le_crossings_add_principal
      t a b m ha hab hprincipal
  exact Eq.subst
    (motive := fun value : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤ value)
    (add_assoc _ _ _).symm hbound

theorem Complex.norm_logarithmicPhaseQuantitativePacket_le_rightInactive_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hm : m < 0)
    (hcenter : (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      2 / 3 +
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
  have hab_real : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  have hprincipal :=
    Complex.norm_intervalIntegral_logarithmicPhase_realOscillation_le_left_nonstationary_tail_explicit
      t ht ht_nonneg a b m (a : ℝ) (b : ℝ) ha_real le_rfl le_rfl hab_real hcenter hm
  have hbound :=
    Complex.norm_logarithmicPhaseQuantitativePacket_le_crossings_add_principal
      t a b m ha hab hprincipal
  exact Eq.subst
    (motive := fun value : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤ value)
    (add_assoc _ _ _).symm hbound

theorem Complex.norm_logarithmicPhaseQuantitativePacket_le_active_stationary_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hm : m < 0)
    (center radius : ℝ)
    (hcenter : center = Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hradius : 0 < radius)
    (hleft_center : (a : ℝ) ≤ center - radius)
    (hright : center + radius ≤ (b : ℝ)) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      2 / 3 +
        (2 * ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m - (center - radius)) /
            (center - radius))⁻¹ +
          ((center - radius) - (a : ℝ)) •
            ((‖t‖ / (a : ℝ) ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
                (Complex.logarithmicPhaseFourierStationaryPoint t m -
                  (center - radius)) /
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
      (le_trans hwindow_order hright) hleft_center hcenter_left hm
  have hright_bound :=
    Complex.norm_intervalIntegral_logarithmicPhase_realOscillation_le_right_nonstationary_tail_explicit
      t ht ht_nonneg a b m (center + radius) (b : ℝ)
      (lt_of_lt_of_le (lt_of_lt_of_le ha_real hleft_center) hwindow_order)
      (le_trans hleft_center hwindow_order) le_rfl hright hcenter_right hm
  have hcentral :
      ‖∫ x in center - radius..center + radius,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤ (center + radius) - (center - radius) := by
    have hraw :=
      Complex.norm_intervalIntegral_logarithmicPhase_packet_centralWindow_le_two_radius
        t a b m center radius hleft_center hright (le_of_lt hradius)
    have heq :=
      Complex.integral_logarithmicPhase_packet_eq_integral_realPhaseOscillation_on_subinterval
        t a b m (center - radius) (center + radius)
        hleft_center hright hwindow_order
    exact
      Eq.subst
        (motive := fun value : ℂ =>
          ‖value‖ ≤ (center + radius) - (center - radius))
        heq
        hraw
  have hleft_integrable :=
    Complex.intervalIntegrable_logarithmicPhase_oscillation
      t ht_nonneg m (a : ℝ) (center - radius) ha_real hleft_center
  have hcentral_integrable :=
    Complex.intervalIntegrable_logarithmicPhase_oscillation
      t ht_nonneg m (center - radius) (center + radius)
      (lt_of_lt_of_le ha_real hleft_center) hwindow_order
  have hright_integrable :=
    Complex.intervalIntegrable_logarithmicPhase_oscillation
      t ht_nonneg m (center + radius) (b : ℝ)
      (lt_of_lt_of_le (lt_of_lt_of_le ha_real hleft_center) hwindow_order) hright
  have hprincipal :=
    Complex.norm_intervalIntegral_logarithmicPhase_principal_three_piece_bound
      t m (a : ℝ) center radius (b : ℝ)
      hleft_center hwindow_order hright
      hleft_integrable hcentral_integrable hright_integrable
      hleft_bound hcentral hright_bound
  have hbound :=
    Complex.norm_logarithmicPhaseQuantitativePacket_le_crossings_add_principal
      t a b m ha hab hprincipal
  exact Eq.subst
    (motive := fun value : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤ value)
    (Real.add_reassociate_four_left _ _ _ _) hbound

end
end LFunctions
end Boundary
