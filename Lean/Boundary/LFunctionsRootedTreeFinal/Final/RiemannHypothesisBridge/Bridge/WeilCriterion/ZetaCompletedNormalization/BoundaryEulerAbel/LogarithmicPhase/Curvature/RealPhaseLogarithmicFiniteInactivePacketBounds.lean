import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveDerivativeGaps

/-!
# Closed packet bounds for the finite inactive classes

The deterministic one-third derivative gaps are inserted into the phase-
adapted closed majorant.  Antitonicity in the gap removes all dependence on
individual stationary centers, leaving one explicit scalar per endpoint
class and a finite cardinality factor.  The adapted packet parameter remains
the canonical nonnegative parameter `‖t‖`; transport back to `t` is made only
under an explicit nonnegativity hypothesis.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteLeftInactiveGap
    (t : ℝ) (a : ℤ) : ℝ :=
  ‖t‖ * ((1 : ℝ) / 3) /
    (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2

def Complex.logarithmicPhaseFiniteRightInactiveGap
    (t : ℝ) (b : ℤ) : ℝ :=
  ‖t‖ * ((1 : ℝ) / 3) /
    (Complex.logarithmicPhaseQuantitativeSupportRight b *
      (Complex.logarithmicPhaseQuantitativeSupportRight b + 1 / 3))

def Complex.logarithmicPhaseFiniteLeftInactivePacketMajorant
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseAdaptedClosedMajorant t a b
    (Complex.logarithmicPhaseFiniteLeftInactiveGap t a)

def Complex.logarithmicPhaseFiniteRightInactivePacketMajorant
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseAdaptedClosedMajorant t a b
    (Complex.logarithmicPhaseFiniteRightInactiveGap t b)

theorem Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_eq_norm_parameter_of_nonneg
    (t : ℝ) (ht_nonneg : 0 ≤ t) (a b m : ℤ) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ =
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ := by
  have hparameter : t = ‖t‖ :=
    (Real.norm_of_nonneg ht_nonneg).symm
  exact congrArg
    (fun parameter : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
        parameter a b m‖)
    hparameter

theorem Complex.logarithmicPhaseFiniteLeftInactiveGap_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a : ℤ) (ha : 1 ≤ a) :
    0 < Complex.logarithmicPhaseFiniteLeftInactiveGap t a := by
  unfold Complex.logarithmicPhaseFiniteLeftInactiveGap
  have hnorm := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hthird : (0 : ℝ) < 1 / 3 :=
    div_pos zero_lt_one (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have hleft := Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  exact div_pos (mul_pos hnorm hthird) (sq_pos_of_pos hleft)

theorem Complex.logarithmicPhaseFiniteRightInactiveGap_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 < Complex.logarithmicPhaseFiniteRightInactiveGap t b := by
  unfold Complex.logarithmicPhaseFiniteRightInactiveGap
  have hnorm := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hthird : (0 : ℝ) < 1 / 3 :=
    div_pos zero_lt_one (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have hright :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos a b ha hab
  have hrightThird := add_pos hright hthird
  exact div_pos (mul_pos hnorm hthird) (mul_pos hright hrightThird)

theorem Complex.logarithmicPhaseRightInactiveGap_ge_curvature_third
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b) :
    Complex.logarithmicPhaseFiniteRightInactiveGap t b ≤
      Complex.logarithmicPhaseRightInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportRight b) := by
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t a b m).mp hm).2.1
  have hx :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos a b ha hab
  have hgap :=
    Complex.logarithmicPhasePoissonRightInactive_one_third_center_gap
      t a b hab hm
  have hcenterLowerRaw :
      (1 : ℝ) / 3 +
          Complex.logarithmicPhaseQuantitativeSupportRight b ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m :=
    (le_sub_iff_add_le).mp hgap.le
  have hcenterLower :
      Complex.logarithmicPhaseQuantitativeSupportRight b + 1 / 3 ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m :=
    Eq.subst
      (motive := fun value : ℝ => value ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m)
      (add_comm ((1 : ℝ) / 3)
        (Complex.logarithmicPhaseQuantitativeSupportRight b))
      hcenterLowerRaw
  have hfraction := Real.center_fraction_right_lower
    hx (div_pos zero_lt_one (Nat.cast_pos.mpr (Nat.succ_pos 2))) hcenterLower
  have hscaled := mul_le_mul_of_nonneg_left hfraction (norm_nonneg t)
  have hleftNormalize :
      ‖t‖ * (((1 : ℝ) / 3) /
        (Complex.logarithmicPhaseQuantitativeSupportRight b *
          (Complex.logarithmicPhaseQuantitativeSupportRight b + 1 / 3))) =
      Complex.logarithmicPhaseFiniteRightInactiveGap t b := by
    unfold Complex.logarithmicPhaseFiniteRightInactiveGap
    exact (mul_div_assoc ‖t‖ ((1 : ℝ) / 3) _).symm
  have hrightNormalize :
      ‖t‖ *
          ((Complex.logarithmicPhaseFourierStationaryPoint t m -
              Complex.logarithmicPhaseQuantitativeSupportRight b) /
            (Complex.logarithmicPhaseQuantitativeSupportRight b *
              Complex.logarithmicPhaseFourierStationaryPoint t m)) =
        ‖t‖ *
            (Complex.logarithmicPhaseFourierStationaryPoint t m -
              Complex.logarithmicPhaseQuantitativeSupportRight b) /
          (Complex.logarithmicPhaseQuantitativeSupportRight b *
            Complex.logarithmicPhaseFourierStationaryPoint t m) :=
    (mul_div_assoc ‖t‖
      (Complex.logarithmicPhaseFourierStationaryPoint t m -
        Complex.logarithmicPhaseQuantitativeSupportRight b)
      (Complex.logarithmicPhaseQuantitativeSupportRight b *
        Complex.logarithmicPhaseFourierStationaryPoint t m)).symm
  have hscaledRight :
      ‖t‖ * (((1 : ℝ) / 3) /
          (Complex.logarithmicPhaseQuantitativeSupportRight b *
            (Complex.logarithmicPhaseQuantitativeSupportRight b + 1 / 3))) ≤
        ‖t‖ *
            (Complex.logarithmicPhaseFourierStationaryPoint t m -
              Complex.logarithmicPhaseQuantitativeSupportRight b) /
          (Complex.logarithmicPhaseQuantitativeSupportRight b *
            Complex.logarithmicPhaseFourierStationaryPoint t m) :=
    Eq.subst
      (motive := fun value : ℝ =>
        ‖t‖ * (((1 : ℝ) / 3) /
          (Complex.logarithmicPhaseQuantitativeSupportRight b *
            (Complex.logarithmicPhaseQuantitativeSupportRight b + 1 / 3))) ≤ value)
      hrightNormalize hscaled
  have hscaledNormalized :
      Complex.logarithmicPhaseFiniteRightInactiveGap t b ≤
        ‖t‖ *
            (Complex.logarithmicPhaseFourierStationaryPoint t m -
              Complex.logarithmicPhaseQuantitativeSupportRight b) /
          (Complex.logarithmicPhaseQuantitativeSupportRight b *
            Complex.logarithmicPhaseFourierStationaryPoint t m) :=
    Eq.subst
      (motive := fun value : ℝ => value ≤
        ‖t‖ *
            (Complex.logarithmicPhaseFourierStationaryPoint t m -
              Complex.logarithmicPhaseQuantitativeSupportRight b) /
          (Complex.logarithmicPhaseQuantitativeSupportRight b *
            Complex.logarithmicPhaseFourierStationaryPoint t m))
      hleftNormalize hscaledRight
  exact Eq.subst
    (motive := fun value : ℝ =>
      Complex.logarithmicPhaseFiniteRightInactiveGap t b ≤ value)
    (Complex.logarithmicPhaseRightInactiveGap_eq_center_fraction
      t ht hmNeg hx).symm
    hscaledNormalized

theorem Complex.norm_finiteLeftInactive_packet_le_deterministicMajorant
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseFiniteLeftInactivePacketMajorant t a b := by
  have hgap :=
    Complex.logarithmicPhaseLeftInactiveGap_ge_curvature_third
      t ht a b ha hab hm
  have hdetPos :=
    Complex.logarithmicPhaseFiniteLeftInactiveGap_pos t ht a ha
  have hactualPos := lt_of_lt_of_le hdetPos hgap
  have hstrict :
      ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a <
        2 * Real.pi * (-(m : ℝ)) := by
    exact sub_pos.mp hactualPos
  have hpacket :=
    Complex.norm_logarithmicPhaseLeftInactiveModePacket_le
      t a b m ha hab hstrict
  have hleftNonneg :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hmajorant :=
    Complex.logarithmicPhaseAdaptedClosedMajorant_gap_antitone
      t a b hab hleftNonneg hdetPos hgap
  unfold Complex.logarithmicPhaseLeftInactiveClosedMajorant at hpacket
  unfold Complex.logarithmicPhaseFiniteLeftInactivePacketMajorant
  exact le_trans hpacket hmajorant

theorem Complex.norm_finiteRightInactive_packet_le_deterministicMajorant
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseFiniteRightInactivePacketMajorant t a b := by
  have hgap :=
    Complex.logarithmicPhaseRightInactiveGap_ge_curvature_third
      t ht a b ha hab hm
  have hdetPos :=
    Complex.logarithmicPhaseFiniteRightInactiveGap_pos t ht a b ha hab
  have hactualPos := lt_of_lt_of_le hdetPos hgap
  have hstrict :
      2 * Real.pi * (-(m : ℝ)) <
        ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b := by
    exact sub_pos.mp hactualPos
  have hpacket :=
    Complex.norm_logarithmicPhaseRightInactiveModePacket_le
      t a b m ha hab hstrict
  have hleftNonneg :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hmajorant :=
    Complex.logarithmicPhaseAdaptedClosedMajorant_gap_antitone
      t a b hab hleftNonneg hdetPos hgap
  unfold Complex.logarithmicPhaseRightInactiveClosedMajorant at hpacket
  unfold Complex.logarithmicPhaseFiniteRightInactivePacketMajorant
  exact le_trans hpacket hmajorant

theorem Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_le_card_mul_majorant
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget t a b ≤
      ((Complex.logarithmicPhasePoissonLeftInactiveModes t a b).card : ℝ) *
        Complex.logarithmicPhaseFiniteLeftInactivePacketMajorant t a b := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
  have hsum := Finset.sum_le_sum (fun m hm => by
    have hcanonical :=
      Complex.norm_finiteLeftInactive_packet_le_deterministicMajorant
        t ht a b ha hab hm
    have hparameter :=
      Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_eq_norm_parameter_of_nonneg
        t ht_nonneg a b m
    exact Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          Complex.logarithmicPhaseFiniteLeftInactivePacketMajorant t a b)
      hparameter.symm hcanonical)
  have hconstant := Finset.sum_const_real_eq_card_mul
    (Complex.logarithmicPhasePoissonLeftInactiveModes t a b)
    (Complex.logarithmicPhaseFiniteLeftInactivePacketMajorant t a b)
  exact hsum.trans_eq hconstant

theorem Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_le_card_mul_majorant
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget t a b ≤
      ((Complex.logarithmicPhasePoissonRightInactiveModes t a b).card : ℝ) *
        Complex.logarithmicPhaseFiniteRightInactivePacketMajorant t a b := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
  have hsum := Finset.sum_le_sum (fun m hm => by
    have hcanonical :=
      Complex.norm_finiteRightInactive_packet_le_deterministicMajorant
        t ht a b ha hab hm
    have hparameter :=
      Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_eq_norm_parameter_of_nonneg
        t ht_nonneg a b m
    exact Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          Complex.logarithmicPhaseFiniteRightInactivePacketMajorant t a b)
      hparameter.symm hcanonical)
  have hconstant := Finset.sum_const_real_eq_card_mul
    (Complex.logarithmicPhasePoissonRightInactiveModes t a b)
    (Complex.logarithmicPhaseFiniteRightInactivePacketMajorant t a b)
  exact hsum.trans_eq hconstant

end

end LFunctions
end Boundary
