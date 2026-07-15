import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicEndpointAngularClosure

/-!
# Completion of endpoint angular packing

The right clipped center is at least `4b/7`, while its full center layer has
numerator below `(5/3)b²`.  Since `5/3 < 96/49 = 6(4/7)²`, the retained
angular factor closes the right width.  Combining both sides gives at most two
endpoint modes and replaces the provisional four-mode budget loss.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.three_mul_scale_ge_four
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    (4 : ℝ) ≤ 3 * Complex.logarithmicPhaseBProcessScale t := by
  have hscale := Real.four_thirds_le_BProcessScale t ht
  have hthreePos : (0 : ℝ) < 3 := Nat.cast_pos.mpr (Nat.succ_pos 2)
  have hscaled := mul_le_mul_of_nonneg_left hscale hthreePos.le
  have hleft : 3 * (4 / 3 : ℝ) = 4 := by
    exact (mul_comm (3 : ℝ) (4 / 3)).trans
      (div_mul_cancel₀ 4 (ne_of_gt hthreePos))
  exact Eq.subst
    (motive := fun value : ℝ => value ≤
      3 * Complex.logarithmicPhaseBProcessScale t)
    hleft hscaled

theorem Real.four_sevenths_le_scale_div_add_one
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    (4 / 7 : ℝ) ≤
      Complex.logarithmicPhaseBProcessScale t /
        (Complex.logarithmicPhaseBProcessScale t + 1) := by
  let S := Complex.logarithmicPhaseBProcessScale t
  have hsevenPos : (0 : ℝ) < 7 := Nat.cast_pos.mpr (Nat.succ_pos 6)
  have haddPos := Complex.logarithmicPhaseBProcessScale_add_one_pos t
  have hthreeS := Real.three_mul_scale_ge_four t ht
  have htarget : (4 / 7 : ℝ) * (S + 1) ≤ S := by
    have hscaled := (div_le_iff₀ hsevenPos).mpr
      (show (4 : ℝ) * (S + 1) ≤ S * 7 by
        have hfourAdd : 4 * (S + 1) = 4 * S + 4 :=
          (mul_add 4 S 1).trans
            (congrArg (fun value : ℝ => 4 * S + value) (mul_one 4))
        have hsevenEq : (7 : ℝ) = 4 + 3 :=
          (Real.endpoint_nat_cast_add 4 3 7 rfl).symm
        have hseven : S * 7 = 4 * S + 3 * S := by
          calc
            S * 7 = 7 * S := mul_comm _ _
            _ = (4 + 3) * S := congrArg (fun value : ℝ => value * S) hsevenEq
            _ = 4 * S + 3 * S := add_mul 4 3 S
        have hadd := add_le_add_left hthreeS (4 * S)
        exact Eq.subst
          (motive := fun value : ℝ => value ≤ S * 7)
          hfourAdd.symm
          (Eq.subst
            (motive := fun value : ℝ => 4 * S + 4 ≤ value)
            hseven.symm hadd))
    have hproductDiv :
        (4 / 7 : ℝ) * (S + 1) = (4 * (S + 1)) / 7 :=
      div_mul_eq_mul_div 4 7 (S + 1)
    exact Eq.subst (motive := fun value : ℝ => value ≤ S)
      hproductDiv.symm hscaled
  exact (le_div_iff₀ haddPos).mpr htarget

theorem Complex.rightClippedCenterLower_ge_four_sevenths_b
    (t : ℝ) (ht : 1 ≤ ‖t‖) {b : ℕ} :
    (4 / 7 : ℝ) * (b : ℝ) ≤
      Complex.logarithmicPhaseBProcessRightClippedCenterLower t (b : ℤ) := by
  have hratio := Real.four_sevenths_le_scale_div_add_one t ht
  have hbNonneg : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hscaled := mul_le_mul_of_nonneg_right hratio hbNonneg
  unfold Complex.logarithmicPhaseBProcessRightClippedCenterLower
  have hright :
      (Complex.logarithmicPhaseBProcessScale t /
          (Complex.logarithmicPhaseBProcessScale t + 1)) * (b : ℝ) =
        (b : ℝ) * Complex.logarithmicPhaseBProcessScale t /
          (Complex.logarithmicPhaseBProcessScale t + 1) := by
    calc
      (Complex.logarithmicPhaseBProcessScale t /
          (Complex.logarithmicPhaseBProcessScale t + 1)) * (b : ℝ) =
          ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t) /
            (Complex.logarithmicPhaseBProcessScale t + 1) := by
        exact (div_mul_eq_mul_div _ _ _).trans
          (congrArg
            (fun value : ℝ => value /
              (Complex.logarithmicPhaseBProcessScale t + 1))
            (mul_comm _ _))
      _ = (b : ℝ) * Complex.logarithmicPhaseBProcessScale t /
          (Complex.logarithmicPhaseBProcessScale t + 1) := rfl
  exact Eq.subst
    (motive := fun value : ℝ => (4 / 7 : ℝ) * (b : ℝ) ≤ value)
    hright hscaled

theorem Real.b_mul_scale_sub_one_lt_b_sq
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (b : ℝ) * (Complex.logarithmicPhaseBProcessScale t - 1) <
      (b : ℝ) ^ 2 := by
  have hscaleA := Real.longGeometry_scale_lt_a hgeometry
  have hab : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hsubScale :
      Complex.logarithmicPhaseBProcessScale t - 1 < (b : ℝ) :=
    lt_trans (sub_lt_self _ zero_lt_one) (lt_of_lt_of_le hscaleA hab)
  have hbPos : 0 < (b : ℝ) := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one
      (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry))
  have hmul := mul_lt_mul_of_pos_left hsubScale hbPos
  exact Eq.subst
    (motive := fun value : ℝ =>
      (b : ℝ) * (Complex.logarithmicPhaseBProcessScale t - 1) < value)
    (pow_two (b : ℝ)).symm hmul

theorem Real.two_thirds_norm_lt_two_thirds_b_sq
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (2 / 3 : ℝ) * ‖t‖ < (2 / 3 : ℝ) * (b : ℝ) ^ 2 := by
  have hnormA := Real.longGeometry_norm_lt_a_sq hgeometry
  have hab : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have haNonneg : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have hbNonneg : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hsquareRaw := mul_le_mul hab hab haNonneg hbNonneg
  have hsquare : (a : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ (b : ℝ) ^ 2)
      (pow_two (a : ℝ)).symm
      (Eq.subst
        (motive := fun value : ℝ => (a : ℝ) * (a : ℝ) ≤ value)
        (pow_two (b : ℝ)).symm hsquareRaw)
  have hnormB := lt_of_lt_of_le hnormA hsquare
  exact mul_lt_mul_of_pos_left hnormB Real.two_thirds_pos

theorem Real.right_endpoint_numerator_lt_five_thirds_b_sq
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (b : ℝ) * (Complex.logarithmicPhaseBProcessScale t - 1) +
        (2 / 3 : ℝ) * ‖t‖ <
      (5 / 3 : ℝ) * (b : ℝ) ^ 2 := by
  have hfirst := Real.b_mul_scale_sub_one_lt_b_sq hgeometry
  have hsecond := Real.two_thirds_norm_lt_two_thirds_b_sq hgeometry
  have hadd := add_lt_add hfirst hsecond
  have hfactor :
      (b : ℝ) ^ 2 + (2 / 3 : ℝ) * (b : ℝ) ^ 2 =
        (5 / 3 : ℝ) * (b : ℝ) ^ 2 := by
    calc
      (b : ℝ) ^ 2 + (2 / 3 : ℝ) * (b : ℝ) ^ 2 =
          1 * (b : ℝ) ^ 2 + (2 / 3 : ℝ) * (b : ℝ) ^ 2 := by
        exact congrArg (fun value : ℝ => value + (2 / 3 : ℝ) * (b : ℝ) ^ 2)
          (one_mul ((b : ℝ) ^ 2)).symm
      _ = (1 + 2 / 3 : ℝ) * (b : ℝ) ^ 2 :=
        (add_mul 1 (2 / 3) ((b : ℝ) ^ 2)).symm
      _ = (5 / 3 : ℝ) * (b : ℝ) ^ 2 := by
        have hthreeNe : (3 : ℝ) ≠ 0 :=
          ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
        exact congrArg (fun value : ℝ => value * (b : ℝ) ^ 2)
          ((eq_div_iff hthreeNe).mpr
            (show (1 + 2 / 3 : ℝ) * 3 = 5 from by
              calc
                (1 + 2 / 3 : ℝ) * 3 = 1 * 3 + (2 / 3) * 3 := add_mul _ _ _
                _ = 1 * 3 + 2 := congrArg (fun value : ℝ => 1 * 3 + value)
                  (div_mul_cancel₀ 2 hthreeNe)
                _ = 3 + 2 := congrArg (fun value : ℝ => value + 2) (one_mul 3)
                _ = 5 := Real.endpoint_nat_cast_add 3 2 5 rfl))
  exact lt_of_lt_of_eq hadd hfactor

theorem Real.five_thirds_lt_ninety_six_forty_ninths :
    (5 / 3 : ℝ) < 96 / 49 := by
  have hthreePos : (0 : ℝ) < 3 := Nat.cast_pos.mpr (Nat.succ_pos 2)
  have hfortyNinePos : (0 : ℝ) < 49 := Nat.cast_pos.mpr (Nat.succ_pos 48)
  have hleft : (5 : ℝ) * 49 = 245 := Real.endpoint_nat_cast_mul 5 49 245 rfl
  have hright : (96 : ℝ) * 3 = 288 := Real.endpoint_nat_cast_mul 96 3 288 rfl
  have hnatSum : (245 : ℕ) < 245 + 43 :=
    Nat.lt_add_of_pos_right (Nat.succ_pos 42)
  have hsum : (245 : ℕ) + 43 = 288 := rfl
  have hnat : (245 : ℕ) < 288 := Eq.subst
    (motive := fun value : ℕ => 245 < value) hsum hnatSum
  have hcast : (245 : ℝ) < 288 := Nat.cast_lt.mpr hnat
  exact (div_lt_div_iff₀ hthreePos hfortyNinePos).mpr
    (Eq.subst (motive := fun value : ℝ => value < 96 * 3) hleft.symm
      (Eq.subst (motive := fun value : ℝ => (245 : ℝ) < value)
        hright.symm hcast))

theorem Real.six_mul_four_sevenths_square
    (x : ℝ) :
    6 * (((4 / 7 : ℝ) * x) ^ 2) = (96 / 49 : ℝ) * x ^ 2 := by
  have hcoeff : 6 * (4 / 7 : ℝ) ^ 2 = 96 / 49 := by
    have hsevenNe : (7 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 6))
    have hfortyNineNe : (49 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 48))
    calc
      6 * (4 / 7 : ℝ) ^ 2 = 6 * ((4 * 4) / (7 * 7)) := by
        exact congrArg (fun value : ℝ => 6 * value)
          ((pow_two (4 / 7 : ℝ)).trans (div_mul_div_comm 4 7 4 7))
      _ = 96 / 49 := by
        exact (eq_div_iff hfortyNineNe).mpr
          (show ((6 : ℝ) * ((4 * 4) / (7 * 7))) * 49 = 96 from by
          have hden : (7 * 7 : ℝ) = 49 :=
            Real.endpoint_nat_cast_mul 7 7 49 rfl
          exact Eq.subst
            (motive := fun denominator : ℝ =>
              (6 * ((4 * 4) / denominator)) * 49 = 96)
            hden.symm
            (calc
              ((6 : ℝ) * ((4 * 4) / 49)) * 49 =
                  6 * (((4 * 4) / 49) * 49) := mul_assoc _ _ _
              _ = (6 : ℝ) * (4 * 4) := by
                exact congrArg (fun value : ℝ => (6 : ℝ) * value)
                  (div_mul_cancel₀ (4 * 4) hfortyNineNe)
              _ = (6 : ℝ) * 16 := congrArg (fun value : ℝ => (6 : ℝ) * value)
                Real.endpoint_four_mul_four_eq_sixteen
              _ = 96 := Real.endpoint_nat_cast_mul 6 16 96 rfl))
  exact (congrArg (fun value : ℝ => 6 * value)
    (Real.square_mul_square (4 / 7 : ℝ) x)).trans
    ((mul_assoc 6 ((4 / 7 : ℝ) ^ 2) (x ^ 2)).symm.trans
      (congrArg (fun value : ℝ => value * x ^ 2) hcoeff))

theorem Complex.rightEndpoint_angular_width
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ *
        (((b : ℝ) + 2 / 3) -
          Complex.logarithmicPhaseBProcessRightClippedCenterLower t (b : ℤ)) <
      (2 * Real.pi) *
        (Complex.logarithmicPhaseBProcessRightClippedCenterLower t (b : ℤ)) ^ 2 := by
  let S := Complex.logarithmicPhaseBProcessScale t
  have hgap := Complex.rightEndpointCenterLayer_gap_eq t (b : ℤ)
  have hnorm := Complex.logarithmicPhaseBProcess_norm_eq_scale_sub_mul_add t
  have haddNe : S + 1 ≠ 0 :=
    ne_of_gt (Complex.logarithmicPhaseBProcessScale_add_one_pos t)
  have hcancel := Real.mul_div_cancel_add_factor (b : ℝ) S haddNe
  have hcancelNorm :
      ‖t‖ * ((b : ℝ) / (S + 1)) = (b : ℝ) * (S - 1) :=
    (congrArg (fun value : ℝ => value * ((b : ℝ) / (S + 1))) hnorm).trans
      hcancel
  have hexact :
      ‖t‖ *
          (((b : ℝ) + 2 / 3) -
            Complex.logarithmicPhaseBProcessRightClippedCenterLower t (b : ℤ)) =
        (b : ℝ) * (S - 1) + (2 / 3 : ℝ) * ‖t‖ := by
    calc
      ‖t‖ *
          (((b : ℝ) + 2 / 3) -
            Complex.logarithmicPhaseBProcessRightClippedCenterLower t (b : ℤ)) =
          ‖t‖ * ((b : ℝ) / (S + 1) + 2 / 3) :=
        congrArg (fun value : ℝ => ‖t‖ * value) hgap
      _ = ‖t‖ * ((b : ℝ) / (S + 1)) + ‖t‖ * (2 / 3) := mul_add _ _ _
      _ = (b : ℝ) * (S - 1) + (2 / 3) * ‖t‖ := by
        exact congrArg₂ (fun left right : ℝ => left + right)
          hcancelNorm
          (mul_comm ‖t‖ (2 / 3))
  have hnumerator := Real.right_endpoint_numerator_lt_five_thirds_b_sq hgeometry
  have hcoeff := Real.five_thirds_lt_ninety_six_forty_ninths
  have hbPos : 0 < (b : ℝ) := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one
      (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry))
  have hbSqPos : 0 < (b : ℝ) ^ 2 := sq_pos_of_pos hbPos
  have hcoefficient := mul_lt_mul_of_pos_right hcoeff hbSqPos
  have hlower := Complex.rightClippedCenterLower_ge_four_sevenths_b
    t ht (b := b)
  have hfourNonneg : 0 ≤ (4 / 7 : ℝ) * (b : ℝ) :=
    mul_nonneg
      (div_nonneg (Nat.cast_nonneg 4) (Nat.cast_nonneg 7)) hbPos.le
  have hcenterNonneg := le_trans hfourNonneg hlower
  have hsquare := Real.square_le_square_of_nonneg hfourNonneg hlower
  have hsixSquare := mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg 6)
  have hnormalize := Real.six_mul_four_sevenths_square (b : ℝ)
  have htoSix :
      (96 / 49 : ℝ) * (b : ℝ) ^ 2 ≤
        6 * (Complex.logarithmicPhaseBProcessRightClippedCenterLower
          t (b : ℤ)) ^ 2 :=
    Eq.mp
      (congrArg
        (fun value : ℝ => value ≤
          6 * (Complex.logarithmicPhaseBProcessRightClippedCenterLower
            t (b : ℤ)) ^ 2)
        hnormalize)
      hsixSquare
  have hpiSquare := mul_lt_mul_of_pos_right Real.six_lt_two_mul_pi
    (sq_pos_of_pos
      (Complex.logarithmicPhaseBProcessRightClipped_lower_pos t
        (Int.ofNat_le.mpr
          (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry))))
  exact Eq.subst
    (motive := fun value : ℝ => value <
      (2 * Real.pi) *
        (Complex.logarithmicPhaseBProcessRightClippedCenterLower t (b : ℤ)) ^ 2)
    hexact.symm
    (lt_trans hnumerator
      (lt_trans hcoefficient
        (lt_of_le_of_lt htoSix hpiSquare)))

theorem Complex.logarithmicPhasePoissonBProcessEndpointModes_card_le_two
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)).card ≤ 2 := by
  exact
    Complex.logarithmicPhasePoissonBProcessEndpointModes_card_le_two_of_side_widths
      ht hgeometry
      (Complex.leftEndpoint_angular_width ht hgeometry)
      (Complex.rightEndpoint_angular_width ht hgeometry)

theorem Finset.sum_le_two_mul_of_card_le_two
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (C : ℝ)
    (hcard : s.card ≤ 2)
    (hC : 0 ≤ C)
    (hpoint : ∀ x ∈ s, f x ≤ C) :
    ∑ x ∈ s, f x ≤ 2 * C := by
  have hsum := Finset.sum_le_card_mul_of_pointwise_le s f C hpoint
  have hcast : (s.card : ℝ) ≤ 2 := Nat.cast_le.mpr hcard
  have hmul := mul_le_mul_of_nonneg_right hcast hC
  exact le_trans hsum hmul

theorem Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_two_perModeMajorant
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget
        t (a : ℤ) (b : ℤ) ≤
      2 * Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant
        t (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointBudget
  exact Finset.sum_le_two_mul_of_card_le_two
    (Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant
      t (b : ℤ))
    (Complex.logarithmicPhasePoissonBProcessEndpointModes_card_le_two
      ht hgeometry)
    (Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant_nonneg ht)
    (fun m hm =>
      Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_le_perModeMajorant
        ht hgeometry hm)

end

end LFunctions
end Boundary
