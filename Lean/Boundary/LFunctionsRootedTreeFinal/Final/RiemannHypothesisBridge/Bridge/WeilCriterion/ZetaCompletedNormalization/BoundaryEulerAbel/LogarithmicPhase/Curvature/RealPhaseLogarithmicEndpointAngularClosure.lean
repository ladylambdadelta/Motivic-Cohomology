import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicEndpointSideWidths

/-!
# Closure of the two endpoint angular widths

This file discharges the two inequalities left abstract by the side-packing
owner.  All estimates are arranged as positive scalar comparisons.  The
retained angular constant `2π > 6` supplies the final strict margin.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.endpoint_nat_cast_mul
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * b = c :=
  (Nat.cast_mul a b).symm.trans
    (congrArg (fun n : ℕ => (n : ℝ)) h)

theorem Real.endpoint_nat_cast_add
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + b = c :=
  (Nat.cast_add a b).symm.trans
    (congrArg (fun n : ℕ => (n : ℝ)) h)

theorem Real.one_le_half_mul_of_two_le
    {x : ℝ} (hx : 2 ≤ x) :
    1 ≤ (1 / 2 : ℝ) * x := by
  have hhalfNonneg : (0 : ℝ) ≤ 1 / 2 :=
    div_nonneg zero_le_one (Nat.cast_nonneg 2)
  have hscaled := mul_le_mul_of_nonneg_left hx hhalfNonneg
  have hnormalize : (1 / 2 : ℝ) * 2 = 1 := by
    exact div_mul_cancel₀ 1
      (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 1)))
  exact Eq.subst (motive := fun value : ℝ => value ≤ (1 / 2 : ℝ) * x)
    hnormalize hscaled

theorem Real.add_one_le_three_halves_mul
    {x : ℝ} (hx : 2 ≤ x) :
    x + 1 ≤ (3 / 2 : ℝ) * x := by
  have hone := Real.one_le_half_mul_of_two_le hx
  have hadd := add_le_add_left hone x
  have hright : x + (1 / 2 : ℝ) * x = (3 / 2 : ℝ) * x := by
    calc
      x + (1 / 2 : ℝ) * x = 1 * x + (1 / 2 : ℝ) * x := by
        exact congrArg (fun value : ℝ => value + (1 / 2 : ℝ) * x)
          (one_mul x).symm
      _ = (1 + 1 / 2 : ℝ) * x := (add_mul 1 (1 / 2) x).symm
      _ = (3 / 2 : ℝ) * x := by
        exact congrArg (fun value : ℝ => value * x)
          (show (1 + 1 / 2 : ℝ) = (3 : ℝ) / 2 from by
            have htwoNe : (2 : ℝ) ≠ 0 :=
              ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 1))
            exact (eq_div_iff htwoNe).mpr (show (1 + 1 / 2 : ℝ) * 2 = 3 from by
              calc
                (1 + 1 / 2 : ℝ) * 2 = 1 * 2 + (1 / 2) * 2 := add_mul _ _ _
                _ = 1 * 2 + 1 := congrArg (fun value : ℝ => 1 * 2 + value)
                  (div_mul_cancel₀ 1 htwoNe)
                _ = (2 : ℝ) + 1 := congrArg (fun value : ℝ => value + 1)
                  (one_mul (2 : ℝ))
                _ = (3 : ℝ) := _root_.two_add_one_eq_three))
  exact le_trans hadd (le_of_eq hright)

theorem Real.two_thirds_mul_norm_lt_two_thirds_mul_a_sq
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (2 / 3 : ℝ) * ‖t‖ < (2 / 3 : ℝ) * (a : ℝ) ^ 2 := by
  exact mul_lt_mul_of_pos_left
    (Real.longGeometry_norm_lt_a_sq hgeometry)
    Real.two_thirds_pos

theorem Real.a_mul_scale_add_one_lt_three_halves_a_sq
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (a : ℝ) * (Complex.logarithmicPhaseBProcessScale t + 1) <
      (3 / 2 : ℝ) * (a : ℝ) ^ 2 := by
  have hscaleA := Real.longGeometry_scale_lt_a hgeometry
  have hadd := add_lt_add_right hscaleA 1
  have haPos : 0 < (a : ℝ) := Nat.cast_pos.mpr
    (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)
  have hmul := mul_lt_mul_of_pos_left hadd haPos
  have hthreeHalf := Real.add_one_le_three_halves_mul
    (Nat.cast_le.mpr
      (Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry))
  have hscaled := mul_le_mul_of_nonneg_left hthreeHalf haPos.le
  have hright :
      (a : ℝ) * ((3 / 2 : ℝ) * (a : ℝ)) =
        (3 / 2 : ℝ) * (a : ℝ) ^ 2 := by
    calc
      (a : ℝ) * ((3 / 2 : ℝ) * (a : ℝ)) =
          (3 / 2 : ℝ) * ((a : ℝ) * (a : ℝ)) := by
        exact mul_left_comm (a : ℝ) (3 / 2) (a : ℝ)
      _ = (3 / 2 : ℝ) * (a : ℝ) ^ 2 := by
        exact congrArg (fun value : ℝ => (3 / 2 : ℝ) * value)
          (pow_two (a : ℝ)).symm
  exact lt_of_lt_of_le hmul
    (Eq.subst
      (motive := fun value : ℝ =>
        (a : ℝ) * ((a : ℝ) + 1) ≤ value)
      hright hscaled)

theorem Real.left_endpoint_numerator_lt_thirteen_sixths_a_sq
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (a : ℝ) * (Complex.logarithmicPhaseBProcessScale t + 1) +
        (2 / 3 : ℝ) * ‖t‖ <
      (13 / 6 : ℝ) * (a : ℝ) ^ 2 := by
  have hfirst := Real.a_mul_scale_add_one_lt_three_halves_a_sq hgeometry
  have hsecond := Real.two_thirds_mul_norm_lt_two_thirds_mul_a_sq hgeometry
  have hadd := add_lt_add hfirst hsecond
  have hcoeff : (3 / 2 : ℝ) + 2 / 3 = (13 : ℝ) / 6 := by
    have hsixNe : (6 : ℝ) ≠ 0 := ne_of_gt
      (Nat.cast_pos.mpr (Nat.succ_pos 5))
    exact (eq_div_iff hsixNe).mpr
      (show ((3 / 2 : ℝ) + 2 / 3) * 6 = 13 from by
        have htwoNe : (2 : ℝ) ≠ 0 := ne_of_gt
          (Nat.cast_pos.mpr (Nat.succ_pos 1))
        have hthreeNe : (3 : ℝ) ≠ 0 := ne_of_gt
          (Nat.cast_pos.mpr (Nat.succ_pos 2))
        have hsixTwoThree : (6 : ℝ) = 2 * 3 :=
          (Real.endpoint_nat_cast_mul 2 3 6 rfl).symm
        have hsixThreeTwo : (6 : ℝ) = 3 * 2 :=
          (Real.endpoint_nat_cast_mul 3 2 6 rfl).symm
        calc
          ((3 / 2 : ℝ) + 2 / 3) * 6 = (3 / 2) * 6 + (2 / 3) * 6 :=
            add_mul _ _ _
          _ = 9 + 4 := by
            exact congrArg₂ (fun left right : ℝ => left + right)
              (calc
                (3 / 2 : ℝ) * 6 = (3 / 2) * (2 * 3) :=
                  congrArg (fun value : ℝ => (3 / 2) * value) hsixTwoThree
                _ = ((3 / 2) * 2) * 3 := (mul_assoc _ _ _).symm
                _ = 3 * 3 := by
                  exact congrArg (fun value : ℝ => value * 3)
                    (div_mul_cancel₀ 3 htwoNe)
                _ = 9 := Real.endpoint_three_mul_three_eq_nine)
              (calc
                (2 / 3 : ℝ) * 6 = (2 / 3) * (3 * 2) :=
                  congrArg (fun value : ℝ => (2 / 3) * value) hsixThreeTwo
                _ = ((2 / 3) * 3) * 2 := (mul_assoc _ _ _).symm
                _ = 2 * 2 := by
                  exact congrArg (fun value : ℝ => value * 2)
                    (div_mul_cancel₀ 2 hthreeNe)
                _ = 4 := Real.endpoint_nat_cast_mul 2 2 4 rfl)
          _ = 13 := Real.endpoint_nat_cast_add 9 4 13 rfl)
  have hfactor :
      (3 / 2 : ℝ) * (a : ℝ) ^ 2 +
          (2 / 3 : ℝ) * (a : ℝ) ^ 2 =
        (13 / 6 : ℝ) * (a : ℝ) ^ 2 := by
    exact (add_mul (3 / 2) (2 / 3) ((a : ℝ) ^ 2)).symm.trans
      (congrArg (fun value : ℝ => value * (a : ℝ) ^ 2) hcoeff)
  exact lt_of_lt_of_eq hadd hfactor

theorem Real.thirteen_sixths_a_sq_lt_six_cutoff_left_sq
    {a : ℕ} (ha : 2 ≤ a) :
    (13 / 6 : ℝ) * (a : ℝ) ^ 2 <
      6 * ((a : ℝ) - 2 / 3) ^ 2 := by
  have haReal : (2 : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr ha
  have htwoThirdsA := Real.two_thirds_mul_a_le_a_sub_two_thirds ha
  have htwoThirdsNonneg : (0 : ℝ) ≤ (2 / 3) * (a : ℝ) :=
    mul_nonneg (le_of_lt Real.two_thirds_pos) (Nat.cast_nonneg a)
  have hsquare := Real.square_le_square_of_nonneg
    htwoThirdsNonneg htwoThirdsA
  have hscaled := mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg 6)
  have hnormalize :
      6 * (((2 / 3 : ℝ) * (a : ℝ)) ^ 2) =
        (8 / 3 : ℝ) * (a : ℝ) ^ 2 := by
    have hcoeff : 6 * (2 / 3 : ℝ) ^ 2 = 8 / 3 := by
      have hthreeNe : (3 : ℝ) ≠ 0 := ne_of_gt
        (Nat.cast_pos.mpr (Nat.succ_pos 2))
      calc
        6 * (2 / 3 : ℝ) ^ 2 = 6 * ((2 / 3 : ℝ) * (2 / 3)) :=
          congrArg (fun value : ℝ => 6 * value) (pow_two (2 / 3 : ℝ))
        _ = (6 * (2 / 3 : ℝ)) * (2 / 3) :=
          (mul_assoc (6 : ℝ) (2 / 3) (2 / 3)).symm
        _ = 4 * (2 / 3) := by
          exact congrArg (fun value : ℝ => value * (2 / 3))
            (show (6 : ℝ) * (2 / 3) = 4 from by
              exact (mul_div_assoc 6 2 3).symm.trans
                ((div_eq_iff hthreeNe).mpr
                  ((Real.endpoint_nat_cast_mul 6 2 12 rfl).trans
                    (Real.endpoint_nat_cast_mul 4 3 12 rfl).symm)))
        _ = 8 / 3 := by
          calc
            (4 : ℝ) * (2 / 3) = (4 * 2) / 3 :=
              (mul_div_assoc (4 : ℝ) 2 3).symm
            _ = 8 / 3 := congrArg (fun value : ℝ => value / 3)
              (Real.endpoint_nat_cast_mul 4 2 8 rfl)
    exact (congrArg (fun value : ℝ => 6 * value)
      (Real.square_mul_square (2 / 3 : ℝ) (a : ℝ))).trans
      ((mul_assoc 6 ((2 / 3 : ℝ) ^ 2) ((a : ℝ) ^ 2)).symm.trans
        (congrArg (fun value : ℝ => value * (a : ℝ) ^ 2) hcoeff))
  have hcoeffStrict : (13 / 6 : ℝ) < 8 / 3 := by
    have hsixPos : (0 : ℝ) < 6 := Nat.cast_pos.mpr (Nat.succ_pos 5)
    have hthreePos : (0 : ℝ) < 3 := Nat.cast_pos.mpr (Nat.succ_pos 2)
    have h39 : (13 : ℝ) * 3 = 39 := Real.endpoint_nat_cast_mul 13 3 39 rfl
    have h48 : (8 : ℝ) * 6 = 48 := Real.endpoint_nat_cast_mul 8 6 48 rfl
    have hnatSum : (39 : ℕ) < 39 + 9 :=
      Nat.lt_add_of_pos_right (Nat.succ_pos 8)
    have hsumNat : (39 : ℕ) + 9 = 48 := rfl
    have hnat : (39 : ℕ) < 48 := Eq.subst
      (motive := fun value : ℕ => 39 < value) hsumNat hnatSum
    have hcast : (39 : ℝ) < 48 := Nat.cast_lt.mpr hnat
    exact (div_lt_div_iff₀ hsixPos hthreePos).mpr
      (Eq.subst (motive := fun left : ℝ => left < 8 * 6) h39.symm
        (Eq.subst (motive := fun right : ℝ => (39 : ℝ) < right) h48.symm hcast))
  have haSqPos : 0 < (a : ℝ) ^ 2 :=
    sq_pos_of_pos (lt_of_lt_of_le zero_lt_two haReal)
  have hstrict := mul_lt_mul_of_pos_right hcoeffStrict haSqPos
  have hnormalizedBound :
      (8 / 3 : ℝ) * (a : ℝ) ^ 2 ≤
        6 * ((a : ℝ) - 2 / 3) ^ 2 := by
    exact Eq.mp
      (congrArg
        (fun value : ℝ =>
          value ≤ 6 * ((a : ℝ) - 2 / 3) ^ 2)
        hnormalize)
      hscaled
  exact lt_of_lt_of_le hstrict hnormalizedBound

theorem Complex.leftEndpoint_angular_width
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ *
        (Complex.logarithmicPhaseBProcessLeftClippedCenterUpper t (a : ℤ) -
          Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) <
      (2 * Real.pi) *
        (Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) ^ 2 := by
  let S := Complex.logarithmicPhaseBProcessScale t
  have hgap := Complex.leftEndpointCenterLayer_gap_eq t ht (a : ℤ)
  have hnorm := Complex.logarithmicPhaseBProcess_norm_eq_scale_sub_mul_add t
  have hsubNe : S - 1 ≠ 0 :=
    ne_of_gt (Complex.logarithmicPhaseBProcessScale_sub_one_pos t ht)
  have hcancel := Real.mul_div_cancel_sub_factor (a : ℝ) S hsubNe
  have hcancelNorm :
      ‖t‖ * ((a : ℝ) / (S - 1)) = (a : ℝ) * (S + 1) :=
    (congrArg (fun value : ℝ => value * ((a : ℝ) / (S - 1))) hnorm).trans
      hcancel
  have hexact :
      ‖t‖ *
          (Complex.logarithmicPhaseBProcessLeftClippedCenterUpper t (a : ℤ) -
            Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) =
        (a : ℝ) * (S + 1) + (2 / 3 : ℝ) * ‖t‖ := by
    calc
      ‖t‖ *
          (Complex.logarithmicPhaseBProcessLeftClippedCenterUpper t (a : ℤ) -
            Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) =
          ‖t‖ * ((a : ℝ) / (S - 1) + 2 / 3) :=
        congrArg (fun value : ℝ => ‖t‖ * value) hgap
      _ = ‖t‖ * ((a : ℝ) / (S - 1)) + ‖t‖ * (2 / 3) :=
        mul_add _ _ _
      _ = (a : ℝ) * (S + 1) + (2 / 3) * ‖t‖ := by
        exact congrArg₂ (fun left right : ℝ => left + right)
          hcancelNorm
          (mul_comm ‖t‖ (2 / 3))
  have hnumerator :=
    Real.left_endpoint_numerator_lt_thirteen_sixths_a_sq hgeometry
  have hcutoff :=
    Real.thirteen_sixths_a_sq_lt_six_cutoff_left_sq
      (Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry)
  have hsix := lt_trans hnumerator hcutoff
  have hsquarePos :
      0 < ((a : ℝ) - 2 / 3) ^ 2 :=
    sq_pos_of_pos
      (Complex.integerBlockCutoffSupportLeftEndpoint_pos
        (Int.ofNat_le.mpr
          (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)))
  have hpiScaled := mul_lt_mul_of_pos_right Real.six_lt_two_mul_pi hsquarePos
  unfold Real.integerBlockCutoffSupportLeftEndpoint
  exact Eq.subst
    (motive := fun value : ℝ =>
      value < (2 * Real.pi) * ((a : ℝ) - 2 / 3) ^ 2)
    hexact.symm
    (lt_trans hsix hpiScaled)

end

end LFunctions
end Boundary
