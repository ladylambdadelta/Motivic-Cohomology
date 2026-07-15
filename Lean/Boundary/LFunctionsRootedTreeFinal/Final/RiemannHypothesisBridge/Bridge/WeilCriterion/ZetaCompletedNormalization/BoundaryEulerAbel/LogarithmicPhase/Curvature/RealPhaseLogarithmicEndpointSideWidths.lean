import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicEndpointSidePacking

/-!
# Angular widths of the two endpoint sides

Writing `S = sqrt (1 + ‖t‖)`, the exact identity
`‖t‖ = (S - 1)(S + 1)` cancels the apparent denominators in the two clipped
center layers.  Elementary fixed-ratio estimates then place each whole side
in a frequency interval of width less than one.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseBProcess_norm_eq_scale_sq_sub_one
    (t : ℝ) :
    ‖t‖ = Complex.logarithmicPhaseBProcessScale t ^ 2 - 1 := by
  have hsquare :=
    Complex.logarithmicPhaseBProcessScale_sq_eq_one_add_norm t
  have hsub := congrArg (fun value : ℝ => value - 1) hsquare
  have hright : 1 + ‖t‖ - 1 = ‖t‖ := add_sub_cancel_left 1 ‖t‖
  exact (hsub.trans hright).symm

theorem Real.square_sub_one_eq_sub_mul_add
    (S : ℝ) :
    S ^ 2 - 1 = (S - 1) * (S + 1) := by
  calc
    S ^ 2 - 1 = S * S - 1 * 1 := by
      exact congrArg₂ (fun left right : ℝ => left - right)
        (pow_two S) (one_mul 1).symm
    _ = (S + 1) * (S - 1) := mul_self_sub_mul_self S 1
    _ = (S - 1) * (S + 1) := mul_comm _ _

theorem Complex.logarithmicPhaseBProcess_norm_eq_scale_sub_mul_add
    (t : ℝ) :
    ‖t‖ =
      (Complex.logarithmicPhaseBProcessScale t - 1) *
        (Complex.logarithmicPhaseBProcessScale t + 1) := by
  exact (Complex.logarithmicPhaseBProcess_norm_eq_scale_sq_sub_one t).trans
    (Real.square_sub_one_eq_sub_mul_add
      (Complex.logarithmicPhaseBProcessScale t))

theorem Real.mul_div_cancel_sub_factor
    (a S : ℝ) (hsub : S - 1 ≠ 0) :
    ((S - 1) * (S + 1)) * (a / (S - 1)) = a * (S + 1) := by
  calc
    ((S - 1) * (S + 1)) * (a / (S - 1)) =
        (a / (S - 1)) * ((S - 1) * (S + 1)) :=
      mul_comm _ _
    _ = ((a / (S - 1)) * (S - 1)) * (S + 1) :=
      (mul_assoc _ _ _).symm
    _ = a * (S + 1) := by
      exact congrArg (fun value : ℝ => value * (S + 1))
        (div_mul_cancel₀ a hsub)

theorem Real.mul_div_cancel_add_factor
    (b S : ℝ) (hadd : S + 1 ≠ 0) :
    ((S - 1) * (S + 1)) * (b / (S + 1)) = b * (S - 1) := by
  calc
    ((S - 1) * (S + 1)) * (b / (S + 1)) =
        (b / (S + 1)) * ((S - 1) * (S + 1)) :=
      mul_comm _ _
    _ = (b / (S + 1)) * ((S + 1) * (S - 1)) := by
      exact congrArg (fun value : ℝ => (b / (S + 1)) * value)
        (mul_comm (S - 1) (S + 1))
    _ = ((b / (S + 1)) * (S + 1)) * (S - 1) :=
      (mul_assoc _ _ _).symm
    _ = b * (S - 1) := by
      exact congrArg (fun value : ℝ => value * (S - 1))
        (div_mul_cancel₀ b hadd)

theorem Real.add_sub_sub_eq_add
    (x q r : ℝ) :
    (x + q) - (x - r) = q + r := by
  calc
    (x + q) - (x - r) = (x + q) - (x + (-r)) := by
      exact congrArg (fun value : ℝ => (x + q) - value)
        (sub_eq_add_neg x r)
    _ = q - (-r) := add_sub_add_left_eq_sub q (-r) x
    _ = q + r := sub_neg_eq_add q r

theorem Complex.leftEndpointCenterLayer_gap_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a : ℤ) :
    Complex.logarithmicPhaseBProcessLeftClippedCenterUpper t a -
        Real.integerBlockCutoffSupportLeftEndpoint a =
      (a : ℝ) /
          (Complex.logarithmicPhaseBProcessScale t - 1) + 2 / 3 := by
  let S := Complex.logarithmicPhaseBProcessScale t
  have hsubNe : S - 1 ≠ 0 :=
    ne_of_gt (Complex.logarithmicPhaseBProcessScale_sub_one_pos t ht)
  unfold Complex.logarithmicPhaseBProcessLeftClippedCenterUpper
  unfold Real.integerBlockCutoffSupportLeftEndpoint
  have hquotient :
      (a : ℝ) * S / (S - 1) =
        (a : ℝ) + (a : ℝ) / (S - 1) := by
    have hleft :
        ((a : ℝ) * S / (S - 1)) * (S - 1) = (a : ℝ) * S :=
      div_mul_cancel₀ ((a : ℝ) * S) hsubNe
    have hright :
        ((a : ℝ) + (a : ℝ) / (S - 1)) * (S - 1) =
          (a : ℝ) * S := by
      calc
        ((a : ℝ) + (a : ℝ) / (S - 1)) * (S - 1) =
            (a : ℝ) * (S - 1) + (a : ℝ) := by
          exact (add_mul (a : ℝ) ((a : ℝ) / (S - 1)) (S - 1)).trans
            (congrArg (fun value : ℝ => (a : ℝ) * (S - 1) + value)
              (div_mul_cancel₀ (a : ℝ) hsubNe))
        _ = (a : ℝ) * S := by
          calc
            (a : ℝ) * (S - 1) + (a : ℝ) =
                (a : ℝ) * (S - 1) + (a : ℝ) * 1 := by
              exact congrArg (fun value : ℝ => (a : ℝ) * (S - 1) + value)
                (mul_one (a : ℝ)).symm
            _ = (a : ℝ) * ((S - 1) + 1) :=
              (mul_add (a : ℝ) (S - 1) 1).symm
            _ = (a : ℝ) * S := by
              exact congrArg (fun value : ℝ => (a : ℝ) * value)
                (sub_add_cancel S 1)
    exact mul_right_cancel₀ hsubNe (hleft.trans hright.symm)
  calc
    (a : ℝ) * S / (S - 1) - ((a : ℝ) - 2 / 3) =
        ((a : ℝ) + (a : ℝ) / (S - 1)) - ((a : ℝ) - 2 / 3) := by
      exact congrArg (fun value : ℝ => value - ((a : ℝ) - 2 / 3)) hquotient
    _ = (a : ℝ) / (S - 1) + 2 / 3 := by
      exact Real.add_sub_sub_eq_add
        (a : ℝ) ((a : ℝ) / (S - 1)) (2 / 3)

theorem Complex.rightEndpointCenterLayer_gap_eq
    (t : ℝ) (b : ℤ) :
    ((b : ℝ) + 2 / 3) -
        Complex.logarithmicPhaseBProcessRightClippedCenterLower t b =
      (b : ℝ) /
          (Complex.logarithmicPhaseBProcessScale t + 1) + 2 / 3 := by
  let S := Complex.logarithmicPhaseBProcessScale t
  have haddNe : S + 1 ≠ 0 :=
    ne_of_gt (Complex.logarithmicPhaseBProcessScale_add_one_pos t)
  unfold Complex.logarithmicPhaseBProcessRightClippedCenterLower
  have hquotient :
      (b : ℝ) * S / (S + 1) =
        (b : ℝ) - (b : ℝ) / (S + 1) := by
    have hleft := div_mul_cancel₀ ((b : ℝ) * S) haddNe
    have hright :
          ((b : ℝ) - (b : ℝ) / (S + 1)) * (S + 1) =
            (b : ℝ) * S := by
        calc
          ((b : ℝ) - (b : ℝ) / (S + 1)) * (S + 1) =
              (b : ℝ) * (S + 1) - (b : ℝ) := by
            exact (sub_mul (b : ℝ) ((b : ℝ) / (S + 1)) (S + 1)).trans
              (congrArg (fun value : ℝ => (b : ℝ) * (S + 1) - value)
                (div_mul_cancel₀ (b : ℝ) haddNe))
          _ = (b : ℝ) * S := by
            calc
              (b : ℝ) * (S + 1) - (b : ℝ) =
                  (b : ℝ) * (S + 1) - (b : ℝ) * 1 := by
                exact congrArg (fun value : ℝ => (b : ℝ) * (S + 1) - value)
                  (mul_one (b : ℝ)).symm
              _ = (b : ℝ) * ((S + 1) - 1) :=
                (mul_sub (b : ℝ) (S + 1) 1).symm
              _ = (b : ℝ) * S := by
                exact congrArg (fun value : ℝ => (b : ℝ) * value)
                  (add_sub_cancel_right S 1)
    exact mul_right_cancel₀ haddNe (hleft.trans hright.symm)
  calc
    ((b : ℝ) + 2 / 3) - (b : ℝ) * S / (S + 1) =
        ((b : ℝ) + 2 / 3) - ((b : ℝ) - (b : ℝ) / (S + 1)) := by
      exact congrArg (fun value : ℝ => ((b : ℝ) + 2 / 3) - value) hquotient
    _ = (b : ℝ) / (S + 1) + 2 / 3 := by
      exact (Real.add_sub_sub_eq_add
        (b : ℝ) (2 / 3) ((b : ℝ) / (S + 1))).trans (add_comm _ _)

theorem Real.endpoint_four_mul_four_eq_sixteen :
    (4 : ℝ) * 4 = 16 := by
  have hnat : (4 : ℕ) * 4 = 16 := rfl
  exact (Nat.cast_mul 4 4).symm.trans
    (congrArg (fun n : ℕ => (n : ℝ)) hnat)

theorem Real.endpoint_three_mul_three_eq_nine :
    (3 : ℝ) * 3 = 9 := by
  have hnat : (3 : ℕ) * 3 = 9 := rfl
  exact (Nat.cast_mul 3 3).symm.trans
    (congrArg (fun n : ℕ => (n : ℝ)) hnat)

theorem Real.endpoint_two_mul_nine_eq_eighteen :
    (2 : ℝ) * 9 = 18 := by
  have hnat : (2 : ℕ) * 9 = 18 := rfl
  exact (Nat.cast_mul 2 9).symm.trans
    (congrArg (fun n : ℕ => (n : ℝ)) hnat)

theorem Real.endpoint_sixteen_le_eighteen :
    (16 : ℝ) ≤ 18 := by
  have hnat : (16 : ℕ) ≤ 18 :=
    Nat.le.step (Nat.le.step (Nat.le_refl 16))
  exact Nat.cast_le.mpr hnat

theorem Real.four_thirds_le_BProcessScale
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    (4 / 3 : ℝ) ≤ Complex.logarithmicPhaseBProcessScale t := by
  have hscaleSq := Complex.logarithmicPhaseBProcessScale_sq t
  have honeAddOne : (1 : ℝ) + 1 = 2 := one_add_one_eq_two
  have honeAdded : (1 : ℝ) + 1 ≤ 1 + ‖t‖ := add_le_add_left ht 1
  have htwo : (2 : ℝ) ≤ 1 + ‖t‖ := Eq.subst
    (motive := fun value : ℝ => value ≤ 1 + ‖t‖)
    honeAddOne honeAdded
  have hscaleNonneg := Complex.logarithmicPhaseBProcessScale_nonneg t
  have hfourThirdsNonneg : (0 : ℝ) ≤ 4 / 3 :=
    div_nonneg (Nat.cast_nonneg 4) (Nat.cast_nonneg 3)
  have hsquares : (4 / 3 : ℝ) ^ 2 ≤
      Complex.logarithmicPhaseBProcessScale t ^ 2 := by
    have hleft : (4 / 3 : ℝ) ^ 2 ≤ 2 := by
      have hninePos : (0 : ℝ) < 9 :=
        Nat.cast_pos.mpr (Nat.succ_pos 8)
      have hfraction : (4 / 3 : ℝ) ^ 2 = 16 / 9 := by
        calc
          (4 / 3 : ℝ) ^ 2 = (4 / 3) * (4 / 3) := pow_two _
          _ = (4 * 4) / (3 * 3) := div_mul_div_comm 4 3 4 3
          _ = 16 / (3 * 3) := by
            exact congrArg (fun value : ℝ => value / (3 * 3))
              Real.endpoint_four_mul_four_eq_sixteen
          _ = 16 / 9 := by
            exact congrArg (fun value : ℝ => 16 / value)
              Real.endpoint_three_mul_three_eq_nine
      have hsixteenLeTwoNine : (16 : ℝ) ≤ 2 * 9 :=
        Eq.subst
          (motive := fun value : ℝ => (16 : ℝ) ≤ value)
          Real.endpoint_two_mul_nine_eq_eighteen.symm
          Real.endpoint_sixteen_le_eighteen
      have hratio : (16 / 9 : ℝ) ≤ 2 :=
        (div_le_iff₀ hninePos).mpr
          hsixteenLeTwoNine
      exact Eq.subst (motive := fun value : ℝ => value ≤ 2)
        hfraction.symm hratio
    exact le_trans hleft
      (Eq.subst (motive := fun value : ℝ => 2 ≤ value)
        (Complex.logarithmicPhaseBProcessScale_sq_eq_one_add_norm t).symm htwo)
  exact le_of_sq_le_sq hsquares hscaleNonneg

end

end LFunctions
end Boundary
