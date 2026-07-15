import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveNearWidthArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicEndpointAngularCompletion

/-!
# Cardinality one for each near finite inactive family

The exact collar numerators are dominated by angular squares at their lower
center endpoints.  The generic reflected-frequency packing theorem then shows
that each near family contains at most one integer mode.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseFiniteLeftNearCenterLower_ge_four_sevenths_a
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a : ℕ) :
    (4 / 7 : ℝ) * (a : ℝ) ≤
      Complex.logarithmicPhaseFiniteLeftNearCenterLower t (a : ℤ) := by
  unfold Complex.logarithmicPhaseFiniteLeftNearCenterLower
  exact Complex.rightClippedCenterLower_ge_four_sevenths_b t ht

theorem Real.a_mul_scale_sub_one_lt_a_sq
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (a : ℝ) * (Complex.logarithmicPhaseBProcessScale t - 1) <
      (a : ℝ) ^ 2 := by
  have haPos : 0 < (a : ℝ) := Nat.cast_pos.mpr
    (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)
  have hscale := Real.longGeometry_scale_lt_a hgeometry
  have hsub : Complex.logarithmicPhaseBProcessScale t - 1 < (a : ℝ) :=
    lt_trans (sub_lt_self _ zero_lt_one) hscale
  have hmul := mul_lt_mul_of_pos_left hsub haPos
  exact Eq.subst (motive := fun value : ℝ => _ < value)
    (pow_two (a : ℝ)).symm hmul

theorem Real.one_mul_a_sq_lt_six_mul_four_sevenths_a_sq
    {a : ℕ} (ha : 1 ≤ a) :
    (a : ℝ) ^ 2 <
      6 * (((4 / 7 : ℝ) * (a : ℝ)) ^ 2) := by
  have haPos : 0 < (a : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one ha)
  have haSqPos : 0 < (a : ℝ) ^ 2 := sq_pos_of_pos haPos
  have hthreePos : (0 : ℝ) < 3 :=
    Nat.cast_pos.mpr (Nat.succ_pos 2)
  have hnatThreeFive : (3 : ℕ) < 5 := by
    have hraw : (3 : ℕ) < 3 + 2 :=
      Nat.lt_add_of_pos_right (Nat.succ_pos 1)
    exact Eq.subst (motive := fun value : ℕ => 3 < value) rfl hraw
  have hthreeFive : (3 : ℝ) < 5 := Nat.cast_lt.mpr hnatThreeFive
  have honeFiveThirds : (1 : ℝ) < 5 / 3 :=
    (lt_div_iff₀ hthreePos).mpr
      (Eq.subst (motive := fun value : ℝ => value < 5)
        (one_mul (3 : ℝ)).symm hthreeFive)
  have hcoefficient : (1 : ℝ) < 96 / 49 := by
    exact lt_trans honeFiveThirds
      Real.five_thirds_lt_ninety_six_forty_ninths
  have hscaled := mul_lt_mul_of_pos_right hcoefficient haSqPos
  have hscaledNormalized :
      (a : ℝ) ^ 2 < (96 / 49 : ℝ) * (a : ℝ) ^ 2 :=
    Eq.subst
      (motive := fun value : ℝ => value < (96 / 49 : ℝ) * (a : ℝ) ^ 2)
      (one_mul ((a : ℝ) ^ 2)) hscaled
  have hnormalize := Real.six_mul_four_sevenths_square (a : ℝ)
  exact Eq.subst (motive := fun value : ℝ => _ < value)
    hnormalize.symm hscaledNormalized

theorem Complex.logarithmicPhaseFiniteLeftNear_angular_width
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ *
        (Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) -
          Complex.logarithmicPhaseFiniteLeftNearCenterLower t (a : ℤ)) <
      (2 * Real.pi) *
        (Complex.logarithmicPhaseFiniteLeftNearCenterLower t (a : ℤ)) ^ 2 := by
  have hnumerator :=
    Complex.logarithmicPhaseFiniteLeftNear_scaled_width_le_a_mul_scale_sub_one
      t (a : ℤ)
  have haSquare := Real.a_mul_scale_sub_one_lt_a_sq hgeometry
  have hfourSquare := Real.one_mul_a_sq_lt_six_mul_four_sevenths_a_sq
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hlower :=
    Complex.logarithmicPhaseFiniteLeftNearCenterLower_ge_four_sevenths_a
      t ht a
  have hfourNonneg : 0 ≤ (4 / 7 : ℝ) * (a : ℝ) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg 4) (Nat.cast_nonneg 7))
      (Nat.cast_nonneg a)
  have hlowerNonneg := le_trans hfourNonneg hlower
  have hsquare := Real.square_le_square_of_nonneg hfourNonneg hlower
  have hsixSquare := mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg 6)
  have hpiSquare := mul_lt_mul_of_pos_right Real.six_lt_two_mul_pi
    (sq_pos_of_pos
      (Complex.logarithmicPhaseFiniteLeftNearCenterLower_pos
        t (a : ℤ)
        (Int.ofNat_le.mpr
          (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))))
  exact lt_of_le_of_lt hnumerator
    (lt_trans haSquare
      (lt_trans hfourSquare
        (lt_of_le_of_lt hsixSquare hpiSquare)))

theorem Real.b_mul_scale_add_one_lt_two_b_sq
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (b : ℝ) * (Complex.logarithmicPhaseBProcessScale t + 1) <
      2 * (b : ℝ) ^ 2 := by
  have hbPos : 0 < (b : ℝ) := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one
      (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry))
  have hscale := Real.logarithmicPhaseLongBranchGeometry_sqrt_lt_b hgeometry
  have honeB : (1 : ℝ) ≤ (b : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ (b : ℝ))
      Nat.cast_one
      (Nat.cast_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry))
  have hadd : Complex.logarithmicPhaseBProcessScale t + 1 <
      (b : ℝ) + (b : ℝ) :=
    add_lt_add_of_lt_of_le hscale honeB
  have hmul := mul_lt_mul_of_pos_left hadd hbPos
  have hnormalize :
      (b : ℝ) * ((b : ℝ) + (b : ℝ)) =
        2 * (b : ℝ) ^ 2 := by
    exact Eq.trans (mul_add _ _ _)
      (Eq.trans
        (congrArg₂ (fun left right : ℝ => left + right)
          (pow_two (b : ℝ)).symm (pow_two (b : ℝ)).symm)
        (two_mul ((b : ℝ) ^ 2)).symm)
  exact lt_of_lt_of_eq hmul hnormalize

theorem Complex.logarithmicPhaseFiniteRightNear_angular_width
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ *
        (Complex.logarithmicPhaseFiniteRightNearCenterUpper t (b : ℤ) -
          ((b : ℝ) + 2 / 3)) <
      (2 * Real.pi) * (((b : ℝ) + 2 / 3) ^ 2) := by
  have hnumerator :=
    Complex.logarithmicPhaseFiniteRightNear_scaled_width_le_b_mul_scale_add_one
      t ht (b : ℤ)
  have hbSquare := Real.b_mul_scale_add_one_lt_two_b_sq hgeometry
  have hbPos : 0 < (b : ℝ) := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one
      (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry))
  have hbLe : (b : ℝ) ≤ (b : ℝ) + 2 / 3 :=
    le_add_of_nonneg_right
      (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
  have hsquare := Real.square_le_square_of_nonneg hbPos.le hbLe
  have htwoSquare := mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg 2)
  have hcoefficient : (2 : ℝ) < 2 * Real.pi := by
    have htwoSix : (2 : ℝ) < 6 :=
      Nat.cast_lt.mpr (Nat.lt_add_of_pos_right (Nat.succ_pos 3))
    exact lt_trans htwoSix Real.two_mul_pi_ge_six
  have hpiSquare := mul_lt_mul_of_pos_right hcoefficient
    (sq_pos_of_pos (lt_of_lt_of_le hbPos hbLe))
  exact lt_of_le_of_lt hnumerator
    (lt_trans hbSquare (lt_of_le_of_lt htwoSquare hpiSquare))

theorem Complex.logarithmicPhaseFiniteLeftNear_center_bounds_order
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteLeftNearCenterLower t (a : ℤ) ≤
      Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) := by
  have haTwo := Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry
  have haPos : 0 < (a : ℝ) := Nat.cast_pos.mpr
    (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)
  have hscale := Real.longGeometry_scale_lt_a hgeometry
  have hadd := add_lt_add_right hscale 1
  have htwoThirds := mul_lt_mul_of_pos_left hadd Real.two_thirds_pos
  have haReal : (2 : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr haTwo
  have hmargin : (2 / 3 : ℝ) * ((a : ℝ) + 1) ≤ (a : ℝ) := by
    have hthreeA : 2 * ((a : ℝ) + 1) ≤ 3 * (a : ℝ) := by
      have hbase : 2 * (a : ℝ) + 2 ≤ 2 * (a : ℝ) + (a : ℝ) :=
        add_le_add_left haReal (2 * (a : ℝ))
      have hleft :
          (2 : ℝ) * ((a : ℝ) + 1) = 2 * (a : ℝ) + 2 :=
        Eq.trans (mul_add 2 (a : ℝ) 1)
          (congrArg (fun value : ℝ => 2 * (a : ℝ) + value)
            (mul_one 2))
      have hthree : (3 : ℝ) = 2 + 1 :=
        Real.two_add_one_eq_three.symm
      have hright :
          (3 : ℝ) * (a : ℝ) = 2 * (a : ℝ) + (a : ℝ) :=
        Eq.trans
          (congrArg (fun value : ℝ => value * (a : ℝ)) hthree)
          (Eq.trans (add_mul 2 1 (a : ℝ))
            (congrArg (fun value : ℝ => 2 * (a : ℝ) + value)
              (one_mul (a : ℝ))))
      exact Eq.subst (motive := fun value : ℝ => value ≤ _)
        hleft.symm
        (Eq.subst (motive := fun value : ℝ => _ ≤ value)
          hright.symm hbase)
    have hthreePos : (0 : ℝ) < 3 :=
      Nat.cast_pos.mpr (Nat.succ_pos 2)
    have hrightOrder : (3 : ℝ) * (a : ℝ) = (a : ℝ) * 3 :=
      mul_comm 3 (a : ℝ)
    have hdiv : (2 * ((a : ℝ) + 1)) / 3 ≤ (a : ℝ) :=
      (div_le_iff₀ hthreePos).mpr
        (Eq.subst (motive := fun value : ℝ => _ ≤ value)
          hrightOrder hthreeA)
    have hquotient :
        (2 / 3 : ℝ) * ((a : ℝ) + 1) =
          (2 * ((a : ℝ) + 1)) / 3 :=
      div_mul_eq_mul_div 2 3 ((a : ℝ) + 1)
    exact Eq.subst (motive := fun value : ℝ => value ≤ (a : ℝ))
      hquotient.symm hdiv
  have htarget :
      (2 / 3 : ℝ) *
          (Complex.logarithmicPhaseBProcessScale t + 1) ≤ (a : ℝ) :=
    le_trans htwoThirds.le hmargin
  unfold Complex.logarithmicPhaseFiniteLeftNearCenterLower
  unfold Real.integerBlockCutoffSupportLeftEndpoint
  have hdenom := Complex.logarithmicPhaseBProcessScale_add_one_pos t
  have hresidual :
      0 ≤ (a : ℝ) -
        (2 / 3) * (Complex.logarithmicPhaseBProcessScale t + 1) :=
    sub_nonneg.mpr htarget
  have hbase :
      (a : ℝ) * Complex.logarithmicPhaseBProcessScale t ≤
        (a : ℝ) * Complex.logarithmicPhaseBProcessScale t +
          ((a : ℝ) -
            (2 / 3) * (Complex.logarithmicPhaseBProcessScale t + 1)) :=
    le_add_of_nonneg_right hresidual
  have hexpand :
      ((a : ℝ) - 2 / 3) *
          (Complex.logarithmicPhaseBProcessScale t + 1) =
        (a : ℝ) * Complex.logarithmicPhaseBProcessScale t +
          ((a : ℝ) -
            (2 / 3) * (Complex.logarithmicPhaseBProcessScale t + 1)) := by
    calc
      ((a : ℝ) - 2 / 3) *
          (Complex.logarithmicPhaseBProcessScale t + 1) =
          (a : ℝ) * (Complex.logarithmicPhaseBProcessScale t + 1) -
            (2 / 3) *
              (Complex.logarithmicPhaseBProcessScale t + 1) :=
        sub_mul _ _ _
      _ = ((a : ℝ) * Complex.logarithmicPhaseBProcessScale t +
            (a : ℝ)) -
            (2 / 3) *
              (Complex.logarithmicPhaseBProcessScale t + 1) :=
        congrArg
          (fun value : ℝ =>
            value - (2 / 3) *
              (Complex.logarithmicPhaseBProcessScale t + 1))
          (Eq.trans
            (mul_add (a : ℝ)
              (Complex.logarithmicPhaseBProcessScale t) 1)
            (congrArg
              (fun value : ℝ =>
                (a : ℝ) * Complex.logarithmicPhaseBProcessScale t + value)
              (mul_one (a : ℝ))))
      _ = (a : ℝ) * Complex.logarithmicPhaseBProcessScale t +
          ((a : ℝ) -
            (2 / 3) * (Complex.logarithmicPhaseBProcessScale t + 1)) :=
        add_sub_assoc _ _ _
  exact (div_le_iff₀ hdenom).mpr
    (Eq.subst (motive := fun value : ℝ => _ ≤ value)
      hexpand.symm hbase)

theorem Complex.logarithmicPhaseFiniteRightNear_center_bounds_order
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (b : ℝ) + 2 / 3 ≤
      Complex.logarithmicPhaseFiniteRightNearCenterUpper t (b : ℤ) := by
  have hbPos : 0 < (b : ℝ) := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one
      (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry))
  have hscale := Real.logarithmicPhaseLongBranchGeometry_sqrt_lt_b hgeometry
  have hsub : Complex.logarithmicPhaseBProcessScale t - 1 < (b : ℝ) :=
    lt_trans (sub_lt_self _ zero_lt_one) hscale
  have hthird : (2 / 3 : ℝ) *
      (Complex.logarithmicPhaseBProcessScale t - 1) ≤ (b : ℝ) :=
    le_trans
      (mul_le_mul_of_nonneg_left hsub.le
        (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3)))
      (le_trans
        (mul_le_mul_of_nonneg_right
          (show (2 / 3 : ℝ) ≤ 1 from
            (div_le_one₀ (Nat.cast_pos.mpr (Nat.succ_pos 2))).mpr
              (Nat.cast_le.mpr (Nat.le_succ 2)))
          hbPos.le)
        (le_of_eq (one_mul (b : ℝ))))
  unfold Complex.logarithmicPhaseFiniteRightNearCenterUpper
  have hsubPos := Complex.logarithmicPhaseBProcessScale_sub_one_pos t ht
  have hbase :
      (b : ℝ) * (Complex.logarithmicPhaseBProcessScale t - 1) +
          (2 / 3) * (Complex.logarithmicPhaseBProcessScale t - 1) ≤
        (b : ℝ) * (Complex.logarithmicPhaseBProcessScale t - 1) +
          (b : ℝ) :=
    add_le_add_left hthird
      ((b : ℝ) * (Complex.logarithmicPhaseBProcessScale t - 1))
  have hleftExpand :
      ((b : ℝ) + 2 / 3) *
          (Complex.logarithmicPhaseBProcessScale t - 1) =
        (b : ℝ) * (Complex.logarithmicPhaseBProcessScale t - 1) +
          (2 / 3) * (Complex.logarithmicPhaseBProcessScale t - 1) :=
    add_mul _ _ _
  have hrightExpand :
      (b : ℝ) * (Complex.logarithmicPhaseBProcessScale t - 1) +
          (b : ℝ) =
        (b : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    calc
      (b : ℝ) * (Complex.logarithmicPhaseBProcessScale t - 1) +
          (b : ℝ) =
          ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t -
            (b : ℝ) * 1) + (b : ℝ) :=
        congrArg (fun value : ℝ => value + (b : ℝ))
          (mul_sub (b : ℝ)
            (Complex.logarithmicPhaseBProcessScale t) 1)
      _ = ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t -
            (b : ℝ)) + (b : ℝ) :=
        congrArg
          (fun value : ℝ =>
            ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t - value) +
              (b : ℝ))
          (mul_one (b : ℝ))
      _ = (b : ℝ) * Complex.logarithmicPhaseBProcessScale t :=
        sub_add_cancel _ _
  exact (le_div_iff₀ hsubPos).mpr
    (Eq.subst (motive := fun value : ℝ => value ≤ _)
      hleftExpand.symm
      (Eq.subst (motive := fun value : ℝ => _ ≤ value)
        hrightExpand hbase))

theorem Complex.logarithmicPhaseFiniteLeftNear_card_le_one
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhaseFiniteLeftNearEndpointModes
      t (a : ℤ) (b : ℤ)).card ≤ 1 := by
  have ha := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  exact Complex.integerModeFamily_card_le_one_of_center_bounds
    t (Complex.logarithmicPhaseFiniteLeftNearEndpointModes
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhaseFiniteLeftNearCenterLower_pos t (a : ℤ) ha)
    (Complex.logarithmicPhaseFiniteLeftNear_center_bounds_order hgeometry)
    (Complex.logarithmicPhaseFiniteLeftNear_angular_width ht hgeometry)
    (fun m hm => by
      have hbounds :=
        Complex.logarithmicPhaseFiniteLeftNear_negModeCast_bounds
          t ht (a : ℤ) (b : ℤ) ha
          (Int.ofNat_le.mpr
            (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)) hm
      have hleft :
          Complex.logarithmicPhaseCenterFrequencyCoordinate t
              (Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) ≤
            -(m : ℝ) := by
        unfold Complex.logarithmicPhaseCenterFrequencyCoordinate
        exact hbounds.1.le
      have hright :
          -(m : ℝ) ≤
            Complex.logarithmicPhaseCenterFrequencyCoordinate t
              (Complex.logarithmicPhaseFiniteLeftNearCenterLower
                t (a : ℤ)) := by
        unfold Complex.logarithmicPhaseCenterFrequencyCoordinate
        exact hbounds.2
      exact And.intro hleft hright)

theorem Complex.logarithmicPhaseFiniteRightNear_card_le_one
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhaseFiniteRightNearEndpointModes
      t (a : ℤ) (b : ℤ)).card ≤ 1 := by
  have ha := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hab := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  exact Complex.integerModeFamily_card_le_one_of_center_bounds
    t (Complex.logarithmicPhaseFiniteRightNearEndpointModes
      t (a : ℤ) (b : ℤ))
    (add_pos
      (Nat.cast_pos.mpr
        (lt_of_lt_of_le Nat.zero_lt_one
          (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry)))
      (div_pos
        (Nat.cast_pos.mpr (Nat.succ_pos 1))
        (Nat.cast_pos.mpr (Nat.succ_pos 2))))
    (Complex.logarithmicPhaseFiniteRightNear_center_bounds_order ht hgeometry)
    (Complex.logarithmicPhaseFiniteRightNear_angular_width ht hgeometry)
    (fun m hm => by
      have hbounds :=
        Complex.logarithmicPhaseFiniteRightNear_negModeCast_bounds
          t ht (a : ℤ) (b : ℤ) ha hab hm
      have hleft :
          Complex.logarithmicPhaseCenterFrequencyCoordinate t
              (Complex.logarithmicPhaseFiniteRightNearCenterUpper
                t (b : ℤ)) ≤
            -(m : ℝ) := by
        unfold Complex.logarithmicPhaseCenterFrequencyCoordinate
        exact hbounds.1
      have hright :
          -(m : ℝ) ≤
            Complex.logarithmicPhaseCenterFrequencyCoordinate t
              ((b : ℝ) + 2 / 3) := by
        unfold Complex.logarithmicPhaseCenterFrequencyCoordinate
        exact hbounds.2.le
      exact And.intro hleft hright)

end

end LFunctions
end Boundary
