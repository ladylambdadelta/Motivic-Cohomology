import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveSharpenedNumerics

/-!
# Exact active-family closure

The side-specific active proof previously rounded `32/3` to `11` and `56/3`
to `19`.  This owner retains those rational constants and closes the active
dichotomy at `(166/3)*S`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem two_mul_eight_thirds_eq_sixteen_thirds :
    (2 : ℝ) * (8 / 3) = 16 / 3 :=
  Eq.trans (mul_div_assoc' 2 8 3)
    (congrArg (fun numerator : ℝ => numerator / 3)
      (realOfNat_mul_eq_of_nat_eq 2 8 16 rfl))

private theorem two_mul_fourteen_thirds_eq_twenty_eight_thirds :
    (2 : ℝ) * (14 / 3) = 28 / 3 :=
  Eq.trans (mul_div_assoc' 2 14 3)
    (congrArg (fun numerator : ℝ => numerator / 3)
      (realOfNat_mul_eq_of_nat_eq 2 14 28 rfl))

private theorem four_thirds_add_sixteen_thirds_add_four_eq_thirty_two_thirds :
    (4 / 3 : ℝ) + 16 / 3 + 4 = 32 / 3 := by
  have hthree : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have hfirst : (4 / 3 : ℝ) + 16 / 3 = (4 + 16) / 3 :=
    div_add_div_same 4 16 3
  have hwhole : ((4 + 16 : ℝ) / 3) + 4 =
      ((4 + 16) + 4 * 3) / 3 :=
    div_add' (4 + 16) 4 3 hthree
  have hfourAddSixteen : (4 : ℝ) + 16 = 20 :=
    realOfNat_add_eq_of_nat_eq 4 16 20 rfl
  have hfourMulThree : (4 : ℝ) * 3 = 12 :=
    realOfNat_mul_eq_of_nat_eq 4 3 12 rfl
  have htwentyAddTwelve : (20 : ℝ) + 12 = 32 :=
    realOfNat_add_eq_of_nat_eq 20 12 32 rfl
  have hnumerator : (4 + 16 : ℝ) + 4 * 3 = 32 :=
    Eq.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        hfourAddSixteen hfourMulThree)
      htwentyAddTwelve
  exact Eq.trans
    (congrArg (fun value : ℝ => value + 4) hfirst)
    (Eq.trans hwhole
      (congrArg (fun numerator : ℝ => numerator / 3) hnumerator))

private theorem four_thirds_add_twenty_eight_thirds_add_eight_eq_fifty_six_thirds :
    (4 / 3 : ℝ) + 28 / 3 + 8 = 56 / 3 := by
  have hthree : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have hfirst : (4 / 3 : ℝ) + 28 / 3 = (4 + 28) / 3 :=
    div_add_div_same 4 28 3
  have hwhole : ((4 + 28 : ℝ) / 3) + 8 =
      ((4 + 28) + 8 * 3) / 3 :=
    div_add' (4 + 28) 8 3 hthree
  have hfourAddTwentyEight : (4 : ℝ) + 28 = 32 :=
    realOfNat_add_eq_of_nat_eq 4 28 32 rfl
  have heightMulThree : (8 : ℝ) * 3 = 24 :=
    realOfNat_mul_eq_of_nat_eq 8 3 24 rfl
  have hthirtyTwoAddTwentyFour : (32 : ℝ) + 24 = 56 :=
    realOfNat_add_eq_of_nat_eq 32 24 56 rfl
  have hnumerator : (4 + 28 : ℝ) + 8 * 3 = 56 :=
    Eq.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        hfourAddTwentyEight heightMulThree)
      hthirtyTwoAddTwentyFour
  exact Eq.trans
    (congrArg (fun value : ℝ => value + 8) hfirst)
    (Eq.trans hwhole
      (congrArg (fun numerator : ℝ => numerator / 3) hnumerator))

private theorem two_mul_thirty_two_thirds_eq_sixty_four_thirds :
    (2 : ℝ) * (32 / 3) = 64 / 3 :=
  Eq.trans (mul_div_assoc' 2 32 3)
    (congrArg (fun numerator : ℝ => numerator / 3)
      (realOfNat_mul_eq_of_nat_eq 2 32 64 rfl))

private theorem two_mul_fifty_six_thirds_eq_one_hundred_twelve_thirds :
    (2 : ℝ) * (56 / 3) = 112 / 3 :=
  Eq.trans (mul_div_assoc' 2 56 3)
    (congrArg (fun numerator : ℝ => numerator / 3)
      (realOfNat_mul_eq_of_nat_eq 2 56 112 rfl))

private theorem thirty_four_add_sixty_four_thirds_eq_one_hundred_sixty_six_thirds :
    (34 : ℝ) + 64 / 3 = 166 / 3 := by
  have hthree : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have hfraction : (34 : ℝ) + 64 / 3 = (34 * 3 + 64) / 3 :=
    add_div' 64 34 3 hthree
  have hthirtyFourMulThree : (34 : ℝ) * 3 = 102 :=
    realOfNat_mul_eq_of_nat_eq 34 3 102 rfl
  have honeHundredTwoAddSixtyFour : (102 : ℝ) + 64 = 166 :=
    realOfNat_add_eq_of_nat_eq 102 64 166 rfl
  have hnumerator : (34 : ℝ) * 3 + 64 = 166 :=
    Eq.trans
      (congrArg (fun value : ℝ => value + 64) hthirtyFourMulThree)
      honeHundredTwoAddSixtyFour
  exact hfraction.trans
    (congrArg (fun numerator : ℝ => numerator / 3) hnumerator)

theorem Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant_le_thirty_two_thirds_scale_of_interior_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant
        t (b : ℤ) ≤
      (32 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  let S := Complex.logarithmicPhaseBProcessScale t
  have hcrossing : (4 / 3 : ℝ) ≤ (4 / 3) * S := by
    have hone := Complex.logarithmicPhaseBProcessScale_one_le t
    have hmul := mul_le_mul_of_nonneg_left hone
      (div_nonneg (Nat.cast_nonneg 4) (Nat.cast_nonneg 3))
    exact Eq.subst (motive := fun value : ℝ => value ≤ _)
      (mul_one (4 / 3 : ℝ)) hmul
  have hcentralBase :=
    Real.longGeometry_endpointSupportRight_div_scale_le_eight_thirds_scale
      ht hgeometry hnonempty
  have hcentral := mul_le_mul_of_nonneg_left hcentralBase (Nat.cast_nonneg 2)
  have hcentralNormalize : 2 * ((8 / 3) * S) = (16 / 3) * S := by
    exact Eq.trans (mul_assoc 2 (8 / 3) S).symm
      (congrArg (fun coefficient : ℝ => coefficient * S)
        two_mul_eight_thirds_eq_sixteen_thirds)
  have htailBase :=
    Real.longGeometry_blockRight_mul_scale_div_norm_le_two_mul_scale_of_nonempty
      ht hgeometry hnonempty
  have htail := mul_le_mul_of_nonneg_left htailBase (Nat.cast_nonneg 2)
  have htailNormalize : 2 * (2 * S) = 4 * S := by
    exact Eq.trans (mul_assoc 2 2 S).symm
      (congrArg (fun coefficient : ℝ => coefficient * S)
        (realOfNat_mul_eq_of_nat_eq 2 2 4 rfl))
  unfold Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant
  have hcombined := add_le_add
    (add_le_add hcrossing (le_trans hcentral (le_of_eq hcentralNormalize)))
    (le_trans htail (le_of_eq htailNormalize))
  have hfactor :
      (4 / 3 : ℝ) * S + (16 / 3) * S + 4 * S =
        ((4 / 3 : ℝ) + 16 / 3 + 4) * S := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value + 4 * S)
        (add_mul (4 / 3 : ℝ) (16 / 3) S).symm)
      (add_mul ((4 / 3 : ℝ) + 16 / 3) 4 S).symm
  exact le_trans hcombined
    (le_of_eq (hfactor.trans
      (congrArg (fun coefficient : ℝ => coefficient * S)
        four_thirds_add_sixteen_thirds_add_four_eq_thirty_two_thirds)))

theorem Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant_le_fifty_six_thirds_scale_of_endpoint_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessEndpointModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant
        t (b : ℤ) ≤
      (56 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  let S := Complex.logarithmicPhaseBProcessScale t
  have hcrossing : (4 / 3 : ℝ) ≤ (4 / 3) * S := by
    have hone := Complex.logarithmicPhaseBProcessScale_one_le t
    have hmul := mul_le_mul_of_nonneg_left hone
      (div_nonneg (Nat.cast_nonneg 4) (Nat.cast_nonneg 3))
    exact Eq.subst (motive := fun value : ℝ => value ≤ _)
      (mul_one (4 / 3 : ℝ)) hmul
  have hcentralBase :=
    Real.endpointNonempty_supportRight_div_scale_le_fourteen_thirds_scale
      ht hgeometry hnonempty
  have hcentral := mul_le_mul_of_nonneg_left hcentralBase (Nat.cast_nonneg 2)
  have hcentralNormalize : 2 * ((14 / 3) * S) = (28 / 3) * S := by
    exact Eq.trans (mul_assoc 2 (14 / 3) S).symm
      (congrArg (fun coefficient : ℝ => coefficient * S)
        two_mul_fourteen_thirds_eq_twenty_eight_thirds)
  have htailBase :=
    Real.endpointNonempty_blockRight_mul_scale_div_norm_le_four_scale
      ht hgeometry hnonempty
  have htail := mul_le_mul_of_nonneg_left htailBase (Nat.cast_nonneg 2)
  have htailNormalize : 2 * (4 * S) = 8 * S := by
    exact Eq.trans (mul_assoc 2 4 S).symm
      (congrArg (fun coefficient : ℝ => coefficient * S)
        Real.two_mul_four_eq_eight)
  unfold Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant
  have hcombined := add_le_add
    (add_le_add hcrossing (le_trans hcentral (le_of_eq hcentralNormalize)))
    (le_trans htail (le_of_eq htailNormalize))
  have hfactor :
      (4 / 3 : ℝ) * S + (28 / 3) * S + 8 * S =
        ((4 / 3 : ℝ) + 28 / 3 + 8) * S := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value + 8 * S)
        (add_mul (4 / 3 : ℝ) (28 / 3) S).symm)
      (add_mul ((4 / 3 : ℝ) + 28 / 3) 8 S).symm
  exact le_trans hcombined
    (le_of_eq (hfactor.trans
      (congrArg (fun coefficient : ℝ => coefficient * S)
        four_thirds_add_twenty_eight_thirds_add_eight_eq_fifty_six_thirds)))

theorem Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_sixty_four_thirds_scale_of_interior_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget
        t (a : ℤ) (b : ℤ) ≤
      (64 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hcard :=
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_two_sideMajorant
      ht hgeometry
  have hper :=
    Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant_le_thirty_two_thirds_scale_of_interior_nonempty
      ht hgeometry hnonempty
  have htwo := mul_le_mul_of_nonneg_left hper (Nat.cast_nonneg 2)
  have hnormalize :
      2 * ((32 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t) =
        (64 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.trans (mul_assoc 2 (32 / 3 : ℝ) _).symm
      (congrArg
        (fun coefficient : ℝ => coefficient *
          Complex.logarithmicPhaseBProcessScale t)
        two_mul_thirty_two_thirds_eq_sixty_four_thirds)
  exact le_trans hcard (le_trans htwo (le_of_eq hnormalize))

theorem Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_one_hundred_twelve_thirds_scale_of_endpoint_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessEndpointModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget
        t (a : ℤ) (b : ℤ) ≤
      (112 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hcard :=
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_two_sideMajorant
      ht hgeometry
  have hper :=
    Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant_le_fifty_six_thirds_scale_of_endpoint_nonempty
      ht hgeometry hnonempty
  have htwo := mul_le_mul_of_nonneg_left hper (Nat.cast_nonneg 2)
  have hnormalize :
      2 * ((56 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t) =
        (112 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.trans (mul_assoc 2 (56 / 3 : ℝ) _).symm
      (congrArg
        (fun coefficient : ℝ => coefficient *
          Complex.logarithmicPhaseBProcessScale t)
        two_mul_fifty_six_thirds_eq_one_hundred_twelve_thirds)
  exact le_trans hcard (le_trans htwo (le_of_eq hnormalize))

theorem Complex.logarithmicPhaseBProcessCompleteActiveBudget_le_one_hundred_sixty_six_thirds_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessCompleteActiveBudget
        t (a : ℤ) (b : ℤ) ≤
      (166 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  match
    Complex.logarithmicPhasePoissonBProcessInteriorModes_empty_or_nonempty
      t (a : ℤ) (b : ℤ) with
  | Or.inl hinteriorEmpty =>
      have hinteriorZero :=
        Complex.logarithmicPhaseBProcessInteriorBudget_eq_zero_of_empty
          t (a : ℤ) (b : ℤ) hinteriorEmpty
      have hendpoint :
          Complex.logarithmicPhaseBProcessUniversalEndpointBudget
              t (a : ℤ) (b : ℤ) ≤
            (112 / 3 : ℝ) *
              Complex.logarithmicPhaseBProcessScale t := by
        match
          (Complex.logarithmicPhasePoissonBProcessEndpointModes
            t (a : ℤ) (b : ℤ)).eq_empty_or_nonempty with
        | Or.inl hendpointEmpty =>
            have hzero :=
              Complex.logarithmicPhaseBProcessEndpointBudget_eq_zero_of_empty
                t (a : ℤ) (b : ℤ) hendpointEmpty
            exact Eq.subst (motive := fun value : ℝ => value ≤ _)
              hzero.symm
              (mul_nonneg
                (div_nonneg (Nat.cast_nonneg 112) (Nat.cast_nonneg 3))
                (Complex.logarithmicPhaseBProcessScale_nonneg t))
        | Or.inr hendpointNonempty =>
            exact
              Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_one_hundred_twelve_thirds_scale_of_endpoint_nonempty
                ht hgeometry hendpointNonempty
      unfold Complex.logarithmicPhaseBProcessCompleteActiveBudget
      have hcoefficient : (112 / 3 : ℝ) ≤ 166 / 3 :=
        have hnat : (112 : ℕ) ≤ 166 :=
          Eq.subst (motive := fun value : ℕ => 112 ≤ value)
            (show 112 + 54 = 166 from rfl)
            (Nat.le_add_right 112 54)
        div_le_div_of_nonneg_right (Nat.cast_le.mpr hnat)
          (Nat.cast_nonneg 3)
      have henlarge := mul_le_mul_of_nonneg_right hcoefficient
        (Complex.logarithmicPhaseBProcessScale_nonneg t)
      exact Eq.subst (motive := fun value : ℝ => value + _ ≤ _)
        hinteriorZero.symm
        (Eq.subst (motive := fun value : ℝ => value ≤ _)
          (zero_add _).symm (le_trans hendpoint henlarge))
  | Or.inr hinteriorNonempty =>
      have hinteriorClosed :=
        Complex.logarithmicPhaseBProcessInteriorBudget_le_closedMajorant
          t ht (a : ℤ) (b : ℤ)
          (Int.ofNat_le.mpr
            (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
          (Int.ofNat_zero_le b)
      have hinterior := le_trans hinteriorClosed
        (Complex.logarithmicPhaseBProcessClosedInteriorMajorant_le_thirty_four_scale_of_nonempty
          ht hgeometry hinteriorNonempty)
      have hendpoint :=
        Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_sixty_four_thirds_scale_of_interior_nonempty
          ht hgeometry hinteriorNonempty
      unfold Complex.logarithmicPhaseBProcessCompleteActiveBudget
      have hsum := add_le_add hinterior hendpoint
      exact le_trans hsum
        (le_of_eq
          (Eq.trans
            (add_mul 34 (64 / 3 : ℝ)
              (Complex.logarithmicPhaseBProcessScale t)).symm
            (congrArg
              (fun coefficient : ℝ => coefficient *
                Complex.logarithmicPhaseBProcessScale t)
              thirty_four_add_sixty_four_thirds_eq_one_hundred_sixty_six_thirds)))

end

end LFunctions
end Boundary
