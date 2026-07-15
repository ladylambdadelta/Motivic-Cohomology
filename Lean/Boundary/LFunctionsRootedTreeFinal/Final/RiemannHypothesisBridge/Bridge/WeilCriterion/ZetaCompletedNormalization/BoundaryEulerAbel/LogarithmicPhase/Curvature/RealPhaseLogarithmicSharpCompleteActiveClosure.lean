import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicBProcessSharpFrequencyClosure
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicEndpointAngularCompletion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicCompleteActiveBudget

/-!
# Sharp complete active-family closure

The sharpened interior estimate is combined with the proved two-mode endpoint
packing theorem.  Endpoint terms are normalized directly against the refined
B-process scale, producing a complete active coefficient of `64`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun value : ℕ => (value : ℝ)) h)

private theorem realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun value : ℕ => (value : ℝ)) h)

theorem Real.longGeometry_endpointSupportRight_div_scale_le_eight_thirds_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
        Complex.logarithmicPhaseBProcessScale t ≤
      (8 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessEndpointSupportRight
  have hb :=
    Real.longGeometry_blockRight_div_scale_le_two_mul_scale_of_nonempty
      ht hgeometry hnonempty
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have hmargin :
      (2 / 3 : ℝ) / Complex.logarithmicPhaseBProcessScale t ≤ 2 / 3 := by
    have hone := Complex.logarithmicPhaseBProcessScale_one_le t
    have hmul := mul_le_mul_of_nonneg_left hone
      (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
    have htarget : (2 / 3 : ℝ) ≤
        (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t :=
      Eq.subst
        (motive := fun value : ℝ => value ≤
          (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t)
        (mul_one (2 / 3 : ℝ)) hmul
    exact (div_le_iff₀ hscalePos).mpr htarget
  have hmarginScale : (2 / 3 : ℝ) ≤
      (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    have hone := Complex.logarithmicPhaseBProcessScale_one_le t
    have hmul := mul_le_mul_of_nonneg_left hone
      (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
    exact Eq.subst (motive := fun value : ℝ => value ≤ _)
      (mul_one (2 / 3 : ℝ)) hmul
  have hsplit :
      ((b : ℝ) + 2 / 3) /
          Complex.logarithmicPhaseBProcessScale t =
        (b : ℝ) / Complex.logarithmicPhaseBProcessScale t +
          (2 / 3) / Complex.logarithmicPhaseBProcessScale t :=
    add_div _ _ _
  have hadd := add_le_add hb (le_trans hmargin hmarginScale)
  have hnormalize :
      2 * Complex.logarithmicPhaseBProcessScale t +
          (2 / 3) * Complex.logarithmicPhaseBProcessScale t =
        (8 / 3) * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.trans (add_mul 2 (2 / 3) _).symm
      (congrArg
        (fun coefficient : ℝ => coefficient *
          Complex.logarithmicPhaseBProcessScale t)
        (show (2 : ℝ) + 2 / 3 = 8 / 3 from by
          have hthreeNe : (3 : ℝ) ≠ 0 :=
            ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
          have htwoMulThree : (2 : ℝ) * 3 = 6 :=
            realOfNat_mul_eq_of_nat_eq 2 3 6 rfl
          have htwo : (2 : ℝ) = 6 / 3 :=
            (eq_div_iff hthreeNe).mpr htwoMulThree
          have hsum : (6 / 3 : ℝ) + 2 / 3 = (6 + 2) / 3 :=
            div_add_div_same 6 2 3
          have hnumerator : (6 : ℝ) + 2 = 8 :=
            realOfNat_add_eq_of_nat_eq 6 2 8 rfl
          exact Eq.trans
            (congrArg (fun value : ℝ => value + 2 / 3) htwo)
            (Eq.trans hsum
              (congrArg (fun value : ℝ => value / 3) hnumerator))))
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hsplit.symm (le_trans hadd (le_of_eq hnormalize))

theorem Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant_le_fifteen_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant
        t (b : ℤ) ≤
      15 * Complex.logarithmicPhaseBProcessScale t := by
  let S := Complex.logarithmicPhaseBProcessScale t
  have hcrossing : (4 / 3 : ℝ) ≤ (4 / 3) * S := by
    have hone := Complex.logarithmicPhaseBProcessScale_one_le t
    have hmul := mul_le_mul_of_nonneg_left hone
      (div_nonneg (Nat.cast_nonneg 4) (Nat.cast_nonneg 3))
    exact Eq.subst (motive := fun value : ℝ => value ≤ _)
      (mul_one (4 / 3 : ℝ)) hmul
  have htailBase :=
    Real.longGeometry_blockRight_mul_scale_div_norm_le_two_mul_scale_of_nonempty
      ht hgeometry hnonempty
  have htwoNonneg : (0 : ℝ) ≤ 2 := Nat.cast_nonneg 2
  have htail := mul_le_mul_of_nonneg_left htailBase htwoNonneg
  have htailNormalize : 2 * (2 * S) = 4 * S := by
    have htwoTwo : (2 : ℝ) * 2 = 4 :=
      realOfNat_mul_eq_of_nat_eq 2 2 4 rfl
    exact Eq.trans (mul_assoc 2 2 S).symm
      (congrArg (fun value : ℝ => value * S) htwoTwo)
  have htailFinal := le_trans htail (le_of_eq htailNormalize)
  have hcentralBase :=
    Real.longGeometry_endpointSupportRight_div_scale_le_eight_thirds_scale
      ht hgeometry hnonempty
  have hcentral := mul_le_mul_of_nonneg_left hcentralBase htwoNonneg
  have hcentralNormalize : 2 * ((8 / 3) * S) = (16 / 3) * S := by
    exact Eq.trans (mul_assoc 2 (8 / 3) S).symm
      (congrArg (fun coefficient : ℝ => coefficient * S)
        (show (2 : ℝ) * (8 / 3) = 16 / 3 from by
          have hproduct : (2 : ℝ) * 8 = 16 :=
            realOfNat_mul_eq_of_nat_eq 2 8 16 rfl
          exact Eq.trans (mul_div_assoc (2 : ℝ) 8 3).symm
            (congrArg (fun value : ℝ => value / 3) hproduct)))
  have hcentralFinal := le_trans hcentral (le_of_eq hcentralNormalize)
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant
  have hcombined := add_le_add
    (add_le_add (add_le_add hcrossing htailFinal) hcentralFinal) htailFinal
  have hweighted :
      (4 / 3) * S + 4 * S + (16 / 3) * S + 4 * S =
        (44 / 3) * S := by
    have hfactor := Real.four_weighted_terms_eq_sum_coeff_mul
      (4 / 3) 4 (16 / 3) 4 S
    exact hfactor.trans
      (congrArg (fun coefficient : ℝ => coefficient * S)
        (show (4 / 3 : ℝ) + 4 + 16 / 3 + 4 = 44 / 3 from by
          have hthreeNe : (3 : ℝ) ≠ 0 :=
            ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
          have hfourMulThree : (4 : ℝ) * 3 = 12 :=
            realOfNat_mul_eq_of_nat_eq 4 3 12 rfl
          have hfour : (4 : ℝ) = 12 / 3 :=
            (eq_div_iff hthreeNe).mpr hfourMulThree
          have hreplace :
              (4 / 3 : ℝ) + 4 + 16 / 3 + 4 =
                4 / 3 + 12 / 3 + 16 / 3 + 12 / 3 :=
            congrArg (fun value : ℝ => 4 / 3 + value + 16 / 3 + value)
              hfour
          have hfirst : (4 / 3 : ℝ) + 12 / 3 = (4 + 12) / 3 :=
            div_add_div_same 4 12 3
          have hsecond : ((4 + 12 : ℝ) / 3) + 16 / 3 =
              ((4 + 12) + 16) / 3 :=
            div_add_div_same (4 + 12) 16 3
          have hthird : (((4 + 12 : ℝ) + 16) / 3) + 12 / 3 =
              (((4 + 12) + 16) + 12) / 3 :=
            div_add_div_same ((4 + 12 : ℝ) + 16) 12 3
          have hfourTwelve : (4 : ℝ) + 12 = 16 :=
            realOfNat_add_eq_of_nat_eq 4 12 16 rfl
          have hsixteenSixteen : (16 : ℝ) + 16 = 32 :=
            realOfNat_add_eq_of_nat_eq 16 16 32 rfl
          have hthirtyTwoTwelve : (32 : ℝ) + 12 = 44 :=
            realOfNat_add_eq_of_nat_eq 32 12 44 rfl
          have hnumerator : ((4 + 12 : ℝ) + 16) + 12 = 44 :=
            Eq.trans
              (congrArg (fun value : ℝ => value + 16 + 12) hfourTwelve)
              (Eq.trans
                (congrArg (fun value : ℝ => value + 12) hsixteenSixteen)
                hthirtyTwoTwelve)
          exact Eq.trans hreplace
            (Eq.trans
              (congrArg (fun value : ℝ => value + 16 / 3 + 12 / 3) hfirst)
              (Eq.trans
                (congrArg (fun value : ℝ => value + 12 / 3) hsecond)
                (Eq.trans hthird
                  (congrArg (fun value : ℝ => value / 3) hnumerator))))))
  have hcoefficient : (44 / 3 : ℝ) ≤ 15 := by
    have hthreePos : (0 : ℝ) < 3 :=
      Nat.cast_pos.mpr (Nat.succ_pos 2)
    have hproduct : (15 : ℝ) * 3 = 45 :=
      realOfNat_mul_eq_of_nat_eq 15 3 45 rfl
    have hbound : (44 : ℝ) ≤ 45 :=
      Nat.cast_le.mpr (Nat.le_succ 44)
    exact (div_le_iff₀ hthreePos).mpr
      (Eq.subst (motive := fun value : ℝ => 44 ≤ value)
        hproduct.symm hbound)
  have henlarge := mul_le_mul_of_nonneg_right hcoefficient
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  exact le_trans hcombined (le_trans (le_of_eq hweighted) henlarge)

theorem Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_thirty_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget
        t (a : ℤ) (b : ℤ) ≤
      30 * Complex.logarithmicPhaseBProcessScale t := by
  have hcard :=
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_two_perModeMajorant
      ht hgeometry
  have hpoint :=
    Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant_le_fifteen_scale
      ht hgeometry hnonempty
  have hscaled := mul_le_mul_of_nonneg_left hpoint (Nat.cast_nonneg 2)
  have hnormalize :
      2 * (15 * Complex.logarithmicPhaseBProcessScale t) =
        30 * Complex.logarithmicPhaseBProcessScale t := by
    have hproduct : (2 : ℝ) * 15 = 30 :=
      realOfNat_mul_eq_of_nat_eq 2 15 30 rfl
    exact Eq.trans (mul_assoc 2 15 _).symm
      (congrArg
        (fun value : ℝ =>
          value * Complex.logarithmicPhaseBProcessScale t)
        hproduct)
  exact le_trans hcard (le_trans hscaled (le_of_eq hnormalize))

theorem Complex.logarithmicPhaseBProcessCompleteActiveBudget_le_sixty_four_scale_of_interior_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessCompleteActiveBudget
        t (a : ℤ) (b : ℤ) ≤
      64 * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessCompleteActiveBudget
  have hinterior :
      Complex.logarithmicPhaseBProcessInteriorBudget
          t (a : ℤ) (b : ℤ) ≤
        34 * Complex.logarithmicPhaseBProcessScale t := by
    have hclosed :=
      Complex.logarithmicPhaseBProcessInteriorBudget_le_closedMajorant
        t ht (a : ℤ) (b : ℤ)
        (Int.ofNat_le.mpr
          (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
        (Int.ofNat_zero_le b)
    exact le_trans hclosed
      (Complex.logarithmicPhaseBProcessClosedInteriorMajorant_le_thirty_four_scale_of_nonempty
        ht hgeometry hnonempty)
  have hendpoint :=
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_thirty_scale
      ht hgeometry hnonempty
  have hsum := add_le_add hinterior hendpoint
  have hnormalize :
      34 * Complex.logarithmicPhaseBProcessScale t +
          30 * Complex.logarithmicPhaseBProcessScale t =
        64 * Complex.logarithmicPhaseBProcessScale t := by
    have hsum : (34 : ℝ) + 30 = 64 :=
      realOfNat_add_eq_of_nat_eq 34 30 64 rfl
    exact Eq.trans (add_mul 34 30 _).symm
      (congrArg
        (fun value : ℝ =>
          value * Complex.logarithmicPhaseBProcessScale t)
        hsum)
  exact le_trans hsum (le_of_eq hnormalize)

end

end LFunctions
end Boundary
