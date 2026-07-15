import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicSideSpecificEndpointBudget

/-!
# Side-specific complete active closure

Removing the impossible outward tail from each endpoint packet lowers the
endpoint-family coefficient to `22` when the interior family is nonempty and
to `38` in the endpoint-only branch.  Together with the sharp `34` interior
coefficient, the complete active family is bounded unconditionally by `56*S`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant_le_eleven_scale_of_interior_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant
        t (b : ℤ) ≤
      11 * Complex.logarithmicPhaseBProcessScale t := by
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
    have htwoEight : (2 : ℝ) * 8 = 16 :=
      Real.endpoint_nat_cast_mul 2 8 16 rfl
    have hcoefficient : (2 : ℝ) * (8 / 3) = 16 / 3 :=
      Eq.trans (mul_div_assoc (2 : ℝ) 8 3).symm
        (congrArg (fun numerator : ℝ => numerator / 3) htwoEight)
    exact Eq.trans (mul_assoc 2 (8 / 3) S).symm
      (congrArg (fun coefficient : ℝ => coefficient * S) hcoefficient)
  have hcentralFinal := le_trans hcentral (le_of_eq hcentralNormalize)
  have htailBase :=
    Real.longGeometry_blockRight_mul_scale_div_norm_le_two_mul_scale_of_nonempty
      ht hgeometry hnonempty
  have htail := mul_le_mul_of_nonneg_left htailBase (Nat.cast_nonneg 2)
  have htailNormalize : 2 * (2 * S) = 4 * S := by
    have htwoTwo : (2 : ℝ) * 2 = 4 :=
      Real.endpoint_nat_cast_mul 2 2 4 rfl
    exact Eq.trans (mul_assoc 2 2 S).symm
      (congrArg (fun coefficient : ℝ => coefficient * S) htwoTwo)
  have htailFinal := le_trans htail (le_of_eq htailNormalize)
  unfold Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant
  have hcombined := add_le_add (add_le_add hcrossing hcentralFinal) htailFinal
  have hweighted :
      (4 / 3) * S + (16 / 3) * S + 4 * S = (32 / 3) * S := by
    have hfactor := Real.three_weighted_terms_eq_sum_coeff_mul
      (4 / 3) (16 / 3) 4 S
    have hfirst : (4 / 3 : ℝ) + 16 / 3 = 20 / 3 :=
      Eq.trans (div_add_div_same 4 16 3)
        (congrArg (fun numerator : ℝ => numerator / 3)
          (Real.endpoint_nat_cast_add 4 16 20 rfl))
    have hfourTimesThree : (4 : ℝ) * 3 = 12 :=
      Real.endpoint_nat_cast_mul 4 3 12 rfl
    have hfour : (4 : ℝ) = 12 / 3 :=
      (eq_div_iff (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2)))).mpr
        hfourTimesThree
    have hsecond : (20 / 3 : ℝ) + 12 / 3 = 32 / 3 :=
      Eq.trans (div_add_div_same 20 12 3)
        (congrArg (fun numerator : ℝ => numerator / 3)
          (Real.endpoint_nat_cast_add 20 12 32 rfl))
    have hcoefficient : (4 / 3 : ℝ) + 16 / 3 + 4 = 32 / 3 :=
      Eq.trans (congrArg (fun value : ℝ => value + 4) hfirst)
        (Eq.trans
          (congrArg (fun value : ℝ => 20 / 3 + value) hfour)
          hsecond)
    exact hfactor.trans
      (congrArg (fun coefficient : ℝ => coefficient * S)
        hcoefficient)
  have hcoefficient : (32 / 3 : ℝ) ≤ 11 := by
    have hproduct : (11 : ℝ) * 3 = 33 :=
      Real.endpoint_nat_cast_mul 11 3 33 rfl
    have hcast : (32 : ℝ) ≤ 33 :=
      Nat.cast_le.mpr (Nat.le_succ 32)
    exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos 2))).mpr
      (hcast.trans_eq hproduct.symm)
  have henlarge := mul_le_mul_of_nonneg_right hcoefficient
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  exact le_trans hcombined (le_trans (le_of_eq hweighted) henlarge)

theorem Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant_le_nineteen_scale_of_endpoint_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessEndpointModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant
        t (b : ℤ) ≤
      19 * Complex.logarithmicPhaseBProcessScale t := by
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
    have htwoFourteen : (2 : ℝ) * 14 = 28 :=
      Real.endpoint_nat_cast_mul 2 14 28 rfl
    have hcoefficient : (2 : ℝ) * (14 / 3) = 28 / 3 :=
      Eq.trans (mul_div_assoc (2 : ℝ) 14 3).symm
        (congrArg (fun numerator : ℝ => numerator / 3) htwoFourteen)
    exact Eq.trans (mul_assoc 2 (14 / 3) S).symm
      (congrArg (fun coefficient : ℝ => coefficient * S) hcoefficient)
  have hcentralFinal := le_trans hcentral (le_of_eq hcentralNormalize)
  have htailBase :=
    Real.endpointNonempty_blockRight_mul_scale_div_norm_le_four_scale
      ht hgeometry hnonempty
  have htail := mul_le_mul_of_nonneg_left htailBase (Nat.cast_nonneg 2)
  have htailNormalize : 2 * (4 * S) = 8 * S := by
    have htwoFour : (2 : ℝ) * 4 = 8 :=
      Real.endpoint_nat_cast_mul 2 4 8 rfl
    exact Eq.trans (mul_assoc 2 4 S).symm
      (congrArg (fun coefficient : ℝ => coefficient * S) htwoFour)
  have htailFinal := le_trans htail (le_of_eq htailNormalize)
  unfold Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant
  have hcombined := add_le_add (add_le_add hcrossing hcentralFinal) htailFinal
  have hweighted :
      (4 / 3) * S + (28 / 3) * S + 8 * S = (56 / 3) * S := by
    have hfactor := Real.three_weighted_terms_eq_sum_coeff_mul
      (4 / 3) (28 / 3) 8 S
    have hfirst : (4 / 3 : ℝ) + 28 / 3 = 32 / 3 :=
      Eq.trans (div_add_div_same 4 28 3)
        (congrArg (fun numerator : ℝ => numerator / 3)
          (Real.endpoint_nat_cast_add 4 28 32 rfl))
    have heightTimesThree : (8 : ℝ) * 3 = 24 :=
      Real.endpoint_nat_cast_mul 8 3 24 rfl
    have height : (8 : ℝ) = 24 / 3 :=
      (eq_div_iff (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2)))).mpr
        heightTimesThree
    have hsecond : (32 / 3 : ℝ) + 24 / 3 = 56 / 3 :=
      Eq.trans (div_add_div_same 32 24 3)
        (congrArg (fun numerator : ℝ => numerator / 3)
          (Real.endpoint_nat_cast_add 32 24 56 rfl))
    have hcoefficient : (4 / 3 : ℝ) + 28 / 3 + 8 = 56 / 3 :=
      Eq.trans (congrArg (fun value : ℝ => value + 8) hfirst)
        (Eq.trans
          (congrArg (fun value : ℝ => 32 / 3 + value) height)
          hsecond)
    exact hfactor.trans
      (congrArg (fun coefficient : ℝ => coefficient * S)
        hcoefficient)
  have hcoefficient : (56 / 3 : ℝ) ≤ 19 := by
    have hproduct : (19 : ℝ) * 3 = 57 :=
      Real.endpoint_nat_cast_mul 19 3 57 rfl
    have hcast : (56 : ℝ) ≤ 57 :=
      Nat.cast_le.mpr (Nat.le_succ 56)
    exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos 2))).mpr
      (hcast.trans_eq hproduct.symm)
  have henlarge := mul_le_mul_of_nonneg_right hcoefficient
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  exact le_trans hcombined (le_trans (le_of_eq hweighted) henlarge)

theorem Complex.logarithmicPhaseBProcessCompleteActiveBudget_le_fifty_six_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessCompleteActiveBudget
        t (a : ℤ) (b : ℤ) ≤
      56 * Complex.logarithmicPhaseBProcessScale t := by
  have hinteriorCases :=
    Complex.logarithmicPhasePoissonBProcessInteriorModes_empty_or_nonempty
      t (a : ℤ) (b : ℤ)
  match hinteriorCases with
  | Or.inl hempty =>
      have hinteriorZero :=
        Complex.logarithmicPhaseBProcessInteriorBudget_eq_zero_of_empty
          t (a : ℤ) (b : ℤ) hempty
      have hendpointCases :=
        (Complex.logarithmicPhasePoissonBProcessEndpointModes
          t (a : ℤ) (b : ℤ)).eq_empty_or_nonempty
      have hendpoint :
          Complex.logarithmicPhaseBProcessUniversalEndpointBudget
              t (a : ℤ) (b : ℤ) ≤
            38 * Complex.logarithmicPhaseBProcessScale t := by
        match hendpointCases with
        | Or.inl hzero =>
            have hbudgetZero :=
              Complex.logarithmicPhaseBProcessEndpointBudget_eq_zero_of_empty
                t (a : ℤ) (b : ℤ) hzero
            exact Eq.subst (motive := fun value : ℝ => value ≤ _)
              hbudgetZero.symm
              (mul_nonneg (Nat.cast_nonneg 38)
                (Complex.logarithmicPhaseBProcessScale_nonneg t))
        | Or.inr hnonempty =>
            have hcard :=
              Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_two_sideMajorant
                ht hgeometry
            have hpoint :=
              Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant_le_nineteen_scale_of_endpoint_nonempty
                ht hgeometry hnonempty
            have hscaled := mul_le_mul_of_nonneg_left hpoint (Nat.cast_nonneg 2)
            have htwoNineteen : (2 : ℝ) * 19 = 38 :=
              Real.endpoint_nat_cast_mul 2 19 38 rfl
            have hnormalize :
                (2 : ℝ) * (19 * Complex.logarithmicPhaseBProcessScale t) =
                  38 * Complex.logarithmicPhaseBProcessScale t :=
              Eq.trans (mul_assoc 2 19 _).symm
                (congrArg
                  (fun coefficient : ℝ => coefficient *
                    Complex.logarithmicPhaseBProcessScale t)
                  htwoNineteen)
            exact le_trans hcard
              (le_trans hscaled
                (le_of_eq hnormalize))
      unfold Complex.logarithmicPhaseBProcessCompleteActiveBudget
      have hthirtyEight : 38 * Complex.logarithmicPhaseBProcessScale t ≤
          56 * Complex.logarithmicPhaseBProcessScale t :=
        have hsum : (38 : ℝ) + 18 = 56 :=
          Real.endpoint_nat_cast_add 38 18 56 rfl
        have hcoefficient : (38 : ℝ) ≤ 56 :=
          (le_add_of_nonneg_right (Nat.cast_nonneg 18)).trans_eq hsum
        mul_le_mul_of_nonneg_right hcoefficient
          (Complex.logarithmicPhaseBProcessScale_nonneg t)
      have hzeroEndpoint :
          0 + Complex.logarithmicPhaseBProcessUniversalEndpointBudget
              t (a : ℤ) (b : ℤ) ≤
            56 * Complex.logarithmicPhaseBProcessScale t := by
        have hendpointFinal := le_trans hendpoint hthirtyEight
        exact Eq.subst
          (motive := fun value : ℝ =>
            value ≤ 56 * Complex.logarithmicPhaseBProcessScale t)
          (zero_add
            (Complex.logarithmicPhaseBProcessUniversalEndpointBudget
              t (a : ℤ) (b : ℤ))).symm
          hendpointFinal
      exact Eq.subst (motive := fun value : ℝ => value + _ ≤ _)
        hinteriorZero.symm hzeroEndpoint
  | Or.inr hnonempty =>
      have hinteriorClosed :=
        Complex.logarithmicPhaseBProcessInteriorBudget_le_closedMajorant
          t ht (a : ℤ) (b : ℤ)
          (Int.ofNat_le.mpr
            (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
          (Int.ofNat_zero_le b)
      have hinterior := le_trans hinteriorClosed
        (Complex.logarithmicPhaseBProcessClosedInteriorMajorant_le_thirty_four_scale_of_nonempty
          ht hgeometry hnonempty)
      have hendpointCard :=
        Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_two_sideMajorant
          ht hgeometry
      have hendpointPoint :=
        Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant_le_eleven_scale_of_interior_nonempty
          ht hgeometry hnonempty
      have hendpointScaled :=
        mul_le_mul_of_nonneg_left hendpointPoint (Nat.cast_nonneg 2)
      have htwoEleven : (2 : ℝ) * 11 = 22 :=
        Real.endpoint_nat_cast_mul 2 11 22 rfl
      have hendpointNormalize :
          (2 : ℝ) * (11 * Complex.logarithmicPhaseBProcessScale t) =
            22 * Complex.logarithmicPhaseBProcessScale t :=
        Eq.trans (mul_assoc 2 11 _).symm
          (congrArg
            (fun coefficient : ℝ => coefficient *
              Complex.logarithmicPhaseBProcessScale t)
            htwoEleven)
      have hendpoint :
          Complex.logarithmicPhaseBProcessUniversalEndpointBudget
              t (a : ℤ) (b : ℤ) ≤
            22 * Complex.logarithmicPhaseBProcessScale t :=
        le_trans hendpointCard
          (le_trans hendpointScaled
            (le_of_eq hendpointNormalize))
      unfold Complex.logarithmicPhaseBProcessCompleteActiveBudget
      have hsum := add_le_add hinterior hendpoint
      have hthirtyFourAddTwentyTwo : (34 : ℝ) + 22 = 56 :=
        Real.endpoint_nat_cast_add 34 22 56 rfl
      have hnormalize :
          (34 + 22 : ℝ) * Complex.logarithmicPhaseBProcessScale t =
            56 * Complex.logarithmicPhaseBProcessScale t :=
        congrArg
          (fun coefficient : ℝ => coefficient *
            Complex.logarithmicPhaseBProcessScale t)
          hthirtyFourAddTwentyTwo
      exact le_trans hsum
        (le_of_eq ((add_mul 34 22 _).symm.trans hnormalize))

end

end LFunctions
end Boundary
