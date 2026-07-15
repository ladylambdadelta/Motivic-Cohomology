import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicEndpointNonemptyGeometry

/-!
# Unconditional complete-active dichotomy

If the interior family is nonempty, the sharp frequency-cardinality closure
gives `64*S`.  If it is empty, the interior budget vanishes.  The endpoint
family is then either empty as well, or an endpoint mode gives `b <= 4*norm t`;
the two-mode endpoint packing estimate yields `54*S`.  Thus `64*S` holds in
all cases.
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

theorem Real.endpointNonempty_blockRight_div_scale_le_four_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessEndpointModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    (b : ℝ) / Complex.logarithmicPhaseBProcessScale t ≤
      4 * Complex.logarithmicPhaseBProcessScale t := by
  have hbNorm :=
    Complex.logarithmicPhaseBProcess_natBlockRight_le_four_norm_of_endpoint_nonempty
      ht hgeometry hnonempty
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have hdivision := div_le_div_of_nonneg_right hbNorm hscalePos.le
  have hnormScale :=
    Complex.logarithmicPhaseBProcess_norm_div_scale_le_scale t
  have hscaled := mul_le_mul_of_nonneg_left hnormScale (Nat.cast_nonneg 4)
  have hnormalize :
      (4 * ‖t‖) / Complex.logarithmicPhaseBProcessScale t =
        4 * (‖t‖ / Complex.logarithmicPhaseBProcessScale t) :=
    mul_div_assoc 4 ‖t‖ _
  exact le_trans hdivision
    (Eq.subst (motive := fun value : ℝ => value ≤ _)
      hnormalize.symm hscaled)

theorem Real.endpointNonempty_supportRight_div_scale_le_fourteen_thirds_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessEndpointModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
        Complex.logarithmicPhaseBProcessScale t ≤
      (14 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hb := Real.endpointNonempty_blockRight_div_scale_le_four_scale
    ht hgeometry hnonempty
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have hmargin :
      (2 / 3 : ℝ) / Complex.logarithmicPhaseBProcessScale t ≤
        (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    have hfirst :
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
    have hsecond : (2 / 3 : ℝ) ≤
        (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
      have hone := Complex.logarithmicPhaseBProcessScale_one_le t
      have hmul := mul_le_mul_of_nonneg_left hone
        (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
      exact Eq.subst (motive := fun value : ℝ => value ≤ _)
        (mul_one (2 / 3 : ℝ)) hmul
    exact le_trans hfirst hsecond
  unfold Complex.logarithmicPhaseBProcessEndpointSupportRight
  have hsplit := add_div (b : ℝ) (2 / 3)
    (Complex.logarithmicPhaseBProcessScale t)
  have hadd := add_le_add hb hmargin
  have hnormalize :
      4 * Complex.logarithmicPhaseBProcessScale t +
          (2 / 3) * Complex.logarithmicPhaseBProcessScale t =
        (14 / 3) * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.trans (add_mul 4 (2 / 3) _).symm
      (congrArg
        (fun coefficient : ℝ => coefficient *
          Complex.logarithmicPhaseBProcessScale t)
        (show (4 : ℝ) + 2 / 3 = 14 / 3 from by
          have hthreeNe : (3 : ℝ) ≠ 0 :=
            ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
          have hfourProduct : (4 : ℝ) * 3 = 12 :=
            realOfNat_mul_eq_of_nat_eq 4 3 12 rfl
          have hfour : (4 : ℝ) = 12 / 3 :=
            (eq_div_iff hthreeNe).mpr hfourProduct
          have hsum : (12 / 3 : ℝ) + 2 / 3 = (12 + 2) / 3 :=
            div_add_div_same 12 2 3
          have hnumerator : (12 : ℝ) + 2 = 14 :=
            realOfNat_add_eq_of_nat_eq 12 2 14 rfl
          exact Eq.trans
            (congrArg (fun value : ℝ => value + 2 / 3) hfour)
            (Eq.trans hsum
              (congrArg (fun value : ℝ => value / 3) hnumerator))))
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hsplit.symm (le_trans hadd (le_of_eq hnormalize))

theorem Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant_le_twenty_seven_scale_of_endpoint_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessEndpointModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant
        t (b : ℤ) ≤
      27 * Complex.logarithmicPhaseBProcessScale t := by
  let S := Complex.logarithmicPhaseBProcessScale t
  have hcrossing : (4 / 3 : ℝ) ≤ (4 / 3) * S := by
    have hone := Complex.logarithmicPhaseBProcessScale_one_le t
    have hmul := mul_le_mul_of_nonneg_left hone
      (div_nonneg (Nat.cast_nonneg 4) (Nat.cast_nonneg 3))
    exact Eq.subst (motive := fun value : ℝ => value ≤ _)
      (mul_one (4 / 3 : ℝ)) hmul
  have htailBase :=
    Real.endpointNonempty_blockRight_mul_scale_div_norm_le_four_scale
      ht hgeometry hnonempty
  have htwoNonneg : (0 : ℝ) ≤ 2 := Nat.cast_nonneg 2
  have htail := mul_le_mul_of_nonneg_left htailBase htwoNonneg
  have htailNormalize : 2 * (4 * S) = 8 * S := by
    have hproduct : (2 : ℝ) * 4 = 8 :=
      realOfNat_mul_eq_of_nat_eq 2 4 8 rfl
    exact Eq.trans (mul_assoc 2 4 S).symm
      (congrArg (fun value : ℝ => value * S) hproduct)
  have htailFinal := le_trans htail (le_of_eq htailNormalize)
  have hcentralBase :=
    Real.endpointNonempty_supportRight_div_scale_le_fourteen_thirds_scale
      ht hgeometry hnonempty
  have hcentral := mul_le_mul_of_nonneg_left hcentralBase htwoNonneg
  have hcentralNormalize :
      2 * ((14 / 3) * S) = (28 / 3) * S := by
    exact Eq.trans (mul_assoc 2 (14 / 3) S).symm
      (congrArg (fun coefficient : ℝ => coefficient * S)
        (show (2 : ℝ) * (14 / 3) = 28 / 3 from by
          have hproduct : (2 : ℝ) * 14 = 28 :=
            realOfNat_mul_eq_of_nat_eq 2 14 28 rfl
          exact Eq.trans (mul_div_assoc (2 : ℝ) 14 3).symm
            (congrArg (fun value : ℝ => value / 3) hproduct)))
  have hcentralFinal := le_trans hcentral (le_of_eq hcentralNormalize)
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant
  have hcombined := add_le_add
    (add_le_add (add_le_add hcrossing htailFinal) hcentralFinal) htailFinal
  have hweighted :
      (4 / 3) * S + 8 * S + (28 / 3) * S + 8 * S =
        (80 / 3) * S := by
    have hfactor := Real.four_weighted_terms_eq_sum_coeff_mul
      (4 / 3) 8 (28 / 3) 8 S
    exact hfactor.trans
      (congrArg (fun coefficient : ℝ => coefficient * S)
        (show (4 / 3 : ℝ) + 8 + 28 / 3 + 8 = 80 / 3 from by
          have hthreeNe : (3 : ℝ) ≠ 0 :=
            ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
          have heightProduct : (8 : ℝ) * 3 = 24 :=
            realOfNat_mul_eq_of_nat_eq 8 3 24 rfl
          have height : (8 : ℝ) = 24 / 3 :=
            (eq_div_iff hthreeNe).mpr heightProduct
          have hreplace :
              (4 / 3 : ℝ) + 8 + 28 / 3 + 8 =
                4 / 3 + 24 / 3 + 28 / 3 + 24 / 3 :=
            congrArg (fun value : ℝ => 4 / 3 + value + 28 / 3 + value)
              height
          have hfirst : (4 / 3 : ℝ) + 24 / 3 = (4 + 24) / 3 :=
            div_add_div_same 4 24 3
          have hsecond : ((4 + 24 : ℝ) / 3) + 28 / 3 =
              ((4 + 24) + 28) / 3 :=
            div_add_div_same (4 + 24) 28 3
          have hthird : (((4 + 24 : ℝ) + 28) / 3) + 24 / 3 =
              (((4 + 24) + 28) + 24) / 3 :=
            div_add_div_same ((4 + 24 : ℝ) + 28) 24 3
          have hfourTwentyFour : (4 : ℝ) + 24 = 28 :=
            realOfNat_add_eq_of_nat_eq 4 24 28 rfl
          have htwentyEightTwentyEight : (28 : ℝ) + 28 = 56 :=
            realOfNat_add_eq_of_nat_eq 28 28 56 rfl
          have hfiftySixTwentyFour : (56 : ℝ) + 24 = 80 :=
            realOfNat_add_eq_of_nat_eq 56 24 80 rfl
          have hnumerator : ((4 + 24 : ℝ) + 28) + 24 = 80 :=
            Eq.trans
              (congrArg (fun value : ℝ => value + 28 + 24) hfourTwentyFour)
              (Eq.trans
                (congrArg (fun value : ℝ => value + 24)
                  htwentyEightTwentyEight)
                hfiftySixTwentyFour)
          exact Eq.trans hreplace
            (Eq.trans
              (congrArg (fun value : ℝ => value + 28 / 3 + 24 / 3) hfirst)
              (Eq.trans
                (congrArg (fun value : ℝ => value + 24 / 3) hsecond)
                (Eq.trans hthird
                  (congrArg (fun value : ℝ => value / 3) hnumerator))))))
  have hcoefficient : (80 / 3 : ℝ) ≤ 27 := by
    have hthreePos : (0 : ℝ) < 3 :=
      Nat.cast_pos.mpr (Nat.succ_pos 2)
    have hproduct : (27 : ℝ) * 3 = 81 :=
      realOfNat_mul_eq_of_nat_eq 27 3 81 rfl
    have hbound : (80 : ℝ) ≤ 81 := Nat.cast_le.mpr (Nat.le_succ 80)
    exact (div_le_iff₀ hthreePos).mpr
      (Eq.subst (motive := fun value : ℝ => 80 ≤ value)
        hproduct.symm hbound)
  have henlarge := mul_le_mul_of_nonneg_right hcoefficient
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  exact le_trans hcombined (le_trans (le_of_eq hweighted) henlarge)

theorem Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_fifty_four_scale_of_endpoint_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessEndpointModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget
        t (a : ℤ) (b : ℤ) ≤
      54 * Complex.logarithmicPhaseBProcessScale t := by
  have hcard :=
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_two_perModeMajorant
      ht hgeometry
  have hpoint :=
    Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant_le_twenty_seven_scale_of_endpoint_nonempty
      ht hgeometry hnonempty
  have hscaled := mul_le_mul_of_nonneg_left hpoint (Nat.cast_nonneg 2)
  have hnormalize :
      2 * (27 * Complex.logarithmicPhaseBProcessScale t) =
        54 * Complex.logarithmicPhaseBProcessScale t := by
    have hproduct : (2 : ℝ) * 27 = 54 :=
      realOfNat_mul_eq_of_nat_eq 2 27 54 rfl
    exact Eq.trans (mul_assoc 2 27 _).symm
      (congrArg
        (fun value : ℝ =>
          value * Complex.logarithmicPhaseBProcessScale t)
        hproduct)
  exact le_trans hcard (le_trans hscaled (le_of_eq hnormalize))

theorem Complex.logarithmicPhaseBProcessCompleteActiveBudget_le_fifty_four_scale_of_interior_empty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hempty :
      Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ) = ∅) :
    Complex.logarithmicPhaseBProcessCompleteActiveBudget
        t (a : ℤ) (b : ℤ) ≤
      54 * Complex.logarithmicPhaseBProcessScale t := by
  have hinterior :=
    Complex.logarithmicPhaseBProcessInteriorBudget_eq_zero_of_empty
      t (a : ℤ) (b : ℤ) hempty
  have hendpointCases :=
    (Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)).eq_empty_or_nonempty
  have hendpoint :
      Complex.logarithmicPhaseBProcessUniversalEndpointBudget
          t (a : ℤ) (b : ℤ) ≤
        54 * Complex.logarithmicPhaseBProcessScale t := by
    match hendpointCases with
    | Or.inl hzero =>
        have hbudgetZero :=
          Complex.logarithmicPhaseBProcessEndpointBudget_eq_zero_of_empty
            t (a : ℤ) (b : ℤ) hzero
        exact Eq.subst (motive := fun value : ℝ => value ≤ _)
          hbudgetZero.symm
          (mul_nonneg (Nat.cast_nonneg 54)
            (Complex.logarithmicPhaseBProcessScale_nonneg t))
    | Or.inr hnonempty =>
        exact
          Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_fifty_four_scale_of_endpoint_nonempty
            ht hgeometry hnonempty
  unfold Complex.logarithmicPhaseBProcessCompleteActiveBudget
  exact Eq.subst (motive := fun value : ℝ => value + _ ≤ _)
    hinterior.symm
    (Eq.subst (motive := fun value : ℝ => value ≤ _)
      (zero_add _).symm hendpoint)

theorem Complex.logarithmicPhaseBProcessCompleteActiveBudget_le_sixty_four_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessCompleteActiveBudget
        t (a : ℤ) (b : ℤ) ≤
      64 * Complex.logarithmicPhaseBProcessScale t := by
  have hcases :=
    Complex.logarithmicPhasePoissonBProcessInteriorModes_empty_or_nonempty
      t (a : ℤ) (b : ℤ)
  match hcases with
  | Or.inl hempty =>
      have hfiftyFour :=
        Complex.logarithmicPhaseBProcessCompleteActiveBudget_le_fifty_four_scale_of_interior_empty
          ht hgeometry hempty
      have hcoefficient : (54 : ℝ) ≤ 64 :=
        Nat.cast_le.mpr (show (54 : ℕ) ≤ 64 from by
          exact Eq.subst (motive := fun value : ℕ => 54 ≤ value)
            (show 54 + 10 = 64 from rfl)
            (Nat.le_add_right 54 10))
      have henlarge := mul_le_mul_of_nonneg_right hcoefficient
        (Complex.logarithmicPhaseBProcessScale_nonneg t)
      exact le_trans hfiftyFour henlarge
  | Or.inr hnonempty =>
      exact
        Complex.logarithmicPhaseBProcessCompleteActiveBudget_le_sixty_four_scale_of_interior_nonempty
          ht hgeometry hnonempty

end

end LFunctions
end Boundary
