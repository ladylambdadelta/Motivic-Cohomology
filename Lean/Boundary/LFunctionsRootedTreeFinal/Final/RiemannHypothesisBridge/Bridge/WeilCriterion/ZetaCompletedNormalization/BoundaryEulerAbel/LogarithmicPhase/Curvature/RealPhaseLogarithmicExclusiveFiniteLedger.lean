import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicLeftInactiveExclusiveBudget

/-!
# Sidewise finite-inactive ledger

The left near and left far classes are mutually exclusive.  This owner keeps
that fact visible through the complete finite-inactive assembly and charges the
right side independently.  The resulting coefficient is `121 / 18` instead of
`145 / 18`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteRightSharpBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget t a b +
    Complex.logarithmicPhaseFiniteRightFarCrossingBudget t a b +
      Complex.logarithmicPhaseFiniteRightFarReciprocalBudget t a b

theorem Real.three_term_left_association
    (x y z : ℝ) :
    x + y + z = x + (y + z) :=
  add_assoc x y z

theorem Real.six_term_side_reassociation
    (ln rn lc rc lr rr : ℝ) :
    (ln + rn) + (lc + rc) + (lr + rr) =
      (ln + lc + lr) + (rn + rc + rr) := by
  have hfirst :
      (ln + rn) + (lc + rc) = (ln + lc) + (rn + rc) :=
    add_add_add_comm ln rn lc rc
  have hsecond :
      ((ln + lc) + (rn + rc)) + (lr + rr) =
        ((ln + lc) + lr) + ((rn + rc) + rr) :=
    add_add_add_comm (ln + lc) (rn + rc) lr rr
  exact Eq.trans
    (congrArg (fun value : ℝ => value + (lr + rr)) hfirst)
    hsecond

theorem Complex.logarithmicPhaseFiniteInactiveSharpBudget_eq_sidewise
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteInactiveSharpBudget t a b =
      Complex.logarithmicPhaseFiniteLeftSharpBudget t a b +
        Complex.logarithmicPhaseFiniteRightSharpBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteInactiveSharpBudget
  unfold Complex.logarithmicPhaseFiniteNearQuantitativeBudget
  unfold Complex.logarithmicPhaseFiniteFarSeparatedBudget
  unfold Complex.logarithmicPhaseFiniteFarCrossingBudget
  unfold Complex.logarithmicPhaseFiniteFarReciprocalBudget
  unfold Complex.logarithmicPhaseFiniteLeftSharpBudget
  unfold Complex.logarithmicPhaseFiniteRightSharpBudget
  have hsourceAssociation :=
    (add_assoc
      (Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget t a b +
        Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget t a b)
      (Complex.logarithmicPhaseFiniteLeftFarCrossingBudget t a b +
        Complex.logarithmicPhaseFiniteRightFarCrossingBudget t a b)
      (Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget t a b +
        Complex.logarithmicPhaseFiniteRightFarReciprocalBudget t a b)).symm
  exact Eq.trans hsourceAssociation
    (Real.six_term_side_reassociation
      (Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget t a b)
      (Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget t a b)
      (Complex.logarithmicPhaseFiniteLeftFarCrossingBudget t a b)
      (Complex.logarithmicPhaseFiniteRightFarCrossingBudget t a b)
      (Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget t a b)
      (Complex.logarithmicPhaseFiniteRightFarReciprocalBudget t a b))

theorem Real.right_finite_coefficients_eq_forty_one_ninths
    (scale : ℝ) :
    (4 / 3 : ℝ) * scale + (8 / 9 : ℝ) * scale +
        (7 / 3 : ℝ) * scale =
      (41 / 9 : ℝ) * scale := by
  have hnineNonzero : (9 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 8))
  have hnineThree : (9 : ℝ) = 3 * 3 := by
    have hnat : (9 : ℕ) = 3 * 3 := rfl
    exact Eq.trans Nat.cast_ofNat.symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        (Nat.cast_mul 3 3))
  have hfourProduct : (4 : ℝ) * 3 = 12 := by
    have hnat : (4 * 3 : ℕ) = 12 := rfl
    exact Eq.trans (Nat.cast_mul 4 3).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hfour : (4 / 3 : ℝ) * 9 = 12 := by
    have hthreeNonzero : (3 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
    have hcancel : (4 / 3 : ℝ) * 3 = 4 :=
      div_mul_cancel₀ 4 hthreeNonzero
    exact Eq.trans
      (congrArg (fun value : ℝ => (4 / 3 : ℝ) * value) hnineThree)
      (Eq.trans
        (mul_assoc (4 / 3 : ℝ) 3 3).symm
        (Eq.trans (congrArg (fun value : ℝ => value * 3) hcancel)
          hfourProduct))
  have height : (8 / 9 : ℝ) * 9 = 8 :=
    div_mul_cancel₀ 8 hnineNonzero
  have hsevenProduct : (7 : ℝ) * 3 = 21 := by
    have hnat : (7 * 3 : ℕ) = 21 := rfl
    exact Eq.trans (Nat.cast_mul 7 3).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hseven : (7 / 3 : ℝ) * 9 = 21 := by
    have hthreeNonzero : (3 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
    have hcancel : (7 / 3 : ℝ) * 3 = 7 :=
      div_mul_cancel₀ 7 hthreeNonzero
    exact Eq.trans
      (congrArg (fun value : ℝ => (7 / 3 : ℝ) * value) hnineThree)
      (Eq.trans
        (mul_assoc (7 / 3 : ℝ) 3 3).symm
        (Eq.trans (congrArg (fun value : ℝ => value * 3) hcancel)
          hsevenProduct))
  have hfirstPair :
      ((4 / 3 : ℝ) + 8 / 9) * 9 =
        (4 / 3) * 9 + (8 / 9) * 9 :=
    add_mul (4 / 3) (8 / 9) 9
  have hdistributed :
      ((4 / 3 : ℝ) + 8 / 9 + 7 / 3) * 9 =
        (4 / 3) * 9 + (8 / 9) * 9 + (7 / 3) * 9 := by
    exact Eq.trans (add_mul ((4 / 3 : ℝ) + 8 / 9) (7 / 3) 9)
      (congrArg (fun value : ℝ => value + (7 / 3) * 9) hfirstPair)
  have hnormalized :
      (4 / 3 : ℝ) * 9 + (8 / 9) * 9 + (7 / 3) * 9 =
        (12 : ℝ) + 8 + 21 :=
    congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right) hfour height)
      hseven
  have hcastFirst : (12 : ℝ) + 8 = ((12 + 8 : ℕ) : ℝ) :=
    (Nat.cast_add 12 8).symm
  have hcastSum :
      (12 : ℝ) + 8 + 21 = ((12 + 8 + 21 : ℕ) : ℝ) := by
    exact Eq.trans (congrArg (fun value : ℝ => value + 21) hcastFirst)
      (Nat.cast_add (12 + 8) 21).symm
  have hnatSum : (12 + 8 + 21 : ℕ) = 41 := rfl
  have hsum : (12 : ℝ) + 8 + 21 = 41 := by
    exact Eq.trans hcastSum
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnatSum)
        Nat.cast_ofNat)
  have hcoefficient : (4 / 3 : ℝ) + 8 / 9 + 7 / 3 = 41 / 9 :=
    (eq_div_iff hnineNonzero).mpr
      (Eq.trans hdistributed (Eq.trans hnormalized hsum))
  have hfirst :
      (4 / 3 : ℝ) * scale + (8 / 9 : ℝ) * scale =
        ((4 / 3 : ℝ) + 8 / 9) * scale :=
    (add_mul (4 / 3 : ℝ) (8 / 9) scale).symm
  have hsecond :
      (((4 / 3 : ℝ) + 8 / 9) * scale) + (7 / 3 : ℝ) * scale =
        ((4 / 3 : ℝ) + 8 / 9 + 7 / 3) * scale :=
    (add_mul ((4 / 3 : ℝ) + 8 / 9) (7 / 3) scale).symm
  exact Eq.trans
    (congrArg (fun value : ℝ => value + (7 / 3 : ℝ) * scale) hfirst)
    (Eq.trans hsecond
      (congrArg (fun coefficient : ℝ => coefficient * scale) hcoefficient))

theorem Complex.logarithmicPhaseFiniteRightSharpBudget_le_forty_one_ninths_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteRightSharpBudget
        t (a : ℤ) (b : ℤ) ≤
      (41 / 9 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hnear :=
    Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget_le_four_thirds_scale
      ht hgeometry
  have hcrossing :=
    Complex.logarithmicPhaseFiniteRightFarCrossingBudget_le_eight_ninths_scale
      t ht a b hgeometry
  have hreciprocal :=
    Complex.logarithmicPhaseFiniteRightFarReciprocalBudget_le_seven_thirds_scale
      t ht a b hgeometry
  have hsum := add_le_add (add_le_add hnear hcrossing) hreciprocal
  unfold Complex.logarithmicPhaseFiniteRightSharpBudget
  exact le_trans hsum
    (le_of_eq
      (Real.right_finite_coefficients_eq_forty_one_ninths
        (Complex.logarithmicPhaseBProcessScale t)))

theorem Real.exclusive_finite_coefficients_eq_one_hundred_twenty_one_eighteenths
    (scale : ℝ) :
    (13 / 6 : ℝ) * scale + (41 / 9 : ℝ) * scale =
      (121 / 18 : ℝ) * scale := by
  have heighteenNonzero : (18 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 17))
  have heighteenSix : (18 : ℝ) = 6 * 3 := by
    have hnat : (18 : ℕ) = 6 * 3 := rfl
    exact Eq.trans Nat.cast_ofNat.symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        (Nat.cast_mul 6 3))
  have heighteenNine : (18 : ℝ) = 9 * 2 := by
    have hnat : (18 : ℕ) = 9 * 2 := rfl
    exact Eq.trans Nat.cast_ofNat.symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        (Nat.cast_mul 9 2))
  have hthirteenProduct : (13 : ℝ) * 3 = 39 := by
    have hnat : (13 * 3 : ℕ) = 39 := rfl
    exact Eq.trans (Nat.cast_mul 13 3).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hthirteen : (13 / 6 : ℝ) * 18 = 39 := by
    have hsixNonzero : (6 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 5))
    have hcancel : (13 / 6 : ℝ) * 6 = 13 :=
      div_mul_cancel₀ 13 hsixNonzero
    exact Eq.trans
      (congrArg (fun value : ℝ => (13 / 6 : ℝ) * value) heighteenSix)
      (Eq.trans
        (mul_assoc (13 / 6 : ℝ) 6 3).symm
        (Eq.trans (congrArg (fun value : ℝ => value * 3) hcancel)
          hthirteenProduct))
  have hfortyOneProduct : (41 : ℝ) * 2 = 82 := by
    have hnat : (41 * 2 : ℕ) = 82 := rfl
    exact Eq.trans (Nat.cast_mul 41 2).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hfortyOne : (41 / 9 : ℝ) * 18 = 82 := by
    have hnineNonzero : (9 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 8))
    have hcancel : (41 / 9 : ℝ) * 9 = 41 :=
      div_mul_cancel₀ 41 hnineNonzero
    exact Eq.trans
      (congrArg (fun value : ℝ => (41 / 9 : ℝ) * value) heighteenNine)
      (Eq.trans
        (mul_assoc (41 / 9 : ℝ) 9 2).symm
        (Eq.trans (congrArg (fun value : ℝ => value * 2) hcancel)
          hfortyOneProduct))
  have hdistributed :
      ((13 / 6 : ℝ) + 41 / 9) * 18 =
        (13 / 6) * 18 + (41 / 9) * 18 :=
    add_mul (13 / 6) (41 / 9) 18
  have hnormalized :
      (13 / 6 : ℝ) * 18 + (41 / 9) * 18 = (39 : ℝ) + 82 :=
    congrArg₂ (fun left right : ℝ => left + right) hthirteen hfortyOne
  have hsum : (39 : ℝ) + 82 = 121 := by
    have hnat : (39 + 82 : ℕ) = 121 := rfl
    exact Eq.trans (Nat.cast_add 39 82).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hcoefficient : (13 / 6 : ℝ) + 41 / 9 = 121 / 18 :=
    (eq_div_iff heighteenNonzero).mpr
      (Eq.trans hdistributed (Eq.trans hnormalized hsum))
  have hcollect :=
    (add_mul (13 / 6 : ℝ) (41 / 9) scale).symm
  exact Eq.trans hcollect
    (congrArg (fun coefficient : ℝ => coefficient * scale) hcoefficient)

theorem Complex.logarithmicPhaseFiniteInactiveSharpBudget_le_one_hundred_twenty_one_eighteenths_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteInactiveSharpBudget
        t (a : ℤ) (b : ℤ) ≤
      (121 / 18 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hleft :=
    Complex.logarithmicPhaseFiniteLeftSharpBudget_le_thirteen_sixths_scale
      t ht ht_nonneg a b hgeometry
  have hright :=
    Complex.logarithmicPhaseFiniteRightSharpBudget_le_forty_one_ninths_scale
      t ht ht_nonneg a b hgeometry
  have hsidewise :=
    Complex.logarithmicPhaseFiniteInactiveSharpBudget_eq_sidewise
      t (a : ℤ) (b : ℤ)
  have hsum := add_le_add hleft hright
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hsidewise.symm
    (le_trans hsum
      (le_of_eq
        (Real.exclusive_finite_coefficients_eq_one_hundred_twenty_one_eighteenths
          (Complex.logarithmicPhaseBProcessScale t))))

theorem Real.old_new_finite_coefficient_difference :
    (145 / 18 : ℝ) - 121 / 18 = 4 / 3 := by
  have hsubtract : (145 : ℝ) - 121 = 24 := by
    have hadd : (24 : ℝ) + 121 = 145 := by
      have hnat : (24 + 121 : ℕ) = 145 := rfl
      exact Eq.trans (Nat.cast_add 24 121).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          Nat.cast_ofNat)
    exact (eq_sub_of_add_eq hadd).symm
  have heighteenNonzero : (18 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 17))
  have hthreeNonzero : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have hcross : (24 : ℝ) * 3 = 4 * 18 := by
    have hnat : (24 * 3 : ℕ) = 4 * 18 := rfl
    exact Eq.trans (Nat.cast_mul 24 3).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        (Nat.cast_mul 4 18))
  have hfraction : (24 / 18 : ℝ) = 4 / 3 :=
    (div_eq_div_iff heighteenNonzero hthreeNonzero).mpr hcross
  exact Eq.trans (div_sub_div_same 145 121 18)
    (Eq.trans (congrArg (fun value : ℝ => value / 18) hsubtract)
      hfraction)

theorem Real.one_hundred_twenty_one_eighteenths_nonneg :
    (0 : ℝ) ≤ 121 / 18 :=
  div_nonneg (Nat.cast_nonneg 121) (Nat.cast_nonneg 18)

theorem Complex.logarithmicPhaseExclusiveFiniteMajorant_nonneg
    (t : ℝ) :
    0 ≤ (121 / 18 : ℝ) * Complex.logarithmicPhaseBProcessScale t :=
  mul_nonneg Real.one_hundred_twenty_one_eighteenths_nonneg
    (Complex.logarithmicPhaseBProcessScale_nonneg t)

theorem Complex.logarithmicPhaseExclusiveFiniteMajorant_le_old
    (t : ℝ) :
    (121 / 18 : ℝ) * Complex.logarithmicPhaseBProcessScale t ≤
      (145 / 18 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hdifferenceNonneg :
      (0 : ℝ) ≤ (145 / 18 : ℝ) - 121 / 18 :=
    Eq.subst (motive := fun value : ℝ => 0 ≤ value)
      Real.old_new_finite_coefficient_difference.symm
      (div_nonneg (Nat.cast_nonneg 4) (Nat.cast_nonneg 3))
  have hcoefficient : (121 / 18 : ℝ) ≤ 145 / 18 :=
    sub_nonneg.mp hdifferenceNonneg
  exact mul_le_mul_of_nonneg_right hcoefficient
    (Complex.logarithmicPhaseBProcessScale_nonneg t)

end

end LFunctions
end Boundary
