import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicPositiveTailArithmetic

/-!
# Arithmetic lower bounds for the far-negative residual

The floor frequency is chosen using the wider cutoff endpoint `a - 2/3`,
whereas the phase-adapted packet estimate starts at `a - 1/3`.  Their exact
reciprocal difference produces a deterministic residual of curvature size.
This owner isolates that difference and compares it to the left curvature and
third-derivative scales.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseWideSupportLeft (a : ℕ) : ℝ :=
  (a : ℝ) - 2 / 3

def Complex.logarithmicPhaseNarrowSupportLeft (a : ℕ) : ℝ :=
  (a : ℝ) - 1 / 3

def Complex.logarithmicPhaseSupportReciprocalResidual
    (t : ℝ) (a : ℕ) : ℝ :=
  ‖t‖ / Complex.logarithmicPhaseWideSupportLeft a -
    ‖t‖ / Complex.logarithmicPhaseNarrowSupportLeft a

theorem Complex.logarithmicPhaseWideSupportLeft_eq_integerEndpoint
    (a : ℕ) :
    Complex.logarithmicPhaseWideSupportLeft a =
      Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) := by
  rfl

theorem Complex.logarithmicPhaseNarrowSupportLeft_eq_quantitativeEndpoint
    (a : ℕ) :
    Complex.logarithmicPhaseNarrowSupportLeft a =
      Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) := by
  rfl

theorem Complex.logarithmicPhaseWideSupportLeft_pos
    (a : ℕ) (ha : 2 ≤ a) :
    0 < Complex.logarithmicPhaseWideSupportLeft a := by
  unfold Complex.logarithmicPhaseWideSupportLeft
  have haReal : (2 : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr ha
  have htwoThirdLtTwo : (2 : ℝ) / 3 < 2 := by
    have hthreePos : (0 : ℝ) < 3 :=
      Nat.cast_pos.mpr (Nat.zero_lt_succ 2)
    have htwoLtSix : (2 : ℝ) < 6 :=
      Nat.cast_lt.mpr (Nat.lt_add_of_pos_right (Nat.zero_lt_succ 3))
    have htwoMulThree : (2 : ℝ) * 3 = 6 :=
      Eq.trans (Nat.cast_mul 2 3).symm Nat.cast_ofNat
    exact (div_lt_iff₀ hthreePos).mpr
      (Eq.subst (motive := fun right : ℝ => (2 : ℝ) < right)
        htwoMulThree.symm htwoLtSix)
  exact sub_pos.mpr (lt_of_lt_of_le htwoThirdLtTwo haReal)

theorem Complex.logarithmicPhaseNarrowSupportLeft_pos
    (a : ℕ) (ha : 2 ≤ a) :
    0 < Complex.logarithmicPhaseNarrowSupportLeft a := by
  exact Eq.subst
    (Complex.logarithmicPhaseNarrowSupportLeft_eq_quantitativeEndpoint a).symm
    (Complex.quantitativeSupportLeft_pos_of_two_le a ha)

theorem Complex.logarithmicPhaseWideSupportLeft_lt_narrow
    (a : ℕ) :
    Complex.logarithmicPhaseWideSupportLeft a <
      Complex.logarithmicPhaseNarrowSupportLeft a := by
  unfold Complex.logarithmicPhaseWideSupportLeft
  unfold Complex.logarithmicPhaseNarrowSupportLeft
  have hthird : (1 : ℝ) / 3 < 2 / 3 := by
    have hthreePos : (0 : ℝ) < 3 :=
      Nat.cast_pos.mpr (Nat.zero_lt_succ 2)
    have honeLtTwo : (1 : ℝ) < 2 := one_lt_two
    exact (div_lt_div_iff_of_pos_right hthreePos).mpr honeLtTwo
  exact sub_lt_sub_left hthird (a : ℝ)

theorem Complex.logarithmicPhaseNarrow_sub_wide_eq_one_third
    (a : ℕ) :
    Complex.logarithmicPhaseNarrowSupportLeft a -
        Complex.logarithmicPhaseWideSupportLeft a =
      (1 : ℝ) / 3 := by
  unfold Complex.logarithmicPhaseWideSupportLeft
  unfold Complex.logarithmicPhaseNarrowSupportLeft
  have hcancel :
      ((a : ℝ) - 1 / 3) - ((a : ℝ) - 2 / 3) =
        2 / 3 - 1 / 3 := by
    have hcommute :=
      sub_sub_sub_comm (a : ℝ) (1 / 3 : ℝ) (a : ℝ) (2 / 3 : ℝ)
    have hself : (a : ℝ) - (a : ℝ) = 0 := sub_self (a : ℝ)
    have hselfTransport :
        ((a : ℝ) - (a : ℝ)) - ((1 : ℝ) / 3 - 2 / 3) =
          0 - ((1 : ℝ) / 3 - 2 / 3) :=
      congrArg (fun value : ℝ => value - ((1 : ℝ) / 3 - 2 / 3)) hself
    have hnegation :
        0 - ((1 : ℝ) / 3 - 2 / 3) = 2 / 3 - 1 / 3 :=
      Eq.trans (zero_sub ((1 : ℝ) / 3 - 2 / 3))
        (neg_sub ((1 : ℝ) / 3) (2 / 3))
    exact Eq.trans hcommute (Eq.trans hselfTransport hnegation)
  have hfraction : (2 : ℝ) / 3 - 1 / 3 = 1 / 3 := by
    exact Eq.trans (sub_div 2 1 3).symm
      (congrArg (fun numerator : ℝ => numerator / 3)
        (sub_eq_iff_eq_add.mpr (one_add_one_eq_two.symm)))
  exact Eq.trans hcancel hfraction

theorem Real.div_sub_div_eq_mul_sub_div_mul
    (T x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    T / x - T / y = T * (y - x) / (x * y) := by
  have hfractions := div_sub_div T T hx hy
  have hcommute :
      (T * y - x * T) / (x * y) =
        (T * y - T * x) / (x * y) :=
    congrArg (fun numerator : ℝ => numerator / (x * y))
      (congrArg (fun value : ℝ => T * y - value) (mul_comm x T))
  have hfactor :
      (T * y - T * x) / (x * y) =
        T * (y - x) / (x * y) :=
    congrArg (fun numerator : ℝ => numerator / (x * y))
      (mul_sub T y x).symm
  exact Eq.trans hfractions (Eq.trans hcommute hfactor)

theorem Complex.logarithmicPhaseSupportReciprocalResidual_eq
    (t : ℝ) (a : ℕ) (ha : 2 ≤ a) :
    Complex.logarithmicPhaseSupportReciprocalResidual t a =
      ‖t‖ * ((1 : ℝ) / 3) /
        (Complex.logarithmicPhaseWideSupportLeft a *
          Complex.logarithmicPhaseNarrowSupportLeft a) := by
  unfold Complex.logarithmicPhaseSupportReciprocalResidual
  have hwide := Complex.logarithmicPhaseWideSupportLeft_pos a ha
  have hnarrow := Complex.logarithmicPhaseNarrowSupportLeft_pos a ha
  have hdifference := Real.div_sub_div_eq_mul_sub_div_mul
    ‖t‖
    (Complex.logarithmicPhaseWideSupportLeft a)
    (Complex.logarithmicPhaseNarrowSupportLeft a)
    (ne_of_gt hwide) (ne_of_gt hnarrow)
  have hwidth :=
    Complex.logarithmicPhaseNarrow_sub_wide_eq_one_third a
  exact Eq.trans hdifference
    (congrArg
      (fun width : ℝ => ‖t‖ * width /
        (Complex.logarithmicPhaseWideSupportLeft a *
          Complex.logarithmicPhaseNarrowSupportLeft a)) hwidth)

theorem Complex.logarithmicPhaseSupportReciprocalResidual_nonneg
    (t : ℝ) (a : ℕ) (ha : 2 ≤ a) :
    0 ≤ Complex.logarithmicPhaseSupportReciprocalResidual t a := by
  have hwide := Complex.logarithmicPhaseWideSupportLeft_pos a ha
  have hnarrow := Complex.logarithmicPhaseNarrowSupportLeft_pos a ha
  unfold Complex.logarithmicPhaseSupportReciprocalResidual
  exact sub_nonneg.mpr
    (Real.div_antitone_on_pos (norm_nonneg t) hwide
      (Complex.logarithmicPhaseWideSupportLeft_lt_narrow a).le)

theorem Complex.logarithmicPhaseFarNegativeResidualGap_ge_supportResidual
    (t : ℝ) (a : ℕ)
    (ha : 2 ≤ a) :
    Complex.logarithmicPhaseSupportReciprocalResidual t a ≤
      Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ) := by
  unfold Complex.logarithmicPhaseFarNegativeResidualGap
  unfold Complex.logarithmicPhaseSupportReciprocalResidual
  have haOne : (1 : ℤ) ≤ (a : ℤ) :=
    Int.ofNat_le.mpr
      (le_trans (Nat.succ_le_succ (Nat.zero_le 1)) ha)
  have hbaseline := Complex.modeRangeLower_floor_baseline t (a : ℤ) haOne
  have hsubtract := sub_le_sub_right hbaseline
    (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ))
  exact hsubtract

theorem Complex.three_mul_supportResidual_ge_curvature
    (t : ℝ) (a : ℕ)
    (ha : 2 ≤ a) :
    Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseNarrowSupportLeft a) ≤
      3 * Complex.logarithmicPhaseSupportReciprocalResidual t a := by
  have hwide := Complex.logarithmicPhaseWideSupportLeft_pos a ha
  have hnarrow := Complex.logarithmicPhaseNarrowSupportLeft_pos a ha
  have horder := Complex.logarithmicPhaseWideSupportLeft_lt_narrow a
  have hresidual :=
    Complex.logarithmicPhaseSupportReciprocalResidual_eq t a ha
  unfold Complex.logarithmicPhaseAdaptedCurvatureUpper
  have hdenominatorOrder :
      Complex.logarithmicPhaseWideSupportLeft a *
          Complex.logarithmicPhaseNarrowSupportLeft a ≤
        Complex.logarithmicPhaseNarrowSupportLeft a ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right horder.le hnarrow.le
    exact Eq.subst (pow_two (Complex.logarithmicPhaseNarrowSupportLeft a)).symm
      hmul
  have hdivision := div_le_div_of_nonneg_left
    (norm_nonneg t)
    (mul_pos hwide hnarrow)
    hdenominatorOrder
  have hthreeResidual :
      3 * Complex.logarithmicPhaseSupportReciprocalResidual t a =
        ‖t‖ /
          (Complex.logarithmicPhaseWideSupportLeft a *
            Complex.logarithmicPhaseNarrowSupportLeft a) := by
    exact Eq.trans (congrArg (fun value : ℝ => 3 * value) hresidual)
      (by
        have hthreeNe : (3 : ℝ) ≠ 0 :=
          ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 2))
        have hcancel : 3 * ((1 : ℝ) / 3) = 1 :=
          Eq.trans (mul_comm 3 (1 / 3))
            (div_mul_cancel₀ 1 hthreeNe)
        have hnumerator :
            3 * (‖t‖ * ((1 : ℝ) / 3)) = ‖t‖ := by
          exact Eq.trans (mul_assoc 3 ‖t‖ ((1 : ℝ) / 3)).symm
            (Eq.trans
              (congrArg (fun value : ℝ => value * ((1 : ℝ) / 3))
                (mul_comm 3 ‖t‖))
              (Eq.trans (mul_assoc ‖t‖ 3 ((1 : ℝ) / 3))
                (Eq.trans
                  (congrArg (fun value : ℝ => ‖t‖ * value) hcancel)
                  (mul_one ‖t‖))))
        exact Eq.trans (mul_div_assoc 3 (‖t‖ * (1 / 3)) _).symm
          (congrArg (fun numerator : ℝ => numerator /
            (Complex.logarithmicPhaseWideSupportLeft a *
              Complex.logarithmicPhaseNarrowSupportLeft a))
            hnumerator))
  exact le_trans hdivision (le_of_eq hthreeResidual.symm)

theorem Complex.curvature_le_three_mul_farNegativeResidual
    (t : ℝ) (a : ℕ)
    (ha : 2 ≤ a) :
    Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ)) ≤
      3 * Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ) := by
  have hcurvature :=
    Complex.three_mul_supportResidual_ge_curvature t a ha
  have hresidual :=
    Complex.logarithmicPhaseFarNegativeResidualGap_ge_supportResidual t a ha
  have hscaled := mul_le_mul_of_nonneg_left hresidual (Nat.cast_nonneg 3)
  have hcombined := le_trans hcurvature hscaled
  exact Eq.mp
    (congrArg
      (fun endpoint : ℝ =>
        Complex.logarithmicPhaseAdaptedCurvatureUpper t endpoint ≤
          3 * Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
      (Complex.logarithmicPhaseNarrowSupportLeft_eq_quantitativeEndpoint a))
    hcombined

end
end LFunctions
end Boundary
