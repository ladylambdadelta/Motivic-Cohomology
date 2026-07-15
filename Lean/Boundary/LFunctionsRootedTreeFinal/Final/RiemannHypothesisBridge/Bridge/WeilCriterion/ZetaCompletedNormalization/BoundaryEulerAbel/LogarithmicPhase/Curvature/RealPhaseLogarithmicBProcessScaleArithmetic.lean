import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicBProcessNonemptyGeometry

/-!
# Scale arithmetic for the balanced logarithmic B-process

This file records the elementary comparisons used to reduce the closed active
majorant.  On a long dyadic block the block length exceeds
`S = sqrt (1 + ‖t‖)` and is at most `a`, hence `S < a`.  In the nonempty
interior regime one also has `b <= 2‖t‖`.  Together with
`S^2 = 1 + ‖t‖`, these comparisons control every scalar factor in the closed
B-process expression.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.longGeometry_length_le_a
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ≤ (a : ℝ) := by
  have hcomparable :=
    Real.logarithmicPhaseLongBranchGeometry_comparable hgeometry
  have hcast : (((b + 1 : ℕ) : ℝ)) ≤ ((2 * a : ℕ) : ℝ) :=
    Nat.cast_le.mpr hcomparable
  have htwoA : ((2 * a : ℕ) : ℝ) = 2 * (a : ℝ) :=
    Nat.cast_mul 2 a
  have hright : (((b + 1 : ℕ) : ℝ)) ≤ 2 * (a : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ =>
        (((b + 1 : ℕ) : ℝ)) ≤ value)
      htwoA hcast
  have hsub := sub_le_sub_right hright (a : ℝ)
  have hnormalize : 2 * (a : ℝ) - (a : ℝ) = (a : ℝ) := by
    calc
      2 * (a : ℝ) - (a : ℝ) =
          ((a : ℝ) + (a : ℝ)) - (a : ℝ) := by
        exact congrArg (fun value : ℝ => value - (a : ℝ))
          (two_mul (a : ℝ))
      _ = (a : ℝ) := add_sub_cancel_right _ _
  exact le_trans hsub (le_of_eq hnormalize)

theorem Real.longGeometry_scale_lt_a
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessScale t < (a : ℝ) := by
  unfold Complex.logarithmicPhaseBProcessScale
  exact lt_of_lt_of_le
    (Real.logarithmicPhaseLongBranchGeometry_sqrt hgeometry)
    (Real.longGeometry_length_le_a hgeometry)

theorem Real.longGeometry_scale_le_a
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessScale t ≤ (a : ℝ) :=
  (Real.longGeometry_scale_lt_a hgeometry).le

theorem Complex.logarithmicPhaseBProcessScale_sq_eq_one_add_norm
    (t : ℝ) :
    Complex.logarithmicPhaseBProcessScale t ^ 2 = 1 + ‖t‖ := by
  have hmul := Complex.logarithmicPhaseBProcessScale_sq t
  exact (pow_two _).trans hmul

theorem Complex.logarithmicPhaseBProcess_norm_le_scale_sq
    (t : ℝ) :
    ‖t‖ ≤ Complex.logarithmicPhaseBProcessScale t ^ 2 := by
  have hnorm : ‖t‖ ≤ 1 + ‖t‖ :=
    le_add_of_nonneg_left zero_le_one
  exact le_trans hnorm
    (le_of_eq
      (Complex.logarithmicPhaseBProcessScale_sq_eq_one_add_norm t).symm)

theorem Complex.logarithmicPhaseBProcess_scale_sq_le_two_mul_norm
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    Complex.logarithmicPhaseBProcessScale t ^ 2 ≤ 2 * ‖t‖ := by
  have hone := ht
  have hadd := add_le_add_right hone ‖t‖
  have hright : ‖t‖ + ‖t‖ = 2 * ‖t‖ :=
    (two_mul ‖t‖).symm
  exact Eq.subst
    (motive := fun value : ℝ =>
      Complex.logarithmicPhaseBProcessScale t ^ 2 ≤ value)
    hright
    (Eq.subst
      (motive := fun value : ℝ => value ≤ ‖t‖ + ‖t‖)
      (Complex.logarithmicPhaseBProcessScale_sq_eq_one_add_norm t).symm
      hadd)

theorem Complex.logarithmicPhaseBProcess_norm_div_scale_le_scale
    (t : ℝ) :
    ‖t‖ / Complex.logarithmicPhaseBProcessScale t ≤
      Complex.logarithmicPhaseBProcessScale t := by
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have hnorm := Complex.logarithmicPhaseBProcess_norm_le_scale_sq t
  have hproduct :
      Complex.logarithmicPhaseBProcessScale t *
          Complex.logarithmicPhaseBProcessScale t =
        Complex.logarithmicPhaseBProcessScale t ^ 2 :=
    (pow_two _).symm
  exact (div_le_iff₀ hscalePos).mpr
    (le_trans hnorm (le_of_eq hproduct.symm))

theorem Complex.logarithmicPhaseBProcess_scale_div_norm_le_two_div_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    Complex.logarithmicPhaseBProcessScale t / ‖t‖ ≤
      2 / Complex.logarithmicPhaseBProcessScale t := by
  have hnormPos := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have hsquare :=
    Complex.logarithmicPhaseBProcess_scale_sq_le_two_mul_norm t ht
  have hproduct :
      Complex.logarithmicPhaseBProcessScale t *
          Complex.logarithmicPhaseBProcessScale t =
        Complex.logarithmicPhaseBProcessScale t ^ 2 :=
    (pow_two _).symm
  have hquotient :
      Complex.logarithmicPhaseBProcessScale t ≤
        (2 * ‖t‖) / Complex.logarithmicPhaseBProcessScale t :=
    (le_div_iff₀ hscalePos).mpr
      (le_trans (le_of_eq hproduct) hsquare)
  have hnormalize :
      (2 * ‖t‖) / Complex.logarithmicPhaseBProcessScale t =
        (2 / Complex.logarithmicPhaseBProcessScale t) * ‖t‖ :=
    (div_mul_eq_mul_div 2
      (Complex.logarithmicPhaseBProcessScale t) ‖t‖).symm
  have htarget :
      Complex.logarithmicPhaseBProcessScale t ≤
        (2 / Complex.logarithmicPhaseBProcessScale t) * ‖t‖ :=
    le_trans hquotient (le_of_eq hnormalize)
  exact (div_le_iff₀ hnormPos).mpr htarget

theorem Real.longGeometry_norm_div_a_le_scale
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ / (a : ℝ) ≤ Complex.logarithmicPhaseBProcessScale t := by
  have haPos : 0 < (a : ℝ) :=
    Nat.cast_pos.mpr
      (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)
  have hscaleA := Real.longGeometry_scale_le_a hgeometry
  have hnormScale :=
    Complex.logarithmicPhaseBProcess_norm_div_scale_le_scale t
  have hdivisionMono :
      ‖t‖ / (a : ℝ) ≤
        ‖t‖ / Complex.logarithmicPhaseBProcessScale t := by
    exact div_le_div_of_nonneg_left
      (norm_nonneg t)
      (Complex.logarithmicPhaseBProcessScale_pos t)
      hscaleA
  exact le_trans hdivisionMono hnormScale

theorem Real.longGeometry_blockRight_div_scale_le_two_mul_scale_of_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    (b : ℝ) / Complex.logarithmicPhaseBProcessScale t ≤
      2 * Complex.logarithmicPhaseBProcessScale t := by
  have hbNorm :=
    Complex.logarithmicPhaseBProcess_natBlockRight_le_two_mul_norm_of_nonempty
      t ht
      (Real.logarithmicPhaseLongBranchGeometry_comparable hgeometry)
      hnonempty
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have hdivision := div_le_div_of_nonneg_right hbNorm hscalePos.le
  have hnormScale :=
    Complex.logarithmicPhaseBProcess_norm_div_scale_le_scale t
  have hscaled := mul_le_mul_of_nonneg_left hnormScale zero_le_two
  have hnormalize :
      (2 * ‖t‖) / Complex.logarithmicPhaseBProcessScale t =
        2 * (‖t‖ / Complex.logarithmicPhaseBProcessScale t) :=
    mul_div_assoc 2 ‖t‖
      (Complex.logarithmicPhaseBProcessScale t)
  exact le_trans hdivision
    (le_trans (le_of_eq hnormalize) hscaled)

theorem Real.longGeometry_blockRight_mul_scale_div_norm_le_four_mul_scale_of_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    (b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ ≤
      4 * Complex.logarithmicPhaseBProcessScale t := by
  have hbNorm :=
    Complex.logarithmicPhaseBProcess_natBlockRight_le_two_mul_norm_of_nonempty
      t ht
      (Real.logarithmicPhaseLongBranchGeometry_comparable hgeometry)
      hnonempty
  have hmul := mul_le_mul_of_nonneg_right hbNorm
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have hnormPos := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hdiv := div_le_div_of_nonneg_right hmul hnormPos.le
  have hcancel :
      (2 * ‖t‖) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ =
        2 * Complex.logarithmicPhaseBProcessScale t := by
    calc
      (2 * ‖t‖) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ =
          (2 * Complex.logarithmicPhaseBProcessScale t) * ‖t‖ / ‖t‖ := by
        exact congrArg (fun value : ℝ => value / ‖t‖)
          (calc
            (2 * ‖t‖) * Complex.logarithmicPhaseBProcessScale t =
                2 * (‖t‖ * Complex.logarithmicPhaseBProcessScale t) :=
              mul_assoc 2 ‖t‖ _
            _ = 2 * (Complex.logarithmicPhaseBProcessScale t * ‖t‖) :=
              congrArg (fun value : ℝ => 2 * value) (mul_comm _ _)
            _ = (2 * Complex.logarithmicPhaseBProcessScale t) * ‖t‖ :=
              (mul_assoc 2 _ ‖t‖).symm)
      _ = 2 * Complex.logarithmicPhaseBProcessScale t :=
        mul_div_cancel_right₀ _ (ne_of_gt hnormPos)
  have htwoFour :
      2 * Complex.logarithmicPhaseBProcessScale t ≤
        4 * Complex.logarithmicPhaseBProcessScale t :=
    mul_le_mul_of_nonneg_right
      (show (2 : ℝ) ≤ 4 from by
        calc
          (2 : ℝ) ≤ 2 + 2 :=
            le_add_of_nonneg_right zero_le_two
          _ = 4 := two_add_two_eq_four)
      (Complex.logarithmicPhaseBProcessScale_nonneg t)
  exact le_trans hdiv
    (le_trans (le_of_eq hcancel) htwoFour)

end

end LFunctions
end Boundary
