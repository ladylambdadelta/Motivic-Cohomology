import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicOutsideEndpointWidths

/-!
# Completion of balanced endpoint frequency widths

This owner proves the right-collar width and the exact multiplicative clipped
width formulas.  All four endpoint frequency layers are consequently shorter
than one on a long block.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.longGeometry_norm_lt_b_sq
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ < (b : ℝ) ^ 2 := by
  have hab := Real.logarithmicPhaseLongBranchGeometry_order hgeometry
  have habReal : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
  have haNonneg : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have hbNonneg : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hsquare := mul_le_mul habReal habReal haNonneg hbNonneg
  have haSquare : (a : ℝ) * (a : ℝ) = (a : ℝ) ^ 2 :=
    (pow_two _).symm
  have hbSquare : (b : ℝ) * (b : ℝ) = (b : ℝ) ^ 2 :=
    (pow_two _).symm
  have hsquareCast : (a : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ (b : ℝ) ^ 2)
      haSquare
      (Eq.subst
        (motive := fun value : ℝ =>
          (a : ℝ) * (a : ℝ) ≤ value)
        hbSquare hsquare)
  exact lt_of_lt_of_le
    (Real.longGeometry_norm_lt_a_sq hgeometry) hsquareCast

theorem Complex.rightOutsideFrequencyWidth_lt_one
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessRightOutsideFrequencyUpper t (b : ℤ) -
        Complex.logarithmicPhaseBProcessRightOutsideFrequencyLower t (b : ℤ) < 1 := by
  let left := (b : ℝ)
  let right := (b : ℝ) + 2 / 3
  have hbPos : 0 < (b : ℝ) :=
    Nat.cast_pos.mpr
      (lt_of_lt_of_le Nat.zero_lt_one
        (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry))
  have hleftRight : left ≤ right :=
    le_add_of_nonneg_right
      (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
  have hbound :=
    Complex.logarithmicPhaseCenterFrequencyCoordinate_sub_le_norm_mul_gap_div_left_sq
      t hbPos hleftRight
  have hgap : right - left = (2 / 3 : ℝ) :=
    add_sub_cancel_left left (2 / 3)
  have hgapOne : (2 / 3 : ℝ) ≤ 1 :=
    (div_le_one (Nat.cast_pos.mpr (Nat.succ_pos 2))).mpr
      (Nat.cast_le.mpr (Nat.le_succ 2))
  have hmulGap : ‖t‖ * (right - left) ≤ ‖t‖ := by
    have hscaled := mul_le_mul_of_nonneg_left hgapOne (norm_nonneg t)
    have hscaledOne : ‖t‖ * (2 / 3 : ℝ) ≤ ‖t‖ :=
      le_trans hscaled (le_of_eq (mul_one ‖t‖))
    exact Eq.subst
      (motive := fun value : ℝ => ‖t‖ * value ≤ ‖t‖)
      hgap.symm
      hscaledOne
  have hnormSquare := Real.longGeometry_norm_lt_b_sq hgeometry
  have hratio : ‖t‖ * (right - left) / left ^ 2 < 1 := by
    have hleftSqPos : 0 < left ^ 2 := sq_pos_of_pos hbPos
    exact (div_lt_one hleftSqPos).mpr
      (lt_of_le_of_lt hmulGap hnormSquare)
  exact lt_of_le_of_lt hbound hratio

theorem Real.div_mul_div_self_sub_one
    (a scale : ℝ)
    (ha : a ≠ 0)
    (hscale : scale ≠ 0)
    (hsub : scale - 1 ≠ 0) :
    (a * scale / (scale - 1))⁻¹ =
      (scale - 1) / (a * scale) := by
  exact inv_div (a * scale) (scale - 1)

theorem Real.div_mul_div_self_add_one
    (b scale : ℝ)
    (hb : b ≠ 0)
    (hscale : scale ≠ 0) :
    (b * scale / (scale + 1))⁻¹ =
      (scale + 1) / (b * scale) := by
  exact inv_div (b * scale) (scale + 1)

theorem Complex.leftClippedFrequencyWidth_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a : ℤ} (ha : 1 ≤ a) :
    Complex.logarithmicPhaseBProcessLeftClippedFrequencyUpper t a -
        Complex.logarithmicPhaseBProcessLeftClippedFrequencyLower t a =
      ‖t‖ /
        (2 * Real.pi * (a : ℝ) *
          Complex.logarithmicPhaseBProcessScale t) := by
  let scale := Complex.logarithmicPhaseBProcessScale t
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have hsubPos := Complex.logarithmicPhaseBProcessScale_sub_one_pos t ht
  unfold Complex.logarithmicPhaseBProcessLeftClippedFrequencyUpper
  unfold Complex.logarithmicPhaseBProcessLeftClippedFrequencyLower
  unfold Complex.logarithmicPhaseBProcessLeftClippedCenterUpper
  unfold Complex.logarithmicPhaseCenterFrequencyCoordinate
  have hfirst :
      ‖t‖ / (2 * Real.pi * (a : ℝ)) =
        ‖t‖ * scale /
          (2 * Real.pi * (a : ℝ) * scale) := by
    have hbaseNonzero : 2 * Real.pi * (a : ℝ) ≠ 0 :=
      mul_ne_zero (ne_of_gt Complex.two_mul_pi_pos) (ne_of_gt haPos)
    have hdenominatorNonzero :
        2 * Real.pi * (a : ℝ) * scale ≠ 0 :=
      mul_ne_zero hbaseNonzero (ne_of_gt hscalePos)
    have hcrossProduct :
        ‖t‖ * (2 * Real.pi * (a : ℝ) * scale) =
          (‖t‖ * scale) * (2 * Real.pi * (a : ℝ)) :=
      Eq.trans
        (congrArg (fun value : ℝ => ‖t‖ * value)
          (mul_comm (2 * Real.pi * (a : ℝ)) scale))
        (mul_assoc ‖t‖ scale (2 * Real.pi * (a : ℝ))).symm
    exact (div_eq_div_iff hbaseNonzero hdenominatorNonzero).mpr
      hcrossProduct
  have hsecond :
      ‖t‖ /
          (2 * Real.pi * ((a : ℝ) * scale / (scale - 1))) =
        ‖t‖ * (scale - 1) /
          (2 * Real.pi * (a : ℝ) * scale) := by
    have hdenominator :
        2 * Real.pi * ((a : ℝ) * scale / (scale - 1)) =
          (2 * Real.pi * (a : ℝ) * scale) / (scale - 1) := by
      exact (mul_div_assoc (2 * Real.pi) ((a : ℝ) * scale)
        (scale - 1)).symm.trans
        (congrArg (fun value : ℝ => value / (scale - 1))
          (mul_assoc (2 * Real.pi) (a : ℝ) scale).symm)
    exact Eq.subst
      (motive := fun denominator : ℝ =>
        ‖t‖ / denominator =
          ‖t‖ * (scale - 1) /
            (2 * Real.pi * (a : ℝ) * scale))
      hdenominator.symm
      (div_div_eq_mul_div ‖t‖
        (2 * Real.pi * (a : ℝ) * scale) (scale - 1))
  have hsubtraction :
      ‖t‖ * scale /
          (2 * Real.pi * (a : ℝ) * scale) -
        ‖t‖ * (scale - 1) /
          (2 * Real.pi * (a : ℝ) * scale) =
        ‖t‖ /
          (2 * Real.pi * (a : ℝ) * scale) := by
    have hcombined := sub_div
      (‖t‖ * scale) (‖t‖ * (scale - 1))
      (2 * Real.pi * (a : ℝ) * scale)
    have hnumerator :
        ‖t‖ * scale - ‖t‖ * (scale - 1) = ‖t‖ := by
      calc
        ‖t‖ * scale - ‖t‖ * (scale - 1) =
            ‖t‖ * (scale - (scale - 1)) :=
          (mul_sub ‖t‖ scale (scale - 1)).symm
        _ = ‖t‖ * 1 := by
          exact congrArg (fun value : ℝ => ‖t‖ * value)
            (sub_sub_cancel scale 1)
        _ = ‖t‖ := mul_one _
    exact hcombined.symm.trans
      (congrArg
        (fun numerator : ℝ => numerator /
          (2 * Real.pi * (a : ℝ) * scale)) hnumerator)
  exact
    (congrArg₂ (fun first second : ℝ => first - second)
      hfirst hsecond).trans hsubtraction

theorem Complex.leftClippedFrequencyWidth_lt_one
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessLeftClippedFrequencyUpper t (a : ℤ) -
        Complex.logarithmicPhaseBProcessLeftClippedFrequencyLower t (a : ℤ) < 1 := by
  have hformula := Complex.leftClippedFrequencyWidth_eq
    t ht (Int.ofNat_le.mpr
      (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  have hscaleA := Real.longGeometry_scale_lt_a hgeometry
  have hnormScale := Complex.logarithmicPhaseBProcess_norm_le_scale_sq t
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have haPos : 0 < (a : ℝ) :=
    Nat.cast_pos.mpr
      (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)
  have hnormProduct : ‖t‖ < (a : ℝ) *
      Complex.logarithmicPhaseBProcessScale t := by
    have hscaled := mul_lt_mul_of_pos_right hscaleA hscalePos
    have hscaleSq :
        Complex.logarithmicPhaseBProcessScale t ^ 2 =
          Complex.logarithmicPhaseBProcessScale t *
            Complex.logarithmicPhaseBProcessScale t :=
      pow_two _
    exact lt_of_le_of_lt hnormScale
      (lt_of_eq_of_lt hscaleSq hscaled)
  have htwoPiProduct :
      (a : ℝ) * Complex.logarithmicPhaseBProcessScale t <
        2 * Real.pi * (a : ℝ) *
          Complex.logarithmicPhaseBProcessScale t := by
    have htwoPi := Real.two_mul_pi_gt_one
    have hpositive := mul_pos haPos hscalePos
    have hscaled := mul_lt_mul_of_pos_right htwoPi hpositive
    have hleft :
        1 * ((a : ℝ) * Complex.logarithmicPhaseBProcessScale t) =
          (a : ℝ) * Complex.logarithmicPhaseBProcessScale t :=
      one_mul _
    have hright :
        2 * Real.pi *
            ((a : ℝ) * Complex.logarithmicPhaseBProcessScale t) =
          2 * Real.pi * (a : ℝ) *
            Complex.logarithmicPhaseBProcessScale t :=
      (mul_assoc (2 * Real.pi) (a : ℝ)
        (Complex.logarithmicPhaseBProcessScale t)).symm
    exact (lt_of_eq_of_lt hleft.symm hscaled).trans_eq hright
  have hdenominatorPos :
      0 < 2 * Real.pi * (a : ℝ) *
        Complex.logarithmicPhaseBProcessScale t :=
    mul_pos (mul_pos Complex.two_mul_pi_pos haPos) hscalePos
  have hratio := (div_lt_one hdenominatorPos).mpr
    (lt_trans hnormProduct htwoPiProduct)
  exact Eq.subst
    (motive := fun value : ℝ => value < 1)
    hformula.symm hratio

end

end LFunctions
end Boundary
