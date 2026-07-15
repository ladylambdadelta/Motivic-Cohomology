import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicEndpointWidthsCompletion

/-!
# Cardinality of balanced endpoint classes

The right-clipped frequency width is the same `‖t‖/(2πbS)` scale as the
left-clipped width.  Once this final width is established, the generic integer
packing theorem shows that each of the four endpoint classes contains at most
one mode.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.rightClippedFrequencyWidth_eq
    (t : ℝ) {b : ℤ} (hb : 1 ≤ b) :
    Complex.logarithmicPhaseBProcessRightClippedFrequencyUpper t b -
        Complex.logarithmicPhaseBProcessRightClippedFrequencyLower t b =
      ‖t‖ /
        (2 * Real.pi * (b : ℝ) *
          Complex.logarithmicPhaseBProcessScale t) := by
  let scale := Complex.logarithmicPhaseBProcessScale t
  have hbPos : 0 < (b : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one hb)
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  unfold Complex.logarithmicPhaseBProcessRightClippedFrequencyUpper
  unfold Complex.logarithmicPhaseBProcessRightClippedFrequencyLower
  unfold Complex.logarithmicPhaseBProcessRightClippedCenterLower
  unfold Complex.logarithmicPhaseCenterFrequencyCoordinate
  have hfirst :
      ‖t‖ /
          (2 * Real.pi * ((b : ℝ) * scale / (scale + 1))) =
        ‖t‖ * (scale + 1) /
          (2 * Real.pi * (b : ℝ) * scale) := by
    have hdenominator :
        2 * Real.pi * ((b : ℝ) * scale / (scale + 1)) =
          (2 * Real.pi * (b : ℝ) * scale) / (scale + 1) := by
      exact (mul_div_assoc (2 * Real.pi) ((b : ℝ) * scale)
        (scale + 1)).symm.trans
        (congrArg (fun value : ℝ => value / (scale + 1))
          (mul_assoc (2 * Real.pi) (b : ℝ) scale).symm)
    exact Eq.subst
      (motive := fun denominator : ℝ =>
        ‖t‖ / denominator =
          ‖t‖ * (scale + 1) /
            (2 * Real.pi * (b : ℝ) * scale))
      hdenominator.symm
      (div_div_eq_mul_div ‖t‖
        (2 * Real.pi * (b : ℝ) * scale) (scale + 1))
  have hsecond :
      ‖t‖ / (2 * Real.pi * (b : ℝ)) =
        ‖t‖ * scale /
          (2 * Real.pi * (b : ℝ) * scale) := by
    have hdenominatorNe :
        2 * Real.pi * (b : ℝ) * scale ≠ 0 :=
      mul_ne_zero
        (mul_ne_zero (ne_of_gt Complex.two_mul_pi_pos) (ne_of_gt hbPos))
        (ne_of_gt hscalePos)
    have hbaseNe : 2 * Real.pi * (b : ℝ) ≠ 0 :=
      mul_ne_zero (ne_of_gt Complex.two_mul_pi_pos) (ne_of_gt hbPos)
    have hcrossProduct :
        ‖t‖ * (2 * Real.pi * (b : ℝ) * scale) =
          (‖t‖ * scale) * (2 * Real.pi * (b : ℝ)) :=
      Eq.trans
        (congrArg (fun value : ℝ => ‖t‖ * value)
          (mul_comm (2 * Real.pi * (b : ℝ)) scale))
        (mul_assoc ‖t‖ scale (2 * Real.pi * (b : ℝ))).symm
    exact (div_eq_div_iff hbaseNe hdenominatorNe).mpr hcrossProduct
  have hsubtraction :
      ‖t‖ * (scale + 1) /
          (2 * Real.pi * (b : ℝ) * scale) -
        ‖t‖ * scale /
          (2 * Real.pi * (b : ℝ) * scale) =
        ‖t‖ /
          (2 * Real.pi * (b : ℝ) * scale) := by
    have hcombined := sub_div
      (‖t‖ * (scale + 1)) (‖t‖ * scale)
      (2 * Real.pi * (b : ℝ) * scale)
    have hnumerator :
        ‖t‖ * (scale + 1) - ‖t‖ * scale = ‖t‖ := by
      calc
        ‖t‖ * (scale + 1) - ‖t‖ * scale =
            ‖t‖ * ((scale + 1) - scale) :=
          (mul_sub ‖t‖ (scale + 1) scale).symm
        _ = ‖t‖ * 1 := by
          exact congrArg (fun value : ℝ => ‖t‖ * value)
            (add_sub_cancel_left scale 1)
        _ = ‖t‖ := mul_one _
    exact hcombined.symm.trans
      (congrArg
        (fun numerator : ℝ => numerator /
          (2 * Real.pi * (b : ℝ) * scale)) hnumerator)
  exact
    (congrArg₂ (fun first second : ℝ => first - second)
      hfirst hsecond).trans hsubtraction

theorem Complex.rightClippedFrequencyWidth_lt_one
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessRightClippedFrequencyUpper t (b : ℤ) -
        Complex.logarithmicPhaseBProcessRightClippedFrequencyLower t (b : ℤ) < 1 := by
  have hformula := Complex.rightClippedFrequencyWidth_eq t
    (Int.ofNat_le.mpr
      (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry))
  have hscaleB : Complex.logarithmicPhaseBProcessScale t < (b : ℝ) :=
    lt_of_lt_of_le
      (Real.longGeometry_scale_lt_a hgeometry)
      (Nat.cast_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_order hgeometry))
  have hnormScale := Complex.logarithmicPhaseBProcess_norm_le_scale_sq t
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have hbPos : 0 < (b : ℝ) :=
    Nat.cast_pos.mpr
      (lt_of_lt_of_le Nat.zero_lt_one
        (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry))
  have hnormProduct : ‖t‖ < (b : ℝ) *
      Complex.logarithmicPhaseBProcessScale t := by
    have hscaled := mul_lt_mul_of_pos_right hscaleB hscalePos
    have hscaleSq :
        Complex.logarithmicPhaseBProcessScale t ^ 2 =
          Complex.logarithmicPhaseBProcessScale t *
            Complex.logarithmicPhaseBProcessScale t :=
      pow_two _
    exact lt_of_le_of_lt hnormScale
      (lt_of_eq_of_lt hscaleSq hscaled)
  have htwoPiProduct :
      (b : ℝ) * Complex.logarithmicPhaseBProcessScale t <
        2 * Real.pi * (b : ℝ) *
          Complex.logarithmicPhaseBProcessScale t := by
    have hpositive := mul_pos hbPos hscalePos
    have hscaled :=
      mul_lt_mul_of_pos_right Real.two_mul_pi_gt_one hpositive
    have hleft :
        1 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t) =
          (b : ℝ) * Complex.logarithmicPhaseBProcessScale t :=
      one_mul _
    have hright :
        2 * Real.pi *
            ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t) =
          2 * Real.pi * (b : ℝ) *
            Complex.logarithmicPhaseBProcessScale t :=
      (mul_assoc (2 * Real.pi) (b : ℝ)
        (Complex.logarithmicPhaseBProcessScale t)).symm
    exact (lt_of_eq_of_lt hleft.symm hscaled).trans_eq hright
  have hdenominatorPos :
      0 < 2 * Real.pi * (b : ℝ) *
        Complex.logarithmicPhaseBProcessScale t :=
    mul_pos (mul_pos Complex.two_mul_pi_pos hbPos) hscalePos
  have hratio := (div_lt_one hdenominatorPos).mpr
    (lt_trans hnormProduct htwoPiProduct)
  exact Eq.subst
    (motive := fun value : ℝ => value < 1)
    hformula.symm hratio

theorem Complex.leftOutsideModes_card_le_one
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhasePoissonBProcessLeftOutsideModes
      t (a : ℤ) (b : ℤ)).card ≤ 1 := by
  let lower := -Complex.logarithmicPhaseBProcessLeftOutsideFrequencyUpper t (a : ℤ)
  let upper := -Complex.logarithmicPhaseBProcessLeftOutsideFrequencyLower t (a : ℤ)
  have hwidth : upper - lower < 1 := by
    exact Eq.subst
      (motive := fun value : ℝ => value < 1)
      (Real.reflected_interval_width
        (Complex.logarithmicPhaseBProcessLeftOutsideFrequencyLower t (a : ℤ))
        (Complex.logarithmicPhaseBProcessLeftOutsideFrequencyUpper t (a : ℤ))).symm
      (Complex.leftOutsideFrequencyWidth_lt_one hgeometry)
  exact Finset.card_le_one_of_cast_mem_short_interval
    _ hwidth (fun m hm =>
      Complex.logarithmicPhaseBProcessLeftOutside_modeCast_bounds
        t ht (a : ℤ) (b : ℤ)
        (Int.ofNat_le.mpr
          (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)) hm)

theorem Complex.rightOutsideModes_card_le_one
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhasePoissonBProcessRightOutsideModes
      t (a : ℤ) (b : ℤ)).card ≤ 1 := by
  let lower := -Complex.logarithmicPhaseBProcessRightOutsideFrequencyUpper t (b : ℤ)
  let upper := -Complex.logarithmicPhaseBProcessRightOutsideFrequencyLower t (b : ℤ)
  have hwidth : upper - lower < 1 := by
    exact Eq.subst
      (motive := fun value : ℝ => value < 1)
      (Real.reflected_interval_width
        (Complex.logarithmicPhaseBProcessRightOutsideFrequencyLower t (b : ℤ))
        (Complex.logarithmicPhaseBProcessRightOutsideFrequencyUpper t (b : ℤ))).symm
      (Complex.rightOutsideFrequencyWidth_lt_one hgeometry)
  exact Finset.card_le_one_of_cast_mem_short_interval
    _ hwidth (fun m hm =>
      Complex.logarithmicPhaseBProcessRightOutside_modeCast_bounds
        t ht (a : ℤ) (b : ℤ)
        (Int.ofNat_le.mpr
          (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry)) hm)

theorem Complex.leftClippedModes_card_le_one
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhasePoissonBProcessLeftClippedModes
      t (a : ℤ) (b : ℤ)).card ≤ 1 := by
  let lower := -Complex.logarithmicPhaseBProcessLeftClippedFrequencyUpper t (a : ℤ)
  let upper := -Complex.logarithmicPhaseBProcessLeftClippedFrequencyLower t (a : ℤ)
  have hwidth : upper - lower < 1 := by
    exact Eq.subst
      (motive := fun value : ℝ => value < 1)
      (Real.reflected_interval_width
        (Complex.logarithmicPhaseBProcessLeftClippedFrequencyLower t (a : ℤ))
        (Complex.logarithmicPhaseBProcessLeftClippedFrequencyUpper t (a : ℤ))).symm
      (Complex.leftClippedFrequencyWidth_lt_one ht hgeometry)
  exact Finset.card_le_one_of_cast_mem_short_interval
    _ hwidth (fun m hm =>
      Complex.logarithmicPhaseBProcessLeftClipped_modeCast_bounds
        t ht (a : ℤ) (b : ℤ)
        (Int.ofNat_le.mpr
          (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)) hm)

theorem Complex.rightClippedModes_card_le_one
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhasePoissonBProcessRightClippedModes
      t (a : ℤ) (b : ℤ)).card ≤ 1 := by
  let lower := -Complex.logarithmicPhaseBProcessRightClippedFrequencyUpper t (b : ℤ)
  let upper := -Complex.logarithmicPhaseBProcessRightClippedFrequencyLower t (b : ℤ)
  have hwidth : upper - lower < 1 := by
    exact Eq.subst
      (motive := fun value : ℝ => value < 1)
      (Real.reflected_interval_width
        (Complex.logarithmicPhaseBProcessRightClippedFrequencyLower t (b : ℤ))
        (Complex.logarithmicPhaseBProcessRightClippedFrequencyUpper t (b : ℤ))).symm
      (Complex.rightClippedFrequencyWidth_lt_one hgeometry)
  exact Finset.card_le_one_of_cast_mem_short_interval
    _ hwidth (fun m hm =>
      Complex.logarithmicPhaseBProcessRightClipped_modeCast_bounds
        t ht (a : ℤ) (b : ℤ)
        (Int.ofNat_le.mpr
          (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry)) hm)

end

end LFunctions
end Boundary
