import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.BProcessCenterFrequencyTransport

/-!
# Center layers for balanced endpoint modes

This owner places each endpoint class in an explicit interval of stationary
centers.  Outside modes lie in the two cutoff collars.  Clipped modes lie in
multiplicative layers determined by the balanced scale `S`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseBProcessLeftClippedCenterUpper
    (t : ℝ) (a : ℤ) : ℝ :=
  (a : ℝ) * Complex.logarithmicPhaseBProcessScale t /
    (Complex.logarithmicPhaseBProcessScale t - 1)

def Complex.logarithmicPhaseBProcessRightClippedCenterLower
    (t : ℝ) (b : ℤ) : ℝ :=
  (b : ℝ) * Complex.logarithmicPhaseBProcessScale t /
    (Complex.logarithmicPhaseBProcessScale t + 1)

theorem Complex.logarithmicPhaseBProcessScale_gt_one
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    1 < Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessScale
  have hnormPos : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have hone : (1 : ℝ) < 1 + ‖t‖ := lt_add_of_pos_right 1 hnormPos
  have hsqrt := Real.sqrt_lt_sqrt (le_of_lt zero_lt_one) hone
  exact Eq.subst
    (motive := fun value : ℝ => value < Real.sqrt (1 + ‖t‖))
    Real.sqrt_one hsqrt

theorem Complex.logarithmicPhaseBProcessScale_sub_one_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    0 < Complex.logarithmicPhaseBProcessScale t - 1 :=
  sub_pos.mpr (Complex.logarithmicPhaseBProcessScale_gt_one t ht)

theorem Complex.logarithmicPhaseBProcessScale_add_one_pos
    (t : ℝ) :
    0 < Complex.logarithmicPhaseBProcessScale t + 1 :=
  add_pos (Complex.logarithmicPhaseBProcessScale_pos t) zero_lt_one

theorem Complex.logarithmicPhaseBProcessWindowLeft_eq_center_mul_scale_sub_one_div_scale
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhaseBProcessWindowLeft t m =
      Complex.logarithmicPhaseFourierStationaryPoint t m *
        (Complex.logarithmicPhaseBProcessScale t - 1) /
          Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessWindowLeft
  unfold Complex.logarithmicPhaseBProcessRadius
  let center := Complex.logarithmicPhaseFourierStationaryPoint t m
  let scale := Complex.logarithmicPhaseBProcessScale t
  have hscaleNe : scale ≠ 0 :=
    Complex.logarithmicPhaseBProcessScale_ne_zero t
  calc
    center - center / scale =
        center * 1 - center * scale⁻¹ := by
      exact congrArg₂ (fun left right : ℝ => left - right)
        (mul_one center).symm (div_eq_mul_inv center scale)
    _ = center * (1 - scale⁻¹) :=
      (mul_sub center 1 scale⁻¹).symm
    _ = center * ((scale - 1) / scale) := by
      exact congrArg (fun value : ℝ => center * value)
        (calc
          1 - scale⁻¹ = scale / scale - 1 / scale := by
            exact congrArg₂ (fun left right : ℝ => left - right)
              (div_self hscaleNe).symm (one_div scale).symm
          _ = (scale - 1) / scale := (sub_div scale 1 scale).symm)
    _ = center * (scale - 1) / scale :=
      (mul_div_assoc center (scale - 1) scale).symm

theorem Complex.logarithmicPhaseBProcessWindowRight_eq_center_mul_scale_add_one_div_scale
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhaseBProcessWindowRight t m =
      Complex.logarithmicPhaseFourierStationaryPoint t m *
        (Complex.logarithmicPhaseBProcessScale t + 1) /
          Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessWindowRight
  unfold Complex.logarithmicPhaseBProcessRadius
  let center := Complex.logarithmicPhaseFourierStationaryPoint t m
  let scale := Complex.logarithmicPhaseBProcessScale t
  have hscaleNe : scale ≠ 0 :=
    Complex.logarithmicPhaseBProcessScale_ne_zero t
  calc
    center + center / scale = center * 1 + center * scale⁻¹ := by
      exact congrArg₂ (fun left right : ℝ => left + right)
        (mul_one center).symm (div_eq_mul_inv center scale)
    _ = center * (1 + scale⁻¹) :=
      (mul_add center 1 scale⁻¹).symm
    _ = center * ((scale + 1) / scale) := by
      exact congrArg (fun value : ℝ => center * value)
        (calc
          1 + scale⁻¹ = scale / scale + 1 / scale := by
            exact congrArg₂ (fun left right : ℝ => left + right)
              (div_self hscaleNe).symm (one_div scale).symm
          _ = (scale + 1) / scale := (add_div scale 1 scale).symm)
    _ = center * (scale + 1) / scale :=
      (mul_div_assoc center (scale + 1) scale).symm

theorem Complex.logarithmicPhaseBProcessLeftClipped_center_lt_upper
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a m : ℤ}
    (hclip : Complex.logarithmicPhaseBProcessWindowLeft t m < (a : ℝ)) :
    Complex.logarithmicPhaseFourierStationaryPoint t m <
      Complex.logarithmicPhaseBProcessLeftClippedCenterUpper t a := by
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have hsubPos :=
    Complex.logarithmicPhaseBProcessScale_sub_one_pos t ht
  have hwindow :=
    Complex.logarithmicPhaseBProcessWindowLeft_eq_center_mul_scale_sub_one_div_scale
      t m
  have hnormalized :
      Complex.logarithmicPhaseFourierStationaryPoint t m *
          (Complex.logarithmicPhaseBProcessScale t - 1) /
          Complex.logarithmicPhaseBProcessScale t < (a : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ => value < (a : ℝ))
      hwindow hclip
  have hmulScale := (div_lt_iff₀ hscalePos).mp hnormalized
  unfold Complex.logarithmicPhaseBProcessLeftClippedCenterUpper
  exact (lt_div_iff₀ hsubPos).mpr hmulScale

theorem Complex.logarithmicPhaseBProcessRightClipped_lower_lt_center
    (t : ℝ) {b m : ℤ}
    (hclip : (b : ℝ) < Complex.logarithmicPhaseBProcessWindowRight t m) :
    Complex.logarithmicPhaseBProcessRightClippedCenterLower t b <
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have haddPos := Complex.logarithmicPhaseBProcessScale_add_one_pos t
  have hwindow :=
    Complex.logarithmicPhaseBProcessWindowRight_eq_center_mul_scale_add_one_div_scale
      t m
  have hnormalized :
      (b : ℝ) <
        Complex.logarithmicPhaseFourierStationaryPoint t m *
          (Complex.logarithmicPhaseBProcessScale t + 1) /
          Complex.logarithmicPhaseBProcessScale t :=
    Eq.subst
      (motive := fun value : ℝ => (b : ℝ) < value)
      hwindow hclip
  have hmulScale := (lt_div_iff₀ hscalePos).mp hnormalized
  unfold Complex.logarithmicPhaseBProcessRightClippedCenterLower
  exact (div_lt_iff₀ haddPos).mpr hmulScale

theorem Complex.logarithmicPhaseBProcessLeftOutside_center_bounds
    (t : ℝ) (a b : ℤ) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessLeftOutsideModes t a b) :
    Real.integerBlockCutoffSupportLeftEndpoint a ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m ∧
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤ (a : ℝ) := by
  have hclass :=
    (Complex.mem_logarithmicPhasePoissonBProcessLeftOutsideModes_iff
      t a b m).mp hm
  have hactive :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_mem_active
      t a b hclass.1
  have hactiveData :=
    (Complex.mem_logarithmicPhasePoissonActiveModes_iff t a b m).mp hactive
  exact And.intro hactiveData.2.2.1 hclass.2.le

theorem Complex.logarithmicPhaseBProcessRightOutside_center_bounds
    (t : ℝ) (a b : ℤ) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessRightOutsideModes t a b) :
    (b : ℝ) ≤ Complex.logarithmicPhaseFourierStationaryPoint t m ∧
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤
        (b : ℝ) + 2 / 3 := by
  have hclass :=
    (Complex.mem_logarithmicPhasePoissonBProcessRightOutsideModes_iff
      t a b m).mp hm
  have hactive :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_mem_active
      t a b hclass.1
  have hactiveData :=
    (Complex.mem_logarithmicPhasePoissonActiveModes_iff t a b m).mp hactive
  exact And.intro hclass.2.le hactiveData.2.2.2

end

end LFunctions
end Boundary
