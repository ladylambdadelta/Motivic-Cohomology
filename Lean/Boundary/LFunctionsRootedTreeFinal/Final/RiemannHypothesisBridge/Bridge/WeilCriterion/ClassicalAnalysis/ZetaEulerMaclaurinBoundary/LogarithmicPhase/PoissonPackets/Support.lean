import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.IntegerBlockFourierPackets
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.CorrectedFrequencyStationary
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.StationaryPhase.FiniteStationaryDecomposition
namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff FourierTransform Interval
open MeasureTheory

theorem Complex.summable_integer_frequency_inverse_square :
    Summable (fun m : ℤ => |(m : ℝ)| ^ (-2 : ℝ)) := by
  exact Real.summable_abs_int_rpow (by exact one_lt_two)

theorem Complex.summable_scaled_integer_frequency_inverse_square (C : ℝ) :
    Summable (fun m : ℤ => C * |(m : ℝ)| ^ (-2 : ℝ)) := by
  exact
    (Complex.summable_integer_frequency_inverse_square).mul_left C

theorem Complex.summable_scaled_integer_frequency_inverse_square_on_set
    (C : ℝ) (selected : Set ℤ) :
    Summable (fun m : selected => C * |(m : ℝ)| ^ (-2 : ℝ)) := by
  exact
    (Complex.summable_scaled_integer_frequency_inverse_square C).subtype selected

theorem Complex.summable_logarithmicPhase_integerBlockFourierPacket
    (extension : SchwartzMap ℝ ℂ) :
    Summable (fun m : ℤ =>
      SchwartzMap.fourierTransformCLM ℝ extension (m : ℝ)) := by
  have hdecay :
      (SchwartzMap.fourierTransformCLM ℝ extension) =O[Filter.cocompact ℝ]
        (fun x : ℝ => ‖x‖ ^ (-2 : ℝ)) := by
    exact (SchwartzMap.fourierTransformCLM ℝ extension).isBigO_cocompact_rpow (-2)
  have hdecay_integer :
      (fun m : ℤ => SchwartzMap.fourierTransformCLM ℝ extension (m : ℝ)) =O[Filter.cofinite]
        (fun m : ℤ => ‖(m : ℝ)‖ ^ (-2 : ℝ)) := by
    exact hdecay.comp_tendsto Int.tendsto_coe_cofinite
  have hmajorant :
      Summable (fun m : ℤ => ‖(m : ℝ)‖ ^ (-2 : ℝ)) := by
    exact Real.summable_abs_int_rpow (by exact one_lt_two)
  exact summable_of_isBigO hmajorant hdecay_integer

theorem Complex.summable_norm_logarithmicPhase_integerBlockFourierPacket
    (extension : SchwartzMap ℝ ℂ) :
    Summable (fun m : ℤ => ‖SchwartzMap.fourierTransformCLM ℝ extension (m : ℝ)‖) := by
  exact (Complex.summable_logarithmicPhase_integerBlockFourierPacket extension).norm

theorem Complex.norm_intervalIntegral_le_constant_mul_length
    (f : ℝ → ℂ)
    (left right C : ℝ)
    (hleft_right : left ≤ right)
    (hC : 0 ≤ C)
    (hpointwise : ∀ x ∈ Ι left right, ‖f x‖ ≤ C) :
    ‖∫ x in left..right, f x‖ ≤ C * (right - left) := by
  have hraw :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := left) (b := right) (f := f) (C := C) hpointwise
  have hlength : C * |right - left| = C * (right - left) := by
    exact congrArg (fun value : ℝ => C * value)
      (abs_of_nonneg (sub_nonneg.mpr hleft_right))
  exact
    Eq.subst
      (motive := fun bound : ℝ => ‖∫ x in left..right, f x‖ ≤ bound)
      hlength
      hraw

theorem Complex.integral_norm_le_constant_smul_length
    (f : ℝ → ℂ)
    (left right C : ℝ)
    (hleft_right : left ≤ right)
    (hC : 0 ≤ C)
    (hfi : IntervalIntegrable (fun x : ℝ => ‖f x‖) volume left right)
    (hpointwise : ∀ x ∈ Set.Icc left right, ‖f x‖ ≤ C) :
    (∫ x in left..right, ‖f x‖) ≤ (right - left) • C := by
  have hconstant :
      IntervalIntegrable (fun _ : ℝ => C) volume left right :=
    intervalIntegrable_const
  have hmono :=
    intervalIntegral.integral_mono_on
      hleft_right hfi hconstant hpointwise
  exact hmono.trans_eq (intervalIntegral.integral_const C)

theorem Complex.norm_intervalIntegral_logarithmicPhase_remainder_le_left_endpoint_gap
    (t : ℝ) (m : ℤ) (ht : 1 ≤ ‖t‖)
    {left right : ℝ} (hleft : 0 < left) (hleft_right : left ≤ right)
    {a : ℤ} (hcenter : Complex.logarithmicPhaseFourierStationaryPoint t m < left)
    (hm : m < 0) :
    ‖∫ x in left..right,
        Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x‖ ≤
      ((‖t‖ / left ^ 2) /
        ((2 * Real.pi * (-(m : ℝ))) *
          (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right) ^ 2) *
        (right - left) := by
  have hright_pos : 0 < right := lt_of_lt_of_le hleft hleft_right
  let f : ℝ → ℂ :=
    Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m
  let C : ℝ :=
    (‖t‖ / left ^ 2) /
      ((2 * Real.pi * (-(m : ℝ))) *
        (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right) ^ 2
  have hC_nonneg : 0 ≤ C := by
    change 0 ≤ (‖t‖ / left ^ 2) /
      ((2 * Real.pi * (-(m : ℝ))) *
        (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right) ^ 2
    exact div_nonneg
      (div_nonneg (norm_nonneg t) (sq_nonneg left))
      (sq_nonneg _)
  have hpointwise : ∀ x ∈ Ι left right, ‖f x‖ ≤ C := by
    intro x hx
    have hx_uIcc : x ∈ Set.uIcc left right :=
      Set.uIoc_subset_uIcc hx
    have hx_Icc : x ∈ Set.Icc left right :=
      (Set.uIcc_of_le hleft_right) ▸ hx_uIcc
    change ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x‖ ≤
      (‖t‖ / left ^ 2) /
        ((2 * Real.pi * (-(m : ℝ))) *
          (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right) ^ 2
    exact
      Complex.norm_logarithmicPhaseFourierIntegrationCoefficientDerivative_le_left_endpoint_gap
        hm hleft hleft_right hcenter hx_Icc
  exact
    Complex.norm_intervalIntegral_le_constant_mul_length
      f left right C hleft_right hC_nonneg hpointwise

theorem Complex.norm_intervalIntegral_logarithmicPhase_remainder_le_right_endpoint_gap
    (t : ℝ) (m : ℤ) (ht : 1 ≤ ‖t‖)
    {left right : ℝ} (hleft : 0 < left) (hleft_right : left ≤ right)
    (hcenter : right < Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hm : m < 0) :
    ‖∫ x in left..right,
        Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x‖ ≤
      ((‖t‖ / left ^ 2) /
        ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right) ^ 2) *
        (right - left) := by
  let f : ℝ → ℂ :=
    Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m
  let C : ℝ :=
    (‖t‖ / left ^ 2) /
      ((2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right) ^ 2
  have hC_nonneg : 0 ≤ C := by
    change 0 ≤ (‖t‖ / left ^ 2) /
      ((2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right) ^ 2
    exact div_nonneg
      (div_nonneg (norm_nonneg t) (sq_nonneg left))
      (sq_nonneg _)
  have hpointwise : ∀ x ∈ Ι left right, ‖f x‖ ≤ C := by
    intro x hx
    have hx_uIcc : x ∈ Set.uIcc left right :=
      Set.uIoc_subset_uIcc hx
    have hx_Icc : x ∈ Set.Icc left right :=
      (Set.uIcc_of_le hleft_right) ▸ hx_uIcc
    change ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x‖ ≤
      (‖t‖ / left ^ 2) /
        ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right) ^ 2
    exact
      Complex.norm_logarithmicPhaseFourierIntegrationCoefficientDerivative_le_right_endpoint_gap
        hm hleft hleft_right hcenter hx_Icc
  exact
    Complex.norm_intervalIntegral_le_constant_mul_length
      f left right C hleft_right hC_nonneg hpointwise

/-- Left endpoint of the compact support interval for a canonical positive
integer-block cutoff. -/
def Real.integerBlockCutoffSupportLeftEndpoint
    (a : ℤ) : ℝ :=
  (a : ℝ) - 2 / 3

/-- A finite integer-frequency range containing every negative logarithmic
stationary center in the canonical cutoff support. -/
def Complex.logarithmicPhasePoissonModeRange
    (t : ℝ)
    (a : ℤ) : Finset ℤ :=
  Finset.Icc
    (Int.floor
      ((-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
        (2 * Real.pi)))
    0

/-- Canonical active Poisson modes: negative integer frequencies whose
stationary centers lie in the full compact cutoff-support interval. -/
def Complex.logarithmicPhasePoissonActiveModes
    (t : ℝ)
    (a b : ℤ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonModeRange t a).filter
    (fun m : ℤ =>
      m < 0 ∧
        Complex.logarithmicPhaseFourierStationaryPoint t m ∈
          Set.Icc
            (Real.integerBlockCutoffSupportLeftEndpoint a)
            ((b : ℝ) + 2 / 3))

/-- Interior stationary modes whose radius-`radius` windows remain inside the
principal logarithmic block.  Endpoint-transition modes are intentionally not
included in this family. -/
def Complex.logarithmicPhasePoissonInteriorActiveModes
    (t : ℝ)
    (a b : ℤ)
    (radius : ℝ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonModeRange t a).filter
    (fun m : ℤ =>
      m < 0 ∧
        (a : ℝ) ≤ Complex.logarithmicPhaseFourierStationaryPoint t m - radius ∧
        Complex.logarithmicPhaseFourierStationaryPoint t m + radius ≤ (b : ℝ))

theorem Complex.mem_logarithmicPhasePoissonInteriorActiveModes_iff
    (t : ℝ) (a b m : ℤ) (radius : ℝ) :
    m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius ↔
      m ∈ Complex.logarithmicPhasePoissonModeRange t a ∧
        m < 0 ∧
          (a : ℝ) ≤ Complex.logarithmicPhaseFourierStationaryPoint t m - radius ∧
          Complex.logarithmicPhaseFourierStationaryPoint t m + radius ≤ (b : ℝ) := by
  exact Finset.mem_filter

theorem Complex.logarithmicPhasePoissonInteriorActiveModes_card_le_modeRange_card
    (t : ℝ) (a b : ℤ) (radius : ℝ) :
    (Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius).card ≤
      (Complex.logarithmicPhasePoissonModeRange t a).card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Membership in the canonical compact-support active-mode family. -/
theorem Complex.mem_logarithmicPhasePoissonActiveModes_iff
    (t : ℝ)
    (a b m : ℤ) :
    m ∈ Complex.logarithmicPhasePoissonActiveModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonModeRange t a ∧
        m < 0 ∧
          Complex.logarithmicPhaseFourierStationaryPoint t m ∈
            Set.Icc
              (Real.integerBlockCutoffSupportLeftEndpoint a)
              ((b : ℝ) + 2 / 3) := by
  exact Finset.mem_filter

/-- Active Poisson centers are finite, with cardinality bounded by their
canonical enclosing integer-frequency interval. -/
theorem Complex.logarithmicPhasePoissonActiveModes_card_le_modeRange_card
    (t : ℝ)
    (a b : ℤ) :
    (Complex.logarithmicPhasePoissonActiveModes t a b).card ≤
      (Complex.logarithmicPhasePoissonModeRange t a).card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- The finite in-range complement of the canonical active Poisson family. -/
def Complex.logarithmicPhasePoissonInRangeInactiveModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  Complex.logarithmicPhasePoissonModeRange t a \
    Complex.logarithmicPhasePoissonActiveModes t a b

theorem Complex.logarithmicPhasePoissonActive_union_inRangeInactive_eq_modeRange
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonActiveModes t a b ∪
        Complex.logarithmicPhasePoissonInRangeInactiveModes t a b =
      Complex.logarithmicPhasePoissonModeRange t a := by
  exact
    (Finset.union_comm _ _).trans
      (Finset.sdiff_union_of_subset (Finset.filter_subset _ _))

theorem Complex.logarithmicPhasePoissonActive_disjoint_inRangeInactive
    (t : ℝ) (a b : ℤ) :
    Disjoint
      (Complex.logarithmicPhasePoissonActiveModes t a b)
      (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b) := by
  exact Finset.disjoint_sdiff

theorem Complex.logarithmicPhasePoissonInRangeInactive_card_le_modeRange_card
    (t : ℝ) (a b : ℤ) :
    (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card ≤
      (Complex.logarithmicPhasePoissonModeRange t a).card := by
  exact Finset.card_le_card (Finset.sdiff_subset)

theorem Complex.logarithmicPhasePoissonInteriorActiveModes_subset_activeModes
    (t : ℝ) (a b : ℤ) (radius : ℝ)
    (hradius_nonneg : 0 ≤ radius) :
    Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius ⊆
      Complex.logarithmicPhasePoissonActiveModes t a b := by
  intro m hm
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonInteriorActiveModes_iff
      t a b m radius).mp hm
  have htwo : 0 ≤ (2 / 3 : ℝ) := by
    exact div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3)
  have hleft_margin :
      (a : ℝ) - 2 / 3 ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m := by
    have hsub : (a : ℝ) - 2 / 3 ≤ (a : ℝ) := by
      exact sub_le_self _ htwo
    exact
      hsub.trans
        (le_trans hmem.2.2.1
          (sub_le_self _ hradius_nonneg))
  have hright_margin :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤
        (b : ℝ) + 2 / 3 := by
    exact
      (le_trans
        (le_trans
          (le_add_of_nonneg_right hradius_nonneg)
          hmem.2.2.2)
        (le_add_of_nonneg_right htwo))
  exact
    (Complex.mem_logarithmicPhasePoissonActiveModes_iff
      t a b m).mpr
      ⟨hmem.1, hmem.2.1, ⟨hleft_margin, hright_margin⟩⟩

/-- Endpoint-transition active modes: support-active modes not covered by the
interior stationary-window family. -/
def Complex.logarithmicPhasePoissonEndpointActiveModes
    (t : ℝ) (a b : ℤ) (radius : ℝ) : Finset ℤ :=
  Complex.logarithmicPhasePoissonActiveModes t a b \
    Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius

theorem Complex.logarithmicPhasePoissonInterior_union_endpoint_eq_active
    (t : ℝ) (a b : ℤ) (radius : ℝ)
    (hsubset :
      Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius ⊆
        Complex.logarithmicPhasePoissonActiveModes t a b) :
    Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius ∪
        Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius =
      Complex.logarithmicPhasePoissonActiveModes t a b := by
  exact
    (Finset.union_comm _ _).trans
      (Finset.sdiff_union_of_subset hsubset)

theorem Complex.logarithmicPhasePoissonInterior_union_endpoint_eq_active_of_nonneg
    (t : ℝ) (a b : ℤ) (radius : ℝ)
    (hradius_nonneg : 0 ≤ radius) :
    Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius ∪
        Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius =
      Complex.logarithmicPhasePoissonActiveModes t a b := by
  exact
    Complex.logarithmicPhasePoissonInterior_union_endpoint_eq_active
      t a b radius
      (Complex.logarithmicPhasePoissonInteriorActiveModes_subset_activeModes
        t a b radius hradius_nonneg)

/-- Away from zero, the real logarithmic phase is smooth to every order. -/
theorem Complex.contDiffAt_logarithmicPhaseRealPhase
    (t x : ℝ)
    (hx : x ≠ 0) :
    ContDiffAt ℝ ∞
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x := by
  have hconstant : ContDiffAt ℝ ∞ (fun _y : ℝ => -t) x :=
    contDiffAt_const
  have hlog : ContDiffAt ℝ ∞ Real.log x :=
    Real.contDiffAt_log.mpr hx
  exact hconstant.mul hlog

/-- On a positive integer block, the cutoff logarithmic oscillator is globally
smooth even though the bare logarithm is singular at zero. -/
theorem Complex.contDiff_logarithmicPhase_integerBlockCutoffFunction
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ContDiff ℝ ∞
      (Complex.phaseCutoffFunction
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.integerBlockCutoff a b)) := by
  exact contDiff_iff_contDiffAt.mpr
    (fun x : ℝ =>
      match Classical.em (x = 0) with
      | Or.inl hx => by
          have hzero_eventually :
              Complex.phaseCutoffFunction
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                    t)
                  (Real.integerBlockCutoff a b) =ᶠ[nhds 0]
                (fun _y : ℝ => (0 : ℂ)) := by
            show
              {y : ℝ |
                Complex.phaseCutoffFunction
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                      t)
                    (Real.integerBlockCutoff a b) y = 0} ∈ nhds 0
            exact
              Filter.mem_of_superset
                (Iio_mem_nhds Real.one_div_three_pos)
                (fun y hy =>
                  (congrArg
                    (fun value : ℝ =>
                      value •
                        Complex.exp
                          (Complex.I *
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                              t y : ℂ)))
                    (Real.integerBlockCutoff_eq_zero_of_le_one_div_three
                      hab ha (le_of_lt hy))).trans
                    (zero_smul ℝ
                      (Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            t y : ℂ)))))
          have hat_zero :
              ContDiffAt ℝ ∞
                (Complex.phaseCutoffFunction
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                    t)
                  (Real.integerBlockCutoff a b)) 0 :=
            contDiffAt_const.congr_of_eventuallyEq hzero_eventually
          exact
            Eq.subst
              (motive := fun point : ℝ =>
                ContDiffAt ℝ ∞
                  (Complex.phaseCutoffFunction
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                      t)
                    (Real.integerBlockCutoff a b)) point)
              hx.symm
              hat_zero
      | Or.inr hx =>
          Complex.contDiffAt_phaseCutoffFunction
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.integerBlockCutoff a b)
            x
            (Complex.contDiffAt_logarithmicPhaseRealPhase t x hx)
            (Real.contDiff_integerBlockCutoff a b).contDiffAt)

end

end LFunctions
end Boundary
