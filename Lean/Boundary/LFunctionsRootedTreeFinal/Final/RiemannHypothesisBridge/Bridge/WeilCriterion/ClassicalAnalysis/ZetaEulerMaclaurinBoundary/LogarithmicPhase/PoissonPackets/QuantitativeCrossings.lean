import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeReconstruction

/-!
# Fixed-collar crossing estimates for quantitative logarithmic packets

The explicit cutoff has width `1 / 3` on each side.  This file owns the
pointwise and interval estimates that are independent of the Fourier mode.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff FourierTransform Interval
open MeasureTheory

theorem Complex.quantitativeLogarithmicFrequencyTwistIntegrand_eq_oscillation
    (t : ℝ)
    (a b m : ℤ)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.quantitativeLogarithmicBlockCutoff a b) m x =
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x := by
  exact
    (congrArg
      (fun value : ℝ =>
        value •
          Complex.exp
            (Complex.I *
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t)
                m x : ℂ)))
      (Real.quantitativeLogarithmicBlockCutoff_eq_one_of_mem_Icc hx)).trans
      (one_smul ℝ
        (Complex.exp
          (Complex.I *
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                t)
              m x : ℂ))))

theorem Complex.quantitativeLogarithmicFrequencyTwistIntegrand_eq_zero_left
    (t : ℝ)
    (a b m : ℤ)
    {x : ℝ}
    (hx : x ≤ (a : ℝ) - 1 / 3) :
    Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.quantitativeLogarithmicBlockCutoff a b) m x = 0 := by
  exact
    (congrArg
      (fun value : ℝ =>
        value •
          Complex.exp
            (Complex.I *
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t)
                m x : ℂ)))
      (Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_left a b hx)).trans
      (zero_smul ℝ
        (Complex.exp
          (Complex.I *
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                t)
              m x : ℂ))))

theorem Complex.quantitativeLogarithmicFrequencyTwistIntegrand_eq_zero_right
    (t : ℝ)
    (a b m : ℤ)
    {x : ℝ}
    (hx : (b : ℝ) + 1 / 3 ≤ x) :
    Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.quantitativeLogarithmicBlockCutoff a b) m x = 0 := by
  exact
    (congrArg
      (fun value : ℝ =>
        value •
          Complex.exp
            (Complex.I *
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t)
                m x : ℂ)))
      (Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_right a b hx)).trans
      (zero_smul ℝ
        (Complex.exp
          (Complex.I *
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                t)
              m x : ℂ))))

theorem Complex.norm_quantitativeLogarithmicFrequencyTwistIntegrand_le_one
    (t : ℝ)
    (a b m : ℤ)
    (x : ℝ) :
    ‖Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.quantitativeLogarithmicBlockCutoff a b) m x‖ ≤ 1 := by
  have hnorm :
      ‖Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.quantitativeLogarithmicBlockCutoff a b) m x‖ =
        |Real.quantitativeLogarithmicBlockCutoff a b x| :=
    Complex.norm_phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.quantitativeLogarithmicBlockCutoff a b) m x
  have habsolute :
      |Real.quantitativeLogarithmicBlockCutoff a b x| =
        Real.quantitativeLogarithmicBlockCutoff a b x :=
    abs_of_nonneg (Real.quantitativeLogarithmicBlockCutoff_nonneg a b x)
  exact
    Eq.subst
      (motive := fun value : ℝ => value ≤ 1)
      (hnorm.trans habsolute).symm
      (Real.quantitativeLogarithmicBlockCutoff_le_one a b x)

theorem Complex.norm_intervalIntegral_quantitativeLogarithmic_leftCrossing_le
    (t : ℝ)
    (a b m : ℤ) :
    ‖∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.quantitativeLogarithmicBlockCutoff a b) m x‖ ≤ 1 / 3 := by
  let integrand : ℝ → ℂ :=
    Complex.phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.quantitativeLogarithmicBlockCutoff a b) m
  have hmargin_nonneg : (0 : ℝ) ≤ 1 / 3 := le_of_lt Real.one_div_three_pos
  have hpointwise :
      ∀ x ∈ Ι ((a : ℝ) - 1 / 3) (a : ℝ), ‖integrand x‖ ≤ (1 : ℝ) :=
    fun x _hx =>
      Complex.norm_quantitativeLogarithmicFrequencyTwistIntegrand_le_one t a b m x
  have hraw :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (a : ℝ) - 1 / 3) (b := (a : ℝ)) (f := integrand) (C := 1)
      hpointwise
  have hlength :
      (1 : ℝ) * |(a : ℝ) - ((a : ℝ) - 1 / 3)| = 1 / 3 := by
    have hdiff : (a : ℝ) - ((a : ℝ) - 1 / 3) = 1 / 3 := by
      calc
        (a : ℝ) - ((a : ℝ) - 1 / 3) =
            (a : ℝ) + -((a : ℝ) - 1 / 3) :=
          sub_eq_add_neg _ _
        _ = (a : ℝ) + (-(a : ℝ) + 1 / 3) :=
          congrArg (fun value : ℝ => (a : ℝ) + value)
            ((neg_sub _ _).trans
              ((sub_eq_add_neg _ _).trans (add_comm _ _)))
        _ = ((a : ℝ) + -(a : ℝ)) + 1 / 3 :=
          (add_assoc _ _ _).symm
        _ = 0 + 1 / 3 := congrArg (fun value : ℝ => value + 1 / 3) (sub_self (a : ℝ))
        _ = 1 / 3 := zero_add (1 / 3)
    exact
      (one_mul |(a : ℝ) - ((a : ℝ) - 1 / 3)|).trans
        ((congrArg abs hdiff).trans (abs_of_nonneg hmargin_nonneg))
  exact
    Eq.subst
      (motive := fun bound : ℝ => ‖∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ), integrand x‖ ≤ bound)
      hlength
      hraw

theorem Complex.norm_intervalIntegral_quantitativeLogarithmic_rightCrossing_le
    (t : ℝ)
    (a b m : ℤ) :
    ‖∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.quantitativeLogarithmicBlockCutoff a b) m x‖ ≤ 1 / 3 := by
  let integrand : ℝ → ℂ :=
    Complex.phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.quantitativeLogarithmicBlockCutoff a b) m
  have hmargin_nonneg : (0 : ℝ) ≤ 1 / 3 := le_of_lt Real.one_div_three_pos
  have hpointwise :
      ∀ x ∈ Ι (b : ℝ) ((b : ℝ) + 1 / 3), ‖integrand x‖ ≤ (1 : ℝ) :=
    fun x _hx =>
      Complex.norm_quantitativeLogarithmicFrequencyTwistIntegrand_le_one t a b m x
  have hraw :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (b : ℝ)) (b := (b : ℝ) + 1 / 3) (f := integrand) (C := 1)
      hpointwise
  have hlength :
      (1 : ℝ) * |((b : ℝ) + 1 / 3) - (b : ℝ)| = 1 / 3 := by
    exact
      (one_mul |((b : ℝ) + 1 / 3) - (b : ℝ)|).trans
        ((congrArg abs (add_sub_cancel_left (b : ℝ) (1 / 3))).trans
          (abs_of_nonneg hmargin_nonneg))
  exact
    Eq.subst
      (motive := fun bound : ℝ => ‖∫ x in (b : ℝ)..((b : ℝ) + 1 / 3), integrand x‖ ≤ bound)
      hlength
      hraw

theorem Complex.norm_quantitativeLogarithmic_crossings_le_two_div_three
    (t : ℝ)
    (a b m : ℤ) :
    ‖∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.quantitativeLogarithmicBlockCutoff a b) m x‖ +
      ‖∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.quantitativeLogarithmicBlockCutoff a b) m x‖ ≤ 2 / 3 := by
  have hsum :=
    add_le_add
      (Complex.norm_intervalIntegral_quantitativeLogarithmic_leftCrossing_le t a b m)
      (Complex.norm_intervalIntegral_quantitativeLogarithmic_rightCrossing_le t a b m)
  have hvalue : (1 / 3 : ℝ) + 1 / 3 = 2 / 3 := by
    calc
      (1 / 3 : ℝ) + 1 / 3 = (1 + 1) / 3 := (add_div _ _ _).symm
      _ = 2 / 3 := congrArg (fun value : ℝ => value / 3) (one_add_one_eq_two)
  exact Eq.subst (motive := fun bound : ℝ => _ ≤ bound) hvalue hsum

theorem Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_interval
    (t : ℝ)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m =
      ∫ x in ((a : ℝ) - 1 / 3)..((b : ℝ) + 1 / 3),
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.quantitativeLogarithmicBlockCutoff a b) m x := by
  change
    (∫ x : ℝ,
      Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.quantitativeLogarithmicBlockCutoff a b) m x) = _
  let integrand : ℝ → ℂ :=
    Complex.phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.quantitativeLogarithmicBlockCutoff a b) m
  have hab_real : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  have hmargin_nonneg : (0 : ℝ) ≤ 1 / 3 := le_of_lt Real.one_div_three_pos
  have hendpoints : (a : ℝ) - 1 / 3 ≤ (b : ℝ) + 1 / 3 :=
    le_trans
      (sub_le_self (a : ℝ) hmargin_nonneg)
      (le_trans hab_real (le_add_of_nonneg_right hmargin_nonneg))
  have hrestricted :
      (∫ x : ℝ, integrand x) =
        ∫ x in Set.Ioc ((a : ℝ) - 1 / 3) ((b : ℝ) + 1 / 3), integrand x := by
    have hindicator :
        (∫ x : ℝ, integrand x) =
          ∫ x : ℝ,
            Set.indicator (Set.Ioc ((a : ℝ) - 1 / 3) ((b : ℝ) + 1 / 3)) integrand x := by
      exact integral_congr_ae
        (Filter.Eventually.of_forall
          (fun x : ℝ =>
            match Classical.em
                (x ∈ Set.Ioc ((a : ℝ) - 1 / 3) ((b : ℝ) + 1 / 3)) with
            | Or.inl hx => (Set.indicator_of_mem hx (f := integrand)).symm
            | Or.inr hx => by
                have houtside :
                    x ≤ (a : ℝ) - 1 / 3 ∨ (b : ℝ) + 1 / 3 < x :=
                  Or.elim
                    (not_and_or.mp (fun hbounds => hx hbounds))
                    (fun hleft => Or.inl (le_of_not_gt hleft))
                    (fun hright => Or.inr (lt_of_not_ge hright))
                have hzero : integrand x = 0 :=
                  Or.elim houtside
                    (fun hleft =>
                      Complex.quantitativeLogarithmicFrequencyTwistIntegrand_eq_zero_left
                        t a b m hleft)
                    (fun hright =>
                      Complex.quantitativeLogarithmicFrequencyTwistIntegrand_eq_zero_right
                        t a b m (le_of_lt hright))
                exact hzero.trans (Set.indicator_of_not_mem hx (f := integrand)).symm))
    exact hindicator.trans (integral_indicator measurableSet_Ioc)
  exact hrestricted.trans (intervalIntegral.integral_of_le hendpoints).symm

theorem Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_three_parts
    (t : ℝ)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m =
      (∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.quantitativeLogarithmicBlockCutoff a b) m x) +
      (∫ x in (a : ℝ)..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x) +
      (∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.quantitativeLogarithmicBlockCutoff a b) m x) := by
  let integrand : ℝ → ℂ :=
    Complex.phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.quantitativeLogarithmicBlockCutoff a b) m
  have hsmooth : ContDiff ℝ ∞ integrand :=
    Complex.contDiff_phaseCutoffFrequencyTwistIntegrand_of_productSmooth
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.quantitativeLogarithmicBlockCutoff a b)
      m
      (Complex.contDiff_logarithmicPhase_quantitativeBlockCutoffFunction t a b ha)
  have hcontinuous : Continuous integrand := hsmooth.continuous
  have hleft :
      IntervalIntegrable integrand volume ((a : ℝ) - 1 / 3) (a : ℝ) :=
    hcontinuous.intervalIntegrable ((a : ℝ) - 1 / 3) (a : ℝ)
  have hmiddle : IntervalIntegrable integrand volume (a : ℝ) (b : ℝ) :=
    hcontinuous.intervalIntegrable (a : ℝ) (b : ℝ)
  have hright :
      IntervalIntegrable integrand volume (b : ℝ) ((b : ℝ) + 1 / 3) :=
    hcontinuous.intervalIntegrable (b : ℝ) ((b : ℝ) + 1 / 3)
  have hfirst :
      (∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ), integrand x) +
          ∫ x in (a : ℝ)..(b : ℝ), integrand x =
        ∫ x in ((a : ℝ) - 1 / 3)..(b : ℝ), integrand x :=
    intervalIntegral.integral_add_adjacent_intervals hleft hmiddle
  have hsecond :
      (∫ x in ((a : ℝ) - 1 / 3)..(b : ℝ), integrand x) +
          ∫ x in (b : ℝ)..((b : ℝ) + 1 / 3), integrand x =
        ∫ x in ((a : ℝ) - 1 / 3)..((b : ℝ) + 1 / 3), integrand x :=
    intervalIntegral.integral_add_adjacent_intervals (hleft.trans hmiddle) hright
  have hthree :
      (∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ), integrand x) +
          (∫ x in (a : ℝ)..(b : ℝ), integrand x) +
            (∫ x in (b : ℝ)..((b : ℝ) + 1 / 3), integrand x) =
        ∫ x in ((a : ℝ) - 1 / 3)..((b : ℝ) + 1 / 3), integrand x :=
    (congrArg
      (fun value : ℂ => value + ∫ x in (b : ℝ)..((b : ℝ) + 1 / 3), integrand x)
      hfirst).trans hsecond
  have hmiddle_integrands :
      Set.EqOn integrand
        (Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m))
        (Set.uIcc (a : ℝ) (b : ℝ)) := by
    intro x hx
    have hab_real : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
    have hinterval : Set.uIcc (a : ℝ) (b : ℝ) = Set.Icc (a : ℝ) (b : ℝ) :=
      Set.uIcc_of_le hab_real
    exact
      Complex.quantitativeLogarithmicFrequencyTwistIntegrand_eq_oscillation
        t a b m (hinterval ▸ hx)
  have hmiddle_eq :
      (∫ x in (a : ℝ)..(b : ℝ), integrand x) =
        ∫ x in (a : ℝ)..(b : ℝ),
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m) x :=
    intervalIntegral.integral_congr hmiddle_integrands
  have hfinite :=
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_interval t a b m ha hab
  exact
    hfinite.trans
      (hthree.symm.trans
        (congrArg₂ (fun left right : ℂ => left + right)
          (congrArg
            (fun middle : ℂ =>
              (∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ), integrand x) + middle)
            hmiddle_eq)
          rfl))

end
end LFunctions
end Boundary
