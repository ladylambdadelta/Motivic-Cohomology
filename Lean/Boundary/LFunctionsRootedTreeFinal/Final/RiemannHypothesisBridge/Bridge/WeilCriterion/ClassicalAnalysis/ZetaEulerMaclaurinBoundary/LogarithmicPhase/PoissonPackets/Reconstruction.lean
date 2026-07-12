import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.Support
namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff FourierTransform Interval
open MeasureTheory

def Complex.logarithmicPhaseIntegerBlockSchwartz
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) : SchwartzMap ℝ ℂ :=
  Complex.phaseCutoffSchwartzOfSmoothProduct
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
    (Real.integerBlockCutoff a b)
    (Complex.contDiff_logarithmicPhase_integerBlockCutoffFunction t a b ha hab)
    (Real.hasCompactSupport_integerBlockCutoff a b)

/-- On the closed real block, a logarithmic Poisson packet has unit cutoff and
is exactly the corresponding frequency-twisted oscillation. -/
theorem Complex.logarithmicPhase_integerBlockCutoffFrequencyTwistIntegrand_eq
    (t : ℝ)
    (a b m : ℤ)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.integerBlockCutoff a b) m x =
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
      (Real.integerBlockCutoff_eq_one_of_mem_real_Icc hx)).trans
      (one_smul ℝ
        (Complex.exp
          (Complex.I *
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m x : ℂ))))

/-- A positive-block logarithmic packet vanishes throughout the fixed left
neighborhood containing the logarithmic singularity. -/
theorem Complex.logarithmicPhase_integerBlockCutoffFrequencyTwistIntegrand_eq_zero_left
    (t : ℝ)
    (a b m : ℤ)
    (hab : a ≤ b)
    {x : ℝ}
    (hx : x ≤ (a : ℝ) - 2 / 3) :
    Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.integerBlockCutoff a b) m x = 0 := by
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
      (Real.integerBlockCutoff_eq_zero_of_left_margin hab hx)).trans
      (zero_smul ℝ
        (Complex.exp
          (Complex.I *
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m x : ℂ))))

/-- A logarithmic packet vanishes beyond the right transition margin. -/
theorem Complex.logarithmicPhase_integerBlockCutoffFrequencyTwistIntegrand_eq_zero_right
    (t : ℝ)
    (a b m : ℤ)
    (hab : a ≤ b)
    {x : ℝ}
    (hx : (b : ℝ) + 2 / 3 ≤ x) :
    Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.integerBlockCutoff a b) m x = 0 := by
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
      (Real.integerBlockCutoff_eq_zero_of_right_margin hab hx)).trans
      (zero_smul ℝ
        (Complex.exp
          (Complex.I *
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m x : ℂ))))

/-- Every logarithmic Fourier packet is exactly the finite interval integral
over the canonical cutoff support bounds. -/
theorem Complex.integral_logarithmicPhase_integerBlockCutoffFrequencyTwist_eq_interval
    (t : ℝ)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    (∫ x : ℝ,
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x) =
      ∫ x in ((a : ℝ) - 2 / 3)..((b : ℝ) + 2 / 3),
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x := by
  let integrand : ℝ → ℂ :=
    Complex.phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.integerBlockCutoff a b) m
  have hab_real : (a : ℝ) ≤ (b : ℝ) :=
    Int.cast_le.mpr hab
  have hmargin_nonneg : (0 : ℝ) ≤ 2 / 3 :=
    le_of_lt
      (lt_trans Real.one_div_three_pos
        Real.one_div_three_lt_two_div_three)
  have hendpoints : (a : ℝ) - 2 / 3 ≤ (b : ℝ) + 2 / 3 :=
    le_trans
      (sub_le_self (a : ℝ) hmargin_nonneg)
      (le_trans hab_real (le_add_of_nonneg_right hmargin_nonneg))
  have hrestricted :
      (∫ x : ℝ, integrand x) =
        ∫ x in Set.Ioc ((a : ℝ) - 2 / 3) ((b : ℝ) + 2 / 3), integrand x := by
    have hindicator :
        (∫ x : ℝ, integrand x) =
          ∫ x : ℝ, Set.indicator (Set.Ioc ((a : ℝ) - 2 / 3) ((b : ℝ) + 2 / 3)) integrand x := by
      exact integral_congr_ae
        (Filter.Eventually.of_forall
        (fun x : ℝ =>
          match Classical.em
              (x ∈ Set.Ioc ((a : ℝ) - 2 / 3) ((b : ℝ) + 2 / 3)) with
          | Or.inl hx =>
              (Set.indicator_of_mem hx (f := integrand)).symm
          | Or.inr hx => by
              have houtside :
                  x ≤ (a : ℝ) - 2 / 3 ∨ (b : ℝ) + 2 / 3 < x :=
                Or.elim
                  (not_and_or.mp (fun hbounds => hx hbounds))
                  (fun hleft => Or.inl (le_of_not_gt hleft))
                  (fun hright => Or.inr (lt_of_not_ge hright))
              have hzero : integrand x = 0 :=
                Or.elim houtside
                  (fun hleft =>
                    Complex.logarithmicPhase_integerBlockCutoffFrequencyTwistIntegrand_eq_zero_left
                      t a b m hab hleft)
                  (fun hright =>
                    Complex.logarithmicPhase_integerBlockCutoffFrequencyTwistIntegrand_eq_zero_right
                      t a b m hab (le_of_lt hright))
              exact
                hzero.trans
                  (Set.indicator_of_not_mem hx (f := integrand)).symm))
    exact hindicator.trans (integral_indicator measurableSet_Ioc)
  exact
    hrestricted.trans
      (intervalIntegral.integral_of_le hendpoints).symm

/-- Exact decomposition of one logarithmic Fourier packet into the left
cutoff crossing, the principal block, and the right cutoff crossing. -/
theorem Complex.integral_logarithmicPhase_integerBlockCutoffFrequencyTwist_eq_three_parts
    (t : ℝ)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    (∫ x : ℝ,
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x) =
      (∫ x in ((a : ℝ) - 2 / 3)..(a : ℝ),
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x) +
      (∫ x in (a : ℝ)..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x) +
      (∫ x in (b : ℝ)..((b : ℝ) + 2 / 3),
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x) := by
  let integrand : ℝ → ℂ :=
    Complex.phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.integerBlockCutoff a b) m
  have hsmooth : ContDiff ℝ ∞ integrand :=
    Complex.contDiff_phaseCutoffFrequencyTwistIntegrand_of_productSmooth
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.integerBlockCutoff a b)
      m
      (Complex.contDiff_logarithmicPhase_integerBlockCutoffFunction
        t a b ha hab)
  have hcontinuous : Continuous integrand :=
    hsmooth.continuous
  have hleft :
      IntervalIntegrable integrand volume ((a : ℝ) - 2 / 3) (a : ℝ) :=
    hcontinuous.intervalIntegrable ((a : ℝ) - 2 / 3) (a : ℝ)
  have hmiddle :
      IntervalIntegrable integrand volume (a : ℝ) (b : ℝ) :=
    hcontinuous.intervalIntegrable (a : ℝ) (b : ℝ)
  have hright :
      IntervalIntegrable integrand volume (b : ℝ) ((b : ℝ) + 2 / 3) :=
    hcontinuous.intervalIntegrable (b : ℝ) ((b : ℝ) + 2 / 3)
  have hfirst :
      (∫ x in ((a : ℝ) - 2 / 3)..(a : ℝ), integrand x) +
          ∫ x in (a : ℝ)..(b : ℝ), integrand x =
        ∫ x in ((a : ℝ) - 2 / 3)..(b : ℝ), integrand x :=
    intervalIntegral.integral_add_adjacent_intervals hleft hmiddle
  have hsecond :
      (∫ x in ((a : ℝ) - 2 / 3)..(b : ℝ), integrand x) +
          ∫ x in (b : ℝ)..((b : ℝ) + 2 / 3), integrand x =
        ∫ x in ((a : ℝ) - 2 / 3)..((b : ℝ) + 2 / 3), integrand x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hleft.trans hmiddle) hright
  have hthree :
      (∫ x in ((a : ℝ) - 2 / 3)..(a : ℝ), integrand x) +
          (∫ x in (a : ℝ)..(b : ℝ), integrand x) +
            (∫ x in (b : ℝ)..((b : ℝ) + 2 / 3), integrand x) =
        ∫ x in ((a : ℝ) - 2 / 3)..((b : ℝ) + 2 / 3), integrand x :=
    (congrArg
      (fun value : ℂ =>
        value + ∫ x in (b : ℝ)..((b : ℝ) + 2 / 3), integrand x)
      hfirst).trans hsecond
  have hmiddle_integrands :
      Set.EqOn integrand
        (Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m))
        (Set.uIcc (a : ℝ) (b : ℝ)) := by
    intro x hx
    have hab_real : (a : ℝ) ≤ (b : ℝ) :=
      Int.cast_le.mpr hab
    have hinterval : Set.uIcc (a : ℝ) (b : ℝ) =
        Set.Icc (a : ℝ) (b : ℝ) :=
      Set.uIcc_of_le hab_real
    exact
      Complex.logarithmicPhase_integerBlockCutoffFrequencyTwistIntegrand_eq
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
    Complex.integral_logarithmicPhase_integerBlockCutoffFrequencyTwist_eq_interval
      t a b m ha hab
  exact
    hfinite.trans
      (hthree.symm.trans
        (congrArg₂ (fun left right : ℂ => left + right)
          (congrArg
            (fun middle : ℂ =>
              (∫ x in ((a : ℝ) - 2 / 3)..(a : ℝ), integrand x) + middle)
            hmiddle_eq)
          rfl))

/-- The left cutoff-crossing contribution of every logarithmic packet is at
most the fixed transition width `2/3`. -/
theorem Complex.norm_intervalIntegral_logarithmicPhase_leftCutoffCrossing_le
    (t : ℝ)
    (a b m : ℤ) :
    ‖∫ x in ((a : ℝ) - 2 / 3)..(a : ℝ),
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x‖ ≤ 2 / 3 := by
  let integrand : ℝ → ℂ :=
    Complex.phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.integerBlockCutoff a b) m
  have hpointwise :
      ∀ x ∈ Set.Ioc ((a : ℝ) - 2 / 3) (a : ℝ),
        ‖integrand x‖ ≤ (1 : ℝ) := by
    intro x _hx
    have hnorm : ‖integrand x‖ = |Real.integerBlockCutoff a b x| :=
      Complex.norm_phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.integerBlockCutoff a b) m x
    have habsolute :
        |Real.integerBlockCutoff a b x| = Real.integerBlockCutoff a b x :=
      abs_of_nonneg (Real.integerBlockCutoff_nonneg a b x)
    exact
      Eq.subst
        (motive := fun value : ℝ => value ≤ 1)
        (hnorm.trans habsolute).symm
        (Real.integerBlockCutoff_le_one a b x)
  have hpointwise' :
      ∀ x ∈ Ι ((a : ℝ) - 2 / 3) (a : ℝ),
        ‖integrand x‖ ≤ (1 : ℝ) := by
    intro x hx
    exact
      hpointwise x
        (Eq.mp
          (congrArg (fun s : Set ℝ => x ∈ s)
            (Set.uIoc_of_le
              (sub_le_self (a : ℝ)
                (le_of_lt
                  (lt_trans Real.one_div_three_pos
                    Real.one_div_three_lt_two_div_three)))))
          hx)
  have hraw :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (a : ℝ) - 2 / 3) (b := (a : ℝ)) (f := integrand) (C := 1)
      hpointwise'
  have hlength :
      (1 : ℝ) * |(a : ℝ) - ((a : ℝ) - 2 / 3)| = 2 / 3 := by
    have hdiff :
        (a : ℝ) - ((a : ℝ) - 2 / 3) = 2 / 3 := by
      calc
        (a : ℝ) - ((a : ℝ) - 2 / 3) = (a : ℝ) + -((a : ℝ) - 2 / 3) :=
          sub_eq_add_neg _ _
        _ = (a : ℝ) + (-(a : ℝ) + 2 / 3) :=
          congrArg (fun value : ℝ => (a : ℝ) + value)
            ((neg_sub _ _).trans
              ((sub_eq_add_neg _ _).trans (add_comm _ _)))
        _ = ((a : ℝ) + -(a : ℝ)) + 2 / 3 :=
          (add_assoc _ _ _).symm
        _ = 0 + 2 / 3 := congrArg (fun value : ℝ => value + 2 / 3) (add_neg_cancel (a : ℝ))
        _ = 2 / 3 := zero_add _
    exact
      (one_mul |(a : ℝ) - ((a : ℝ) - 2 / 3)|).trans
        ((congrArg abs hdiff).trans
          (abs_of_nonneg
            (le_of_lt
              (lt_trans Real.one_div_three_pos
                Real.one_div_three_lt_two_div_three))))
  exact
    Eq.subst
      (motive := fun bound : ℝ => ‖∫ x in ((a : ℝ) - 2 / 3)..(a : ℝ),
        integrand x‖ ≤ bound)
      hlength
      hraw

/-- The right cutoff-crossing contribution of every logarithmic packet is at
most the fixed transition width `2/3`. -/
theorem Complex.norm_intervalIntegral_logarithmicPhase_rightCutoffCrossing_le
    (t : ℝ)
    (a b m : ℤ) :
    ‖∫ x in (b : ℝ)..((b : ℝ) + 2 / 3),
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x‖ ≤ 2 / 3 := by
  let integrand : ℝ → ℂ :=
    Complex.phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.integerBlockCutoff a b) m
  have hpointwise :
      ∀ x ∈ Set.Ioc (b : ℝ) ((b : ℝ) + 2 / 3),
        ‖integrand x‖ ≤ (1 : ℝ) := by
    intro x _hx
    have hnorm : ‖integrand x‖ = |Real.integerBlockCutoff a b x| :=
      Complex.norm_phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.integerBlockCutoff a b) m x
    have habsolute :
        |Real.integerBlockCutoff a b x| = Real.integerBlockCutoff a b x :=
      abs_of_nonneg (Real.integerBlockCutoff_nonneg a b x)
    exact
      Eq.subst
        (motive := fun value : ℝ => value ≤ 1)
        (hnorm.trans habsolute).symm
        (Real.integerBlockCutoff_le_one a b x)
  have hpointwise' :
      ∀ x ∈ Ι (b : ℝ) ((b : ℝ) + 2 / 3),
        ‖integrand x‖ ≤ (1 : ℝ) := by
    intro x hx
    exact
      hpointwise x
        (Eq.mp
          (congrArg (fun s : Set ℝ => x ∈ s)
            (Set.uIoc_of_le
              (a := (b : ℝ)) (b := (b : ℝ) + 2 / 3)
              (le_add_of_nonneg_right
                (le_of_lt
                  (lt_trans Real.one_div_three_pos
                    Real.one_div_three_lt_two_div_three)))))
          hx)
  have hraw :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (b : ℝ)) (b := (b : ℝ) + 2 / 3) (f := integrand) (C := 1)
      hpointwise'
  have hlength :
      (1 : ℝ) * |((b : ℝ) + 2 / 3) - (b : ℝ)| = 2 / 3 := by
    exact
      (one_mul |((b : ℝ) + 2 / 3) - (b : ℝ)|).trans
        ((congrArg abs (add_sub_cancel_left (b : ℝ) (2 / 3 : ℝ))).trans
          (abs_of_nonneg
            (le_of_lt
              (lt_trans Real.one_div_three_pos
                Real.one_div_three_lt_two_div_three))))
  exact
    Eq.subst
      (motive := fun bound : ℝ => ‖∫ x in (b : ℝ)..((b : ℝ) + 2 / 3),
        integrand x‖ ≤ bound)
      hlength
      hraw

/-! The first central-window budget is the geometric length bound.  It is
independent of the Fourier mode and is the local term later combined with
the stationary and nonstationary estimates. -/
theorem Complex.norm_intervalIntegral_logarithmicPhase_packet_le_length
    (t : ℝ)
    (a b m : ℤ)
    (left right : ℝ)
    (hleft_right : left ≤ right) :
    ‖∫ x in left..right,
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x‖ ≤ right - left := by
  let integrand : ℝ → ℂ :=
    Complex.phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.integerBlockCutoff a b) m
  have hpointwise :
      ∀ x ∈ Ι left right, ‖integrand x‖ ≤ (1 : ℝ) := by
    intro x _hx
    have hnorm : ‖integrand x‖ = |Real.integerBlockCutoff a b x| :=
      Complex.norm_phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.integerBlockCutoff a b) m x
    have habsolute :
        |Real.integerBlockCutoff a b x| = Real.integerBlockCutoff a b x :=
      abs_of_nonneg (Real.integerBlockCutoff_nonneg a b x)
    exact
      Eq.subst
        (motive := fun value : ℝ => value ≤ 1)
        (hnorm.trans habsolute).symm
        (Real.integerBlockCutoff_le_one a b x)
  have hraw :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := left) (b := right) (f := integrand) (C := 1) hpointwise
  have hlength :
      (1 : ℝ) * |right - left| = right - left := by
    exact
      (one_mul |right - left|).trans
        (abs_of_nonneg (sub_nonneg.mpr hleft_right))
  exact
    Eq.subst
      (motive := fun bound : ℝ => ‖∫ x in left..right, integrand x‖ ≤ bound)
      hlength
      hraw

/-! A central window whose endpoints stay inside the principal block has the
expected geometric budget.  This is the central-window owner used by the
stationary packet decomposition. -/
theorem Complex.norm_intervalIntegral_logarithmicPhase_packet_centralWindow_le_two_radius
    (t : ℝ)
    (a b m : ℤ)
    (center radius : ℝ)
    (hleft : (a : ℝ) ≤ center - radius)
    (hright : center + radius ≤ (b : ℝ))
    (_hradius : 0 ≤ radius) :
    ‖∫ x in center - radius..center + radius,
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x‖ ≤
      (center + radius) - (center - radius) := by
  have hinterval : center - radius ≤ center + radius := by
    have hraw : center - radius ≤ center - -radius :=
      (sub_le_sub_iff_left center).mpr
        (le_trans (neg_nonpos.mpr _hradius) _hradius)
    have hsum : center - -radius = center + radius :=
      sub_neg_eq_add center radius
    exact
      Eq.subst
        (motive := fun value : ℝ => center - radius ≤ value)
        hsum
        hraw
  have hlength :=
    Complex.norm_intervalIntegral_logarithmicPhase_packet_le_length
      t a b m (center - radius) (center + radius) hinterval
  exact hlength

theorem Complex.norm_intervalIntegral_logarithmicPhase_principal_three_piece_bound
    (t : ℝ)
    (m : ℤ)
    (left center radius right : ℝ)
    (hleft_center : left ≤ center - radius)
    (hcenter_right : center - radius ≤ center + radius)
    (hright : center + radius ≤ right)
    (hleft_integrable :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m) x)
        volume left (center - radius))
    (hcentral_integrable :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m) x)
        volume (center - radius) (center + radius))
    (hright_integrable :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m) x)
        volume (center + radius) right)
    {leftBound centralBound rightBound : ℝ}
    (hleft_bound :
      ‖∫ x in left..center - radius,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤ leftBound)
    (hcentral_bound :
      ‖∫ x in center - radius..center + radius,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤ centralBound)
    (hright_bound :
      ‖∫ x in center + radius..right,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤ rightBound) :
    ‖∫ x in left..right,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤ leftBound + centralBound + rightBound := by
  exact
    norm_intervalIntegral_le_three_piece_bounds
      (fun x : ℝ =>
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x)
      left center radius right hleft_center hcenter_right hright
      hleft_integrable hcentral_integrable hright_integrable
      hleft_bound hcentral_bound hright_bound

theorem Complex.integral_logarithmicPhase_packet_eq_integral_realPhaseOscillation_on_subinterval
    (t : ℝ)
    (a b m : ℤ)
    (left right : ℝ)
    (hleft : (a : ℝ) ≤ left)
    (hright : right ≤ (b : ℝ))
    (hleft_right : left ≤ right) :
    (∫ x in left..right,
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x) =
      ∫ x in left..right,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x := by
  refine intervalIntegral.integral_congr_ae ?_
  exact
    Filter.Eventually.of_forall
      (fun x hx => by
        have hx_uIcc : x ∈ Set.uIcc left right :=
          Set.uIoc_subset_uIcc hx
        have hx_Icc : x ∈ Set.Icc left right :=
          (Set.uIcc_of_le hleft_right) ▸ hx_uIcc
        have hx_block : x ∈ Set.Icc (a : ℝ) (b : ℝ) :=
          ⟨le_trans hleft hx_Icc.1, le_trans hx_Icc.2 hright⟩
        exact
          Complex.logarithmicPhase_integerBlockCutoffFrequencyTwistIntegrand_eq
            t a b m hx_block)

theorem Complex.norm_intervalIntegral_logarithmicPhase_packet_le_nonstationary_tail
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b m : ℤ)
    (left right : ℝ)
    (hleft : 0 < left)
    (hleft_block : (a : ℝ) ≤ left)
    (hright_block : right ≤ (b : ℝ))
    (hleft_right : left ≤ right)
    (hstationary : ∀ x ∈ [[left, right]],
      x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hcoefficientDerivative_integrable :
      IntervalIntegrable
        (fun x : ℝ =>
          -(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
            (Complex.realPhaseDerivativeDenominator
              (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2)
        volume left right)
    (hoscillationDerivative_integrable :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x *
            Complex.realPhaseDerivativeDenominator
              (Complex.logarithmicPhaseFourierTwistedDerivative t m) x)
        volume left right) :
    ‖∫ x in left..right,
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x‖ ≤
      ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) right‖ +
        ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) left‖ +
        ∫ x in left..right,
          ‖-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
            (Complex.realPhaseDerivativeDenominator
              (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2‖ := by
  have hpacket :=
    Complex.integral_logarithmicPhase_packet_eq_integral_realPhaseOscillation_on_subinterval
      t a b m left right hleft_block hright_block hleft_right
  have htail :=
    Complex.norm_intervalIntegral_logarithmicPhaseFourierOscillation_le_nonstationary_tail
      t ht ht_nonneg m left right hleft hleft_right hstationary
      hcoefficientDerivative_integrable hoscillationDerivative_integrable
  exact
    Eq.subst
      (motive := fun value : ℂ => ‖value‖ ≤
        ‖Complex.realPhaseIntegrationCoefficient
            (Complex.logarithmicPhaseFourierTwistedDerivative t m) right‖ +
          ‖Complex.realPhaseIntegrationCoefficient
            (Complex.logarithmicPhaseFourierTwistedDerivative t m) left‖ +
          ∫ x in left..right,
            ‖-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
              (Complex.realPhaseDerivativeDenominator
                (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2‖)
      hpacket.symm
      htail

theorem Complex.intervalIntegrable_logarithmicPhase_oscillationDerivative
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (m : ℤ)
    (left right : ℝ)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    IntervalIntegrable
      (fun x : ℝ =>
        Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m) x *
          Complex.realPhaseDerivativeDenominator
            (Complex.logarithmicPhaseFourierTwistedDerivative t m) x)
      volume left right := by
  refine ContinuousOn.intervalIntegrable_of_Icc hleft_right ?_
  intro x hx
  have hx_pos : 0 < x := lt_of_lt_of_le hleft hx.1
  have htwist :=
    Complex.logarithmicPhaseFourierTwist_hasDerivAt
      t ht_nonneg m hx_pos
  have htwistedDerivative :=
    Complex.logarithmicPhaseFourierTwistedDerivative_hasDerivAt
      t ht_nonneg m hx_pos
  have hoscillation :
      ContinuousAt
        (Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m)) x :=
    (Complex.hasDerivAt_realPhaseOscillation htwist).continuousAt
  have hrealDerivative :
      ContinuousAt
        (fun y : ℝ =>
          (Complex.logarithmicPhaseFourierTwistedDerivative t m y : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp htwistedDerivative.continuousAt
  have hdenominator :
      ContinuousAt
        (Complex.realPhaseDerivativeDenominator
          (Complex.logarithmicPhaseFourierTwistedDerivative t m)) x := by
    change ContinuousAt
      (fun y : ℝ =>
        Complex.I *
          (Complex.logarithmicPhaseFourierTwistedDerivative t m y : ℂ)) x
    exact continuousAt_const.mul hrealDerivative
  exact
    (hoscillation.mul hdenominator).continuousWithinAt

theorem Complex.intervalIntegrable_logarithmicPhase_oscillation
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (m : ℤ)
    (left right : ℝ)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    IntervalIntegrable
      (fun x : ℝ =>
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x)
      volume left right := by
  refine ContinuousOn.intervalIntegrable_of_Icc hleft_right ?_
  intro x hx
  have hx_pos : 0 < x := lt_of_lt_of_le hleft hx.1
  have htwist :=
    Complex.logarithmicPhaseFourierTwist_hasDerivAt
      t ht_nonneg m hx_pos
  exact
    (Complex.hasDerivAt_realPhaseOscillation htwist).continuousAt.continuousWithinAt

theorem Complex.intervalIntegrable_logarithmicPhase_coefficientDerivative
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (m : ℤ)
    (left right : ℝ)
    (hleft : 0 < left)
    (hleft_right : left ≤ right)
    (hstationary :
      ∀ x ∈ Set.Icc left right,
        x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m) :
    IntervalIntegrable
      (fun x : ℝ =>
        -(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
          (Complex.realPhaseDerivativeDenominator
            (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2)
      volume left right := by
  refine ContinuousOn.intervalIntegrable_of_Icc hleft_right ?_
  intro x hx
  have hx_pos : 0 < x := lt_of_lt_of_le hleft hx.1
  have htwistedDerivative :=
    Complex.logarithmicPhaseFourierTwistedDerivative_hasDerivAt
      t ht_nonneg m hx_pos
  have hdenominator_ne :
      Complex.realPhaseDerivativeDenominator
        (Complex.logarithmicPhaseFourierTwistedDerivative t m) x ≠ 0 :=
    Complex.logarithmicPhaseFourierDerivativeDenominator_ne_zero
      t ht ht_nonneg m hx_pos (hstationary x hx)
  have htwisted_continuous :
      ContinuousAt
        (fun y : ℝ =>
          (Complex.logarithmicPhaseFourierTwistedDerivative t m y : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp htwistedDerivative.continuousAt
  have hdenominator_continuous :
      ContinuousAt
        (Complex.realPhaseDerivativeDenominator
          (Complex.logarithmicPhaseFourierTwistedDerivative t m)) x := by
    change ContinuousAt
      (fun y : ℝ =>
        Complex.I *
          (Complex.logarithmicPhaseFourierTwistedDerivative t m y : ℂ)) x
    exact continuousAt_const.mul htwisted_continuous
  have hdenominator_sq_continuous :
      ContinuousAt
        (fun y : ℝ =>
          (Complex.realPhaseDerivativeDenominator
            (Complex.logarithmicPhaseFourierTwistedDerivative t m) y) ^ 2) x :=
    hdenominator_continuous.pow 2
  have hdenominator_sq_ne :
      (Complex.realPhaseDerivativeDenominator
        (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hdenominator_ne
  have hreal_continuous :
      ContinuousAt (fun y : ℝ => (y : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt
  have hreal_sq_continuous :
      ContinuousAt (fun y : ℝ => (y : ℂ) ^ 2) x :=
    hreal_continuous.pow 2
  have hreal_sq_ne : (x : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hx_pos))
  have hquotient_continuous :
      ContinuousAt (fun y : ℝ => (‖t‖ : ℂ) / (y : ℂ) ^ 2) x :=
    continuousAt_const.div hreal_sq_continuous hreal_sq_ne
  have hnumerator_continuous :
      ContinuousAt
        (fun y : ℝ =>
          -(Complex.I * ((‖t‖ : ℂ) / (y : ℂ) ^ 2))) x :=
    (continuousAt_const.mul hquotient_continuous).neg
  change ContinuousWithinAt
    (fun y : ℝ =>
      -(Complex.I * ((‖t‖ : ℂ) / (y : ℂ) ^ 2)) /
        (Complex.realPhaseDerivativeDenominator
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) y) ^ 2)
    (Set.Icc left right) x
  exact
    (hnumerator_continuous.div hdenominator_sq_continuous hdenominator_sq_ne).continuousWithinAt

theorem Complex.integral_logarithmicPhase_remainder_norm_le_right_endpoint_gap
    (t : ℝ) (m : ℤ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    {left right : ℝ} (hleft : 0 < left) (hleft_right : left ≤ right)
    (hcenter : right < Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hm : m < 0) :
    (∫ x in left..right,
        ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x‖) ≤
      (right - left) •
        ((‖t‖ / left ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right) ^ 2) := by
  have hstationary :
      ∀ x ∈ Set.Icc left right,
        x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m := by
    intro x hx
    exact
      Complex.logarithmicPhaseFourierStationaryPoint_ne_of_lt t
        (lt_of_le_of_lt hx.2 hcenter)
  have hfi :=
    Complex.intervalIntegrable_logarithmicPhase_coefficientDerivative
      t ht ht_nonneg m left right hleft hleft_right hstationary
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
  have hpointwise : ∀ x ∈ Set.Icc left right, ‖f x‖ ≤ C := by
    intro x hx
    change ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x‖ ≤
      (‖t‖ / left ^ 2) /
        ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right) ^ 2
    exact
      Complex.norm_logarithmicPhaseFourierIntegrationCoefficientDerivative_le_right_endpoint_gap
        hm hleft hleft_right hcenter hx
  exact
    Complex.integral_norm_le_constant_smul_length
      f left right C hleft_right hC_nonneg hfi.norm hpointwise

theorem Complex.integral_logarithmicPhase_remainder_norm_le_left_endpoint_gap
    (t : ℝ) (m : ℤ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    {left right : ℝ} (hleft : 0 < left) (hleft_right : left ≤ right)
    (hcenter : Complex.logarithmicPhaseFourierStationaryPoint t m < left)
    (hm : m < 0) :
    (∫ x in left..right,
        ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x‖) ≤
      (right - left) •
        ((‖t‖ / left ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right) ^ 2) := by
  have hstationary :
      ∀ x ∈ Set.Icc left right,
        x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m := by
    intro x hx
    exact
      Complex.logarithmicPhaseFourierStationaryPoint_ne_of_gt t
        (lt_of_lt_of_le hcenter hx.1)
  have hfi :=
    Complex.intervalIntegrable_logarithmicPhase_coefficientDerivative
      t ht ht_nonneg m left right hleft hleft_right hstationary
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
  have hpointwise : ∀ x ∈ Set.Icc left right, ‖f x‖ ≤ C := by
    intro x hx
    change ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x‖ ≤
      (‖t‖ / left ^ 2) /
        ((2 * Real.pi * (-(m : ℝ))) *
          (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right) ^ 2
    exact
      Complex.norm_logarithmicPhaseFourierIntegrationCoefficientDerivative_le_left_endpoint_gap
        hm hleft hleft_right hcenter hx
  exact
    Complex.integral_norm_le_constant_smul_length
      f left right C hleft_right hC_nonneg hfi.norm hpointwise

theorem Complex.norm_intervalIntegral_logarithmicPhase_packet_le_left_nonstationary_tail_explicit
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) (a b m : ℤ)
    (left right : ℝ) (hleft : 0 < left)
    (hleft_block : (a : ℝ) ≤ left) (hright_block : right ≤ (b : ℝ))
    (hleft_right : left ≤ right)
    (hcenter : right < Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hm : m < 0) :
    ‖∫ x in left..right,
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x‖ ≤
      2 * ((2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right)⁻¹ +
      (right - left) •
        ((‖t‖ / left ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right) ^ 2) := by
  have hstationary_Icc :
      ∀ x ∈ Set.Icc left right,
        x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m := by
    intro x hx
    exact
      Complex.logarithmicPhaseFourierStationaryPoint_ne_of_lt t
        (lt_of_le_of_lt hx.2 hcenter)
  have hstationary_uIcc :
      ∀ x ∈ [[left, right]],
        x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m := by
    intro x hx
    exact hstationary_Icc x ((Set.uIcc_of_le hleft_right) ▸ hx)
  have hcoefficient :=
    Complex.intervalIntegrable_logarithmicPhase_coefficientDerivative
      t ht ht_nonneg m left right hleft hleft_right hstationary_Icc
  have hoscillation :=
    Complex.intervalIntegrable_logarithmicPhase_oscillationDerivative
      t ht_nonneg m left right hleft hleft_right
  have htail :=
    Complex.norm_intervalIntegral_logarithmicPhase_packet_le_nonstationary_tail
      t ht ht_nonneg a b m left right hleft hleft_block hright_block hleft_right
      hstationary_uIcc hcoefficient hoscillation
  let D : ℝ :=
    ((2 * Real.pi * (-(m : ℝ))) *
      (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right)⁻¹
  let C : ℝ :=
    (‖t‖ / left ^ 2) /
      ((2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right) ^ 2
  have hleft_coeff :=
    Complex.norm_logarithmicPhaseFourierIntegrationCoefficient_le_right_endpoint_gap_inv
      hm hleft hleft_right hcenter ⟨le_rfl, hleft_right⟩
  have hright_coeff :=
    Complex.norm_logarithmicPhaseFourierIntegrationCoefficient_le_right_endpoint_gap_inv
      hm hleft hleft_right hcenter ⟨hleft_right, le_rfl⟩
  have hcoeff :
      ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) right‖ +
        ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) left‖ ≤
      D + D := add_le_add hright_coeff hleft_coeff
  have hrem :=
    Complex.integral_logarithmicPhase_remainder_norm_le_right_endpoint_gap
      t m ht ht_nonneg hleft hleft_right hcenter hm
  have hrem' :
      (∫ x in left..right,
        ‖-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
          (Complex.realPhaseDerivativeDenominator
            (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2‖) ≤
        (right - left) • C := by
    change
      (∫ x in left..right,
        ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x‖) ≤
        (right - left) • C
    exact hrem
  have hsum :
      ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) right‖ +
        ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) left‖ +
        ∫ x in left..right,
          ‖-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
            (Complex.realPhaseDerivativeDenominator
              (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2‖ ≤
      D + D + (right - left) • C :=
    add_le_add hcoeff hrem'
  have htarget :
      D + D + (right - left) • C =
        2 * ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right)⁻¹ +
          (right - left) •
            ((‖t‖ / left ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
                (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right) ^ 2) := by
    calc
      _ = 2 * D + (right - left) • C := by
        exact congrArg (fun value : ℝ => value + (right - left) • C)
          (two_mul D).symm
      _ = 2 * ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right)⁻¹ +
          (right - left) •
            ((‖t‖ / left ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
                (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right) ^ 2) := by
        rfl
  exact le_trans htail (hsum.trans_eq htarget)

theorem Complex.norm_intervalIntegral_logarithmicPhase_packet_le_right_nonstationary_tail_explicit
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) (a b m : ℤ)
    (left right : ℝ) (hleft : 0 < left)
    (hleft_block : (a : ℝ) ≤ left) (hright_block : right ≤ (b : ℝ))
    (hleft_right : left ≤ right)
    (hcenter : Complex.logarithmicPhaseFourierStationaryPoint t m < left)
    (hm : m < 0) :
    ‖∫ x in left..right,
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x‖ ≤
      2 * ((2 * Real.pi * (-(m : ℝ))) *
        (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right)⁻¹ +
      (right - left) •
        ((‖t‖ / left ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right) ^ 2) := by
  have hstationary_Icc :
      ∀ x ∈ Set.Icc left right,
        x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m := by
    intro x hx
    exact
      Complex.logarithmicPhaseFourierStationaryPoint_ne_of_gt t
        (lt_of_lt_of_le hcenter hx.1)
  have hstationary_uIcc :
      ∀ x ∈ [[left, right]],
        x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m := by
    intro x hx
    exact hstationary_Icc x ((Set.uIcc_of_le hleft_right) ▸ hx)
  have hcoefficient :=
    Complex.intervalIntegrable_logarithmicPhase_coefficientDerivative
      t ht ht_nonneg m left right hleft hleft_right hstationary_Icc
  have hoscillation :=
    Complex.intervalIntegrable_logarithmicPhase_oscillationDerivative
      t ht_nonneg m left right hleft hleft_right
  have htail :=
    Complex.norm_intervalIntegral_logarithmicPhase_packet_le_nonstationary_tail
      t ht ht_nonneg a b m left right hleft hleft_block hright_block hleft_right
      hstationary_uIcc hcoefficient hoscillation
  let D : ℝ :=
    ((2 * Real.pi * (-(m : ℝ))) *
      (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right)⁻¹
  let C : ℝ :=
    (‖t‖ / left ^ 2) /
      ((2 * Real.pi * (-(m : ℝ))) *
        (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right) ^ 2
  have hleft_coeff :=
    Complex.norm_logarithmicPhaseFourierIntegrationCoefficient_le_left_endpoint_gap_inv
      hm hleft hleft_right hcenter ⟨le_rfl, hleft_right⟩
  have hright_coeff :=
    Complex.norm_logarithmicPhaseFourierIntegrationCoefficient_le_left_endpoint_gap_inv
      hm hleft hleft_right hcenter ⟨hleft_right, le_rfl⟩
  have hcoeff :
      ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) right‖ +
        ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) left‖ ≤
      D + D := add_le_add hright_coeff hleft_coeff
  have hrem :=
    Complex.integral_logarithmicPhase_remainder_norm_le_left_endpoint_gap
      t m ht ht_nonneg hleft hleft_right hcenter hm
  have hrem' :
      (∫ x in left..right,
        ‖-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
          (Complex.realPhaseDerivativeDenominator
            (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2‖) ≤
        (right - left) • C := by
    change
      (∫ x in left..right,
        ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x‖) ≤
        (right - left) • C
    exact hrem
  have hsum :
      ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) right‖ +
        ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) left‖ +
        ∫ x in left..right,
          ‖-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
            (Complex.realPhaseDerivativeDenominator
              (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2‖ ≤
      D + D + (right - left) • C :=
    add_le_add hcoeff hrem'
  have htarget :
      D + D + (right - left) • C =
        2 * ((2 * Real.pi * (-(m : ℝ))) *
          (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right)⁻¹ +
          (right - left) •
            ((‖t‖ / left ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
                (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right) ^ 2) := by
    calc
      _ = 2 * D + (right - left) • C := by
        exact congrArg (fun value : ℝ => value + (right - left) • C)
          (two_mul D).symm
      _ = 2 * ((2 * Real.pi * (-(m : ℝ))) *
          (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right)⁻¹ +
          (right - left) •
            ((‖t‖ / left ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
                (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right) ^ 2) := by
        rfl
  exact le_trans htail (hsum.trans_eq htarget)

theorem Complex.norm_intervalIntegral_logarithmicPhase_realOscillation_le_left_nonstationary_tail_explicit
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) (a b m : ℤ)
    (left right : ℝ) (hleft : 0 < left)
    (hleft_block : (a : ℝ) ≤ left) (hright_block : right ≤ (b : ℝ))
    (hleft_right : left ≤ right)
    (hcenter : right < Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hm : m < 0) :
    ‖∫ x in left..right,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤
      2 * ((2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right)⁻¹ +
      (right - left) •
        ((‖t‖ / left ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right) ^ 2) := by
  have hcut :=
    Complex.norm_intervalIntegral_logarithmicPhase_packet_le_left_nonstationary_tail_explicit
      t ht ht_nonneg a b m left right hleft hleft_block hright_block hleft_right hcenter hm
  have heq :=
    Complex.integral_logarithmicPhase_packet_eq_integral_realPhaseOscillation_on_subinterval
      t a b m left right hleft_block hright_block hleft_right
  exact
    Eq.subst
      (motive := fun value : ℂ => ‖value‖ ≤
        2 * ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right)⁻¹ +
        (right - left) •
          ((‖t‖ / left ^ 2) /
            ((2 * Real.pi * (-(m : ℝ))) *
              (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right) ^ 2))
      heq
      hcut

theorem Complex.norm_intervalIntegral_logarithmicPhase_realOscillation_le_right_nonstationary_tail_explicit
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) (a b m : ℤ)
    (left right : ℝ) (hleft : 0 < left)
    (hleft_block : (a : ℝ) ≤ left) (hright_block : right ≤ (b : ℝ))
    (hleft_right : left ≤ right)
    (hcenter : Complex.logarithmicPhaseFourierStationaryPoint t m < left)
    (hm : m < 0) :
    ‖∫ x in left..right,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤
      2 * ((2 * Real.pi * (-(m : ℝ))) *
        (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right)⁻¹ +
      (right - left) •
        ((‖t‖ / left ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right) ^ 2) := by
  have hcut :=
    Complex.norm_intervalIntegral_logarithmicPhase_packet_le_right_nonstationary_tail_explicit
      t ht ht_nonneg a b m left right hleft hleft_block hright_block hleft_right hcenter hm
  have heq :=
    Complex.integral_logarithmicPhase_packet_eq_integral_realPhaseOscillation_on_subinterval
      t a b m left right hleft_block hright_block hleft_right
  exact
    Eq.subst
      (motive := fun value : ℂ => ‖value‖ ≤
        2 * ((2 * Real.pi * (-(m : ℝ))) *
          (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right)⁻¹ +
        (right - left) •
          ((‖t‖ / left ^ 2) /
            ((2 * Real.pi * (-(m : ℝ))) *
              (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right) ^ 2))
      heq
      hcut

theorem Complex.norm_intervalIntegral_logarithmicPhase_packet_le_nonstationary_tail_of_closed_nonstationarity
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) (a b m : ℤ)
    (left right : ℝ) (hleft : 0 < left)
    (hleft_block : (a : ℝ) ≤ left) (hright_block : right ≤ (b : ℝ))
    (hleft_right : left ≤ right)
    (hstationary : ∀ x ∈ Set.Icc left right,
      x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m) :
    ‖∫ x in left..right,
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x‖ ≤
      ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) right‖ +
        ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) left‖ +
        ∫ x in left..right,
          ‖-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
            (Complex.realPhaseDerivativeDenominator
              (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2‖ := by
  have hstationary_uIoc : ∀ x ∈ [[left, right]],
      x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m := by
    intro x hx
    exact hstationary x
      ((Set.uIcc_of_le hleft_right) ▸ hx)
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_packet_le_nonstationary_tail
      t ht ht_nonneg a b m left right hleft hleft_block hright_block hleft_right
      hstationary_uIoc
      (Complex.intervalIntegrable_logarithmicPhase_coefficientDerivative
        t ht ht_nonneg m left right hleft hleft_right hstationary)
      (Complex.intervalIntegrable_logarithmicPhase_oscillationDerivative
        t ht_nonneg m left right hleft hleft_right)

theorem Complex.norm_intervalIntegral_logarithmicPhase_packet_le_left_nonstationary_tail
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) (a b m : ℤ)
    (left right : ℝ) (hleft : 0 < left)
    (hleft_block : (a : ℝ) ≤ left) (hright_block : right ≤ (b : ℝ))
    (hleft_right : left ≤ right)
    (hright_center : right <
      Complex.logarithmicPhaseFourierStationaryPoint t m) :
    ‖∫ x in left..right,
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x‖ ≤
      ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) right‖ +
        ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) left‖ +
        ∫ x in left..right,
          ‖-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
            (Complex.realPhaseDerivativeDenominator
              (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2‖ := by
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_packet_le_nonstationary_tail_of_closed_nonstationarity
      t ht ht_nonneg a b m left right hleft hleft_block hright_block hleft_right
      (fun x hx =>
        Complex.logarithmicPhaseFourierStationaryPoint_ne_of_lt t
          (lt_of_le_of_lt hx.2 hright_center))

theorem Complex.norm_intervalIntegral_logarithmicPhase_packet_le_right_nonstationary_tail
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) (a b m : ℤ)
    (left right : ℝ) (hleft : 0 < left)
    (hleft_block : (a : ℝ) ≤ left) (hright_block : right ≤ (b : ℝ))
    (hleft_right : left ≤ right)
    (hcenter_left :
      Complex.logarithmicPhaseFourierStationaryPoint t m < left) :
    ‖∫ x in left..right,
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x‖ ≤
      ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) right‖ +
        ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) left‖ +
        ∫ x in left..right,
          ‖-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
            (Complex.realPhaseDerivativeDenominator
              (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2‖ := by
  exact
      Complex.norm_intervalIntegral_logarithmicPhase_packet_le_nonstationary_tail_of_closed_nonstationarity
        t ht ht_nonneg a b m left right hleft hleft_block hright_block hleft_right
        (fun x hx =>
          Complex.logarithmicPhaseFourierStationaryPoint_ne_of_gt t
            (lt_of_lt_of_le hcenter_left hx.1))

/-- The complete principal-strip cutoff crossing budget for one Fourier mode
is bounded by the total transition width `4/3`. -/
theorem Complex.norm_logarithmicPhase_cutoffCrossingSum_le
    (t : ℝ)
    (a b m : ℤ) :
    ‖(∫ x in ((a : ℝ) - 2 / 3)..(a : ℝ),
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x) +
      (∫ x in (b : ℝ)..((b : ℝ) + 2 / 3),
        Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.integerBlockCutoff a b) m x)‖ ≤ 4 / 3 := by
  have htriangle :
      ‖(∫ x in ((a : ℝ) - 2 / 3)..(a : ℝ),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.integerBlockCutoff a b) m x) +
        (∫ x in (b : ℝ)..((b : ℝ) + 2 / 3),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.integerBlockCutoff a b) m x)‖ ≤
        ‖∫ x in ((a : ℝ) - 2 / 3)..(a : ℝ),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.integerBlockCutoff a b) m x‖ +
        ‖∫ x in (b : ℝ)..((b : ℝ) + 2 / 3),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.integerBlockCutoff a b) m x‖ :=
    norm_add_le _ _
  have hsum :
      ‖∫ x in ((a : ℝ) - 2 / 3)..(a : ℝ),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.integerBlockCutoff a b) m x‖ +
        ‖∫ x in (b : ℝ)..((b : ℝ) + 2 / 3),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.integerBlockCutoff a b) m x‖ ≤
        (2 / 3 : ℝ) + 2 / 3 :=
    add_le_add
      (Complex.norm_intervalIntegral_logarithmicPhase_leftCutoffCrossing_le
        t a b m)
      (Complex.norm_intervalIntegral_logarithmicPhase_rightCutoffCrossing_le
        t a b m)
  exact
    le_trans htriangle
      (Eq.subst
        (motive := fun bound : ℝ =>
          ‖∫ x in ((a : ℝ) - 2 / 3)..(a : ℝ),
              Complex.phaseCutoffFrequencyTwistIntegrand
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t)
                (Real.integerBlockCutoff a b) m x‖ +
            ‖∫ x in (b : ℝ)..((b : ℝ) + 2 / 3),
              Complex.phaseCutoffFrequencyTwistIntegrand
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t)
                (Real.integerBlockCutoff a b) m x‖ ≤ bound)
        Real.two_div_three_add_two_div_three_eq_four_div_three
        hsum)

/-- The canonical logarithmic Schwartz extension agrees with the original
oscillator at every block integer. -/
theorem Complex.logarithmicPhaseIntegerBlockSchwartz_apply_of_mem
    (t : ℝ)
    (a b n : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hn : n ∈ Finset.Icc a b) :
    Complex.logarithmicPhaseIntegerBlockSchwartz t a b ha hab (n : ℝ) =
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t (n : ℝ) : ℂ)) := by
  exact
    (congrArg
      (fun value : ℝ =>
        value •
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                t (n : ℝ) : ℂ)))
      (Real.integerBlockCutoff_eq_one_of_mem_Icc a b n hn)).trans
      (one_smul ℝ
        (Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))))

/-- The canonical logarithmic Schwartz extension vanishes at every integer
outside its block. -/
theorem Complex.logarithmicPhaseIntegerBlockSchwartz_apply_eq_zero_of_not_mem
    (t : ℝ)
    (a b n : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hn : n ∉ Finset.Icc a b) :
    Complex.logarithmicPhaseIntegerBlockSchwartz t a b ha hab (n : ℝ) = 0 := by
  exact
    (congrArg
      (fun value : ℝ =>
        value •
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                t (n : ℝ) : ℂ)))
      (Real.integerBlockCutoff_eq_zero_of_not_mem_Icc hab hn)).trans
      (zero_smul ℝ
        (Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))))

/-- Exact Poisson reconstruction of a positive logarithmic integer block into
its correctly normalized integer-frequency packets. -/
theorem Complex.logarithmicPhase_integerBlock_poisson_packet_reconstruction
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    (∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))) =
      ∑' m : ℤ,
        ∫ x : ℝ,
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.integerBlockCutoff a b) m x := by
  let extension : SchwartzMap ℝ ℂ :=
    Complex.logarithmicPhaseIntegerBlockSchwartz t a b ha hab
  have hreconstruction :=
    Complex.finite_integerSample_poisson_reconstruction
      extension
      (Finset.Icc a b)
      (fun n hn =>
        Complex.logarithmicPhaseIntegerBlockSchwartz_apply_eq_zero_of_not_mem
          t a b n ha hab hn)
  have hsamples :
      (∑ n ∈ Finset.Icc a b, extension (n : ℝ)) =
        ∑ n ∈ Finset.Icc a b,
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                t (n : ℝ) : ℂ)) :=
    Finset.sum_congr rfl
      (fun n hn =>
        Complex.logarithmicPhaseIntegerBlockSchwartz_apply_of_mem
          t a b n ha hab hn)
  have hmode :
      ∀ m : ℤ,
        SchwartzMap.fourierTransformCLM ℝ extension (m : ℝ) =
          ∫ x : ℝ,
            Complex.phaseCutoffFrequencyTwistIntegrand
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              (Real.integerBlockCutoff a b) m x :=
    fun m : ℤ =>
      Complex.fourierTransform_phaseCutoffSchwartzOfSmoothProduct_eq_frequencyTwistIntegral
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.integerBlockCutoff a b)
        (Complex.contDiff_logarithmicPhase_integerBlockCutoffFunction
          t a b ha hab)
        (Real.hasCompactSupport_integerBlockCutoff a b)
        m
  exact
    hsamples.symm.trans
      (hreconstruction.trans (tsum_congr hmode))

theorem Complex.summable_logarithmicPhase_integerBlockFourierPacket_sequence
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Summable (fun m : ℤ =>
      Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m) := by
  let extension : SchwartzMap ℝ ℂ :=
    Complex.logarithmicPhaseIntegerBlockSchwartz t a b ha hab
  have hsum :=
    Complex.summable_logarithmicPhase_integerBlockFourierPacket extension
  have hmode :
      ∀ m : ℤ,
        SchwartzMap.fourierTransformCLM ℝ extension (m : ℝ) =
          Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m := by
    intro m
    exact
      Complex.fourierTransform_phaseCutoffSchwartzOfSmoothProduct_eq_frequencyTwistIntegral
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.integerBlockCutoff a b)
        (Complex.contDiff_logarithmicPhase_integerBlockCutoffFunction
          t a b ha hab)
        (Real.hasCompactSupport_integerBlockCutoff a b)
        m
  exact hsum.congr hmode

theorem Complex.logarithmicPhase_integerBlockFourierPacket_sequence_isBigO_inverse_square
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (fun m : ℤ =>
      Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m) =O[Filter.cofinite]
      (fun m : ℤ => ‖(m : ℝ)‖ ^ (-2 : ℝ)) := by
  let extension : SchwartzMap ℝ ℂ :=
    Complex.logarithmicPhaseIntegerBlockSchwartz t a b ha hab
  have hdecay :
      (SchwartzMap.fourierTransformCLM ℝ extension) =O[Filter.cocompact ℝ]
        (fun x : ℝ => ‖x‖ ^ (-2 : ℝ)) := by
    exact (SchwartzMap.fourierTransformCLM ℝ extension).isBigO_cocompact_rpow (-2)
  have hdecay_integer :
      (fun m : ℤ => SchwartzMap.fourierTransformCLM ℝ extension (m : ℝ)) =O[Filter.cofinite]
        (fun m : ℤ => ‖(m : ℝ)‖ ^ (-2 : ℝ)) := by
    exact hdecay.comp_tendsto Int.tendsto_coe_cofinite
  have hmode :
      ∀ m : ℤ,
        SchwartzMap.fourierTransformCLM ℝ extension (m : ℝ) =
          Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m := by
    intro m
    exact
      Complex.fourierTransform_phaseCutoffSchwartzOfSmoothProduct_eq_frequencyTwistIntegral
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.integerBlockCutoff a b)
        (Complex.contDiff_logarithmicPhase_integerBlockCutoffFunction
          t a b ha hab)
        (Real.hasCompactSupport_integerBlockCutoff a b)
        m
  exact hdecay_integer.congr_left hmode

theorem Complex.logarithmicPhase_integerBlockFourierPacket_sequence_eventually_le_inverse_square
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∃ C : ℝ, ∀ᶠ m : ℤ in Filter.cofinite,
      ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ C * ‖(m : ℝ)‖ ^ (-2 : ℝ) := by
  rcases
      (Asymptotics.isBigO_iff.mp
        (Complex.logarithmicPhase_integerBlockFourierPacket_sequence_isBigO_inverse_square
          t a b ha hab)) with
    ⟨C, hC⟩
  refine ⟨C, hC.mono (fun m hm => ?_)⟩
  exact
    hm.trans_eq
      (congrArg (fun value : ℝ => C * value)
        (Real.norm_of_nonneg (Real.rpow_nonneg _ _)))

theorem Complex.logarithmicPhase_integerBlockFourierPacket_sequence_finite_exception_inverse_square
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∃ C : ℝ, ∃ exceptional : Set ℤ,
      exceptional.Finite ∧
        ∀ m : ℤ, m ∉ exceptional →
          ‖Complex.integerBlockFourierPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m‖ ≤ C * ‖(m : ℝ)‖ ^ (-2 : ℝ) := by
  rcases
      Complex.logarithmicPhase_integerBlockFourierPacket_sequence_eventually_le_inverse_square
        t a b ha hab with
    ⟨C, hC⟩
  let exceptional : Set ℤ :=
    {m : ℤ |
      ¬ (‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤ C * ‖(m : ℝ)‖ ^ (-2 : ℝ))}
  have hexceptional_finite : exceptional.Finite := by
    change {m : ℤ |
      ¬ (‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤ C * ‖(m : ℝ)‖ ^ (-2 : ℝ))}.Finite
    exact Filter.eventually_cofinite.mp hC
  refine ⟨C, exceptional, hexceptional_finite, ?_⟩
  intro m hm
  change ¬ ¬ (‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤ C * ‖(m : ℝ)‖ ^ (-2 : ℝ)) at hm
  exact Classical.byContradiction (fun hfalse => hm hfalse)

end

end LFunctions
end Boundary
