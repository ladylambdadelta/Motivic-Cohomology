import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusBase.Owner
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Boundary

open Real Complex Set MeasureTheory
open AddCircle

noncomputable section

section Mellin

/-- The weighted integrand norm is continuous on the full product. -/
theorem continuous_weightedLaplaceKernel_norm
    (φ : LFunctions.ZetaTestFunction) :
    ContinuousOn
      (fun p : ℂ × ℝ => ‖(p.2 : ℂ) * φ p.2 * Complex.exp (p.1 * p.2)‖)
      ((Set.univ : Set (ℂ × ℝ))) := by
  exact (continuous_weightedLaplaceIntegrand φ).norm.continuousOn

/-- The weighted integrand norm is continuous on the closed-ball/support product. -/
theorem continuousOn_weightedLaplaceKernel_norm_on_closedBall_support
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    ContinuousOn
      (fun p : ℂ × ℝ => ‖(p.2 : ℂ) * φ p.2 * Complex.exp (p.1 * p.2)‖)
      ((Metric.closedBall z 1 : Set ℂ) ×ˢ (tsupport φ)) := by
  have hfull := continuous_weightedLaplaceKernel_norm φ
  exact hfull.mono (by
    intro p hp
    exact mem_univ p)

/-- The closed-ball/support product is compact. -/
theorem isCompact_closedBall_prod_tsupport
    (φ : LFunctions.ZetaTestFunction) (hφ : HasCompactSupport φ) (z : ℂ) :
    IsCompact ((Metric.closedBall z 1 : Set ℂ) ×ˢ (tsupport φ)) := by
  exact (isCompact_closedBall z 1).prod hφ.isCompact

/-- The weighted integrand norm admits a uniform bound on the closed-ball/support product. -/
theorem exists_uniform_bound_weightedLaplaceKernel_norm_on_closedBall_support
    (φ : LFunctions.ZetaTestFunction) (hφ : HasCompactSupport φ) (z : ℂ) :
    ∃ C : ℝ, ∀ p ∈ ((Metric.closedBall z 1 : Set ℂ) ×ˢ (tsupport φ)),
      ‖(p.2 : ℂ) * φ p.2 * Complex.exp (p.1 * p.2)‖ ≤ C := by
  have hcomp := isCompact_closedBall_prod_tsupport φ hφ z
  have hbdd :
      BddAbove
        ((fun p : ℂ × ℝ => ‖(p.2 : ℂ) * φ p.2 * Complex.exp (p.1 * p.2)‖) ''
          ((Metric.closedBall z 1 : Set ℂ) ×ˢ (tsupport φ))) := by
    exact (hcomp.image_of_continuousOn
      (continuousOn_weightedLaplaceKernel_norm_on_closedBall_support φ z)).bddAbove
  rcases hbdd with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro p hp
  exact hC (show ‖(p.2 : ℂ) * φ p.2 * Complex.exp (p.1 * p.2)‖ ∈
    (fun p : ℂ × ℝ => ‖(p.2 : ℂ) * φ p.2 * Complex.exp (p.1 * p.2)‖) ''
      ((Metric.closedBall z 1 : Set ℂ) ×ˢ (tsupport φ)) from
    ⟨p, hp, rfl⟩)

/-- The weighted Laplace derivative kernel is uniformly bounded on a fixed closed ball. -/
theorem weightedLaplaceKernel_uniform_bound_on_closedBall_exists
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    ∃ C : ℝ, ∀ w : ℂ, w ∈ Metric.closedBall z 1 →
      ∀ t : ℝ, t ∈ tsupport φ.toZetaTestFunction' →
        ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_bound_weightedLaplaceKernel_norm_on_closedBall_support
      (φ := φ.toZetaTestFunction') φ.toZetaTestFunction.hasCompactSupport z
  refine ⟨C, ?_⟩
  intro w hw t ht
  exact hC (w, t) ⟨hw, ht⟩

/-- The bump constant used in the support bounds is strictly positive. -/
theorem weightedLaplaceKernel_positive_bump (C : ℝ) : 0 < max C 0 + 1 := by
  have h1 : (0 : ℝ) < 1 := zero_lt_one
  exact add_pos_of_nonneg_of_pos (le_max_right C 0) h1

/-- The support bound is increased from `C` to the bump constant by a single monotonicity step. -/
theorem weightedLaplaceKernel_bound_le_bump (C : ℝ) {x : ℝ} (hx : x ≤ C) :
    x ≤ max C 0 + 1 := by
  have hCmax : C ≤ max C 0 := le_max_left C 0
  have hle' : max C 0 ≤ max C 0 + 1 := by
    exact le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 from zero_le_one)
  exact le_trans hx (le_trans hCmax hle')

/-- The weighted Laplace derivative kernel is uniformly bounded on a fixed closed ball with a positive constant. -/
theorem weightedLaplaceKernel_uniform_bound_on_closedBall
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z 1 →
      ∀ t : ℝ, t ∈ tsupport φ.toZetaTestFunction' →
        ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ C := by
  rcases weightedLaplaceKernel_uniform_bound_on_closedBall_exists (φ := φ) z with ⟨C, hC⟩
  refine ⟨max C 0 + 1, weightedLaplaceKernel_positive_bump C, ?_⟩
  intro w hw t ht
  have hbound : ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ C := by
    exact hC w hw t ht
  exact weightedLaplaceKernel_bound_le_bump C hbound

/-- A pointwise support bound used to keep the almost-everywhere theorem direct. -/
theorem weightedLaplaceKernel_bound_pointwise_on_support_of_mem
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) (C : ℝ)
    (hC : ∀ w : ℂ, w ∈ Metric.closedBall z 1 →
      ∀ t : ℝ, t ∈ tsupport φ.toZetaTestFunction' →
        ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ C)
    {t : ℝ} (ht : t ∈ tsupport φ.toZetaTestFunction') :
    ∀ w ∈ Metric.ball z 1,
      ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ max C 0 + 1 := by
  intro w hw
  have hw' : w ∈ Metric.closedBall z 1 := Metric.mem_closedBall.2 (le_of_lt hw)
  have hbound : ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ C := by
    exact hC w hw' t ht
  exact weightedLaplaceKernel_bound_le_bump C hbound

/-- The inside-the-ball support bound is a direct coercion from the closed-ball bound. -/
theorem weightedLaplaceKernel_bound_pointwise_on_support_of_mem_ball
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) (C : ℝ)
    (hC : ∀ w : ℂ, w ∈ Metric.closedBall z 1 →
      ∀ t : ℝ, t ∈ tsupport φ.toZetaTestFunction' →
        ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ C)
    {t : ℝ} (ht : t ∈ tsupport φ.toZetaTestFunction')
    {w : ℂ} (hw : w ∈ Metric.ball z 1) :
    ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ max C 0 + 1 := by
  have hw' : w ∈ Metric.closedBall z 1 := Metric.mem_closedBall.2 (le_of_lt hw)
  have hbound : ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ C := by
    exact hC w hw' t ht
  exact weightedLaplaceKernel_bound_le_bump C hbound

/-- The off-support pointwise bound is a direct zero-kernel estimate. -/
theorem weightedLaplaceKernel_bound_pointwise_on_support_of_nmem_bump
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) (C : ℝ)
    {t : ℝ} (ht : t ∉ tsupport φ.toZetaTestFunction') :
    ∀ w ∈ Metric.ball z 1,
      ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ max C 0 + 1 := by
  intro w _
  have hzero : φ.toZetaTestFunction' t = 0 := image_eq_zero_of_nmem_tsupport ht
  calc
    ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖
        = ‖(t : ℂ) * 0 * Complex.exp (w * t)‖ := by
            exact congrArg (fun x => ‖(t : ℂ) * x * Complex.exp (w * t)‖) hzero
    _ = ‖(0 : ℂ)‖ := by
          exact congrArg norm
            (calc
              (t : ℂ) * 0 * Complex.exp (w * t) =
                  0 * Complex.exp (w * t) := by
                exact congrArg (fun z : ℂ => z * Complex.exp (w * t))
                  (mul_zero (t : ℂ))
              _ = 0 := zero_mul (Complex.exp (w * t)))
    _ = 0 := norm_zero
    _ ≤ max C 0 + 1 := by
          exact add_nonneg (le_max_right C 0) zero_le_one

theorem weightedLaplaceKernel_bound_pointwise_on_support_of_nmem
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) (C : ℝ)
    {t : ℝ} (ht : t ∉ tsupport φ.toZetaTestFunction') :
    ∀ w ∈ Metric.ball z 1,
      ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ max C 0 + 1 := by
  exact weightedLaplaceKernel_bound_pointwise_on_support_of_nmem_bump φ z C ht

theorem weightedLaplaceKernel_bound_pointwise_on_support
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) (C : ℝ)
    (hC : ∀ w : ℂ, w ∈ Metric.closedBall z 1 →
      ∀ t : ℝ, t ∈ tsupport φ.toZetaTestFunction' →
        ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ C)
    (t : ℝ) :
    ∀ w ∈ Metric.ball z 1,
      ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ max C 0 + 1 := by
  intro w hw
  by_cases ht : t ∈ tsupport φ.toZetaTestFunction'
  · exact weightedLaplaceKernel_bound_pointwise_on_support_of_mem φ z C hC ht w hw
  · exact weightedLaplaceKernel_bound_pointwise_on_support_of_nmem φ z C ht w hw

/-- The weighted Laplace kernel is bounded on a closed ball with the support restriction built in. -/
theorem weightedLaplaceKernel_bound_on_support
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᵐ t : ℝ ∂(volume : Measure ℝ), ∀ w ∈ Metric.ball z 1,
        ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ C := by
  rcases weightedLaplaceKernel_uniform_bound_on_closedBall (φ := φ) z with ⟨C, _, hC⟩
  refine ⟨max C 0 + 1, weightedLaplaceKernel_positive_bump C, ?_⟩
  exact Filter.Eventually.of_forall fun t : ℝ =>
    weightedLaplaceKernel_bound_pointwise_on_support φ z C hC t

/-- The exponential kernel differentiated in the spectral variable. -/
theorem hasDerivAt_laplaceKernel_exp
    (t : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (w * t))
      (Complex.exp (z * t) * (t : ℂ)) z := by
  have hmul : HasDerivAt (fun w : ℂ => w * (t : ℂ)) (t : ℂ) z := hasDerivAt_mul_const (t : ℂ)
  exact (Complex.hasDerivAt_exp (z * t)).comp z hmul

/-- The derivative of the constant-times-exponential kernel before normalization. -/
theorem hasDerivAt_laplaceKernel_const_mul_exp_core
    (φ : LFunctions.ZetaTestFunction) (t : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => φ t * Complex.exp (w * t))
      ((t : ℂ) * φ t * Complex.exp (z * t)) z := by
  have hconst : HasDerivAt (fun w : ℂ => φ t) 0 z := hasDerivAt_const z (φ t)
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (w * t))
      (Complex.exp (z * t) * (t : ℂ)) z := hasDerivAt_laplaceKernel_exp t z
  have hprodRaw : HasDerivAt (fun w : ℂ => φ t * Complex.exp (w * t))
      (0 * (Complex.exp (z * t) * (t : ℂ)) + φ t * (Complex.exp (z * t) * (t : ℂ))) z := by
    exact hconst.mul hexp
  have htarget :
      0 * (Complex.exp (z * t) * (t : ℂ)) +
          φ t * (Complex.exp (z * t) * (t : ℂ)) =
        (t : ℂ) * φ t * Complex.exp (z * t) := by
    calc
      0 * (Complex.exp (z * t) * (t : ℂ)) +
          φ t * (Complex.exp (z * t) * (t : ℂ)) =
          0 + φ t * (Complex.exp (z * t) * (t : ℂ)) := by
        exact congrArg
          (fun y : ℂ => y + φ t * (Complex.exp (z * t) * (t : ℂ)))
          (zero_mul (Complex.exp (z * t) * (t : ℂ)))
      _ = φ t * (Complex.exp (z * t) * (t : ℂ)) := zero_add _
      _ = φ t * ((t : ℂ) * Complex.exp (z * t)) := by
        exact congrArg (fun y : ℂ => φ t * y)
          (mul_comm (Complex.exp (z * t)) (t : ℂ))
      _ = (φ t * (t : ℂ)) * Complex.exp (z * t) :=
        mul_assoc (φ t) (t : ℂ) (Complex.exp (z * t))
      _ = ((t : ℂ) * φ t) * Complex.exp (z * t) := by
        exact congrArg (fun y : ℂ => y * Complex.exp (z * t))
          (mul_comm (φ t) (t : ℂ))
      _ = (t : ℂ) * φ t * Complex.exp (z * t) := rfl
  exact Eq.subst
    (motive := fun d : ℂ =>
      HasDerivAt (fun w : ℂ => φ t * Complex.exp (w * t)) d z)
    htarget hprodRaw

/-- The weighted Laplace kernel has the expected pointwise derivative in the spectral variable. -/
theorem hasDerivAt_weightedLaplaceKernel
    (φ : LFunctions.ZetaTestFunction) (t : ℝ) (z : ℂ) :
    HasDerivAt (fun x : ℂ => φ t * Complex.exp (x * t))
      ((t : ℂ) * φ t * Complex.exp (z * t)) z := by
  exact hasDerivAt_laplaceKernel_const_mul_exp_core φ t z

/-- The weighted Laplace kernel admits an almost-everywhere uniform bound on a spectral ball. -/
theorem weightedLaplaceKernel_bound_ae
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᵐ t : ℝ ∂(volume : Measure ℝ), ∀ w ∈ Metric.ball z 1,
        ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ C := by
  rcases weightedLaplaceKernel_bound_on_support φ z with ⟨C, hCpos, hC⟩
  exact ⟨C, hCpos, hC⟩

/-- The support-indicator constant bound is integrable because the support is compact. -/
theorem integrable_support_indicator_const
    (φ : LFunctions.ZetaAdmissibleFunction) (C : ℝ) :
    Integrable (Set.indicator (tsupport φ.toZetaTestFunction') (fun _ : ℝ => C))
      (volume : Measure ℝ) := by
  exact
    (integrable_indicator_iff (isClosed_tsupport _).measurableSet).2
      (integrableOn_const.2 <| Or.inr <|
        φ.toZetaTestFunction.hasCompactSupport.measure_lt_top)

/-- The support bound is captured by the support indicator, pointwise almost everywhere. -/
theorem weightedLaplaceKernel_bound_on_support_indicator
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) (C : ℝ)
    (hdom :
      ∀ᵐ t : ℝ ∂(volume : Measure ℝ), ∀ w ∈ Metric.ball z 1,
        ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ C) :
    ∀ᵐ t : ℝ ∂(volume : Measure ℝ), ∀ w ∈ Metric.ball z 1,
      ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖
        ≤ Set.indicator (tsupport φ.toZetaTestFunction') (fun _ : ℝ => C) t := by
  refine hdom.mono ?_
  intro t ht w hw
  by_cases hts : t ∈ tsupport φ.toZetaTestFunction'
  · calc
      ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖
          ≤ C := ht w hw
      _ =
          Set.indicator (tsupport φ.toZetaTestFunction') (fun _ : ℝ => C) t := by
            exact (Set.indicator_of_mem hts (fun _ : ℝ => C)).symm
  · have hzero : φ.toZetaTestFunction' t = 0 := image_eq_zero_of_nmem_tsupport hts
    calc
      ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖
          = ‖(t : ℂ) * 0 * Complex.exp (w * t)‖ := by
              exact congrArg (fun x => ‖(t : ℂ) * x * Complex.exp (w * t)‖) hzero
      _ = ‖(0 : ℂ)‖ := by
            exact congrArg norm
              (calc
                (t : ℂ) * 0 * Complex.exp (w * t) =
                    0 * Complex.exp (w * t) := by
                  exact congrArg (fun z : ℂ => z * Complex.exp (w * t))
                    (mul_zero (t : ℂ))
                _ = 0 := zero_mul (Complex.exp (w * t)))
      _ = 0 := norm_zero
      _ ≤ 0 := by
            exact le_rfl
      _ =
          Set.indicator (tsupport φ.toZetaTestFunction') (fun _ : ℝ => C) t := by
            exact (Set.indicator_of_not_mem hts (fun _ : ℝ => C)).symm

/-- The zeta Laplace transform is differentiable at every spectral parameter. -/
theorem aestronglyMeasurable_laplaceKernel_eventually
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    ∀ᶠ w in nhds z, AEStronglyMeasurable (fun t : ℝ => φ.toZetaTestFunction' t * Complex.exp (w * t))
      (volume : Measure ℝ) :=
  Filter.Eventually.of_forall fun w =>
    aestronglyMeasurable_laplaceKernel φ.toZetaTestFunction' w

theorem integrable_laplaceKernel_at
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    Integrable (fun t : ℝ => φ.toZetaTestFunction' t * Complex.exp (z * t))
      (volume : Measure ℝ) :=
  integrable_laplaceKernel_of_hasCompactSupport
    φ.toZetaTestFunction' z φ.toZetaTestFunction.hasCompactSupport

theorem aestronglyMeasurable_weightedLaplaceKernel_at
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (z * t))
      (volume : Measure ℝ) :=
  aestronglyMeasurable_weightedLaplaceKernel φ.toZetaTestFunction' z

theorem hasDerivAt_weightedLaplaceKernel_eventually
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ w ∈ Metric.ball z 1,
      HasDerivAt (fun x : ℂ => φ.toZetaTestFunction' t * Complex.exp (x * t))
        ((t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)) w :=
  Filter.Eventually.of_forall fun t : ℝ => fun w _ =>
    hasDerivAt_weightedLaplaceKernel φ.toZetaTestFunction' t w

theorem zetaLaplaceTransform_differentiableAt_of_bound_data
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) (_C : ℝ)
    (bound : ℝ → ℝ)
    (hF_meas :
      ∀ᶠ w in nhds z, AEStronglyMeasurable (fun t : ℝ => φ.toZetaTestFunction' t * Complex.exp (w * t))
        (volume : Measure ℝ))
    (hF_int :
      Integrable (fun t : ℝ => φ.toZetaTestFunction' t * Complex.exp (z * t)) (volume : Measure ℝ))
    (hF'_meas :
      AEStronglyMeasurable (fun t : ℝ => (t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (z * t))
        (volume : Measure ℝ))
    (hdom :
      ∀ᵐ t : ℝ ∂(volume : Measure ℝ), ∀ w ∈ Metric.ball z 1,
        ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ bound t)
    (hbound_int : Integrable bound (volume : Measure ℝ))
    (h_diff :
      ∀ᵐ t : ℝ ∂(volume : Measure ℝ), ∀ w ∈ Metric.ball z 1,
        HasDerivAt (fun x : ℂ => φ.toZetaTestFunction' t * Complex.exp (x * t))
          ((t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)) w) :
    DifferentiableAt ℂ (fun w => zetaLaplaceTransform φ.toZetaTestFunction' w) z := by
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (ε_pos := by positivity) hF_meas hF_int
      hF'_meas hdom hbound_int h_diff
  unfold zetaLaplaceTransform
  exact h.2.differentiableAt

theorem zetaLaplaceTransform_differentiableAt_of_bound
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) (C : ℝ)
    (_hCpos : 0 < C)
    (hdom :
      ∀ᵐ t : ℝ ∂(volume : Measure ℝ), ∀ w ∈ Metric.ball z 1,
        ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ C) :
    DifferentiableAt ℂ (fun w => zetaLaplaceTransform φ.toZetaTestFunction' w) z := by
  have hF_meas := aestronglyMeasurable_laplaceKernel_eventually φ z
  have hF_int := integrable_laplaceKernel_at φ z
  have hF'_meas := aestronglyMeasurable_weightedLaplaceKernel_at φ z
  have h_diff := hasDerivAt_weightedLaplaceKernel_eventually φ z
  have hbound_int := integrable_support_indicator_const φ C
  have hdom' := weightedLaplaceKernel_bound_on_support_indicator φ z C hdom
  exact zetaLaplaceTransform_differentiableAt_of_bound_data
    φ z C (Set.indicator (tsupport φ.toZetaTestFunction') (fun _ : ℝ => C))
    hF_meas hF_int hF'_meas hdom' hbound_int h_diff

theorem zetaLaplaceTransform_differentiableAt
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    DifferentiableAt ℂ (fun w => zetaLaplaceTransform φ.toZetaTestFunction' w) z := by
  rcases weightedLaplaceKernel_bound_ae (φ := φ) z with ⟨C, hCpos, hdom⟩
  exact zetaLaplaceTransform_differentiableAt_of_bound φ z C hCpos hdom

end Mellin
