import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.RectangleAlgebra.Owner

/-!
# Paley-Wiener zero-order kernel bounds

This file owns the zero-order Paley-Wiener kernel envelope, support/interval
indicator majorants, volume normalization, and the zero-order compact-support
Laplace-transform estimate. It is copy-first extracted from the current
Paley-Wiener owner file and is not imported by that parent yet, so declaration
names intentionally match the existing owner surface.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ZetaAdmissibleFunction

/-- The pointwise raw kernel envelope before multiplying by support length. -/
noncomputable def zetaPaleyWienerRawKernelEnvelope
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) : ℝ :=
  zetaPaleyWienerSupportNormEnvelope f *
    zetaPaleyWienerStripExponentialEnvelope I a b

/-- The raw kernel envelope is nonnegative. -/
theorem zetaPaleyWienerRawKernelEnvelope_nonnegative
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    0 ≤ zetaPaleyWienerRawKernelEnvelope f I a b := by
  unfold zetaPaleyWienerRawKernelEnvelope
  exact mul_nonneg
    (zetaPaleyWienerSupportNormEnvelope_nonnegative f)
    (le_of_lt (zetaPaleyWienerStripExponentialEnvelope_pos I a b))

/-- Pointwise kernel domination on the compact support interval. -/
theorem zetaLaplaceKernel_norm_le_rawEnvelope_on_support
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∀ z : ℂ,
      zetaPaleyWienerInVerticalStrip a b z →
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ))‖ ≤
          zetaPaleyWienerRawKernelEnvelope f I a b := by
  intro z hz t ht
  have hsource :
      ‖f.toZetaTestFunction' t‖ ≤ zetaPaleyWienerSupportNormEnvelope f :=
    zetaPaleyWienerTestFunctionNorm_le_envelope f t ht
  have hexp :
      ‖Complex.exp (z * (t : ℂ))‖ ≤
        zetaPaleyWienerStripExponentialEnvelope I a b :=
    zetaPaleyWienerStripExponential_norm_le_envelope
      f I a b z hz t (I.lower_mem t ht) (I.upper_mem t ht)
  have hsourceEnvelope_nonneg :
      0 ≤ zetaPaleyWienerSupportNormEnvelope f :=
    zetaPaleyWienerSupportNormEnvelope_nonnegative f
  have hexp_norm_nonneg :
      0 ≤ ‖Complex.exp (z * (t : ℂ))‖ :=
    norm_nonneg (Complex.exp (z * (t : ℂ)))
  have hproduct :
      ‖f.toZetaTestFunction' t‖ *
          ‖Complex.exp (z * (t : ℂ))‖ ≤
        zetaPaleyWienerSupportNormEnvelope f *
          zetaPaleyWienerStripExponentialEnvelope I a b :=
    mul_le_mul hsource hexp hexp_norm_nonneg hsourceEnvelope_nonneg
  have hnorm :
      ‖f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ))‖ =
        ‖f.toZetaTestFunction' t‖ *
          ‖Complex.exp (z * (t : ℂ))‖ :=
    norm_mul (f.toZetaTestFunction' t) (Complex.exp (z * (t : ℂ)))
  unfold zetaPaleyWienerRawKernelEnvelope
  exact Eq.subst
    (motive := fun v : ℝ =>
      v ≤ zetaPaleyWienerSupportNormEnvelope f *
        zetaPaleyWienerStripExponentialEnvelope I a b)
    hnorm.symm
    hproduct

/-- The Paley-Wiener Laplace kernel at a fixed spectral parameter. -/
noncomputable def zetaPaleyWienerLaplaceKernel
    (f : ZetaAdmissibleFunction) (z : ℂ) (t : ℝ) : ℂ :=
  f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ))

/-- The named Paley-Wiener kernel integrates to the zeta Laplace transform. -/
theorem zetaPaleyWienerLaplaceKernel_integral_eq_transform
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    (∫ t : ℝ, zetaPaleyWienerLaplaceKernel f z t) =
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' z := by
  rfl

/-- The named Paley-Wiener Laplace kernel is integrable. -/
theorem zetaPaleyWienerLaplaceKernel_integrable
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    Integrable (fun t : ℝ => zetaPaleyWienerLaplaceKernel f z t) :=
  integrable_laplaceKernel_at f z

/-- The pointwise norm of the named Paley-Wiener Laplace kernel is integrable. -/
theorem zetaPaleyWienerLaplaceKernel_norm_integrable
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    Integrable (fun t : ℝ => ‖zetaPaleyWienerLaplaceKernel f z t‖) :=
  (zetaPaleyWienerLaplaceKernel_integrable f z).norm

/-- Norm of an integrable complex-valued integral is bounded by the integral of its norm. -/
theorem complex_norm_integral_le_integral_norm_of_integrable
    (g : ℝ → ℂ) (_hg : Integrable g) :
    ‖∫ t : ℝ, g t‖ ≤ ∫ t : ℝ, ‖g t‖ :=
  MeasureTheory.norm_integral_le_integral_norm g

/-- The norm of the named Paley-Wiener kernel integral is bounded by the integral of the
pointwise kernel norm. -/
theorem zetaPaleyWienerLaplaceKernel_norm_integral_le_integral_norm
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    ‖∫ t : ℝ, zetaPaleyWienerLaplaceKernel f z t‖ ≤
      ∫ t : ℝ, ‖zetaPaleyWienerLaplaceKernel f z t‖ := by
  exact complex_norm_integral_le_integral_norm_of_integrable
    (fun t : ℝ => zetaPaleyWienerLaplaceKernel f z t)
    (zetaPaleyWienerLaplaceKernel_integrable f z)

/-- The constant support-indicator majorant used for the real-line integral bound. -/
noncomputable def zetaPaleyWienerSupportIndicatorBound
    (f : ZetaAdmissibleFunction) (B : ℝ) : ℝ → ℝ :=
  Set.indicator (tsupport f.toZetaTestFunction) (fun _ : ℝ => B)

/-- The constant interval-indicator majorant attached to a Paley-Wiener support interval. -/
noncomputable def zetaPaleyWienerIntervalIndicatorBound
    {f : ZetaAdmissibleFunction}
    (I : ZetaPaleyWienerSupportInterval f) (B : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Icc I.lower I.upper) (fun _ : ℝ => B)

/-- A constant indicator on a compact real set is integrable. -/
theorem real_integrable_const_indicator_of_isCompact
    (K : Set ℝ) (hK : IsCompact K) (B : ℝ) :
    Integrable (Set.indicator K (fun _ : ℝ => B)) :=
  (integrable_indicator_iff hK.isClosed.measurableSet).2
    (integrableOn_const.2 (Or.inr hK.measure_lt_top))

/-- The certified support of an admissible source is compact. -/
theorem zetaPaleyWienerSupport_isCompact
    (f : ZetaAdmissibleFunction) :
    IsCompact (tsupport f.toZetaTestFunction) :=
  f.toZetaTestFunction.hasCompactSupport.isCompact

/-- A closed real interval is compact. -/
theorem real_Icc_isCompact
    (lower upper : ℝ) :
    IsCompact (Set.Icc lower upper) :=
  isCompact_Icc

/-- The compact-support indicator bound is integrable. -/
theorem zetaPaleyWienerSupportIndicatorBound_integrable
    (f : ZetaAdmissibleFunction) (B : ℝ) :
    Integrable (zetaPaleyWienerSupportIndicatorBound f B) :=
  real_integrable_const_indicator_of_isCompact
    (tsupport f.toZetaTestFunction)
    (zetaPaleyWienerSupport_isCompact f)
    B

/-- The interval indicator bound is integrable. -/
theorem zetaPaleyWienerIntervalIndicatorBound_integrable
    {f : ZetaAdmissibleFunction}
    (I : ZetaPaleyWienerSupportInterval f) (B : ℝ) :
    Integrable (zetaPaleyWienerIntervalIndicatorBound I B) :=
  real_integrable_const_indicator_of_isCompact
    (Set.Icc I.lower I.upper)
    (real_Icc_isCompact I.lower I.upper)
    B

/-- The certified support is contained in the certified interval. -/
theorem zetaPaleyWienerSupport_subset_interval
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f) :
    tsupport f.toZetaTestFunction ⊆ Set.Icc I.lower I.upper := by
  intro t ht
  exact ⟨I.lower_mem t ht, I.upper_mem t ht⟩

/-- The support-indicator bound is pointwise dominated by the containing-interval
indicator bound. -/
theorem zetaPaleyWienerSupportIndicatorBound_le_intervalIndicatorBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (B : ℝ) (hB_nonneg : 0 ≤ B) :
    ∀ t : ℝ,
      zetaPaleyWienerSupportIndicatorBound f B t ≤
        zetaPaleyWienerIntervalIndicatorBound I B t := by
  intro t
  by_cases hsupport : t ∈ tsupport f.toZetaTestFunction
  · have hinterval : t ∈ Set.Icc I.lower I.upper :=
      zetaPaleyWienerSupport_subset_interval f I hsupport
    have hsupport_value :
        zetaPaleyWienerSupportIndicatorBound f B t = B := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_mem hsupport (fun _ : ℝ => B)
    have hinterval_value :
        zetaPaleyWienerIntervalIndicatorBound I B t = B := by
      unfold zetaPaleyWienerIntervalIndicatorBound
      exact Set.indicator_of_mem hinterval (fun _ : ℝ => B)
    exact Eq.subst
      (motive := fun v : ℝ => v ≤ zetaPaleyWienerIntervalIndicatorBound I B t)
      hsupport_value.symm
      (Eq.subst
        (motive := fun v : ℝ => B ≤ v)
        hinterval_value.symm
        le_rfl)
  · have hsupport_value :
        zetaPaleyWienerSupportIndicatorBound f B t = 0 := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_not_mem hsupport (fun _ : ℝ => B)
    by_cases hinterval : t ∈ Set.Icc I.lower I.upper
    · have hinterval_value :
          zetaPaleyWienerIntervalIndicatorBound I B t = B := by
        unfold zetaPaleyWienerIntervalIndicatorBound
        exact Set.indicator_of_mem hinterval (fun _ : ℝ => B)
      exact Eq.subst
        (motive := fun v : ℝ => v ≤ zetaPaleyWienerIntervalIndicatorBound I B t)
        hsupport_value.symm
        (Eq.subst
          (motive := fun v : ℝ => 0 ≤ v)
          hinterval_value.symm
          hB_nonneg)
    · have hinterval_value :
          zetaPaleyWienerIntervalIndicatorBound I B t = 0 := by
        unfold zetaPaleyWienerIntervalIndicatorBound
        exact Set.indicator_of_not_mem hinterval (fun _ : ℝ => B)
      exact Eq.subst
        (motive := fun v : ℝ => v ≤ zetaPaleyWienerIntervalIndicatorBound I B t)
        hsupport_value.symm
        (Eq.subst
          (motive := fun v : ℝ => 0 ≤ v)
          hinterval_value.symm
          le_rfl)

/-- The Laplace kernel is zero off the source support. -/
theorem zetaPaleyWienerLaplaceKernel_eq_zero_of_not_mem_support
    (f : ZetaAdmissibleFunction) (z : ℂ) {t : ℝ}
    (ht : t ∉ tsupport f.toZetaTestFunction) :
    zetaPaleyWienerLaplaceKernel f z t = 0 := by
  have hsource : f.toZetaTestFunction t = 0 :=
    image_eq_zero_of_nmem_tsupport ht
  have htest :
      f.toZetaTestFunction' t = f.toZetaTestFunction t :=
    ZetaAdmissibleFunction.toZetaTestFunction'_apply f t
  unfold zetaPaleyWienerLaplaceKernel
  calc
    f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ))
        = f.toZetaTestFunction t * Complex.exp (z * (t : ℂ)) := by
          exact congrArg
            (fun v : ℂ => v * Complex.exp (z * (t : ℂ)))
            htest
    _ = 0 * Complex.exp (z * (t : ℂ)) := by
          exact congrArg
            (fun v : ℂ => v * Complex.exp (z * (t : ℂ)))
            hsource
    _ = 0 := zero_mul (Complex.exp (z * (t : ℂ)))

/-- A pointwise support bound induces domination by the constant support indicator. -/
theorem zetaPaleyWienerLaplaceKernel_norm_le_supportIndicatorBound
    (f : ZetaAdmissibleFunction) (z : ℂ) (B : ℝ)
    (hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerLaplaceKernel f z t‖ ≤ B) :
    ∀ t : ℝ,
      ‖zetaPaleyWienerLaplaceKernel f z t‖ ≤
        zetaPaleyWienerSupportIndicatorBound f B t := by
  intro t
  by_cases ht : t ∈ tsupport f.toZetaTestFunction
  · have hindicator :
        zetaPaleyWienerSupportIndicatorBound f B t = B := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_mem ht (fun _ : ℝ => B)
    exact Eq.subst
      (motive := fun v : ℝ => ‖zetaPaleyWienerLaplaceKernel f z t‖ ≤ v)
      hindicator.symm
      (hbound t ht)
  · have hkernel :
        zetaPaleyWienerLaplaceKernel f z t = 0 :=
      zetaPaleyWienerLaplaceKernel_eq_zero_of_not_mem_support f z ht
    have hindicator :
        zetaPaleyWienerSupportIndicatorBound f B t = 0 := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_not_mem ht (fun _ : ℝ => B)
    have hnorm_zero :
        ‖zetaPaleyWienerLaplaceKernel f z t‖ = 0 := by
      exact (congrArg (fun v : ℂ => ‖v‖) hkernel).trans norm_zero
    exact Eq.subst
      (motive := fun v : ℝ => v ≤ zetaPaleyWienerSupportIndicatorBound f B t)
      hnorm_zero.symm
      (Eq.subst
        (motive := fun v : ℝ => 0 ≤ v)
        hindicator.symm
        le_rfl)

/-- Real-line integral monotonicity for integrable pointwise domination. -/
theorem real_integral_mono_of_integrable_pointwise_le
    (u v : ℝ → ℝ)
    (hu : Integrable u) (hv : Integrable v)
    (hle : ∀ t : ℝ, u t ≤ v t) :
    (∫ t : ℝ, u t) ≤ ∫ t : ℝ, v t := by
  exact MeasureTheory.integral_mono hu hv hle

/-- Pointwise domination of the kernel norm by the support-indicator majorant passes to
real-line integrals. -/
theorem zetaPaleyWienerKernelNormIntegral_le_supportIndicatorIntegral
    (f : ZetaAdmissibleFunction) (z : ℂ) (B : ℝ)
    (hindicator :
      ∀ t : ℝ,
        ‖zetaPaleyWienerLaplaceKernel f z t‖ ≤
          zetaPaleyWienerSupportIndicatorBound f B t) :
    (∫ t : ℝ, ‖zetaPaleyWienerLaplaceKernel f z t‖) ≤
      ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t := by
  exact real_integral_mono_of_integrable_pointwise_le
    (fun t : ℝ => ‖zetaPaleyWienerLaplaceKernel f z t‖)
    (zetaPaleyWienerSupportIndicatorBound f B)
    (zetaPaleyWienerLaplaceKernel_norm_integrable f z)
    (zetaPaleyWienerSupportIndicatorBound_integrable f B)
    hindicator

/-- Integrating a support-indicator majorant bounds the norm of the real-line Laplace
integral. -/
theorem zetaLaplaceTransform_norm_le_supportIndicatorIntegral
    (f : ZetaAdmissibleFunction) (z : ℂ) (B : ℝ)
    (hindicator :
      ∀ t : ℝ,
        ‖zetaPaleyWienerLaplaceKernel f z t‖ ≤
          zetaPaleyWienerSupportIndicatorBound f B t) :
    ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
      ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t := by
  have hkernelIntegral :
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ =
        ‖∫ t : ℝ, zetaPaleyWienerLaplaceKernel f z t‖ := by
    exact congrArg (fun v : ℂ => ‖v‖)
      (zetaPaleyWienerLaplaceKernel_integral_eq_transform f z).symm
  have hnormIntegral :
      ‖∫ t : ℝ, zetaPaleyWienerLaplaceKernel f z t‖ ≤
        ∫ t : ℝ, ‖zetaPaleyWienerLaplaceKernel f z t‖ :=
    zetaPaleyWienerLaplaceKernel_norm_integral_le_integral_norm f z
  have hindicatorIntegral :
      (∫ t : ℝ, ‖zetaPaleyWienerLaplaceKernel f z t‖) ≤
        ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t :=
    zetaPaleyWienerKernelNormIntegral_le_supportIndicatorIntegral
      f z B hindicator
  exact Eq.subst
    (motive := fun v : ℝ =>
      v ≤ ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t)
    hkernelIntegral.symm
    (le_trans hnormIntegral hindicatorIntegral)

/-- Pointwise domination of the support indicator by the interval indicator passes to the
real-line integrals. -/
theorem zetaPaleyWienerSupportIndicatorIntegral_le_intervalIndicatorIntegral
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (B : ℝ) (_hB_nonneg : 0 ≤ B)
    (hpoint :
      ∀ t : ℝ,
        zetaPaleyWienerSupportIndicatorBound f B t ≤
          zetaPaleyWienerIntervalIndicatorBound I B t) :
    (∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t) ≤
      ∫ t : ℝ, zetaPaleyWienerIntervalIndicatorBound I B t := by
  exact real_integral_mono_of_integrable_pointwise_le
    (zetaPaleyWienerSupportIndicatorBound f B)
    (zetaPaleyWienerIntervalIndicatorBound I B)
    (zetaPaleyWienerSupportIndicatorBound_integrable f B)
    (zetaPaleyWienerIntervalIndicatorBound_integrable I B)
    hpoint

/-- The integral of a nonnegative constant over an interval indicator is constant times
the interval volume. -/
theorem real_integral_const_indicator_eq_setIntegral_const
    (K : Set ℝ) (hK : MeasurableSet K) (B : ℝ) :
    (∫ t : ℝ, Set.indicator K (fun _ : ℝ => B) t) =
      ∫ _ in K, B := by
  exact integral_indicator hK

/-- The set integral of a real constant is the constant times the set volume. -/
theorem real_setIntegral_const_eq_const_mul_volume
    (K : Set ℝ) (B : ℝ) :
    (∫ _ in K, B) = B * (volume K).toReal := by
  calc
    (∫ _ in K, B) = (volume K).toReal • B := by
      exact MeasureTheory.setIntegral_const B
    _ = (volume K).toReal * B := by
      rfl
    _ = B * (volume K).toReal := by
      exact mul_comm (volume K).toReal B

/-- The integral of a constant over a compact-set indicator is constant times volume. -/
theorem real_integral_const_indicator_of_isCompact_eq_const_mul_volume
    (K : Set ℝ) (hK : IsCompact K) (B : ℝ) :
    (∫ t : ℝ, Set.indicator K (fun _ : ℝ => B) t) =
      B * (volume K).toReal := by
  exact Eq.trans
    (real_integral_const_indicator_eq_setIntegral_const
      K hK.isClosed.measurableSet B)
    (real_setIntegral_const_eq_const_mul_volume K B)

/-- The integral of a nonnegative constant over an interval indicator is constant times
the interval volume. -/
theorem real_integral_const_indicator_Icc_eq_const_mul_volume
    (lower upper B : ℝ) (_hB_nonneg : 0 ≤ B) :
    (∫ t : ℝ, Set.indicator (Set.Icc lower upper) (fun _ : ℝ => B) t) =
      B * (volume (Set.Icc lower upper)).toReal := by
  exact real_integral_const_indicator_of_isCompact_eq_const_mul_volume
    (Set.Icc lower upper) (real_Icc_isCompact lower upper) B

/-- The interval-indicator integral is the constant times the interval volume. -/
theorem zetaPaleyWienerIntervalIndicatorIntegral_eq_bound_mul_volume
    {f : ZetaAdmissibleFunction}
    (I : ZetaPaleyWienerSupportInterval f) (B : ℝ) (hB_nonneg : 0 ≤ B) :
    (∫ t : ℝ, zetaPaleyWienerIntervalIndicatorBound I B t) =
      B * (volume (Set.Icc I.lower I.upper)).toReal := by
  unfold zetaPaleyWienerIntervalIndicatorBound
  exact real_integral_const_indicator_Icc_eq_const_mul_volume
    I.lower I.upper B hB_nonneg

/-- Ordered closed real interval volume in `toReal` form. -/
theorem real_volume_Icc_eq_ofReal_sub
    {lower upper : ℝ} (_hlu : lower ≤ upper) :
    volume (Set.Icc lower upper) = ENNReal.ofReal (upper - lower) := by
  exact Real.volume_Icc

/-- The `toReal` of a nonnegative real embedded in `ENNReal` is the original real. -/
theorem ennreal_toReal_ofReal_of_nonnegative
    {x : ℝ} (hx : 0 ≤ x) :
    (ENNReal.ofReal x).toReal = x := by
  exact ENNReal.toReal_ofReal hx

/-- Ordered closed real interval volume in `toReal` form. -/
theorem real_volume_Icc_toReal_eq_sub
    {lower upper : ℝ} (hlu : lower ≤ upper) :
    (volume (Set.Icc lower upper)).toReal = upper - lower := by
  have hvolume :
      volume (Set.Icc lower upper) = ENNReal.ofReal (upper - lower) :=
    real_volume_Icc_eq_ofReal_sub hlu
  have hsub_nonneg : 0 ≤ upper - lower :=
    sub_nonneg.mpr hlu
  exact Eq.trans
    (congrArg ENNReal.toReal hvolume)
    (ennreal_toReal_ofReal_of_nonnegative hsub_nonneg)

/-- The volume of an ordered closed real interval is its endpoint difference. -/
theorem zetaPaleyWienerIntervalVolume_toReal_eq_upper_sub_lower
    {f : ZetaAdmissibleFunction}
    (I : ZetaPaleyWienerSupportInterval f) :
    (volume (Set.Icc I.lower I.upper)).toReal =
      I.upper - I.lower := by
  exact real_volume_Icc_toReal_eq_sub I.lower_le_upper

/-- The volume of the certified support interval is the certified support interval length. -/
theorem zetaPaleyWienerIntervalVolume_toReal_eq_supportIntervalLength
    {f : ZetaAdmissibleFunction}
    (I : ZetaPaleyWienerSupportInterval f) :
    (volume (Set.Icc I.lower I.upper)).toReal =
      zetaPaleyWienerSupportIntervalLength I := by
  have hvolume :
      (volume (Set.Icc I.lower I.upper)).toReal =
        I.upper - I.lower :=
    zetaPaleyWienerIntervalVolume_toReal_eq_upper_sub_lower I
  have hlength :
      zetaPaleyWienerSupportIntervalLength I =
        I.upper - I.lower :=
    zetaPaleyWienerSupportIntervalLength_eq_upper_sub_lower I
  exact hvolume.trans hlength.symm

/-- The integral of the constant interval indicator is the constant times the certified
interval length. -/
theorem zetaPaleyWienerIntervalIndicatorIntegral_eq_intervalLength_mul_bound
    {f : ZetaAdmissibleFunction}
    (I : ZetaPaleyWienerSupportInterval f) (B : ℝ) (hB_nonneg : 0 ≤ B) :
    (∫ t : ℝ, zetaPaleyWienerIntervalIndicatorBound I B t) =
      B * zetaPaleyWienerSupportIntervalLength I := by
  have hvolume :
      (∫ t : ℝ, zetaPaleyWienerIntervalIndicatorBound I B t) =
        B * (volume (Set.Icc I.lower I.upper)).toReal :=
    zetaPaleyWienerIntervalIndicatorIntegral_eq_bound_mul_volume
      I B hB_nonneg
  have hlength :
      (volume (Set.Icc I.lower I.upper)).toReal =
        zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerIntervalVolume_toReal_eq_supportIntervalLength I
  exact hvolume.trans (congrArg (fun v : ℝ => B * v) hlength)

/-- The support-indicator integral is bounded by any containing support interval length. -/
theorem zetaPaleyWienerSupportIndicatorIntegral_le_intervalLength_mul_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (B : ℝ) (hB_nonneg : 0 ≤ B) :
    (∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t) ≤
      B * zetaPaleyWienerSupportIntervalLength I := by
  have hpoint :
      ∀ t : ℝ,
        zetaPaleyWienerSupportIndicatorBound f B t ≤
          zetaPaleyWienerIntervalIndicatorBound I B t :=
    zetaPaleyWienerSupportIndicatorBound_le_intervalIndicatorBound
      f I B hB_nonneg
  have hintegral :
      (∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t) ≤
        ∫ t : ℝ, zetaPaleyWienerIntervalIndicatorBound I B t :=
    zetaPaleyWienerSupportIndicatorIntegral_le_intervalIndicatorIntegral
      f I B hB_nonneg hpoint
  have hinterval :
      (∫ t : ℝ, zetaPaleyWienerIntervalIndicatorBound I B t) =
        B * zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerIntervalIndicatorIntegral_eq_intervalLength_mul_bound
      I B hB_nonneg
  exact le_trans hintegral (le_of_eq hinterval)

/-- Integral-norm transport from a pointwise compact-support kernel bound. -/
theorem zetaLaplaceTransform_norm_le_supportIntervalLength_mul_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (z : ℂ) (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ))‖ ≤ B) :
    ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
      B * zetaPaleyWienerSupportIntervalLength I := by
  have hkernel_bound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerLaplaceKernel f z t‖ ≤ B := by
    intro t ht
    unfold zetaPaleyWienerLaplaceKernel
    exact hbound t ht
  have hindicator_pointwise :
      ∀ t : ℝ,
        ‖zetaPaleyWienerLaplaceKernel f z t‖ ≤
          zetaPaleyWienerSupportIndicatorBound f B t :=
    zetaPaleyWienerLaplaceKernel_norm_le_supportIndicatorBound
      f z B hkernel_bound
  have hintegral :
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
        ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t :=
    zetaLaplaceTransform_norm_le_supportIndicatorIntegral
      f z B hindicator_pointwise
  have hlength :
      (∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t) ≤
        B * zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerSupportIndicatorIntegral_le_intervalLength_mul_bound
      f I B hB_nonneg
  exact le_trans hintegral hlength

/-- Raw zero-order compact-support product bound for the Laplace transform.

This is the un-bumped estimate: source norm envelope, horizontal exponential envelope,
and support interval length multiply to dominate the integral norm. -/
theorem zetaLaplaceTransform_supportInterval_zeroOrder_le_rawEnvelope
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∀ z : ℂ,
      zetaPaleyWienerInVerticalStrip a b z →
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
        zetaPaleyWienerSupportNormEnvelope f *
          zetaPaleyWienerStripExponentialEnvelope I a b *
          zetaPaleyWienerSupportIntervalLength I := by
  intro z hz
  let B : ℝ :=
    zetaPaleyWienerRawKernelEnvelope f I a b
  have hB_nonneg : 0 ≤ B :=
    zetaPaleyWienerRawKernelEnvelope_nonnegative f I a b
  have hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖f.toZetaTestFunction' t * Complex.exp (z * (t : ℂ))‖ ≤ B := by
    intro t ht
    exact zetaLaplaceKernel_norm_le_rawEnvelope_on_support
      f I a b z hz t ht
  have hintegral :
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
        B * zetaPaleyWienerSupportIntervalLength I :=
    zetaLaplaceTransform_norm_le_supportIntervalLength_mul_bound
      f I z B hB_nonneg hbound
  change
    ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
      zetaPaleyWienerRawKernelEnvelope f I a b *
        zetaPaleyWienerSupportIntervalLength I
  exact hintegral

/-- The concrete zero-order integral estimate from compact support.

The source norm is bounded by `zetaPaleyWienerSupportNormEnvelope`, the horizontal
exponential is bounded by `zetaPaleyWienerStripExponentialEnvelope`, and the support is
contained in the supplied interval of length `zetaPaleyWienerSupportIntervalLength`. -/
theorem zetaLaplaceTransform_supportInterval_zeroOrder_le_envelope
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∀ z : ℂ,
      zetaPaleyWienerInVerticalStrip a b z →
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
        zetaPaleyWienerZeroOrderEnvelope f I a b := by
  intro z hz
  have hraw :
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
        zetaPaleyWienerSupportNormEnvelope f *
          zetaPaleyWienerStripExponentialEnvelope I a b *
          zetaPaleyWienerSupportIntervalLength I :=
    zetaLaplaceTransform_supportInterval_zeroOrder_le_rawEnvelope f I a b z hz
  unfold zetaPaleyWienerZeroOrderEnvelope
  exact weightedLaplaceKernel_bound_le_bump
    (zetaPaleyWienerSupportNormEnvelope f *
      zetaPaleyWienerStripExponentialEnvelope I a b *
      zetaPaleyWienerSupportIntervalLength I)
    hraw

/-- Zero-order compact-support control for the admissible Laplace transform on a fixed
support interval.

This is the analytic estimate before integration by parts: compact support bounds the
source, the support interval bounds the horizontal exponential factor uniformly on the
strip, and the integral is controlled by those two bounds. -/
theorem zetaLaplaceTransform_supportInterval_zeroOrder_integralBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤ C := by
  exact ⟨zetaPaleyWienerZeroOrderEnvelope f I a b,
    zetaPaleyWienerZeroOrderEnvelope_pos f I a b,
    zetaLaplaceTransform_supportInterval_zeroOrder_le_envelope f I a b⟩

/-- Zero-order Paley-Wiener control on a fixed compact support interval.

This is the compact-support estimate before any integration by parts: the horizontal
exponential factor is uniformly bounded on the strip and support interval. -/
theorem zetaLaplaceTransform_supportInterval_zeroOrder_decay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z 0 := by
  exact
    match zetaLaplaceTransform_supportInterval_zeroOrder_integralBound f I a b with
    | ⟨C, hCpos, hCbound⟩ =>
        Exists.intro C
          (And.intro hCpos
            (fun z hz =>
              have hweight :
                  zetaPaleyWienerVerticalWeight z 0 = 1 := by
                unfold zetaPaleyWienerVerticalWeight
                exact zpow_zero (1 + ‖z.im‖)
              have htarget :
                  C * zetaPaleyWienerVerticalWeight z 0 = C := by
                exact Eq.trans (congrArg (fun W : ℝ => C * W) hweight) (mul_one C)
              (hCbound z hz).trans_eq htarget.symm))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
