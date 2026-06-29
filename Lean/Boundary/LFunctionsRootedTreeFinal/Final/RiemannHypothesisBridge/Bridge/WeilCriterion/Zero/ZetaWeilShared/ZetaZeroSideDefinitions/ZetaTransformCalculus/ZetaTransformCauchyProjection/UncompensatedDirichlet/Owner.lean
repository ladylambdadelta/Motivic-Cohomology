import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.ZeroAndScalarWindow.Owner

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

noncomputable def scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow
    (a T x : ℝ) : ℝ :=
  ∫ t in Set.Icc (-T) T,
    (-(a / (a ^ 2 + t ^ 2))) * Real.cos (t * x)

/-- Odd-sine real contribution of the uncompensated Cauchy Fourier window. -/
noncomputable def scalarFourierLaplacePlemelj_uncompensated_oddSineWindow
    (a T x : ℝ) : ℝ :=
  ∫ t in Set.Icc (-T) T,
    (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)

/-- Pointwise domination of the even-cosine integrand by the positive Cauchy
kernel. -/
theorem scalarFourierLaplacePlemelj_uncompensated_evenCosine_integrand_abs_le_kernel
    (a : ℝ) (ha : 0 < a) (t x : ℝ) :
    |(-(a / (a ^ 2 + t ^ 2))) * Real.cos (t * x)| ≤
      a / (a ^ 2 + t ^ 2) := by
  let p : ℝ := a / (a ^ 2 + t ^ 2)
  let c : ℝ := Real.cos (t * x)
  have hden_pos : 0 < a ^ 2 + t ^ 2 :=
    scalarFourierLaplacePlemelj_zero_denominator_pos a ha t
  have hp_nonneg : 0 ≤ p := by
    unfold p
    exact div_nonneg ha.le hden_pos.le
  have hc_abs : |c| ≤ 1 := by
    unfold c
    exact abs_cos_le_one (t * x)
  have habs :
      |(-p) * c| = p * |c| := by
    calc
      |(-p) * c| = |-p| * |c| := by
        exact abs_mul (-p) c
      _ = |p| * |c| := by
        exact congrArg (fun r : ℝ => r * |c|) (abs_neg p)
      _ = p * |c| := by
        exact congrArg (fun r : ℝ => r * |c|) (abs_of_nonneg hp_nonneg)
  have hmul : p * |c| ≤ p * 1 :=
    mul_le_mul_of_nonneg_left hc_abs hp_nonneg
  calc
    |(-(a / (a ^ 2 + t ^ 2))) * Real.cos (t * x)|
        = |(-p) * c| := by
          unfold p
          unfold c
          rfl
    _ = p * |c| := habs
    _ ≤ p * 1 := hmul
    _ = a / (a ^ 2 + t ^ 2) := by
          unfold p
          exact mul_one (a / (a ^ 2 + t ^ 2))

/-- Interval integrability of the positive Cauchy kernel on symmetric finite
windows. -/
theorem scalarFourierLaplacePlemelj_uncompensated_positiveKernel_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => a / (a ^ 2 + t ^ 2))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 :=
    scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha
  have hquot_cont : Continuous (fun t : ℝ => a / (a ^ 2 + t ^ 2)) :=
    continuous_const.div hden_cont hden_ne
  exact hquot_cont.intervalIntegrable (-T) T

/-- Interval majorization of the even-cosine window by the positive Cauchy
kernel mass. -/
theorem scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_abs_le_kernelMass_of_pointwise
    (a : ℝ) (ha : 0 < a) (T x : ℝ)
    (hpoint :
      ∀ t : ℝ,
        |(-(a / (a ^ 2 + t ^ 2))) * Real.cos (t * x)| ≤
          a / (a ^ 2 + t ^ 2)) :
    |scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x| ≤
      |∫ t in Set.Icc (-T) T, (a / (a ^ 2 + t ^ 2) : ℝ)| := by
  let f : ℝ → ℝ :=
    fun t : ℝ => (-(a / (a ^ 2 + t ^ 2))) * Real.cos (t * x)
  let g : ℝ → ℝ :=
    fun t : ℝ => a / (a ^ 2 + t ^ 2)
  have hmajor :
      ∀ᵐ t ∂volume.restrict (Ι (-T) T), ‖f t‖ ≤ g t :=
    Filter.Eventually.of_forall
      (fun t : ℝ => by
        calc
          ‖f t‖ = |f t| := by
            exact Real.norm_eq_abs (f t)
          _ =
              |(-(a / (a ^ 2 + t ^ 2))) * Real.cos (t * x)| := by
                unfold f
                rfl
          _ ≤ a / (a ^ 2 + t ^ 2) := hpoint t
          _ = g t := by
                unfold g
                rfl)
  have hg :
      IntervalIntegrable g volume (-T) T := by
    unfold g
    exact
      scalarFourierLaplacePlemelj_uncompensated_positiveKernel_intervalIntegrable
        a ha T
  have hbound :
      ‖∫ t in (-T)..T, f t‖ ≤
        |∫ t in (-T)..T, g t| :=
    intervalIntegral.norm_integral_le_of_norm_le
      (a := -T) (b := T) (μ := volume) (f := f) (g := g)
      hmajor hg
  calc
    |scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x|
        = ‖∫ t in (-T)..T, f t‖ := by
          unfold scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow
          unfold f
          exact (Real.norm_eq_abs
            (∫ t in (-T)..T,
              (-(a / (a ^ 2 + t ^ 2))) * Real.cos (t * x))).symm
    _ ≤ |∫ t in (-T)..T, g t| := hbound
    _ =
        |∫ t in Set.Icc (-T) T, (a / (a ^ 2 + t ^ 2) : ℝ)| := by
          unfold g
          rfl

/-- Absolute integral majorization of the even-cosine component by the
nonoscillatory Cauchy kernel mass. -/
theorem scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_abs_le_kernelMass
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    |scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x| ≤
      |∫ t in Set.Icc (-T) T, (a / (a ^ 2 + t ^ 2) : ℝ)| := by
  exact
    scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_abs_le_kernelMass_of_pointwise
      a ha T x
      (fun t : ℝ =>
        scalarFourierLaplacePlemelj_uncompensated_evenCosine_integrand_abs_le_kernel
          a ha t x)

/-- Exact arctangent primitive for the positive Cauchy kernel mass. -/
theorem scalarFourierLaplacePlemelj_uncompensated_kernelMass_eq_two_arctan
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    (∫ t in Set.Icc (-T) T, (a / (a ^ 2 + t ^ 2) : ℝ)) =
      (2 : ℝ) * Real.arctan (T / a) := by
  let P : ℝ → ℝ := fun t : ℝ => a / (a ^ 2 + t ^ 2)
  let A : ℝ := (2 : ℝ) * Real.arctan (T / a)
  have hneg_complex :
      (∫ t in Set.Icc (-T) T, ((-P t : ℝ) : ℂ)) =
        ((-A : ℝ) : ℂ) := by
    calc
      (∫ t in Set.Icc (-T) T, ((-P t : ℝ) : ℂ))
          =
          ∫ t in Set.Icc (-T) T,
            ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) := by
            exact intervalIntegral.integral_congr
              (Filter.Eventually.of_forall
                (fun t : ℝ => by
                  unfold P
                  rfl))
      _ =
          (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
            exact
              scalarFourierLaplacePlemelj_zero_real_kernel_integral_eq_arctan
                a ha T
      _ = ((-A : ℝ) : ℂ) := by
            unfold A
            exact congrArg (fun r : ℝ => (r : ℂ))
              (neg_mul (2 : ℝ) (Real.arctan (T / a))).symm
  have hneg_real :
      (∫ t in Set.Icc (-T) T, (-P t : ℝ)) = -A := by
    have hofReal :
        (∫ t in Set.Icc (-T) T, ((-P t : ℝ) : ℂ)) =
          (((∫ t in Set.Icc (-T) T, (-P t : ℝ)) : ℝ) : ℂ) := by
      calc
        (∫ t in Set.Icc (-T) T, ((-P t : ℝ) : ℂ))
            =
            ∫ t in (-T)..T, ((-P t : ℝ) : ℂ) := by
              rfl
        _ =
            (((∫ t in (-T)..T, (-P t : ℝ)) : ℝ) : ℂ) := by
              exact intervalIntegral.integral_ofReal
        _ =
            (((∫ t in Set.Icc (-T) T, (-P t : ℝ)) : ℝ) : ℂ) := by
              rfl
    exact Complex.ofReal_injective (hofReal.symm.trans hneg_complex)
  have hneg_relation :
      (∫ t in Set.Icc (-T) T, (-P t : ℝ)) =
        -(∫ t in Set.Icc (-T) T, P t) := by
    calc
      (∫ t in Set.Icc (-T) T, (-P t : ℝ))
          =
          ∫ t in (-T)..T, (-P t : ℝ) := by
            rfl
      _ =
          -(∫ t in (-T)..T, P t) := by
            exact intervalIntegral.integral_neg
      _ =
          -(∫ t in Set.Icc (-T) T, P t) := by
            rfl
  have hneg_target :
      -(∫ t in Set.Icc (-T) T, P t) = -A :=
    hneg_relation.symm.trans hneg_real
  have htarget :
      (∫ t in Set.Icc (-T) T, P t) = A :=
    neg_injective hneg_target
  exact htarget

/-- Elementary arctangent bound for the positive Cauchy kernel primitive. -/
theorem scalarFourierLaplacePlemelj_two_mul_arctan_abs_le_pi
    (y : ℝ) :
    |(2 : ℝ) * Real.arctan y| ≤ Real.pi := by
  let u : ℝ := Real.arctan y
  have hupper_half : u < Real.pi / 2 := by
    unfold u
    exact Real.arctan_lt_pi_div_two y
  have hlower_half : -(Real.pi / 2) < u := by
    unfold u
    exact Real.neg_pi_div_two_lt_arctan y
  have htwo_pos : (0 : ℝ) < 2 :=
    two_pos
  have hmul_upper :
      (2 : ℝ) * u < 2 * (Real.pi / 2) :=
    mul_lt_mul_of_pos_left hupper_half htwo_pos
  have hmul_lower :
      2 * (-(Real.pi / 2)) < (2 : ℝ) * u :=
    mul_lt_mul_of_pos_left hlower_half htwo_pos
  have htwo_half : (2 : ℝ) * (Real.pi / 2) = Real.pi :=
    two_mul_div_two Real.pi
  have htwo_neg_half : (2 : ℝ) * (-(Real.pi / 2)) = -Real.pi := by
    calc
      (2 : ℝ) * (-(Real.pi / 2)) = -((2 : ℝ) * (Real.pi / 2)) := by
        exact mul_neg (2 : ℝ) (Real.pi / 2)
      _ = -Real.pi := by
        exact congrArg Neg.neg htwo_half
  have hupper : (2 : ℝ) * u ≤ Real.pi :=
    le_of_lt (hmul_upper.trans_eq htwo_half)
  have hlower : -Real.pi ≤ (2 : ℝ) * u :=
    le_of_lt (htwo_neg_half.symm.trans_lt hmul_lower)
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- The symmetric nonoscillatory Cauchy kernel mass is bounded by `π`. -/
theorem scalarFourierLaplacePlemelj_uncompensated_kernelMass_abs_le_pi
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    |∫ t in Set.Icc (-T) T, (a / (a ^ 2 + t ^ 2) : ℝ)| ≤ Real.pi := by
  calc
    |∫ t in Set.Icc (-T) T, (a / (a ^ 2 + t ^ 2) : ℝ)|
        = |(2 : ℝ) * Real.arctan (T / a)| := by
          exact congrArg abs
            (scalarFourierLaplacePlemelj_uncompensated_kernelMass_eq_two_arctan
              a ha T)
    _ ≤ Real.pi :=
          scalarFourierLaplacePlemelj_two_mul_arctan_abs_le_pi (T / a)

/-- Fixed-constant Dirichlet bound for the even-cosine component of the
uncompensated Cauchy kernel. -/
theorem scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_abs_le_pi
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    |scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x| ≤
      Real.pi := by
  exact
    (scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_abs_le_kernelMass
      a ha T x).trans
      (scalarFourierLaplacePlemelj_uncompensated_kernelMass_abs_le_pi
        a ha T)

/-- Uniform Dirichlet bound for the even-cosine part of the uncompensated
Cauchy Fourier window. -/
theorem scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_uniform_bound
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ T x : ℝ,
          |scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x| ≤ C := by
  exact ⟨Real.pi, Real.pi_pos.le,
    fun T x =>
      scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_abs_le_pi
        a ha T x⟩

/-- Nonnegative-radius, positive-frequency normalized half-window Hilbert-sine
Dirichlet bound. -/
theorem scalarFourierLaplacePlemelj_dampedSineIntegral_smallPrefix_scaled_eq
    (A b : ℝ) (hA : 0 ≤ A) (hb : 0 < b) :
    (∫ v in (0)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
      ∫ w in (0)..(A / b),
        (w / (1 + w ^ 2)) * Real.sin (b * w) := by
  let F : ℝ → ℝ :=
    fun v : ℝ => (v / (b ^ 2 + v ^ 2)) * Real.sin v
  have hb_ne : b ≠ 0 :=
    ne_of_gt hb
  have hend : (A / b) * b = A :=
    div_mul_cancel₀ A hb_ne
  have hpoint :
      ∀ w : ℝ,
        b * F (w * b) =
          (w / (1 + w ^ 2)) * Real.sin (b * w) := by
    intro w
    have hcoeff :
        b * ((w * b) / (b ^ 2 + (w * b) ^ 2)) =
          w / (1 + w ^ 2) :=
      scalarFourierLaplacePlemelj_scaledHilbertSineKernel_coefficient_identity
        b hb w
    have hphase : Real.sin (w * b) = Real.sin (b * w) :=
      congrArg Real.sin (mul_comm w b)
    calc
      b * F (w * b)
          =
          b *
            (((w * b) / (b ^ 2 + (w * b) ^ 2)) *
              Real.sin (w * b)) := by
            unfold F
            rfl
      _ =
          (b * ((w * b) / (b ^ 2 + (w * b) ^ 2))) *
            Real.sin (w * b) := by
            exact mul_assoc b
              ((w * b) / (b ^ 2 + (w * b) ^ 2))
              (Real.sin (w * b))
      _ =
          (w / (1 + w ^ 2)) * Real.sin (w * b) := by
            exact congrArg
              (fun r : ℝ => r * Real.sin (w * b))
              hcoeff
      _ =
          (w / (1 + w ^ 2)) * Real.sin (b * w) := by
            exact congrArg
              (fun s : ℝ => (w / (1 + w ^ 2)) * s)
              hphase
  have hsubst :
      b * ∫ w in (0)..(A / b), F (w * b) =
        ∫ v in (0 * b)..((A / b) * b), F v :=
    intervalIntegral.smul_integral_comp_mul_right
      (f := F) (a := 0) (b := A / b) b
  have hconst :
      b * ∫ w in (0)..(A / b), F (w * b) =
        ∫ w in (0)..(A / b),
          (w / (1 + w ^ 2)) * Real.sin (b * w) := by
    calc
      b * ∫ w in (0)..(A / b), F (w * b)
          =
          ∫ w in (0)..(A / b), b * F (w * b) := by
            exact (intervalIntegral.integral_const_mul
              (a := 0) (b := A / b) (μ := volume)
              b
              (fun w : ℝ => F (w * b))).symm
      _ =
          ∫ w in (0)..(A / b),
            (w / (1 + w ^ 2)) * Real.sin (b * w) := by
            exact intervalIntegral.integral_congr
              (Filter.Eventually.of_forall hpoint)
  calc
    (∫ v in (0)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v)
        = ∫ v in (0)..A, F v := by
          unfold F
          rfl
    _ = ∫ v in (0 * b)..((A / b) * b), F v := by
          exact congrArg₂
            (fun l r : ℝ => ∫ v in l..r, F v)
            (zero_mul b).symm
            hend.symm
    _ = b * ∫ w in (0)..(A / b), F (w * b) := by
          exact hsubst.symm
    _ =
        ∫ w in (0)..(A / b),
          (w / (1 + w ^ 2)) * Real.sin (b * w) := hconst

theorem scalarFourierLaplacePlemelj_scaledSmallPrefix_abs_le_one
    (R b : ℝ) (hR_nonneg : 0 ≤ R) (hR_le_one : R ≤ 1) :
    |∫ w in (0)..R,
      (w / (1 + w ^ 2)) * Real.sin (b * w)| ≤ 1 := by
  let f : ℝ → ℝ :=
    fun w : ℝ => (w / (1 + w ^ 2)) * Real.sin (b * w)
  have hpoint : ∀ w ∈ Ι (0 : ℝ) R, ‖f w‖ ≤ (1 : ℝ) := by
    intro w hw
    have hw_nonneg : 0 ≤ w :=
      (mem_uIcc.mp hw).1
    have hw_le_R : w ≤ R :=
      (mem_uIcc.mp hw).2
    have hw_le_one : w ≤ 1 :=
      hw_le_R.trans hR_le_one
    have hden_pos : 0 < 1 + w ^ 2 :=
      add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg w)
    have hcoeff_nonneg : 0 ≤ w / (1 + w ^ 2) :=
      div_nonneg hw_nonneg hden_pos.le
    have hcoeff_le_one : w / (1 + w ^ 2) ≤ 1 := by
      exact (div_le_one hden_pos).mpr
        (hw_le_one.trans
          (le_add_of_nonneg_right (sq_nonneg w)))
    have hsin_abs : |Real.sin (b * w)| ≤ 1 :=
      abs_le.mpr ⟨neg_one_le_sin (b * w), sin_le_one (b * w)⟩
    have habs :
        |f w| ≤ 1 := by
      calc
        |f w| =
            |w / (1 + w ^ 2)| * |Real.sin (b * w)| := by
            unfold f
            exact abs_mul (w / (1 + w ^ 2)) (Real.sin (b * w))
        _ =
            (w / (1 + w ^ 2)) * |Real.sin (b * w)| := by
            exact congrArg
              (fun r : ℝ => r * |Real.sin (b * w)|)
              (abs_of_nonneg hcoeff_nonneg)
        _ ≤ (w / (1 + w ^ 2)) * 1 := by
            exact mul_le_mul_of_nonneg_left hsin_abs hcoeff_nonneg
        _ = w / (1 + w ^ 2) := by
            exact mul_one (w / (1 + w ^ 2))
        _ ≤ 1 := hcoeff_le_one
    calc
      ‖f w‖ = |f w| := by
        exact Real.norm_eq_abs (f w)
      _ ≤ 1 := habs
  have hnorm :
      ‖∫ w in (0)..R, f w‖ ≤ (1 : ℝ) * |R - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hlength : |R - 0| ≤ 1 := by
    calc
      |R - 0| = |R| := by
        exact congrArg abs (sub_zero R)
      _ = R := by
        exact abs_of_nonneg hR_nonneg
      _ ≤ 1 := hR_le_one
  have htarget :
      ‖∫ w in (0)..R, f w‖ ≤ 1 := by
    calc
      ‖∫ w in (0)..R, f w‖ ≤ (1 : ℝ) * |R - 0| := hnorm
      _ = |R - 0| := by
        exact one_mul |R - 0|
      _ ≤ 1 := hlength
  calc
    |∫ w in (0)..R,
      (w / (1 + w ^ 2)) * Real.sin (b * w)|
        = ‖∫ w in (0)..R, f w‖ := by
          unfold f
          exact (Real.norm_eq_abs
            (∫ w in (0)..R,
              (w / (1 + w ^ 2)) * Real.sin (b * w))).symm
    _ ≤ 1 := htarget

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_smallPrefix_abs_le_one
    (A b : ℝ) (hA : 0 ≤ A) (hA_le_b : A ≤ b) (hb : 0 < b) :
    |∫ v in (0)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 1 := by
  have hb_nonneg : 0 ≤ b :=
    hb.le
  have hb_ne : b ≠ 0 :=
    ne_of_gt hb
  have hR_nonneg : 0 ≤ A / b :=
    div_nonneg hA hb_nonneg
  have hR_le_one : A / b ≤ 1 := by
    exact (div_le_one hb).mpr hA_le_b
  have hscale :
      (∫ v in (0)..A,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
        ∫ w in (0)..(A / b),
          (w / (1 + w ^ 2)) * Real.sin (b * w) :=
    scalarFourierLaplacePlemelj_dampedSineIntegral_smallPrefix_scaled_eq
      A b hA hb
  calc
    |∫ v in (0)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v|
        =
        |∫ w in (0)..(A / b),
          (w / (1 + w ^ 2)) * Real.sin (b * w)| := by
          exact congrArg abs hscale
    _ ≤ 1 :=
        scalarFourierLaplacePlemelj_scaledSmallPrefix_abs_le_one
          (A / b) b hR_nonneg hR_le_one

theorem scalarFourierLaplacePlemelj_one_le_two_pi :
    (1 : ℝ) ≤ (2 : ℝ) * Real.pi := by
  have hone_le_pi_half : (1 : ℝ) ≤ Real.pi / 2 :=
    Real.one_le_pi_div_two
  have hpi_half_le_pi : Real.pi / 2 ≤ Real.pi :=
    div_le_self Real.pi_pos.le one_le_two
  have hpi_le_two_pi : Real.pi ≤ (2 : ℝ) * Real.pi := by
    calc
      Real.pi = (1 : ℝ) * Real.pi := by
        exact (one_mul Real.pi).symm
      _ ≤ (2 : ℝ) * Real.pi := by
        exact mul_le_mul_of_nonneg_right one_le_two Real.pi_pos.le
  exact hone_le_pi_half.trans (hpi_half_le_pi.trans hpi_le_two_pi)

theorem scalarFourierLaplacePlemelj_two_le_two_pi :
    (2 : ℝ) ≤ (2 : ℝ) * Real.pi := by
  have hone_le_pi_half : (1 : ℝ) ≤ Real.pi / 2 :=
    Real.one_le_pi_div_two
  have htwo_pos : (0 : ℝ) < 2 :=
    two_pos
  have htwo_le_pi : (2 : ℝ) ≤ Real.pi := by
    have hone_mul_two_le_pi : (1 : ℝ) * 2 ≤ Real.pi :=
      (le_div_iff₀ htwo_pos).mp hone_le_pi_half
    calc
      (2 : ℝ) = (1 : ℝ) * 2 := by
        exact (one_mul 2).symm
      _ ≤ Real.pi := hone_mul_two_le_pi
  have hpi_le_two_pi : Real.pi ≤ (2 : ℝ) * Real.pi := by
    calc
      Real.pi = (1 : ℝ) * Real.pi := by
        exact (one_mul Real.pi).symm
      _ ≤ (2 : ℝ) * Real.pi := by
        exact mul_le_mul_of_nonneg_right one_le_two Real.pi_pos.le
  exact htwo_le_pi.trans hpi_le_two_pi

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_low_abs_le_one
    (A b : ℝ) (hb : 0 < b) (hbA : b ≤ A) (hA_le_one : A ≤ 1) :
    |∫ v in (b)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 1 := by
  let f : ℝ → ℝ :=
    fun v : ℝ => (v / (b ^ 2 + v ^ 2)) * Real.sin v
  have hpoint : ∀ v ∈ Ι b A, ‖f v‖ ≤ (1 : ℝ) := by
    intro v hv
    have hb_le_v : b ≤ v :=
      (mem_uIcc.mp hv).1
    have hv_le_A : v ≤ A :=
      (mem_uIcc.mp hv).2
    have hv_nonneg : 0 ≤ v :=
      hb.le.trans hb_le_v
    have hden_pos : 0 < b ^ 2 + v ^ 2 :=
      scalarFourierLaplacePlemelj_zero_denominator_pos b hb v
    have hcoeff_nonneg : 0 ≤ v / (b ^ 2 + v ^ 2) :=
      div_nonneg hv_nonneg hden_pos.le
    have hsin_abs_le_v : |Real.sin v| ≤ v := by
      calc
        |Real.sin v| ≤ |v| := Real.abs_sin_le_abs v
        _ = v := by
          exact abs_of_nonneg hv_nonneg
    have hv_sq_le_den : v ^ 2 ≤ b ^ 2 + v ^ 2 :=
      le_add_of_nonneg_left (sq_nonneg b)
    have hcoeff_v_le_one :
        (v / (b ^ 2 + v ^ 2)) * v ≤ 1 := by
      calc
        (v / (b ^ 2 + v ^ 2)) * v =
            (v * v) / (b ^ 2 + v ^ 2) := by
            exact div_mul_eq_mul_div v v (b ^ 2 + v ^ 2)
        _ = v ^ 2 / (b ^ 2 + v ^ 2) := by
            exact congrArg
              (fun r : ℝ => r / (b ^ 2 + v ^ 2))
              (pow_two v).symm
        _ ≤ 1 := by
            exact (div_le_one hden_pos).mpr hv_sq_le_den
    have habs :
        |f v| ≤ 1 := by
      calc
        |f v| =
            |v / (b ^ 2 + v ^ 2)| * |Real.sin v| := by
            unfold f
            exact abs_mul (v / (b ^ 2 + v ^ 2)) (Real.sin v)
        _ =
            (v / (b ^ 2 + v ^ 2)) * |Real.sin v| := by
            exact congrArg
              (fun r : ℝ => r * |Real.sin v|)
              (abs_of_nonneg hcoeff_nonneg)
        _ ≤ (v / (b ^ 2 + v ^ 2)) * v := by
            exact mul_le_mul_of_nonneg_left hsin_abs_le_v hcoeff_nonneg
        _ ≤ 1 := hcoeff_v_le_one
    calc
      ‖f v‖ = |f v| := by
        exact Real.norm_eq_abs (f v)
      _ ≤ 1 := habs
  have hnorm :
      ‖∫ v in b..A, f v‖ ≤ (1 : ℝ) * |A - b| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hlength : |A - b| ≤ 1 := by
    have hdiff_nonneg : 0 ≤ A - b :=
      sub_nonneg.mpr hbA
    have hdiff_le_A : A - b ≤ A :=
      sub_le_self A hb.le
    calc
      |A - b| = A - b := by
        exact abs_of_nonneg hdiff_nonneg
      _ ≤ A := hdiff_le_A
      _ ≤ 1 := hA_le_one
  have htarget :
      ‖∫ v in b..A, f v‖ ≤ 1 := by
    calc
      ‖∫ v in b..A, f v‖ ≤ (1 : ℝ) * |A - b| := hnorm
      _ = |A - b| := by
        exact one_mul |A - b|
      _ ≤ 1 := hlength
  calc
    |∫ v in (b)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v|
        = ‖∫ v in b..A, f v‖ := by
          unfold f
          exact (Real.norm_eq_abs
            (∫ v in b..A,
              (v / (b ^ 2 + v ^ 2)) * Real.sin v)).symm
    _ ≤ 1 := htarget

theorem scalarFourierLaplacePlemelj_highTailCauchyAmplitude_nonnegative
    (b c v : ℝ) (hb : 0 < b) (hc : b ≤ c) (hv : v ∈ Set.Ici c) :
    0 ≤ v / (b ^ 2 + v ^ 2) := by
  have hc_nonneg : 0 ≤ c :=
    hb.le.trans hc
  have hc_le_v : c ≤ v :=
    hv
  have hv_nonneg : 0 ≤ v :=
    hc_nonneg.trans hc_le_v
  have hden_pos : 0 < b ^ 2 + v ^ 2 :=
    scalarFourierLaplacePlemelj_zero_denominator_pos b hb v
  exact div_nonneg hv_nonneg hden_pos.le

theorem scalarFourierLaplacePlemelj_highTailCauchyAmplitude_le_one
    (b c v : ℝ) (_hb : 0 < b) (hone_le_c : 1 ≤ c) (hv : v ∈ Set.Ici c) :
    v / (b ^ 2 + v ^ 2) ≤ 1 := by
  have hc_le_v : c ≤ v :=
    hv
  have hone_le_v : 1 ≤ v :=
    hone_le_c.trans hc_le_v
  have hv_nonneg : 0 ≤ v :=
    zero_le_one.trans hone_le_v
  have hden_pos : 0 < b ^ 2 + v ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg b) (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hone_le_v))
  have hv_le_v_sq : v ≤ v ^ 2 := by
    calc
      v = v * 1 := by
        exact (mul_one v).symm
      _ ≤ v * v := by
        exact mul_le_mul_of_nonneg_left hone_le_v hv_nonneg
      _ = v ^ 2 := by
        exact (pow_two v).symm
  have hv_le_den : v ≤ b ^ 2 + v ^ 2 :=
    hv_le_v_sq.trans (le_add_of_nonneg_left (sq_nonneg b))
  exact (div_le_one hden_pos).mpr hv_le_den

theorem scalarFourierLaplacePlemelj_highTailCauchyAmplitude_cross_mul_difference
    (b u v : ℝ) :
    u * (b ^ 2 + v ^ 2) - v * (b ^ 2 + u ^ 2) =
      (v - u) * (u * v - b ^ 2) := by
  have hleft_expand :
      u * (b ^ 2 + v ^ 2) - v * (b ^ 2 + u ^ 2) =
        (u * b ^ 2 - v * b ^ 2) +
          (u * v ^ 2 - v * u ^ 2) := by
    calc
      u * (b ^ 2 + v ^ 2) - v * (b ^ 2 + u ^ 2)
          =
          (u * b ^ 2 + u * v ^ 2) -
            (v * b ^ 2 + v * u ^ 2) := by
            exact congrArg₂ Sub.sub
              (mul_add u (b ^ 2) (v ^ 2))
              (mul_add v (b ^ 2) (u ^ 2))
      _ =
          (u * b ^ 2 - v * b ^ 2) +
            (u * v ^ 2 - v * u ^ 2) := by
            exact add_sub_add_comm
              (u * b ^ 2) (u * v ^ 2)
              (v * b ^ 2) (v * u ^ 2)
  have hright_expand :
      (v - u) * (u * v - b ^ 2) =
        (u * b ^ 2 - v * b ^ 2) +
          (u * v ^ 2 - v * u ^ 2) := by
    calc
      (v - u) * (u * v - b ^ 2)
          = (v - u) * (u * v) - (v - u) * b ^ 2 := by
            exact mul_sub (v - u) (u * v) (b ^ 2)
      _ =
          (v * (u * v) - u * (u * v)) -
            (v * b ^ 2 - u * b ^ 2) := by
            exact congrArg₂ Sub.sub
              (sub_mul v u (u * v))
              (sub_mul v u (b ^ 2))
      _ =
          (v * (u * v) - u * (u * v)) +
            (u * b ^ 2 - v * b ^ 2) := by
            exact sub_sub_eq_add_sub
              (v * (u * v) - u * (u * v))
              (v * b ^ 2)
              (u * b ^ 2)
      _ =
          (u * b ^ 2 - v * b ^ 2) +
            (v * (u * v) - u * (u * v)) := by
            exact add_comm
              (v * (u * v) - u * (u * v))
              (u * b ^ 2 - v * b ^ 2)
      _ =
          (u * b ^ 2 - v * b ^ 2) +
            (u * v ^ 2 - v * u ^ 2) := by
            have hvuv : v * (u * v) = u * v ^ 2 := by
              calc
                v * (u * v) = (v * u) * v := by
                  exact mul_assoc v u v
                _ = (u * v) * v := by
                  exact congrArg (fun r : ℝ => r * v) (mul_comm v u)
                _ = u * (v * v) := by
                  exact (mul_assoc u v v).symm
                _ = u * v ^ 2 := by
                  exact congrArg (fun r : ℝ => u * r) (pow_two v).symm
            have huuv : u * (u * v) = v * u ^ 2 := by
              calc
                u * (u * v) = (u * u) * v := by
                  exact mul_assoc u u v
                _ = u ^ 2 * v := by
                  exact congrArg (fun r : ℝ => r * v) (pow_two u).symm
                _ = v * u ^ 2 := by
                  exact mul_comm (u ^ 2) v
            exact congrArg
              (fun r : ℝ => (u * b ^ 2 - v * b ^ 2) + r)
              (congrArg₂ Sub.sub hvuv huuv)
  exact hleft_expand.trans hright_expand.symm

theorem scalarFourierLaplacePlemelj_highTailCauchyAmplitude_bsq_le_mul
    (b c u v : ℝ) (hb : 0 < b) (_hone_le_c : 1 ≤ c)
    (hb_le_c : b ≤ c) (hu : u ∈ Set.Ici c) (hv : v ∈ Set.Ici c) :
    b ^ 2 ≤ u * v := by
  have hb_le_u : b ≤ u :=
    hb_le_c.trans hu
  have hb_le_v : b ≤ v :=
    hb_le_c.trans hv
  have hu_nonneg : 0 ≤ u :=
    hb.le.trans hb_le_u
  have hmul : b * b ≤ u * v :=
    mul_le_mul hb_le_u hb_le_v hb.le hu_nonneg
  calc
    b ^ 2 = b * b := by
      exact pow_two b
    _ ≤ u * v := hmul

theorem scalarFourierLaplacePlemelj_highTailCauchyAmplitude_cross_mul_le
    (b c u v : ℝ) (hb : 0 < b) (hone_le_c : 1 ≤ c)
    (hb_le_c : b ≤ c) (hu : u ∈ Set.Ici c) (hv : v ∈ Set.Ici c)
    (huv : u ≤ v) :
    v * (b ^ 2 + u ^ 2) ≤ u * (b ^ 2 + v ^ 2) := by
  have hdiff_nonneg : 0 ≤ v - u :=
    sub_nonneg.mpr huv
  have hfactor_nonneg : 0 ≤ u * v - b ^ 2 :=
    sub_nonneg.mpr
      (scalarFourierLaplacePlemelj_highTailCauchyAmplitude_bsq_le_mul
        b c u v hb hone_le_c hb_le_c hu hv)
  have hprod_nonneg :
      0 ≤ (v - u) * (u * v - b ^ 2) :=
    mul_nonneg hdiff_nonneg hfactor_nonneg
  have hdiff_eq :
      u * (b ^ 2 + v ^ 2) - v * (b ^ 2 + u ^ 2) =
        (v - u) * (u * v - b ^ 2) :=
    scalarFourierLaplacePlemelj_highTailCauchyAmplitude_cross_mul_difference
      b u v
  have hsub_nonneg :
      0 ≤ u * (b ^ 2 + v ^ 2) - v * (b ^ 2 + u ^ 2) :=
    hdiff_eq.symm ▸ hprod_nonneg
  exact sub_nonneg.mp hsub_nonneg

theorem scalarFourierLaplacePlemelj_highTailCauchyAmplitude_antitoneOn
    (b c : ℝ) (hb : 0 < b) (hone_le_c : 1 ≤ c) (hb_le_c : b ≤ c) :
    AntitoneOn
      (fun v : ℝ => v / (b ^ 2 + v ^ 2))
      (Set.Ici c) := by
  intro u hu v hv huv
  have hden_u_pos : 0 < b ^ 2 + u ^ 2 :=
    scalarFourierLaplacePlemelj_zero_denominator_pos b hb u
  have hden_v_pos : 0 < b ^ 2 + v ^ 2 :=
    scalarFourierLaplacePlemelj_zero_denominator_pos b hb v
  exact
    (div_le_div_iff₀ hden_v_pos hden_u_pos).mpr
    (scalarFourierLaplacePlemelj_highTailCauchyAmplitude_cross_mul_le
        b c u v hb hone_le_c hb_le_c hu hv huv)

theorem scalarFourierLaplacePlemelj_sine_intervalIntegral_abs_le_two
    (c A : ℝ) :
    |∫ v in c..A, Real.sin v| ≤ 2 := by
  have hsin_eq :
      (∫ v in c..A, Real.sin v) = Real.cos c - Real.cos A :=
    Real.integral_sin
  have htriangle :
      |Real.cos c - Real.cos A| ≤
        |Real.cos c| + |Real.cos A| :=
    abs_sub_le (Real.cos c) (Real.cos A)
  have hcos_sum : |Real.cos c| + |Real.cos A| ≤ 1 + 1 :=
    add_le_add (abs_cos_le_one c) (abs_cos_le_one A)
  calc
    |∫ v in c..A, Real.sin v| =
        |Real.cos c - Real.cos A| := by
        exact congrArg abs hsin_eq
    _ ≤ |Real.cos c| + |Real.cos A| := htriangle
    _ ≤ 1 + 1 := hcos_sum
    _ = 2 := by
        rfl

theorem scalarFourierLaplacePlemelj_dirichletAbel_sine_tail_abs_le_two_of_bonnet_identity
    (g : ℝ → ℝ) (A c ξ : ℝ)
    (hcA : c ≤ A)
    (hcξ : c ≤ ξ) (hξA : ξ ≤ A)
    (hg_nonneg : ∀ v ∈ Set.Ici c, 0 ≤ g v)
    (hg_le_one : ∀ v ∈ Set.Ici c, g v ≤ 1)
    (hg_antitone : AntitoneOn g (Set.Ici c))
    (hprimitive : ∀ x y : ℝ, c ≤ x → x ≤ y → y ≤ A →
      |∫ v in x..y, Real.sin v| ≤ 2)
    (hbonnet :
      (∫ v in c..A, g v * Real.sin v) =
        g A * (∫ v in c..A, Real.sin v) +
          (g c - g A) * (∫ v in c..ξ, Real.sin v)) :
    |∫ v in c..A, g v * Real.sin v| ≤ 2 := by
  have hA_mem : A ∈ Set.Ici c :=
    hcA
  have hc_mem : c ∈ Set.Ici c :=
    le_refl c
  have hgA_nonneg : 0 ≤ g A :=
    hg_nonneg A hA_mem
  have hgA_le_gc : g A ≤ g c :=
    hg_antitone hc_mem hA_mem hcA
  have hdiff_nonneg : 0 ≤ g c - g A :=
    sub_nonneg.mpr hgA_le_gc
  have hcoeff_sum :
      g A + (g c - g A) = g c := by
    calc
      g A + (g c - g A) = (g c - g A) + g A := by
        exact add_comm (g A) (g c - g A)
      _ = g c := by
        exact sub_add_cancel (g c) (g A)
  have hgc_le_one : g c ≤ 1 :=
    hg_le_one c hc_mem
  have hfull :
      |∫ v in c..A, Real.sin v| ≤ 2 :=
    hprimitive c A (le_refl c) hcA (le_refl A)
  have hinitial :
      |∫ v in c..ξ, Real.sin v| ≤ 2 :=
    hprimitive c ξ (le_refl c) hcξ hξA
  have hweighted :
      |g A * (∫ v in c..A, Real.sin v) +
          (g c - g A) * (∫ v in c..ξ, Real.sin v)| ≤
        2 := by
    calc
      |g A * (∫ v in c..A, Real.sin v) +
          (g c - g A) * (∫ v in c..ξ, Real.sin v)|
          ≤
          |g A * (∫ v in c..A, Real.sin v)| +
            |(g c - g A) * (∫ v in c..ξ, Real.sin v)| := by
            exact abs_add
              (g A * (∫ v in c..A, Real.sin v))
              ((g c - g A) * (∫ v in c..ξ, Real.sin v))
      _ =
          g A * |∫ v in c..A, Real.sin v| +
            (g c - g A) * |∫ v in c..ξ, Real.sin v| := by
            exact congrArg₂ HAdd.hAdd
              (calc
                |g A * (∫ v in c..A, Real.sin v)| =
                    |g A| * |∫ v in c..A, Real.sin v| := by
                    exact abs_mul (g A) (∫ v in c..A, Real.sin v)
                _ = g A * |∫ v in c..A, Real.sin v| := by
                    exact congrArg
                      (fun r : ℝ => r * |∫ v in c..A, Real.sin v|)
                      (abs_of_nonneg hgA_nonneg))
              (calc
                |(g c - g A) * (∫ v in c..ξ, Real.sin v)| =
                    |g c - g A| * |∫ v in c..ξ, Real.sin v| := by
                    exact abs_mul (g c - g A) (∫ v in c..ξ, Real.sin v)
                _ =
                    (g c - g A) * |∫ v in c..ξ, Real.sin v| := by
                    exact congrArg
                      (fun r : ℝ => r * |∫ v in c..ξ, Real.sin v|)
                      (abs_of_nonneg hdiff_nonneg))
      _ ≤ g A * 2 + (g c - g A) * 2 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hfull hgA_nonneg)
              (mul_le_mul_of_nonneg_left hinitial hdiff_nonneg)
      _ = (g A + (g c - g A)) * 2 := by
            exact (add_mul (g A) (g c - g A) 2).symm
      _ = g c * 2 := by
            exact congrArg (fun r : ℝ => r * 2) hcoeff_sum
      _ ≤ 1 * 2 := by
            exact mul_le_mul_of_nonneg_right hgc_le_one zero_le_two
      _ = 2 := by
            exact one_mul 2
  calc
    |∫ v in c..A, g v * Real.sin v|
        =
        |g A * (∫ v in c..A, Real.sin v) +
          (g c - g A) * (∫ v in c..ξ, Real.sin v)| := by
          exact congrArg abs hbonnet
    _ ≤ 2 := hweighted

/-- Derivative of the high-tail Cauchy amplitude `v / (b^2 + v^2)`. -/
noncomputable def scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative
    (b v : ℝ) : ℝ :=
  (b ^ 2 - v ^ 2) / (b ^ 2 + v ^ 2) ^ 2

theorem scalarFourierLaplacePlemelj_highTailCauchyAmplitude_derivative_numerator
    (b v : ℝ) :
    1 * (b ^ 2 + v ^ 2) - v * (2 * v) = b ^ 2 - v ^ 2 := by
  have hv_mul_two_mul : v * (2 * v) = 2 * v ^ 2 := by
    calc
      v * (2 * v) = (v * 2) * v := by
        exact (mul_assoc v 2 v).symm
      _ = (2 * v) * v := by
        exact congrArg (fun x : ℝ => x * v) (mul_comm v 2)
      _ = 2 * (v * v) := by
        exact mul_assoc 2 v v
      _ = 2 * v ^ 2 := by
        exact congrArg (fun x : ℝ => 2 * x) (pow_two v).symm
  calc
    1 * (b ^ 2 + v ^ 2) - v * (2 * v) =
        b ^ 2 + v ^ 2 - v * (2 * v) := by
      exact congrArg (fun x : ℝ => x - v * (2 * v))
        (one_mul (b ^ 2 + v ^ 2))
    _ = b ^ 2 + v ^ 2 - 2 * v ^ 2 := by
      exact congrArg (fun x : ℝ => b ^ 2 + v ^ 2 - x) hv_mul_two_mul
    _ = b ^ 2 + (v ^ 2 - 2 * v ^ 2) := by
      exact (sub_eq_add_neg (b ^ 2 + v ^ 2) (2 * v ^ 2)).trans
        (congrArg (fun x : ℝ => b ^ 2 + x)
          (sub_eq_add_neg (v ^ 2) (2 * v ^ 2)).symm)
    _ = b ^ 2 + -(v ^ 2) := by
      have htwo : 2 * v ^ 2 = v ^ 2 + v ^ 2 := by
        exact two_mul (v ^ 2)
      have hsub : v ^ 2 - 2 * v ^ 2 = -(v ^ 2) := by
        calc
          v ^ 2 - 2 * v ^ 2 = v ^ 2 - (v ^ 2 + v ^ 2) := by
            exact congrArg (fun x : ℝ => v ^ 2 - x) htwo
          _ = -(v ^ 2) := by
            exact sub_add_cancel (v ^ 2) (v ^ 2) ▸ sub_self (v ^ 2)
      exact congrArg (fun x : ℝ => b ^ 2 + x) hsub
    _ = b ^ 2 - v ^ 2 := by
      exact (sub_eq_add_neg (b ^ 2) (v ^ 2)).symm

/-- Pointwise derivative of the high-tail Cauchy amplitude. -/
theorem scalarFourierLaplacePlemelj_highTailCauchyAmplitude_hasDerivAt
    (b v : ℝ) (hb : 0 < b) :
    HasDerivAt
      (fun x : ℝ => x / (b ^ 2 + x ^ 2))
      (scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v)
      v := by
  have hden_ne : b ^ 2 + v ^ 2 ≠ 0 :=
    ne_of_gt (scalarFourierLaplacePlemelj_zero_denominator_pos b hb v)
  have hnum : HasDerivAt (fun x : ℝ => x) 1 v :=
    hasDerivAt_id v
  have hden : HasDerivAt (fun x : ℝ => b ^ 2 + x ^ 2) (2 * v) v := by
    have hconst : HasDerivAt (fun _x : ℝ => b ^ 2) 0 v :=
      hasDerivAt_const v (b ^ 2)
    have hsquare : HasDerivAt (fun x : ℝ => x ^ 2) (2 * v) v := by
      exact hasDerivAt_pow 2 v
    exact hconst.add hsquare
  have hquot :
      HasDerivAt
        (fun x : ℝ => x / (b ^ 2 + x ^ 2))
        ((1 * (b ^ 2 + v ^ 2) - v * (2 * v)) /
          (b ^ 2 + v ^ 2) ^ 2)
        v :=
    hnum.div hden hden_ne
  have hderiv_eq :
      ((1 * (b ^ 2 + v ^ 2) - v * (2 * v)) /
          (b ^ 2 + v ^ 2) ^ 2) =
        scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v := by
    unfold scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative
    exact congrArg
      (fun x : ℝ => x / (b ^ 2 + v ^ 2) ^ 2)
      (scalarFourierLaplacePlemelj_highTailCauchyAmplitude_derivative_numerator
        b v)
  exact Eq.subst
    (motive := fun d : ℝ =>
      HasDerivAt
        (fun x : ℝ => x / (b ^ 2 + x ^ 2))
        d
        v)
    hderiv_eq
    hquot

/-- Continuity of the explicit high-tail Cauchy-amplitude derivative. -/
theorem scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative_continuous
    (b : ℝ) (hb : 0 < b) :
    Continuous
      (fun v : ℝ =>
        scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v) := by
  have hnum_cont :
      Continuous (fun v : ℝ => b ^ 2 - v ^ 2) :=
    continuous_const.sub (continuous_id.pow 2)
  have hden_cont :
      Continuous (fun v : ℝ => (b ^ 2 + v ^ 2) ^ 2) :=
    (continuous_const.add (continuous_id.pow 2)).pow 2
  have hden_ne :
      ∀ v : ℝ, (b ^ 2 + v ^ 2) ^ 2 ≠ 0 := by
    intro v
    exact ne_of_gt
      (sq_pos_of_pos
        (scalarFourierLaplacePlemelj_zero_denominator_pos b hb v))
  unfold scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative
  exact hnum_cont.div hden_cont hden_ne

/-- Endpoint drop of the high-tail Cauchy amplitude from its explicit
derivative. -/
theorem scalarFourierLaplacePlemelj_highTailCauchyAmplitude_negDerivative_integral_eq_drop
    (A b c : ℝ) (hb : 0 < b) (hcA : c ≤ A) :
    (∫ v in c..A,
      -scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v) =
      c / (b ^ 2 + c ^ 2) - A / (b ^ 2 + A ^ 2) := by
  have hderiv :
      ∀ v : ℝ, v ∈ [[c, A]] →
        HasDerivAt
          (fun x : ℝ => x / (b ^ 2 + x ^ 2))
          (scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v)
          v := by
    intro v _hv
    exact scalarFourierLaplacePlemelj_highTailCauchyAmplitude_hasDerivAt b v hb
  have hint :
      IntervalIntegrable
        (fun v : ℝ => scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v)
        volume c A := by
    exact
      (scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative_continuous
        b hb).intervalIntegrable c A
  have hftc :
      (∫ v in c..A,
        scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v) =
        A / (b ^ 2 + A ^ 2) - c / (b ^ 2 + c ^ 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    (∫ v in c..A,
      -scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v) =
        -(∫ v in c..A,
          scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v) := by
      exact intervalIntegral.integral_neg
        (fun v : ℝ =>
          scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v)
    _ = -(A / (b ^ 2 + A ^ 2) - c / (b ^ 2 + c ^ 2)) := by
      exact congrArg Neg.neg hftc
    _ = c / (b ^ 2 + c ^ 2) - A / (b ^ 2 + A ^ 2) := by
      exact neg_sub
        (A / (b ^ 2 + A ^ 2))
        (c / (b ^ 2 + c ^ 2))

/-- Integration-by-parts identity for the damped Cauchy-amplitude sine tail. -/
theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_parts_identity_source
    (A b c : ℝ) (hb : 0 < b) (hcA : c ≤ A) :
    (∫ v in c..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
      -(A / (b ^ 2 + A ^ 2)) * Real.cos A +
        (c / (b ^ 2 + c ^ 2)) * Real.cos c +
          ∫ v in c..A,
            scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v *
              Real.cos v := by
  let g : ℝ → ℝ := fun v : ℝ => v / (b ^ 2 + v ^ 2)
  let D : ℝ → ℝ :=
    fun v : ℝ => scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v
  let h : ℝ → ℝ := fun v : ℝ => -Real.cos v
  have hg_deriv :
      ∀ v : ℝ, v ∈ [[c, A]] → HasDerivAt g (D v) v := by
    intro v _hv
    unfold g
    unfold D
    exact scalarFourierLaplacePlemelj_highTailCauchyAmplitude_hasDerivAt b v hb
  have hh_deriv :
      ∀ v : ℝ, v ∈ [[c, A]] → HasDerivAt h (Real.sin v) v := by
    intro v _hv
    unfold h
    have hcos : HasDerivAt (fun x : ℝ => Real.cos x) (-Real.sin v) v :=
      Real.hasDerivAt_cos v
    have hneg : HasDerivAt (fun x : ℝ => -Real.cos x) (-(-Real.sin v)) v :=
      hcos.neg
    have hneg_eq : -(-Real.sin v) = Real.sin v :=
      neg_neg (Real.sin v)
    exact Eq.subst
      (motive := fun d : ℝ =>
        HasDerivAt (fun x : ℝ => -Real.cos x) d v)
      hneg_eq
      hneg
  have hD_int :
      IntervalIntegrable D volume c A := by
    unfold D
    exact
      (scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative_continuous
        b hb).intervalIntegrable c A
  have hsin_int :
      IntervalIntegrable (fun v : ℝ => Real.sin v) volume c A :=
    continuous_sin.intervalIntegrable c A
  have hparts :
      (∫ v in c..A, g v * Real.sin v) =
        g A * h A - g c * h c - ∫ v in c..A, D v * h v :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      hg_deriv hh_deriv hD_int hsin_int
  have htarget :
      (∫ v in c..A, g v * Real.sin v) =
        -(A / (b ^ 2 + A ^ 2)) * Real.cos A +
          (c / (b ^ 2 + c ^ 2)) * Real.cos c +
            ∫ v in c..A, D v * Real.cos v := by
    calc
      (∫ v in c..A, g v * Real.sin v) =
          g A * h A - g c * h c - ∫ v in c..A, D v * h v := hparts
      _ =
          g A * (-Real.cos A) - g c * (-Real.cos c) -
            ∫ v in c..A, D v * (-Real.cos v) := by
            unfold h
      _ =
          -(g A) * Real.cos A + g c * Real.cos c +
            ∫ v in c..A, D v * Real.cos v := by
            have hleft : g A * (-Real.cos A) = -(g A) * Real.cos A := by
              exact mul_neg (g A) (Real.cos A)
            have hmid : g c * (-Real.cos c) = -(g c * Real.cos c) := by
              exact mul_neg (g c) (Real.cos c)
            have hint :
                (∫ v in c..A, D v * (-Real.cos v)) =
                  -(∫ v in c..A, D v * Real.cos v) := by
              have hpoint :
                  (fun v : ℝ => D v * (-Real.cos v)) =
                    fun v : ℝ => -(D v * Real.cos v) := by
                exact funext
                  (fun v =>
                    mul_neg (D v) (Real.cos v))
              exact Eq.trans
                (congrArg
                  (fun F : ℝ → ℝ => ∫ v in c..A, F v)
                  hpoint)
                (intervalIntegral.integral_neg
                  (fun v : ℝ => D v * Real.cos v))
            calc
              g A * (-Real.cos A) - g c * (-Real.cos c) -
                  ∫ v in c..A, D v * (-Real.cos v) =
                  -(g A) * Real.cos A - (-(g c * Real.cos c)) -
                    (-(∫ v in c..A, D v * Real.cos v)) := by
                    exact congrArg₂ Sub.sub
                      (congrArg₂ Sub.sub hleft hmid)
                      hint
              _ = -(g A) * Real.cos A + g c * Real.cos c +
                    ∫ v in c..A, D v * Real.cos v := by
                    calc
                      -(g A) * Real.cos A - (-(g c * Real.cos c)) -
                          (-(∫ v in c..A, D v * Real.cos v)) =
                          (-(g A) * Real.cos A + g c * Real.cos c) -
                            (-(∫ v in c..A, D v * Real.cos v)) := by
                            exact congrArg
                              (fun x : ℝ =>
                                x - (-(∫ v in c..A, D v * Real.cos v)))
                              (sub_neg_eq_add (-(g A) * Real.cos A)
                                (g c * Real.cos c))
                      _ = (-(g A) * Real.cos A + g c * Real.cos c) +
                            ∫ v in c..A, D v * Real.cos v := by
                            exact sub_neg_eq_add
                              (-(g A) * Real.cos A + g c * Real.cos c)
                              (∫ v in c..A, D v * Real.cos v)
                      _ = -(g A) * Real.cos A + g c * Real.cos c +
                            ∫ v in c..A, D v * Real.cos v := by
                            exact add_assoc
                              (-(g A) * Real.cos A)
                              (g c * Real.cos c)
                              (∫ v in c..A, D v * Real.cos v)
      _ =
          -(A / (b ^ 2 + A ^ 2)) * Real.cos A +
          (c / (b ^ 2 + c ^ 2)) * Real.cos c +
            ∫ v in c..A,
              scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v *
                Real.cos v := by
            unfold g
            unfold D
  exact htarget

/-- Total-variation bound for the derivative term in the damped Cauchy-amplitude
sine-tail integration-by-parts formula. -/
theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_derivativeVariation_source
    (A b c : ℝ) (hb : 0 < b) (hone_le_c : 1 ≤ c)
    (hb_le_c : b ≤ c) (hcA : c ≤ A) :
    |∫ v in c..A,
      scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v *
        Real.cos v| ≤
      c / (b ^ 2 + c ^ 2) - A / (b ^ 2 + A ^ 2) := by
  let g : ℝ → ℝ := fun v : ℝ => v / (b ^ 2 + v ^ 2)
  let D : ℝ → ℝ :=
    fun v : ℝ => scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v
  have hD_nonpos :
      ∀ v : ℝ, v ∈ Set.Icc c A → D v ≤ 0 := by
    intro v hv
    have hcv : c ≤ v := hv.1
    have hb_le_v : b ≤ v := hb_le_c.trans hcv
    have hb_nonneg : 0 ≤ b := le_of_lt hb
    have hv_nonneg : 0 ≤ v := hb_nonneg.trans hb_le_v
    have hsq_le : b ^ 2 ≤ v ^ 2 := by
      exact sq_le_sq.mpr (abs_le_abs.mpr hb_le_v)
    have hnum_nonpos : b ^ 2 - v ^ 2 ≤ 0 :=
      sub_nonpos.mpr hsq_le
    have hden_nonneg : 0 ≤ (b ^ 2 + v ^ 2) ^ 2 :=
      sq_nonneg (b ^ 2 + v ^ 2)
    have hden_pos : 0 < (b ^ 2 + v ^ 2) ^ 2 := by
      have hbase_pos : 0 < b ^ 2 + v ^ 2 :=
        scalarFourierLaplacePlemelj_zero_denominator_pos b hb v
      exact sq_pos_of_pos hbase_pos
    unfold D
    unfold scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative
    exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden_nonneg
  have hD_abs_eq_neg :
      ∀ v : ℝ, v ∈ Set.Icc c A → |D v| = -D v := by
    intro v hv
    exact abs_of_nonpos (hD_nonpos v hv)
  have hpoint :
      ∀ v : ℝ, v ∈ Set.Icc c A →
        ‖D v * Real.cos v‖ ≤ -D v := by
    intro v hv
    have hDabs : |D v| = -D v :=
      hD_abs_eq_neg v hv
    have hDneg_nonneg : 0 ≤ -D v :=
      neg_nonneg.mpr (hD_nonpos v hv)
    calc
      ‖D v * Real.cos v‖ = |D v * Real.cos v| := by
        exact Real.norm_eq_abs (D v * Real.cos v)
      _ = |D v| * |Real.cos v| := by
        exact abs_mul (D v) (Real.cos v)
      _ = (-D v) * |Real.cos v| := by
        exact congrArg (fun r : ℝ => r * |Real.cos v|) hDabs
      _ ≤ (-D v) * 1 := by
        exact mul_le_mul_of_nonneg_left (abs_cos_le_one v) hDneg_nonneg
      _ = -D v := by
        exact mul_one (-D v)
  have hnorm :
      |∫ v in c..A, D v * Real.cos v| ≤
        ∫ v in c..A, -D v := by
    have hnorm' :
        ‖∫ v in c..A, D v * Real.cos v‖ ≤
          ∫ v in c..A, -D v :=
      intervalIntegral.norm_integral_le_of_norm_le
        (fun v hv => hpoint v hv)
    exact hnorm'
  have hanti :
      AntitoneOn g (Set.Ici c) :=
    scalarFourierLaplacePlemelj_highTailCauchyAmplitude_antitoneOn
      b c hb hone_le_c hb_le_c
  have hdrop :
      ∫ v in c..A, -D v = g c - g A := by
    unfold D
    unfold g
    exact
      scalarFourierLaplacePlemelj_highTailCauchyAmplitude_negDerivative_integral_eq_drop
        A b c hb hcA
  have htarget :
      |∫ v in c..A, D v * Real.cos v| ≤ g c - g A :=
    hnorm.trans (le_of_eq hdrop)
  unfold D at htarget
  unfold g at htarget
  exact htarget

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_abs_le_two_of_partsVariation
    (A b c : ℝ) (hb : 0 < b) (hone_le_c : 1 ≤ c)
    (hb_le_c : b ≤ c) (hcA : c ≤ A)
    (hparts :
      (∫ v in c..A,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
        -(A / (b ^ 2 + A ^ 2)) * Real.cos A +
          (c / (b ^ 2 + c ^ 2)) * Real.cos c +
            ∫ v in c..A,
              scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v *
                Real.cos v)
    (hvariation :
      |∫ v in c..A,
        scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v *
          Real.cos v| ≤
        c / (b ^ 2 + c ^ 2) - A / (b ^ 2 + A ^ 2)) :
    |∫ v in c..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 2 := by
  let g : ℝ → ℝ := fun v : ℝ => v / (b ^ 2 + v ^ 2)
  let d : ℝ := ∫ v in c..A,
    scalarFourierLaplacePlemelj_highTailCauchyAmplitudeDerivative b v *
      Real.cos v
  have hA_mem : A ∈ Set.Ici c :=
    hcA
  have hc_mem : c ∈ Set.Ici c :=
    le_refl c
  have hgA_nonneg : 0 ≤ g A :=
    scalarFourierLaplacePlemelj_highTailCauchyAmplitude_nonnegative
      b c A hb hb_le_c hA_mem
  have hgc_nonneg : 0 ≤ g c :=
    scalarFourierLaplacePlemelj_highTailCauchyAmplitude_nonnegative
      b c c hb hb_le_c hc_mem
  have hgA_le_gc : g A ≤ g c :=
    scalarFourierLaplacePlemelj_highTailCauchyAmplitude_antitoneOn
      b c hb hone_le_c hb_le_c hc_mem hA_mem hcA
  have hdiff_nonneg : 0 ≤ g c - g A :=
    sub_nonneg.mpr hgA_le_gc
  have hgc_le_one : g c ≤ 1 :=
    scalarFourierLaplacePlemelj_highTailCauchyAmplitude_le_one
      b c c hb hone_le_c hc_mem
  have hvariation_g : |d| ≤ g c - g A := by
    unfold d
    unfold g
    exact hvariation
  have hendpoint :
      |-(g A) * Real.cos A + g c * Real.cos c + d| ≤
        g A + g c + |d| := by
    calc
      |-(g A) * Real.cos A + g c * Real.cos c + d|
          ≤ |-(g A) * Real.cos A| + |g c * Real.cos c| + |d| := by
            exact abs_add_three (-(g A) * Real.cos A) (g c * Real.cos c) d
      _ = g A * |Real.cos A| + g c * |Real.cos c| + |d| := by
            exact congrArg₂ HAdd.hAdd
              (congrArg₂ HAdd.hAdd
                (calc
                  |-(g A) * Real.cos A| =
                      |-(g A)| * |Real.cos A| := by
                      exact abs_mul (-(g A)) (Real.cos A)
                  _ = g A * |Real.cos A| := by
                      have habs_neg : |-(g A)| = |g A| :=
                        abs_neg (g A)
                      have habs_pos : |g A| = g A :=
                        abs_of_nonneg hgA_nonneg
                      exact congrArg
                        (fun r : ℝ => r * |Real.cos A|)
                        (habs_neg.trans habs_pos))
                (calc
                  |g c * Real.cos c| = |g c| * |Real.cos c| := by
                    exact abs_mul (g c) (Real.cos c)
                  _ = g c * |Real.cos c| := by
                    exact congrArg
                      (fun r : ℝ => r * |Real.cos c|)
                      (abs_of_nonneg hgc_nonneg)))
              rfl
      _ ≤ g A * 1 + g c * 1 + |d| := by
            exact add_le_add_right
              (add_le_add
                (mul_le_mul_of_nonneg_left (abs_cos_le_one A) hgA_nonneg)
                (mul_le_mul_of_nonneg_left (abs_cos_le_one c) hgc_nonneg))
              |d|
      _ = g A + g c + |d| := by
            exact congrArg₂ HAdd.hAdd
              (congrArg₂ HAdd.hAdd (mul_one (g A)) (mul_one (g c)))
              rfl
  have hmain :
      |-(g A) * Real.cos A + g c * Real.cos c + d| ≤
        2 := by
    calc
      |-(g A) * Real.cos A + g c * Real.cos c + d|
          ≤ g A + g c + |d| := hendpoint
      _ ≤ g A + g c + (g c - g A) := by
            exact add_le_add_left hvariation_g (g A + g c)
      _ = g c + g c := by
            calc
              g A + g c + (g c - g A) =
                  g c + (g A + (g c - g A)) := by
                    exact add_left_comm (g A) (g c) (g c - g A)
              _ = g c + g c := by
                    have hinner : g A + (g c - g A) = g c := by
                      calc
                        g A + (g c - g A) =
                            (g c - g A) + g A := by
                          exact add_comm (g A) (g c - g A)
                        _ = g c := by
                          exact sub_add_cancel (g c) (g A)
                    exact congrArg (fun r : ℝ => g c + r) hinner
      _ = g c * 2 := by
            exact (two_mul (g c)).symm
      _ ≤ 1 * 2 := by
            exact mul_le_mul_of_nonneg_right hgc_le_one zero_le_two
      _ = 2 := by
            exact one_mul 2
  have hparts_g :
      (∫ v in c..A,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
        -(g A) * Real.cos A + g c * Real.cos c + d := by
    unfold g
    unfold d
    exact hparts
  exact Eq.subst
    (motive := fun x : ℝ => |x| ≤ 2)
    hparts_g.symm
    hmain

/-- Damped Cauchy-amplitude sine tail bound from integration by parts and
total variation.

This is the exact scalar tail estimate needed by the Plemelj projection.  Its
proof is the finite-interval integration-by-parts calculation for
`v / (b ^ 2 + v ^ 2)` against `sin`. -/
theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_abs_le_two_partsVariation_source
    (A b c : ℝ) (hb : 0 < b) (hone_le_c : 1 ≤ c)
    (hb_le_c : b ≤ c) (hcA : c ≤ A) :
    |∫ v in c..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 2 := by
  exact
    scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_abs_le_two_of_partsVariation
      A b c hb hone_le_c hb_le_c hcA
      (scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_parts_identity_source
        A b c hb hcA)
      (scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_derivativeVariation_source
        A b c hb hone_le_c hb_le_c hcA)

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_abs_le_two
    (A b c : ℝ) (hb : 0 < b) (hone_le_c : 1 ≤ c)
    (hb_le_c : b ≤ c) (hcA : c ≤ A) :
    |∫ v in c..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 2 := by
  exact
    scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_abs_le_two_partsVariation_source
      A b c hb hone_le_c hb_le_c hcA

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_split_at_one
    (A b : ℝ) (hb : 0 < b) (hb_le_one : b ≤ 1)
    (hone_le_A : 1 ≤ A) :
    (∫ v in b..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
      (∫ v in b..1,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
        ∫ v in (1 : ℝ)..A,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v := by
  let f : ℝ → ℝ :=
    fun v : ℝ => (v / (b ^ 2 + v ^ 2)) * Real.sin v
  have hden_cont : Continuous (fun v : ℝ => b ^ 2 + v ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ v : ℝ, b ^ 2 + v ^ 2 ≠ 0 := by
    intro v
    exact
      scalarFourierLaplacePlemelj_zero_denominator_ne_zero b hb v
  have hquot_cont : Continuous (fun v : ℝ => v / (b ^ 2 + v ^ 2)) :=
    continuous_id.div hden_cont hden_ne
  have hf_cont : Continuous f := by
    unfold f
    exact hquot_cont.mul Real.continuous_sin
  have hleft : IntervalIntegrable f volume b 1 :=
    hf_cont.intervalIntegrable b 1
  have hright : IntervalIntegrable f volume (1 : ℝ) A :=
    hf_cont.intervalIntegrable 1 A
  calc
    (∫ v in b..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v)
        = ∫ v in b..A, f v := by
          unfold f
          rfl
    _ =
        (∫ v in b..1, f v) + ∫ v in (1 : ℝ)..A, f v := by
          exact
            (intervalIntegral.integral_add_adjacent_intervals
              hleft hright).symm
    _ =
        (∫ v in b..1,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
          ∫ v in (1 : ℝ)..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v := by
          unfold f
          rfl

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_abs_le_two_pi
    (A b c : ℝ) (hb : 0 < b) (hone_le_c : 1 ≤ c)
    (hb_le_c : b ≤ c) (hcA : c ≤ A) :
    |∫ v in c..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤
      (2 : ℝ) * Real.pi := by
  exact
    (scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_abs_le_two
      A b c hb hone_le_c hb_le_c hcA).trans
        scalarFourierLaplacePlemelj_two_le_two_pi

theorem scalarFourierLaplacePlemelj_three_le_two_pi :
    (3 : ℝ) ≤ (2 : ℝ) * Real.pi := by
  have hpi_le_two_pi : Real.pi ≤ (2 : ℝ) * Real.pi := by
    calc
      Real.pi = (1 : ℝ) * Real.pi := by
        exact (one_mul Real.pi).symm
      _ ≤ (2 : ℝ) * Real.pi := by
        exact mul_le_mul_of_nonneg_right one_le_two Real.pi_pos.le
  exact Real.pi_gt_three.le.trans hpi_le_two_pi

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_crossing_abs_le_two_pi
    (A b : ℝ) (hb : 0 < b) (_hbA : b ≤ A)
    (hb_le_one : b ≤ 1) (hone_le_A : 1 ≤ A) :
    |∫ v in (b)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤
      (2 : ℝ) * Real.pi := by
  have hsplit :
      (∫ v in b..A,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
        (∫ v in b..1,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
          ∫ v in (1 : ℝ)..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v :=
    scalarFourierLaplacePlemelj_dampedSineIntegral_tail_split_at_one
      A b hb hb_le_one hone_le_A
  have hlow :
      |∫ v in b..1,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 1 :=
    scalarFourierLaplacePlemelj_dampedSineIntegral_tail_low_abs_le_one
      1 b hb hb_le_one (le_refl 1)
  have hhigh :
      |∫ v in (1 : ℝ)..A,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 2 :=
    scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_abs_le_two
      A b 1 hb (le_refl 1) hb_le_one hone_le_A
  have hsum :
      |(∫ v in b..1,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
        ∫ v in (1 : ℝ)..A,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 3 := by
    calc
      |(∫ v in b..1,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
        ∫ v in (1 : ℝ)..A,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v|
          ≤
          |∫ v in b..1,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v| +
            |∫ v in (1 : ℝ)..A,
              (v / (b ^ 2 + v ^ 2)) * Real.sin v| := by
            exact abs_add
              (∫ v in b..1,
                (v / (b ^ 2 + v ^ 2)) * Real.sin v)
              (∫ v in (1 : ℝ)..A,
                (v / (b ^ 2 + v ^ 2)) * Real.sin v)
      _ ≤ 1 + 2 := by
            exact add_le_add hlow hhigh
      _ = 3 := by
            rfl
  calc
    |∫ v in (b)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v|
        =
        |(∫ v in b..1,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
          ∫ v in (1 : ℝ)..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v| := by
          exact congrArg abs hsplit
    _ ≤ 3 := hsum
    _ ≤ (2 : ℝ) * Real.pi :=
        scalarFourierLaplacePlemelj_three_le_two_pi

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_abs_le_two_pi
    (A b : ℝ) (hb : 0 < b) (hbA : b ≤ A) :
    |∫ v in (b)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤
      (2 : ℝ) * Real.pi := by
  match le_or_gt A 1 with
  | Or.inl hA_le_one =>
      have hlow :
          |∫ v in (b)..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 1 :=
        scalarFourierLaplacePlemelj_dampedSineIntegral_tail_low_abs_le_one
          A b hb hbA hA_le_one
      exact hlow.trans scalarFourierLaplacePlemelj_one_le_two_pi
  | Or.inr hone_lt_A =>
      match le_or_gt b 1 with
      | Or.inl hb_le_one =>
          exact
            scalarFourierLaplacePlemelj_dampedSineIntegral_tail_crossing_abs_le_two_pi
              A b hb hbA hb_le_one (le_of_lt hone_lt_A)
      | Or.inr hone_lt_b =>
          exact
            scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_abs_le_two_pi
              A b b hb (le_of_lt hone_lt_b) (le_refl b) hbA

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_split_at_scale
    (A b : ℝ) (hb : 0 < b) (hbA : b ≤ A) :
    (∫ v in (0)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
      (∫ v in (0)..b,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
        ∫ v in b..A,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v := by
  let f : ℝ → ℝ :=
    fun v : ℝ => (v / (b ^ 2 + v ^ 2)) * Real.sin v
  have hden_cont : Continuous (fun v : ℝ => b ^ 2 + v ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ v : ℝ, b ^ 2 + v ^ 2 ≠ 0 := by
    intro v
    exact
      scalarFourierLaplacePlemelj_zero_denominator_ne_zero b hb v
  have hquot_cont : Continuous (fun v : ℝ => v / (b ^ 2 + v ^ 2)) :=
    continuous_id.div hden_cont hden_ne
  have hf_cont : Continuous f := by
    unfold f
    exact hquot_cont.mul Real.continuous_sin
  have hleft : IntervalIntegrable f volume 0 b :=
    hf_cont.intervalIntegrable 0 b
  have hright : IntervalIntegrable f volume b A :=
    hf_cont.intervalIntegrable b A
  calc
    (∫ v in (0)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v)
        = ∫ v in (0)..A, f v := by
          unfold f
          rfl
    _ =
        (∫ v in (0)..b, f v) + ∫ v in b..A, f v := by
          exact
            (intervalIntegral.integral_add_adjacent_intervals
              hleft hright).symm
    _ =
        (∫ v in (0)..b,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
          ∫ v in b..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v := by
          unfold f
          rfl

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_abs_le_one_add_two_pi
    (A b : ℝ) (hA : 0 ≤ A) (hb : 0 < b) :
    |∫ v in (0)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤
      1 + (2 : ℝ) * Real.pi := by
  match le_or_gt A b with
  | Or.inl hA_le_b =>
      have hsmall :
          |∫ v in (0)..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 1 :=
        scalarFourierLaplacePlemelj_dampedSineIntegral_smallPrefix_abs_le_one
          A b hA hA_le_b hb
      have hone_le_target :
          (1 : ℝ) ≤ 1 + (2 : ℝ) * Real.pi :=
        le_add_of_nonneg_right (mul_nonneg zero_le_two Real.pi_pos.le)
      exact hsmall.trans hone_le_target
  | Or.inr hb_lt_A =>
      have hbA : b ≤ A :=
        le_of_lt hb_lt_A
      have hsplit :
          (∫ v in (0)..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
            (∫ v in (0)..b,
              (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
              ∫ v in b..A,
                (v / (b ^ 2 + v ^ 2)) * Real.sin v :=
        scalarFourierLaplacePlemelj_dampedSineIntegral_split_at_scale
          A b hb hbA
      have hsmall :
          |∫ v in (0)..b,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 1 :=
        scalarFourierLaplacePlemelj_dampedSineIntegral_smallPrefix_abs_le_one
          b b hb.le (le_refl b) hb
      have htail :
          |∫ v in (b)..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤
            (2 : ℝ) * Real.pi :=
        scalarFourierLaplacePlemelj_dampedSineIntegral_tail_abs_le_two_pi
          A b hb hbA
      have hsum :
          |(∫ v in (0)..b,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
            ∫ v in b..A,
              (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤
            1 + (2 : ℝ) * Real.pi := by
        calc
          |(∫ v in (0)..b,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
            ∫ v in b..A,
              (v / (b ^ 2 + v ^ 2)) * Real.sin v|
              ≤
              |∫ v in (0)..b,
                (v / (b ^ 2 + v ^ 2)) * Real.sin v| +
                |∫ v in b..A,
                  (v / (b ^ 2 + v ^ 2)) * Real.sin v| := by
                exact abs_add
                  (∫ v in (0)..b,
                    (v / (b ^ 2 + v ^ 2)) * Real.sin v)
                  (∫ v in b..A,
                    (v / (b ^ 2 + v ^ 2)) * Real.sin v)
          _ ≤ 1 + (2 : ℝ) * Real.pi := by
                exact add_le_add hsmall htail
      calc
        |∫ v in (0)..A,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v|
            =
            |(∫ v in (0)..b,
              (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
              ∫ v in b..A,
                (v / (b ^ 2 + v ^ 2)) * Real.sin v| := by
              exact congrArg abs hsplit
        _ ≤ 1 + (2 : ℝ) * Real.pi := hsum

/-- Positive-frequency change of variables `v = y*u` for the normalized
Hilbert-sine kernel. -/
theorem scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_eq_dampedSineIntegral
    (R y : ℝ) (hy : 0 < y) :
    (∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin (y * u)) =
      ∫ v in (0)..(y * R),
        (v / (y ^ 2 + v ^ 2)) * Real.sin v := by
  let G : ℝ → ℝ :=
    fun v : ℝ => (v / (y ^ 2 + v ^ 2)) * Real.sin v
  have hpoint :
      ∀ u : ℝ,
        (u / (1 + u ^ 2)) * Real.sin (y * u) =
          y * G (u * y) := by
    intro u
    have hcoeff :
        y * ((u * y) / (y ^ 2 + (u * y) ^ 2)) =
          u / (1 + u ^ 2) :=
      scalarFourierLaplacePlemelj_scaledHilbertSineKernel_coefficient_identity
        y hy u
    calc
      (u / (1 + u ^ 2)) * Real.sin (y * u)
          =
          (y * ((u * y) / (y ^ 2 + (u * y) ^ 2))) *
            Real.sin (y * u) := by
            exact congrArg
              (fun r : ℝ => r * Real.sin (y * u))
              hcoeff.symm
      _ =
          y *
            (((u * y) / (y ^ 2 + (u * y) ^ 2)) *
              Real.sin (u * y)) := by
            have hphase : Real.sin (y * u) = Real.sin (u * y) :=
              congrArg Real.sin (mul_comm y u)
            calc
              (y * ((u * y) / (y ^ 2 + (u * y) ^ 2))) *
                  Real.sin (y * u)
                  =
                  (y * ((u * y) / (y ^ 2 + (u * y) ^ 2))) *
                    Real.sin (u * y) := by
                    exact congrArg
                      (fun s : ℝ =>
                        (y * ((u * y) / (y ^ 2 + (u * y) ^ 2))) * s)
                      hphase
              _ =
                  y *
                    (((u * y) / (y ^ 2 + (u * y) ^ 2)) *
                      Real.sin (u * y)) := by
                    exact mul_assoc y
                      ((u * y) / (y ^ 2 + (u * y) ^ 2))
                      (Real.sin (u * y))
      _ = y * G (u * y) := by
            unfold G
            rfl
  have hconst :
      (∫ u in (0)..R,
        (u / (1 + u ^ 2)) * Real.sin (y * u)) =
        y * ∫ u in (0)..R, G (u * y) := by
    calc
      (∫ u in (0)..R,
        (u / (1 + u ^ 2)) * Real.sin (y * u))
          = ∫ u in (0)..R, y * G (u * y) := by
            exact intervalIntegral.integral_congr
              (Filter.Eventually.of_forall hpoint)
      _ = y * ∫ u in (0)..R, G (u * y) := by
            exact intervalIntegral.integral_const_mul
              (a := 0) (b := R) (μ := volume)
              y
              (fun u : ℝ => G (u * y))
  have hsubst :
      y * ∫ u in (0)..R, G (u * y) =
        ∫ v in (0 * y)..(R * y), G v :=
    intervalIntegral.smul_integral_comp_mul_right
      (f := G) (a := 0) (b := R) y
  calc
    (∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin (y * u))
        = y * ∫ u in (0)..R, G (u * y) := hconst
    _ = ∫ v in (0 * y)..(R * y), G v := hsubst
    _ = ∫ v in (0)..(y * R), G v := by
          exact congrArg₂
            (fun l r : ℝ => ∫ v in l..r, G v)
            (zero_mul y)
            (mul_comm R y)
    _ =
        ∫ v in (0)..(y * R),
          (v / (y ^ 2 + v ^ 2)) * Real.sin v := by
          unfold G
          rfl

theorem scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_nonneg_radius_pos_frequency
    (R y : ℝ) (hR : 0 ≤ R) (hy : 0 < y) :
    |∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin (y * u)| ≤
      1 + (2 : ℝ) * Real.pi := by
  have hA_nonneg : 0 ≤ y * R :=
    mul_nonneg hy.le hR
  have hscale :
      (∫ u in (0)..R,
        (u / (1 + u ^ 2)) * Real.sin (y * u)) =
        ∫ v in (0)..(y * R),
          (v / (y ^ 2 + v ^ 2)) * Real.sin v :=
    scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_eq_dampedSineIntegral
      R y hy
  calc
    |∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin (y * u)|
        =
        |∫ v in (0)..(y * R),
          (v / (y ^ 2 + v ^ 2)) * Real.sin v| := by
          exact congrArg abs hscale
    _ ≤ 1 + (2 : ℝ) * Real.pi :=
        scalarFourierLaplacePlemelj_dampedSineIntegral_abs_le_one_add_two_pi
          (y * R) y hA_nonneg hy

/-- The normalized Hilbert-sine kernel is even in the integration variable. -/
theorem scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_integrand_even
    (y u : ℝ) :
    ((-u) / (1 + (-u) ^ 2)) * Real.sin (y * (-u)) =
      (u / (1 + u ^ 2)) * Real.sin (y * u) := by
  have hden : 1 + (-u) ^ 2 = 1 + u ^ 2 := by
    exact congrArg (fun r : ℝ => 1 + r) (neg_sq u)
  have harg : y * (-u) = -(y * u) :=
    mul_neg y u
  have hsin : Real.sin (y * (-u)) = -Real.sin (y * u) :=
    (congrArg Real.sin harg).trans (Real.sin_neg (y * u))
  have hquot :
      (-u) / (1 + (-u) ^ 2) = -(u / (1 + u ^ 2)) := by
    calc
      (-u) / (1 + (-u) ^ 2)
          = (-u) / (1 + u ^ 2) := by
            exact congrArg (fun d : ℝ => (-u) / d) hden
      _ = -(u / (1 + u ^ 2)) := by
            exact neg_div u (1 + u ^ 2)
  calc
    ((-u) / (1 + (-u) ^ 2)) * Real.sin (y * (-u))
        = (-(u / (1 + u ^ 2))) * Real.sin (y * (-u)) := by
          exact congrArg
            (fun r : ℝ => r * Real.sin (y * (-u)))
            hquot
    _ = (-(u / (1 + u ^ 2))) * (-Real.sin (y * u)) := by
          exact congrArg
            (fun s : ℝ => (-(u / (1 + u ^ 2))) * s)
            hsin
    _ = (u / (1 + u ^ 2)) * Real.sin (y * u) := by
          exact neg_mul_neg (u / (1 + u ^ 2)) (Real.sin (y * u))

/-- Positive-frequency normalized half-window Hilbert-sine Dirichlet bound. -/
theorem scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_pos_frequency
    (R y : ℝ) (hy : 0 < y) :
    |∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin (y * u)| ≤
      1 + (2 : ℝ) * Real.pi := by
  match le_or_gt 0 R with
  | Or.inl hR =>
      exact
        scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_nonneg_radius_pos_frequency
          R y hR hy
  | Or.inr hR_neg =>
      let S : ℝ := -R
      let F : ℝ → ℝ :=
        fun u : ℝ => (u / (1 + u ^ 2)) * Real.sin (y * u)
      have hS_nonneg : 0 ≤ S := by
        unfold S
        exact neg_nonneg.mpr (le_of_lt hR_neg)
      have hcomp :
          (∫ u in (0)..S, F (-u)) = ∫ u in R..0, F u := by
        have hR_eq : R = -S := by
          unfold S
          exact (neg_neg R).symm
        calc
          (∫ u in (0)..S, F (-u))
              = ∫ u in (-S)..0, F u := by
                exact intervalIntegral.integral_comp_neg
                  (f := F) (a := 0) (b := S)
          _ = ∫ u in R..0, F u := by
                exact congrArg
                  (fun l : ℝ => ∫ u in l..0, F u)
                  hR_eq.symm
      have heven :
          (∫ u in (0)..S, F (-u)) = ∫ u in (0)..S, F u := by
        exact intervalIntegral.integral_congr
          (Filter.Eventually.of_forall
            (fun u : ℝ => by
              unfold F
              exact
                scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_integrand_even
                  y u))
      have hR_to_S :
          (∫ u in (0)..R, F u) = -∫ u in (0)..S, F u := by
        calc
          (∫ u in (0)..R, F u)
              = -∫ u in R..0, F u := by
                exact intervalIntegral.integral_symm R 0
          _ = -∫ u in (0)..S, F (-u) := by
                exact congrArg Neg.neg hcomp.symm
          _ = -∫ u in (0)..S, F u := by
                exact congrArg Neg.neg heven
      have hS_bound :
          |∫ u in (0)..S, F u| ≤ 1 + (2 : ℝ) * Real.pi := by
        unfold F
        exact
          scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_nonneg_radius_pos_frequency
            S y hS_nonneg hy
      calc
        |∫ u in (0)..R,
          (u / (1 + u ^ 2)) * Real.sin (y * u)|
            = |∫ u in (0)..R, F u| := by
              unfold F
              rfl
        _ = |-∫ u in (0)..S, F u| := by
              exact congrArg abs hR_to_S
        _ = |∫ u in (0)..S, F u| := by
              exact abs_neg (∫ u in (0)..S, F u)
        _ ≤ 1 + (2 : ℝ) * Real.pi := hS_bound

/-- Changing the sign of the frequency negates the normalized half-window
Hilbert-sine integral. -/
theorem scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_neg_frequency
    (R y : ℝ) :
    (∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin ((-y) * u)) =
      -∫ u in (0)..R,
        (u / (1 + u ^ 2)) * Real.sin (y * u) := by
  let F : ℝ → ℝ :=
    fun u : ℝ => (u / (1 + u ^ 2)) * Real.sin (y * u)
  have hpoint :
      ∀ u : ℝ,
        (u / (1 + u ^ 2)) * Real.sin ((-y) * u) = -F u := by
    intro u
    have harg : (-y) * u = -(y * u) :=
      neg_mul y u
    have hsin : Real.sin ((-y) * u) = -Real.sin (y * u) :=
      (congrArg Real.sin harg).trans (Real.sin_neg (y * u))
    calc
      (u / (1 + u ^ 2)) * Real.sin ((-y) * u)
          = (u / (1 + u ^ 2)) * (-Real.sin (y * u)) := by
            exact congrArg
              (fun s : ℝ => (u / (1 + u ^ 2)) * s)
              hsin
      _ = -((u / (1 + u ^ 2)) * Real.sin (y * u)) := by
            exact mul_neg (u / (1 + u ^ 2)) (Real.sin (y * u))
      _ = -F u := by
            unfold F
            rfl
  calc
    (∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin ((-y) * u))
        = ∫ u in (0)..R, -F u := by
          exact intervalIntegral.integral_congr
            (Filter.Eventually.of_forall hpoint)
    _ = -∫ u in (0)..R, F u := by
          exact intervalIntegral.integral_neg
    _ =
        -∫ u in (0)..R,
          (u / (1 + u ^ 2)) * Real.sin (y * u) := by
          unfold F
          rfl

/-- Nonzero-frequency normalized half-window Hilbert-sine Dirichlet bound. -/
theorem scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_ne_zero
    (R y : ℝ) (hy : y ≠ 0) :
    |∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin (y * u)| ≤
      1 + (2 : ℝ) * Real.pi := by
  match lt_or_gt_of_ne hy with
  | Or.inl hy_neg =>
      let yp : ℝ := -y
      have hyp_pos : 0 < yp := by
        unfold yp
        exact neg_pos.mpr hy_neg
      have hneg :
          (∫ u in (0)..R,
            (u / (1 + u ^ 2)) * Real.sin (y * u)) =
            -∫ u in (0)..R,
              (u / (1 + u ^ 2)) * Real.sin (yp * u) := by
        have hy_eq : y = -yp := by
          unfold yp
          exact (neg_neg y).symm
        calc
          (∫ u in (0)..R,
            (u / (1 + u ^ 2)) * Real.sin (y * u))
              =
              ∫ u in (0)..R,
                (u / (1 + u ^ 2)) * Real.sin ((-yp) * u) := by
                exact intervalIntegral.integral_congr
                  (Filter.Eventually.of_forall
                    (fun u : ℝ => by
                      exact congrArg
                        (fun z : ℝ =>
                          (u / (1 + u ^ 2)) * Real.sin (z * u))
                        hy_eq))
          _ =
              -∫ u in (0)..R,
                (u / (1 + u ^ 2)) * Real.sin (yp * u) := by
                exact
                  scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_neg_frequency
                    R yp
      have hpos :
          |∫ u in (0)..R,
            (u / (1 + u ^ 2)) * Real.sin (yp * u)| ≤
            1 + (2 : ℝ) * Real.pi :=
        scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_pos_frequency
          R yp hyp_pos
      calc
        |∫ u in (0)..R,
          (u / (1 + u ^ 2)) * Real.sin (y * u)|
            =
            |-∫ u in (0)..R,
              (u / (1 + u ^ 2)) * Real.sin (yp * u)| := by
              exact congrArg abs hneg
        _ =
            |∫ u in (0)..R,
              (u / (1 + u ^ 2)) * Real.sin (yp * u)| := by
              exact abs_neg
                (∫ u in (0)..R,
                  (u / (1 + u ^ 2)) * Real.sin (yp * u))
        _ ≤ 1 + (2 : ℝ) * Real.pi := hpos
  | Or.inr hy_pos =>
      exact
        scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_pos_frequency
          R y hy_pos

theorem scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi
    (R y : ℝ) :
    |∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin (y * u)| ≤
      1 + (2 : ℝ) * Real.pi := by
  match eq_or_ne y 0 with
  | Or.inl hy =>
      have hzero :
          (∫ u in (0)..R,
            (u / (1 + u ^ 2)) * Real.sin (y * u)) = 0 := by
        calc
          (∫ u in (0)..R,
            (u / (1 + u ^ 2)) * Real.sin (y * u))
              =
              ∫ u in (0)..R,
                (u / (1 + u ^ 2)) * Real.sin (0 * u) := by
                exact intervalIntegral.integral_congr
                  (Filter.Eventually.of_forall
                    (fun u : ℝ => by
                      exact congrArg
                        (fun z : ℝ =>
                          (u / (1 + u ^ 2)) * Real.sin (z * u))
                        hy))
          _ =
              ∫ u in (0)..R, 0 := by
                exact intervalIntegral.integral_congr
                  (Filter.Eventually.of_forall
                    (fun u : ℝ => by
                      exact mul_zero (u / (1 + u ^ 2))))
          _ = 0 := by
                exact intervalIntegral.integral_zero
      have htarget : |(0 : ℝ)| ≤ 1 + (2 : ℝ) * Real.pi := by
        have hC_nonneg : 0 ≤ 1 + (2 : ℝ) * Real.pi :=
          add_nonneg zero_le_one (mul_nonneg zero_le_two Real.pi_pos.le)
        exact (abs_zero : |(0 : ℝ)| = 0).le.trans hC_nonneg
      exact Eq.subst
        (motive := fun z : ℝ => |z| ≤ 1 + (2 : ℝ) * Real.pi)
        hzero.symm
        htarget
  | Or.inr hy =>
      exact
        scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_ne_zero
          R y hy

/-- Scaling reduction from the width-`a` Hilbert-Cauchy sine kernel to the
normalized kernel `u / (1 + u^2)`. -/
theorem scalarFourierLaplacePlemelj_scaledHilbertSineKernel_coefficient_identity
    (a : ℝ) (ha : 0 < a) (u : ℝ) :
    a * ((u * a) / (a ^ 2 + (u * a) ^ 2)) =
      u / (1 + u ^ 2) := by
  have ha_ne : a ≠ 0 :=
    ne_of_gt ha
  have ha_sq_ne : a ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 ha_ne
  have hnum : a * (u * a) = u * a ^ 2 := by
    calc
      a * (u * a) = (a * u) * a := by
        exact (mul_assoc a u a).symm
      _ = (u * a) * a := by
        exact congrArg (fun r : ℝ => r * a) (mul_comm a u)
      _ = u * (a * a) := by
        exact mul_assoc u a a
      _ = u * a ^ 2 := by
        exact congrArg (fun r : ℝ => u * r) (sq a).symm
  have huasq : (u * a) ^ 2 = u ^ 2 * a ^ 2 := by
    exact mul_pow u a 2
  have hden : a ^ 2 + (u * a) ^ 2 = (1 + u ^ 2) * a ^ 2 := by
    calc
      a ^ 2 + (u * a) ^ 2
          = a ^ 2 + u ^ 2 * a ^ 2 := by
            exact congrArg (fun r : ℝ => a ^ 2 + r) huasq
      _ = 1 * a ^ 2 + u ^ 2 * a ^ 2 := by
            exact congrArg
              (fun r : ℝ => r + u ^ 2 * a ^ 2)
              (one_mul (a ^ 2)).symm
      _ = (1 + u ^ 2) * a ^ 2 := by
            exact (add_mul 1 (u ^ 2) (a ^ 2)).symm
  calc
    a * ((u * a) / (a ^ 2 + (u * a) ^ 2))
        = (a * (u * a)) / (a ^ 2 + (u * a) ^ 2) := by
          exact mul_div_assoc' a (u * a) (a ^ 2 + (u * a) ^ 2)
    _ = (u * a ^ 2) / (a ^ 2 + (u * a) ^ 2) := by
          exact congrArg
            (fun r : ℝ => r / (a ^ 2 + (u * a) ^ 2))
            hnum
    _ = (u * a ^ 2) / ((1 + u ^ 2) * a ^ 2) := by
          exact congrArg (fun r : ℝ => (u * a ^ 2) / r) hden
    _ = u / (1 + u ^ 2) := by
          exact mul_div_mul_right u (1 + u ^ 2) ha_sq_ne

theorem scalarFourierLaplacePlemelj_scaledHilbertSineKernel_phase_identity
    (a x u : ℝ) :
    Real.sin ((u * a) * x) = Real.sin ((a * x) * u) := by
  have harg : (u * a) * x = (a * x) * u := by
    calc
      (u * a) * x = u * (a * x) := by
        exact mul_assoc u a x
      _ = (a * x) * u := by
        exact mul_comm u (a * x)
  exact congrArg Real.sin harg

theorem scalarFourierLaplacePlemelj_halfHilbertSineKernel_scaled_integrand_identity
    (a : ℝ) (ha : 0 < a) (x u : ℝ) :
    a *
      (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
        Real.sin ((u * a) * x)) =
      (u / (1 + u ^ 2)) * Real.sin ((a * x) * u) := by
  have hcoeff :
      a * ((u * a) / (a ^ 2 + (u * a) ^ 2)) =
        u / (1 + u ^ 2) :=
    scalarFourierLaplacePlemelj_scaledHilbertSineKernel_coefficient_identity
      a ha u
  have hphase :
      Real.sin ((u * a) * x) = Real.sin ((a * x) * u) :=
    scalarFourierLaplacePlemelj_scaledHilbertSineKernel_phase_identity
      a x u
  calc
    a *
      (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
        Real.sin ((u * a) * x))
        =
        (a * ((u * a) / (a ^ 2 + (u * a) ^ 2))) *
          Real.sin ((u * a) * x) := by
          exact mul_assoc a
            ((u * a) / (a ^ 2 + (u * a) ^ 2))
            (Real.sin ((u * a) * x))
    _ =
        (u / (1 + u ^ 2)) *
          Real.sin ((u * a) * x) := by
          exact congrArg
            (fun r : ℝ => r * Real.sin ((u * a) * x))
            hcoeff
    _ =
        (u / (1 + u ^ 2)) * Real.sin ((a * x) * u) := by
          exact congrArg
            (fun s : ℝ => (u / (1 + u ^ 2)) * s)
            hphase

/-- Endpoint cancellation for the positive scaling `t = a*u`. -/
theorem scalarFourierLaplacePlemelj_halfHilbertSineKernel_scaled_endpoint
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    (T / a) * a = T := by
  exact div_mul_cancel₀ T (ne_of_gt ha)

/-- Change-of-variables form of the half-window Hilbert-Cauchy sine kernel
under `t = a*u`, before applying the pointwise algebra identity. -/
theorem scalarFourierLaplacePlemelj_halfHilbertSineKernel_eq_scaled_integral
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    (∫ t in (0)..T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) =
      a *
        ∫ u in (0)..(T / a),
          (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
            Real.sin ((u * a) * x)) := by
  let F : ℝ → ℝ :=
    fun t : ℝ => (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)
  have hend : (T / a) * a = T :=
    scalarFourierLaplacePlemelj_halfHilbertSineKernel_scaled_endpoint
      a ha T
  have hsubst :
      a *
        ∫ u in (0)..(T / a), F (u * a) =
        ∫ t in (0 * a)..((T / a) * a), F t := by
    exact intervalIntegral.smul_integral_comp_mul_right
      (f := F) (a := 0) (b := T / a) a
  calc
    (∫ t in (0)..T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x))
        = ∫ t in (0)..T, F t := by
          unfold F
          rfl
    _ = ∫ t in (0 * a)..((T / a) * a), F t := by
          exact congrArg₂
            (fun l r : ℝ => ∫ t in l..r, F t)
            (zero_mul a).symm
            hend.symm
    _ =
        a *
          ∫ u in (0)..(T / a), F (u * a) := by
          exact hsubst.symm
    _ =
        a *
          ∫ u in (0)..(T / a),
            (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
              Real.sin ((u * a) * x)) := by
          unfold F
          rfl

theorem scalarFourierLaplacePlemelj_halfHilbertSineKernel_eq_normalized
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    (∫ t in (0)..T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) =
      ∫ u in (0)..(T / a),
        (u / (1 + u ^ 2)) * Real.sin ((a * x) * u) := by
  have hscale :
      (∫ t in (0)..T,
        (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) =
        a *
          ∫ u in (0)..(T / a),
            (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
              Real.sin ((u * a) * x)) :=
    scalarFourierLaplacePlemelj_halfHilbertSineKernel_eq_scaled_integral
      a ha T x
  have hpoint :
      ∀ u : ℝ,
        a *
          (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
            Real.sin ((u * a) * x)) =
          (u / (1 + u ^ 2)) * Real.sin ((a * x) * u) :=
    fun u : ℝ =>
      scalarFourierLaplacePlemelj_halfHilbertSineKernel_scaled_integrand_identity
        a ha x u
  have hintegral :
      a *
        ∫ u in (0)..(T / a),
          (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
            Real.sin ((u * a) * x)) =
        ∫ u in (0)..(T / a),
          (u / (1 + u ^ 2)) * Real.sin ((a * x) * u) := by
    calc
      a *
        ∫ u in (0)..(T / a),
          (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
            Real.sin ((u * a) * x))
          =
          ∫ u in (0)..(T / a),
            a *
              (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
                Real.sin ((u * a) * x)) := by
            exact (intervalIntegral.integral_const_mul
              (a := 0) (b := T / a) (μ := volume)
              a
              (fun u : ℝ =>
                (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
                  Real.sin ((u * a) * x))).symm
      _ =
          ∫ u in (0)..(T / a),
            (u / (1 + u ^ 2)) * Real.sin ((a * x) * u) := by
            exact intervalIntegral.integral_congr
              (Filter.Eventually.of_forall hpoint)
  exact hscale.trans hintegral

theorem scalarFourierLaplacePlemelj_halfHilbertSineKernel_abs_le_one_add_two_pi
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    |∫ t in (0)..T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| ≤
      1 + (2 : ℝ) * Real.pi := by
  have hscale :
      (∫ t in (0)..T,
        (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) =
        ∫ u in (0)..(T / a),
          (u / (1 + u ^ 2)) * Real.sin ((a * x) * u) :=
    scalarFourierLaplacePlemelj_halfHilbertSineKernel_eq_normalized
      a ha T x
  calc
    |∫ t in (0)..T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)|
        =
        |∫ u in (0)..(T / a),
          (u / (1 + u ^ 2)) * Real.sin ((a * x) * u)| := by
          exact congrArg abs hscale
    _ ≤ 1 + (2 : ℝ) * Real.pi :=
        scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi
          (T / a) (a * x)


/-- Symmetric finite windows of the Hilbert-Cauchy sine kernel reduce to twice
the positive half-window because the kernel is even. -/
theorem scalarFourierLaplacePlemelj_finiteHilbertSineKernel_symmetric_eq_two_half
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    (∫ t in Set.Icc (-T) T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) =
      (2 : ℝ) *
        ∫ t in (0)..T,
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) := by
  let f : ℝ → ℝ :=
    fun t : ℝ => (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 :=
    scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha
  have hquot_cont : Continuous (fun t : ℝ => t / (a ^ 2 + t ^ 2)) :=
    continuous_id.div hden_cont hden_ne
  have htx_cont : Continuous (fun t : ℝ => t * x) :=
    continuous_id.mul continuous_const
  have hsin_cont : Continuous (fun t : ℝ => Real.sin (t * x)) :=
    Real.continuous_sin.comp htx_cont
  have hf_cont : Continuous f := by
    unfold f
    exact hquot_cont.mul hsin_cont
  have hf_left : IntervalIntegrable f volume (-T) 0 :=
    hf_cont.intervalIntegrable (-T) 0
  have hf_right : IntervalIntegrable f volume 0 T :=
    hf_cont.intervalIntegrable 0 T
  have heven : ∀ t : ℝ, f (-t) = f t := by
    intro t
    unfold f
    have hden :
        a ^ 2 + (-t) ^ 2 = a ^ 2 + t ^ 2 := by
      exact congrArg (fun u : ℝ => a ^ 2 + u) (neg_sq t)
    have harg : (-t) * x = -(t * x) :=
      neg_mul t x
    have hsin : Real.sin ((-t) * x) = -Real.sin (t * x) := by
      exact (congrArg Real.sin harg).trans (Real.sin_neg (t * x))
    have hdiv :
        (-t) / (a ^ 2 + (-t) ^ 2) =
          -(t / (a ^ 2 + t ^ 2)) := by
      calc
        (-t) / (a ^ 2 + (-t) ^ 2)
            = (-t) / (a ^ 2 + t ^ 2) := by
              exact congrArg (fun d : ℝ => (-t) / d) hden
        _ = -(t / (a ^ 2 + t ^ 2)) := by
              exact neg_div t (a ^ 2 + t ^ 2)
    calc
      ((-t) / (a ^ 2 + (-t) ^ 2)) * Real.sin ((-t) * x)
          =
          (-(t / (a ^ 2 + t ^ 2))) * Real.sin ((-t) * x) := by
            exact congrArg
              (fun r : ℝ => r * Real.sin ((-t) * x))
              hdiv
      _ =
          (-(t / (a ^ 2 + t ^ 2))) * (-Real.sin (t * x)) := by
            exact congrArg
              (fun r : ℝ => (-(t / (a ^ 2 + t ^ 2))) * r)
              hsin
      _ =
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) := by
            exact neg_mul_neg (t / (a ^ 2 + t ^ 2)) (Real.sin (t * x))
  have hleft_eq_right :
      (∫ t in (-T)..0, f t) = ∫ t in (0)..T, f t := by
    have hcomp :
        (∫ t in (0)..T, f (-t)) = ∫ t in (-T)..0, f t := by
      exact
        intervalIntegral.integral_comp_neg
          (f := f) (a := 0) (b := T)
    have hcomp_even :
        (∫ t in (0)..T, f (-t)) = ∫ t in (0)..T, f t := by
      exact
        intervalIntegral.integral_congr
          (Filter.Eventually.of_forall heven)
    exact hcomp.symm.trans hcomp_even
  have hsplit :
      (∫ t in (-T)..T, f t) =
        (∫ t in (-T)..0, f t) + ∫ t in (0)..T, f t := by
    exact
      (intervalIntegral.integral_add_adjacent_intervals
        hf_left hf_right).symm
  calc
    (∫ t in Set.Icc (-T) T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x))
        = ∫ t in (-T)..T, f t := by
          unfold f
          rfl
    _ = (∫ t in (-T)..0, f t) + ∫ t in (0)..T, f t := hsplit
    _ = (∫ t in (0)..T, f t) + ∫ t in (0)..T, f t := by
          exact congrArg
            (fun y : ℝ => y + ∫ t in (0)..T, f t)
            hleft_eq_right
    _ = (2 : ℝ) * ∫ t in (0)..T, f t := by
          exact (two_mul (∫ t in (0)..T, f t)).symm
    _ =
        (2 : ℝ) *
          ∫ t in (0)..T,
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) := by
          unfold f
          rfl

/-- Finite-window Dirichlet bound for the odd Hilbert-Cauchy sine kernel. -/
theorem scalarFourierLaplacePlemelj_finiteHilbertSineKernel_abs_le_two_add_four_pi
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    |∫ t in Set.Icc (-T) T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| ≤
      (2 : ℝ) * (1 + (2 : ℝ) * Real.pi) := by
  have hsym :
      (∫ t in Set.Icc (-T) T,
        (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) =
        (2 : ℝ) *
          ∫ t in (0)..T,
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) :=
    scalarFourierLaplacePlemelj_finiteHilbertSineKernel_symmetric_eq_two_half
      a ha T x
  have hhalf :
      |∫ t in (0)..T,
        (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| ≤
        1 + (2 : ℝ) * Real.pi :=
    scalarFourierLaplacePlemelj_halfHilbertSineKernel_abs_le_one_add_two_pi
      a ha T x
  have htwo_nonneg : (0 : ℝ) ≤ 2 :=
    zero_le_two
  have htwo_abs :
      |(2 : ℝ) *
        ∫ t in (0)..T,
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| =
        (2 : ℝ) *
          |∫ t in (0)..T,
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| := by
    calc
      |(2 : ℝ) *
        ∫ t in (0)..T,
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)|
          =
          |(2 : ℝ)| *
            |∫ t in (0)..T,
              (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| := by
            exact abs_mul (2 : ℝ)
              (∫ t in (0)..T,
                (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x))
      _ =
          (2 : ℝ) *
            |∫ t in (0)..T,
              (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| := by
            exact congrArg
              (fun r : ℝ =>
                r *
                  |∫ t in (0)..T,
                    (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)|)
              (abs_of_nonneg htwo_nonneg)
  have hscaled :
      (2 : ℝ) *
        |∫ t in (0)..T,
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| ≤
        (2 : ℝ) * (1 + (2 : ℝ) * Real.pi) :=
    mul_le_mul_of_nonneg_left hhalf htwo_nonneg
  calc
    |∫ t in Set.Icc (-T) T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)|
        =
        |(2 : ℝ) *
          ∫ t in (0)..T,
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| := by
          exact congrArg abs hsym
    _ =
        (2 : ℝ) *
          |∫ t in (0)..T,
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| := htwo_abs
    _ ≤ (2 : ℝ) * (1 + (2 : ℝ) * Real.pi) := hscaled

/-- Dirichlet bound for the odd-sine Cauchy component after the standard
scale reduction. -/
theorem scalarFourierLaplacePlemelj_uncompensated_oddSineWindow_scaled_abs_le_two_add_four_pi
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    |scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x| ≤
      (2 : ℝ) * (1 + (2 : ℝ) * Real.pi) := by
  exact
    scalarFourierLaplacePlemelj_finiteHilbertSineKernel_abs_le_two_add_four_pi
      a ha T x

/-- Fixed-constant Dirichlet bound for the odd-sine component of the
uncompensated Cauchy kernel. -/
theorem scalarFourierLaplacePlemelj_uncompensated_oddSineWindow_abs_le_two_add_four_pi
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    |scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x| ≤
      (2 : ℝ) * (1 + (2 : ℝ) * Real.pi) := by
  exact
    scalarFourierLaplacePlemelj_uncompensated_oddSineWindow_scaled_abs_le_two_add_four_pi
      a ha T x

/-- Uniform Dirichlet bound for the odd-sine part of the uncompensated Cauchy
Fourier window. -/
theorem scalarFourierLaplacePlemelj_uncompensated_oddSineWindow_uniform_bound
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ T x : ℝ,
          |scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x| ≤ C := by
  exact ⟨(2 : ℝ) * (1 + (2 : ℝ) * Real.pi),
    mul_nonneg zero_le_two
      (add_nonneg zero_le_one (mul_nonneg zero_le_two Real.pi_pos.le)),
    fun T x =>
      scalarFourierLaplacePlemelj_uncompensated_oddSineWindow_abs_le_two_add_four_pi
        a ha T x⟩

/-- Multiplication of two complex numbers presented by real and imaginary
coordinates. -/
theorem scalarFourierLaplacePlemelj_realImag_mul
    (A B C S : ℝ) :
    (((A : ℂ) + ((B : ℝ) : ℂ) * Complex.I) *
        ((C : ℂ) + ((S : ℝ) : ℂ) * Complex.I)) =
      (((A * C - B * S : ℝ) : ℂ) +
        (((A * S + B * C : ℝ) : ℂ) * Complex.I)) := by
  calc
    (((A : ℂ) + ((B : ℝ) : ℂ) * Complex.I) *
        ((C : ℂ) + ((S : ℝ) : ℂ) * Complex.I))
        =
        Complex.mk A B * Complex.mk C S := by
          exact congrArg₂ Mul.mul
            (Complex.mk_eq_add_mul_I A B).symm
            (Complex.mk_eq_add_mul_I C S).symm
    _ = Complex.mk (A * C - B * S) (A * S + B * C) := by
          rfl
    _ =
      (((A * C - B * S : ℝ) : ℂ) +
        (((A * S + B * C : ℝ) : ℂ) * Complex.I)) := by
          exact Complex.mk_eq_add_mul_I (A * C - B * S) (A * S + B * C)

/-- Euler's identity for the real oscillatory factor in the Cauchy Fourier
window. -/
theorem scalarFourierLaplacePlemelj_exp_I_mul_real_eq_cos_add_sin
    (t x : ℝ) :
    Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) =
      ((Real.cos (t * x) : ℝ) : ℂ) +
        (((Real.sin (t * x) : ℝ) : ℂ) * Complex.I) := by
  have harg :
      Complex.I * (t : ℂ) * (x : ℂ) =
        (((t * x : ℝ) : ℂ) * Complex.I) := by
    calc
      Complex.I * (t : ℂ) * (x : ℂ)
          = Complex.I * ((t : ℂ) * (x : ℂ)) := by
            exact mul_assoc Complex.I (t : ℂ) (x : ℂ)
      _ = ((t : ℂ) * (x : ℂ)) * Complex.I := by
            exact mul_comm Complex.I ((t : ℂ) * (x : ℂ))
      _ = (((t * x : ℝ) : ℂ) * Complex.I) := by
            exact congrArg
              (fun z : ℂ => z * Complex.I)
              (Complex.ofReal_mul t x).symm
  calc
    Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))
        =
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) := by
          exact congrArg Complex.exp harg
    _ =
        Complex.cos ((t * x : ℝ) : ℂ) +
          Complex.sin ((t * x : ℝ) : ℂ) * Complex.I := by
          exact Complex.exp_mul_I ((t * x : ℝ) : ℂ)
    _ =
      ((Real.cos (t * x) : ℝ) : ℂ) +
        (((Real.sin (t * x) : ℝ) : ℂ) * Complex.I) := by
          exact congrArg₂ Add.add
            (Complex.ofReal_cos (t * x)).symm
            (congrArg
              (fun z : ℂ => z * Complex.I)
              (Complex.ofReal_sin (t * x)).symm)

/-- Pointwise real/imaginary decomposition of the uncompensated Cauchy Fourier
integrand. -/
theorem scalarFourierLaplacePlemelj_uncompensated_integrand_pointwise_decomposition
    (a : ℝ) (ha : 0 < a) (t x : ℝ) :
    (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) =
      (((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) +
        (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
          Complex.I)) := by
  let A : ℝ := -(a / (a ^ 2 + t ^ 2))
  let B : ℝ := t / (a ^ 2 + t ^ 2)
  let C : ℝ := Real.cos (t * x)
  let S : ℝ := Real.sin (t * x)
  have hkernel :
      (-1 / ((a : ℂ) + t * Complex.I)) =
        ((A : ℝ) : ℂ) + (((B : ℝ) : ℂ) * Complex.I) := by
    calc
      (-1 / ((a : ℂ) + t * Complex.I))
          =
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) +
            (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
            exact scalarFourierLaplacePlemelj_zero_kernel_pointwise_decomposition
              a ha t
      _ = ((A : ℝ) : ℂ) + (((B : ℝ) : ℂ) * Complex.I) := by
            rfl
  have hexp :
      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) =
        ((C : ℝ) : ℂ) + (((S : ℝ) : ℂ) * Complex.I) := by
    calc
      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))
          =
          ((Real.cos (t * x) : ℝ) : ℂ) +
            (((Real.sin (t * x) : ℝ) : ℂ) * Complex.I) := by
            exact scalarFourierLaplacePlemelj_exp_I_mul_real_eq_cos_add_sin
              t x
      _ = ((C : ℝ) : ℂ) + (((S : ℝ) : ℂ) * Complex.I) := by
            rfl
  have hproduct :
      (((A : ℝ) : ℂ) + (((B : ℝ) : ℂ) * Complex.I)) *
          (((C : ℝ) : ℂ) + (((S : ℝ) : ℂ) * Complex.I)) =
        (((A * C - B * S : ℝ) : ℂ) +
          (((A * S + B * C : ℝ) : ℂ) * Complex.I)) :=
    scalarFourierLaplacePlemelj_realImag_mul A B C S
  calc
    (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))
        =
        (((A : ℝ) : ℂ) + (((B : ℝ) : ℂ) * Complex.I)) *
          Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
          exact congrArg
            (fun z : ℂ => z * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))
            hkernel
    _ =
        (((A : ℝ) : ℂ) + (((B : ℝ) : ℂ) * Complex.I)) *
          (((C : ℝ) : ℂ) + (((S : ℝ) : ℂ) * Complex.I)) := by
          exact congrArg
            (fun z : ℂ =>
              (((A : ℝ) : ℂ) + (((B : ℝ) : ℂ) * Complex.I)) * z)
            hexp
    _ =
        (((A * C - B * S : ℝ) : ℂ) +
          (((A * S + B * C : ℝ) : ℂ) * Complex.I)) := hproduct
    _ =
      (((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) +
        (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
          Complex.I)) := by
          rfl

/-- Symmetric interval cancellation for an odd complex-valued function. -/
theorem intervalIntegral_integral_eq_zero_of_forall_neg_eq_neg
    (f : ℝ → ℂ) (T : ℝ) (hodd : ∀ t : ℝ, f (-t) = -f t) :
    ∫ t in (-T)..T, f t = 0 := by
  have hcomp :
      (∫ t in (-T)..T, f (-t)) = ∫ t in (-T)..T, f t := by
    calc
      (∫ t in (-T)..T, f (-t))
          = ∫ t in (-T)..(-(-T)), f t := by
            exact intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := T)
      _ = ∫ t in (-T)..T, f t := by
            exact congrArg
              (fun v : ℝ => ∫ t in (-T)..v, f t)
              (neg_neg T)
  have hneg :
      (∫ t in (-T)..T, f (-t)) = -∫ t in (-T)..T, f t := by
    calc
      (∫ t in (-T)..T, f (-t))
          = ∫ t in (-T)..T, -f t := by
            exact intervalIntegral.integral_congr
              (Filter.Eventually.of_forall hodd)
      _ = -∫ t in (-T)..T, f t := by
            exact intervalIntegral.integral_neg
  have hself_neg : (∫ t in (-T)..T, f t) = -∫ t in (-T)..T, f t :=
    hcomp.symm.trans hneg
  have htwo_zero : (2 : ℂ) * (∫ t in (-T)..T, f t) = 0 := by
    have hsum_zero :
        (∫ t in (-T)..T, f t) + (∫ t in (-T)..T, f t) = 0 := by
      calc
        (∫ t in (-T)..T, f t) + (∫ t in (-T)..T, f t)
            =
            -(∫ t in (-T)..T, f t) + (∫ t in (-T)..T, f t) := by
              exact congrArg
                (fun z : ℂ => z + (∫ t in (-T)..T, f t))
                hself_neg
        _ = 0 := by
            exact neg_add_cancel (∫ t in (-T)..T, f t)
    exact (two_mul (∫ t in (-T)..T, f t)).trans hsum_zero
  exact (mul_eq_zero.mp htwo_zero).resolve_left two_ne_zero

/-- Pointwise oddness of the imaginary remainder in the uncompensated Cauchy
Fourier decomposition. -/
theorem scalarFourierLaplacePlemelj_uncompensated_imaginaryRemainder_pointwise_odd
    (a : ℝ) (ha : 0 < a) (x t : ℝ) :
    (((-(a / (a ^ 2 + (-t) ^ 2)) * Real.sin ((-t) * x) +
        ((-t) / (a ^ 2 + (-t) ^ 2)) * Real.cos ((-t) * x) : ℝ) : ℂ) *
      Complex.I) =
      -((((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
          (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
        Complex.I) := by
  let D : ℝ := a ^ 2 + t ^ 2
  let A : ℝ := -(a / D)
  let B : ℝ := t / D
  let S : ℝ := Real.sin (t * x)
  let C : ℝ := Real.cos (t * x)
  have hden : a ^ 2 + (-t) ^ 2 = D := by
    calc
      a ^ 2 + (-t) ^ 2 = a ^ 2 + t ^ 2 := by
        exact congrArg (fun u : ℝ => a ^ 2 + u) (neg_sq t)
      _ = D := by
        rfl
  have hleft_coeff :
      -(a / (a ^ 2 + (-t) ^ 2)) = A := by
    calc
      -(a / (a ^ 2 + (-t) ^ 2)) = -(a / D) := by
        exact congrArg (fun d : ℝ => -(a / d)) hden
      _ = A := by
        rfl
  have hright_coeff :
      (-t) / (a ^ 2 + (-t) ^ 2) = -B := by
    calc
      (-t) / (a ^ 2 + (-t) ^ 2) = (-t) / D := by
        exact congrArg (fun d : ℝ => (-t) / d) hden
      _ = -(t / D) := by
        exact neg_div t D
      _ = -B := by
        rfl
  have hsin :
      Real.sin ((-t) * x) = -S := by
    calc
      Real.sin ((-t) * x) = Real.sin (-(t * x)) := by
        exact congrArg Real.sin (neg_mul t x)
      _ = -Real.sin (t * x) := by
        exact Real.sin_neg (t * x)
      _ = -S := by
        rfl
  have hcos :
      Real.cos ((-t) * x) = C := by
    calc
      Real.cos ((-t) * x) = Real.cos (-(t * x)) := by
        exact congrArg Real.cos (neg_mul t x)
      _ = Real.cos (t * x) := by
        exact Real.cos_neg (t * x)
      _ = C := by
        rfl
  have hreal_left :
      (-(a / (a ^ 2 + (-t) ^ 2)) * Real.sin ((-t) * x) +
          ((-t) / (a ^ 2 + (-t) ^ 2)) * Real.cos ((-t) * x) : ℝ) =
        A * (-S) + (-B) * C := by
    exact congrArg₂ Add.add
      (congrArg₂ Mul.mul hleft_coeff hsin)
      (congrArg₂ Mul.mul hright_coeff hcos)
  have hreal_neg :
      A * (-S) + (-B) * C = -(A * S + B * C) := by
    calc
      A * (-S) + (-B) * C = -(A * S) + (-B) * C := by
        exact congrArg (fun y : ℝ => y + (-B) * C) (mul_neg A S)
      _ = -(A * S) + -(B * C) := by
        exact congrArg (fun y : ℝ => -(A * S) + y) (neg_mul B C)
      _ = -(A * S + B * C) := by
        exact (neg_add (A * S) (B * C)).symm
  have hreal_right :
      (-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
          (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) =
        A * S + B * C := by
    rfl
  have hreal :
      (-(a / (a ^ 2 + (-t) ^ 2)) * Real.sin ((-t) * x) +
          ((-t) / (a ^ 2 + (-t) ^ 2)) * Real.cos ((-t) * x) : ℝ) =
        -(-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x)) := by
    calc
      (-(a / (a ^ 2 + (-t) ^ 2)) * Real.sin ((-t) * x) +
          ((-t) / (a ^ 2 + (-t) ^ 2)) * Real.cos ((-t) * x) : ℝ)
          = A * (-S) + (-B) * C := hreal_left
      _ = -(A * S + B * C) := hreal_neg
      _ =
          -(-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
              (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x)) := by
            exact congrArg Neg.neg hreal_right.symm
  calc
    (((-(a / (a ^ 2 + (-t) ^ 2)) * Real.sin ((-t) * x) +
        ((-t) / (a ^ 2 + (-t) ^ 2)) * Real.cos ((-t) * x) : ℝ) : ℂ) *
      Complex.I)
        =
        (((-(-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x)) : ℝ) : ℂ) *
          Complex.I) := by
          exact congrArg (fun y : ℝ => ((y : ℂ) * Complex.I)) hreal
    _ =
        (-((( -(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ))) *
          Complex.I := by
          exact congrArg
            (fun z : ℂ => z * Complex.I)
            (Complex.ofReal_neg
              (-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
                (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x)))
    _ =
        -((((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
          Complex.I) := by
          exact neg_mul
            (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
              (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ))
            Complex.I

/-- The imaginary remainder in the symmetric uncompensated Cauchy Fourier
window cancels by oddness. -/
theorem scalarFourierLaplacePlemelj_uncompensated_imaginaryRemainder_integral_eq_zero
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    ∫ t in Set.Icc (-T) T,
      (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
          (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
        Complex.I) = 0 := by
  let f : ℝ → ℂ :=
    fun t : ℝ =>
      (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
          (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
        Complex.I)
  have hodd : ∀ t : ℝ, f (-t) = -f t := by
    intro t
    unfold f
    exact
      scalarFourierLaplacePlemelj_uncompensated_imaginaryRemainder_pointwise_odd
        a ha x t
  exact intervalIntegral_integral_eq_zero_of_forall_neg_eq_neg f T hodd

/-- Interval integrability of the even-cosine scalar component of the
uncompensated real remainder. -/
theorem scalarFourierLaplacePlemelj_uncompensated_evenCosine_component_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 :=
    scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha
  have hcoeff :
      Continuous (fun t : ℝ => -(a / (a ^ 2 + t ^ 2))) :=
    (continuous_const.div hden_cont hden_ne).neg
  have htx : Continuous (fun t : ℝ => t * x) :=
    continuous_id.mul continuous_const
  have hcos : Continuous (fun t : ℝ => Real.cos (t * x)) :=
    Real.continuous_cos.comp htx
  have hreal :
      Continuous
        (fun t : ℝ => -(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x)) :=
    hcoeff.mul hcos
  exact (Complex.continuous_ofReal.comp hreal).intervalIntegrable (-T) T

/-- Interval integrability of the odd-sine scalar component of the
uncompensated real remainder. -/
theorem scalarFourierLaplacePlemelj_uncompensated_oddSine_component_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        (((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 :=
    scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha
  have hcoeff :
      Continuous (fun t : ℝ => t / (a ^ 2 + t ^ 2)) :=
    continuous_id.div hden_cont hden_ne
  have htx : Continuous (fun t : ℝ => t * x) :=
    continuous_id.mul continuous_const
  have hsin : Continuous (fun t : ℝ => Real.sin (t * x)) :=
    Real.continuous_sin.comp htx
  have hreal :
      Continuous
        (fun t : ℝ => (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) :=
    hcoeff.mul hsin
  exact (Complex.continuous_ofReal.comp hreal).intervalIntegrable (-T) T

/-- The even-cosine component commutes with the real-to-complex integral. -/
theorem scalarFourierLaplacePlemelj_uncompensated_evenCosine_component_integral_ofReal
    (a T x : ℝ) :
    (∫ t in Set.Icc (-T) T,
      ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ)) =
      ((scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x : ℝ) : ℂ) := by
  calc
    (∫ t in Set.Icc (-T) T,
      ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ))
        =
        ∫ t in (-T)..T,
          ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) := by
          rfl
    _ =
        ((∫ t in (-T)..T,
          (-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ)) : ℂ) := by
          exact intervalIntegral.integral_ofReal
    _ =
        ((scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x : ℝ) : ℂ) := by
          rfl

/-- The odd-sine component commutes with the real-to-complex integral. -/
theorem scalarFourierLaplacePlemelj_uncompensated_oddSine_component_integral_ofReal
    (a T x : ℝ) :
    (∫ t in Set.Icc (-T) T,
      (((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ)) =
      ((scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x : ℝ) : ℂ) := by
  calc
    (∫ t in Set.Icc (-T) T,
      (((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ))
        =
        ∫ t in (-T)..T,
          (((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) := by
          rfl
    _ =
        ((∫ t in (-T)..T,
          ((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ)) : ℂ) := by
          exact intervalIntegral.integral_ofReal
    _ =
        ((scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x : ℝ) : ℂ) := by
          rfl

/-- The real remainder in the symmetric uncompensated Cauchy Fourier window is
the even-cosine part minus the odd-sine part. -/
theorem scalarFourierLaplacePlemelj_uncompensated_realRemainder_integral_eq_even_sub_odd
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    ∫ t in Set.Icc (-T) T,
      ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) =
      ((scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x -
        scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x : ℝ) : ℂ) := by
  calc
    (∫ t in Set.Icc (-T) T,
      ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ))
        =
        ∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) -
            (((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) := by
          exact intervalIntegral.integral_congr
            (Filter.Eventually.of_forall
              (fun t : ℝ =>
                Complex.ofReal_sub
                  (-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x))
                  ((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x))))
    _ =
        (∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ)) -
          ∫ t in Set.Icc (-T) T,
            (((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) := by
          exact intervalIntegral.integral_sub
            (scalarFourierLaplacePlemelj_uncompensated_evenCosine_component_intervalIntegrable
              a ha T x)
            (scalarFourierLaplacePlemelj_uncompensated_oddSine_component_intervalIntegrable
              a ha T x)
    _ =
        ((scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x : ℝ) : ℂ) -
          ((scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x : ℝ) : ℂ) := by
          exact congrArg₂ Sub.sub
            (scalarFourierLaplacePlemelj_uncompensated_evenCosine_component_integral_ofReal
              a T x)
            (scalarFourierLaplacePlemelj_uncompensated_oddSine_component_integral_ofReal
              a T x)
    _ =
        ((scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x -
          scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x : ℝ) : ℂ) := by
          exact
            (Complex.ofReal_sub
              (scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x)
              (scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x)).symm

/-- Interval integrability of the real remainder in the uncompensated Cauchy
Fourier decomposition. -/
theorem scalarFourierLaplacePlemelj_uncompensated_realRemainder_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 :=
    scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha
  have hleft_coeff :
      Continuous (fun t : ℝ => -(a / (a ^ 2 + t ^ 2))) :=
    (continuous_const.div hden_cont hden_ne).neg
  have hright_coeff :
      Continuous (fun t : ℝ => t / (a ^ 2 + t ^ 2)) :=
    continuous_id.div hden_cont hden_ne
  have htx : Continuous (fun t : ℝ => t * x) :=
    continuous_id.mul continuous_const
  have hcos : Continuous (fun t : ℝ => Real.cos (t * x)) :=
    Real.continuous_cos.comp htx
  have hsin : Continuous (fun t : ℝ => Real.sin (t * x)) :=
    Real.continuous_sin.comp htx
  have hreal :
      Continuous
        (fun t : ℝ =>
          -(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) :=
    (hleft_coeff.mul hcos).sub (hright_coeff.mul hsin)
  exact (Complex.continuous_ofReal.comp hreal).intervalIntegrable (-T) T

/-- Interval integrability of the imaginary remainder in the uncompensated
Cauchy Fourier decomposition. -/
theorem scalarFourierLaplacePlemelj_uncompensated_imaginaryRemainder_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
          Complex.I))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 :=
    scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha
  have hleft_coeff :
      Continuous (fun t : ℝ => -(a / (a ^ 2 + t ^ 2))) :=
    (continuous_const.div hden_cont hden_ne).neg
  have hright_coeff :
      Continuous (fun t : ℝ => t / (a ^ 2 + t ^ 2)) :=
    continuous_id.div hden_cont hden_ne
  have htx : Continuous (fun t : ℝ => t * x) :=
    continuous_id.mul continuous_const
  have hcos : Continuous (fun t : ℝ => Real.cos (t * x)) :=
    Real.continuous_cos.comp htx
  have hsin : Continuous (fun t : ℝ => Real.sin (t * x)) :=
    Real.continuous_sin.comp htx
  have hreal :
      Continuous
        (fun t : ℝ =>
          -(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x)) :=
    (hleft_coeff.mul hsin).add (hright_coeff.mul hcos)
  exact
    ((Complex.continuous_ofReal.comp hreal).mul continuous_const).intervalIntegrable
      (-T) T

/-- Additivity of the real and imaginary remainders in the uncompensated
Cauchy Fourier decomposition on a finite symmetric window. -/
theorem scalarFourierLaplacePlemelj_uncompensated_remainder_integral_add
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    ∫ t in Set.Icc (-T) T,
      (((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) +
        (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
          Complex.I)) =
      (∫ t in Set.Icc (-T) T,
        ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ)) +
        ∫ t in Set.Icc (-T) T,
          (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
              (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
            Complex.I) := by
  exact intervalIntegral.integral_add
    (scalarFourierLaplacePlemelj_uncompensated_realRemainder_intervalIntegrable
      a ha T x)
    (scalarFourierLaplacePlemelj_uncompensated_imaginaryRemainder_intervalIntegrable
      a ha T x)

/-- Exact real decomposition of the uncompensated symmetric Cauchy Fourier
window into its surviving even-cosine and odd-sine pieces. -/
theorem scalarFourierLaplacePlemelj_uncompensated_window_eq_evenCosine_sub_oddSine
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    (∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))) =
      ((scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x -
        scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x : ℝ) : ℂ) := by
  calc
    (∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))) =
        ∫ t in Set.Icc (-T) T,
          (((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
              (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) +
            (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
                (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
              Complex.I)) := by
          exact intervalIntegral.integral_congr
            (Filter.Eventually.of_forall
              (fun t : ℝ =>
                scalarFourierLaplacePlemelj_uncompensated_integrand_pointwise_decomposition
                  a ha t x))
    _ =
        (∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
              (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ)) +
          ∫ t in Set.Icc (-T) T,
            (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
                (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
              Complex.I) := by
          exact
            scalarFourierLaplacePlemelj_uncompensated_remainder_integral_add
              a ha T x
    _ =
        (∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
              (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ)) + 0 := by
          exact congrArg
            (fun z : ℂ =>
              (∫ t in Set.Icc (-T) T,
                ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
                    (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ)) + z)
            (scalarFourierLaplacePlemelj_uncompensated_imaginaryRemainder_integral_eq_zero
              a ha T x)
    _ =
        ∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
              (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) := by
          exact add_zero _
    _ =
      ((scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x -
        scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x : ℝ) : ℂ) := by
          exact
            scalarFourierLaplacePlemelj_uncompensated_realRemainder_integral_eq_even_sub_odd
              a ha T x

/-- Assembly of the uncompensated complex Cauchy window norm from the bounded
even-cosine and odd-sine real components. -/
theorem scalarFourierLaplacePlemelj_uncompensated_window_norm_bound_of_even_odd
    (a : ℝ) (ha : 0 < a) (T x Ceven Codd : ℝ)
    (heven :
      |scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x| ≤ Ceven)
    (hodd :
      |scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x| ≤ Codd) :
    ‖∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))‖ ≤ Ceven + Codd := by
  let E : ℝ := scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x
  let O : ℝ := scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x
  have hdecomp :
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) =
        ((E - O : ℝ) : ℂ) := by
    exact
      scalarFourierLaplacePlemelj_uncompensated_window_eq_evenCosine_sub_oddSine
        a ha T x
  have hnorm :
      ‖((E - O : ℝ) : ℂ)‖ = |E - O| :=
    RCLike.norm_ofReal (K := ℂ) (E - O)
  have htri : |E - O| ≤ |E| + |O| :=
    abs_sub_le E O
  have heven' : |E| ≤ Ceven := by
    unfold E
    exact heven
  have hodd' : |O| ≤ Codd := by
    unfold O
    exact hodd
  calc
    ‖∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))‖ =
        ‖((E - O : ℝ) : ℂ)‖ := by
      exact congrArg norm hdecomp
    _ = |E - O| := hnorm
    _ ≤ |E| + |O| := htri
    _ ≤ Ceven + Codd := by
      exact add_le_add heven' hodd'

/-- Dirichlet decomposition bound for the uncompensated scalar Cauchy Fourier
window.

This is the real-variable core of the near-jump Cauchy estimate: after splitting
`1 / (a + i t)` into its even real and odd imaginary pieces, Dirichlet's
oscillatory-integral bound controls the finite symmetric windows uniformly in
both the radius and frequency. -/
theorem scalarFourierLaplacePlemelj_uncompensated_window_dirichletDecomposition_uniform_norm_bound
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ T x : ℝ,
          ‖∫ t in Set.Icc (-T) T,
            (-1 / ((a : ℂ) + t * Complex.I)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ))‖
          ≤ C := by
  match scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_uniform_bound
    a ha with
  | ⟨Ceven, hCeven_nonneg, heven⟩ =>
      match scalarFourierLaplacePlemelj_uncompensated_oddSineWindow_uniform_bound
        a ha with
      | ⟨Codd, hCodd_nonneg, hodd⟩ =>
          let C : ℝ := Ceven + Codd
          have hC_nonneg : 0 ≤ C := by
            unfold C
            exact add_nonneg hCeven_nonneg hCodd_nonneg
          exact
            ⟨C, hC_nonneg,
              fun T x =>
                scalarFourierLaplacePlemelj_uncompensated_window_norm_bound_of_even_odd
                  a ha T x Ceven Codd (heven T x) (hodd T x)⟩

/-- Global uniform bound for the uncompensated scalar Cauchy Fourier window. -/
theorem scalarFourierLaplacePlemelj_uncompensated_window_uniform_norm_bound
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ T x : ℝ,
          ‖∫ t in Set.Icc (-T) T,
            (-1 / ((a : ℂ) + t * Complex.I)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ))‖
          ≤ C := by
  exact
    scalarFourierLaplacePlemelj_uncompensated_window_dirichletDecomposition_uniform_norm_bound
      a ha

/-- Uncompensated symmetric Cauchy-window bound in a punctured neighborhood of
the Plemelj jump. -/
theorem scalarFourierLaplacePlemelj_uncompensated_punctured_nearZero_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            x ≠ 0 →
            ‖x‖ < δ →
            ‖x‖ ≤ R →
              ‖∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ))‖
              ≤ C := by
  match
    scalarFourierLaplacePlemelj_uncompensated_window_uniform_norm_bound
      a ha
  with
  | ⟨C, hC_nonneg, hC⟩ =>
      exact
        ⟨C, hC_nonneg,
          Eventually.of_forall
            (fun T x _hx_ne _hxδ _hxR =>
              hC T x)⟩

/-- Uniform punctured-neighborhood Cauchy-window estimate near the Plemelj
jump.  This is the shared near-zero Dirichlet estimate used by both signs. -/
theorem scalarFourierLaplacePlemelj_compactInterval_punctured_nearZero_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            x ≠ 0 →
            ‖x‖ < δ →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  match
    scalarFourierLaplacePlemelj_uncompensated_punctured_nearZero_norm_bound_eventually
      a ha R δ hδ
  with
  | ⟨Craw, hCraw_nonneg, hraw⟩ =>
      let Ebound : ℝ := Real.exp (a * R)
      let C : ℝ := Craw * Ebound
      have hEbound_nonneg : 0 ≤ Ebound := by
        unfold Ebound
        exact (Real.exp_pos (a * R)).le
      have hC_nonneg : 0 ≤ C := by
        unfold C
        exact mul_nonneg hCraw_nonneg hEbound_nonneg
      exact
        ⟨C, hC_nonneg,
          hraw.mono
            (fun T hT x hx_ne hxδ hxR =>
              let W : ℂ :=
                ∫ t in Set.Icc (-T) T,
                  (-1 / ((a : ℂ) + t * Complex.I)) *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ))
              let E : ℂ := Complex.exp ((a : ℂ) * (x : ℂ))
              have htarget :
                  (∫ t in Set.Icc (-T) T,
                    (-1 / ((a : ℂ) + t * Complex.I)) *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp ((a : ℂ) * (x : ℂ))) =
                  W * E :=
                (scalarFourierLaplacePlemelj_positive_window_mul_exp_eq_window_with_exp
                  a x T).symm
              have hE_le : ‖E‖ ≤ Ebound := by
                unfold E
                unfold Ebound
                exact
                  scalarFourierLaplacePlemelj_positive_exp_norm_le_intervalEndpoint
                    a ha R x hxR
              have hE_nonneg : 0 ≤ ‖E‖ :=
                norm_nonneg E
              have hmul :
                  ‖W‖ * ‖E‖ ≤ Craw * Ebound :=
                mul_le_mul (hT x hx_ne hxδ hxR) hE_le hE_nonneg hCraw_nonneg
              calc
                ‖(∫ t in Set.Icc (-T) T,
                  (-1 / ((a : ℂ) + t * Complex.I)) *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp ((a : ℂ) * (x : ℂ)))‖
                    = ‖W * E‖ := by
                  exact congrArg norm htarget
                _ = ‖W‖ * ‖E‖ := by
                  exact norm_mul W E
                _ ≤ Craw * Ebound := hmul
                _ = C := by
                  rfl)⟩

/-- Positive-time near-zero compact-interval estimate for the normalized
scalar Fourier-Laplace Plemelj kernel. -/

end FixedLineCauchyProjection

end
end Boundary
