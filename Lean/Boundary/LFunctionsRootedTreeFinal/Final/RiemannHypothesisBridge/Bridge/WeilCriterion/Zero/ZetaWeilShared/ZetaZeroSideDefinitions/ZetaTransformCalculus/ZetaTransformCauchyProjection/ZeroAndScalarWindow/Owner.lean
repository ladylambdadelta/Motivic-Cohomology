import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.NegativeContour.Owner

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

noncomputable def scalarFourierLaplacePlemelj_unweightedWindowMulExp
    (a T x : ℝ) : ℂ :=
  (∫ t in Set.Icc (-T) T,
    (-1 / ((a : ℂ) + t * Complex.I)) *
      Complex.exp
        (Complex.I * (t : ℂ) * (x : ℂ))) *
    Complex.exp ((a : ℂ) * (x : ℂ))

/-- The normalized scalar finite-window Cauchy integral unfolds to the window integral
times the compensating exponential. -/
theorem scalarFourierLaplacePlemelj_unweightedWindowMulExp_eq
    (a T x : ℝ) :
    scalarFourierLaplacePlemelj_unweightedWindowMulExp a T x =
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp ((a : ℂ) * (x : ℂ)) := by
  rfl

/-- The quadratic denominator in the zero-time Cauchy kernel is strictly
positive. -/
theorem scalarFourierLaplacePlemelj_zero_denominator_pos
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    0 < a ^ 2 + t ^ 2 :=
  add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)

/-- The quadratic denominator in the zero-time Cauchy kernel is nonzero. -/
theorem scalarFourierLaplacePlemelj_zero_denominator_ne_zero
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    a ^ 2 + t ^ 2 ≠ 0 :=
  ne_of_gt
    (scalarFourierLaplacePlemelj_zero_denominator_pos a ha t)

/-- Pointwise algebraic decomposition of the zero-time Cauchy kernel into its
real even part and imaginary odd part. -/
theorem scalarFourierLaplacePlemelj_zero_kernel_pointwise_decomposition
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    (-1 / ((a : ℂ) + t * Complex.I)) =
      ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) +
        (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
  have hden_pos : 0 < a ^ 2 + t ^ 2 :=
    scalarFourierLaplacePlemelj_zero_denominator_pos a ha t
  have hden_ne : a ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt hden_pos
  have hz_ne : ((a : ℂ) + t * Complex.I) ≠ 0 := by
    intro hz
    have hre : (((a : ℂ) + t * Complex.I).re) = (0 : ℂ).re :=
      congrArg Complex.re hz
    have ha_zero : a = 0 := by
      have hleft : (((a : ℂ) + t * Complex.I).re) = a := by
        calc
          (((a : ℂ) + t * Complex.I).re) =
              (a : ℂ).re + (t * Complex.I).re :=
            Complex.add_re (a : ℂ) (t * Complex.I)
          _ = a + (t * Complex.I).re :=
            congrArg (fun y : ℝ => y + (t * Complex.I).re)
              (Complex.ofReal_re a)
          _ = a + ((t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im) :=
            congrArg (fun y : ℝ => a + y)
              (Complex.mul_re (t : ℂ) Complex.I)
          _ = a + (t * Complex.I.re - (t : ℂ).im * Complex.I.im) :=
            congrArg
              (fun y : ℝ => a + (y * Complex.I.re - (t : ℂ).im * Complex.I.im))
              (Complex.ofReal_re t)
          _ = a + (t * 0 - (t : ℂ).im * Complex.I.im) :=
            congrArg (fun y : ℝ => a + (t * y - (t : ℂ).im * Complex.I.im))
              Complex.I_re
          _ = a + (0 - (t : ℂ).im * Complex.I.im) :=
            congrArg (fun y : ℝ => a + (y - (t : ℂ).im * Complex.I.im))
              (mul_zero t)
          _ = a + (0 - 0 * Complex.I.im) :=
            congrArg (fun y : ℝ => a + (0 - y * Complex.I.im))
              (Complex.ofReal_im t)
          _ = a + (0 - 0) :=
            congrArg (fun y : ℝ => a + (0 - 0 * y)) Complex.I_im
          _ = a + 0 :=
            congrArg (fun y : ℝ => a + y) (sub_self (0 : ℝ))
          _ = a := add_zero a
      exact hleft.symm.trans (hre.trans Complex.zero_re)
    exact (ne_of_gt ha) ha_zero
  ext
  · field_simp [hz_ne, hden_ne]
    ring
  · field_simp [hz_ne, hden_ne]
    ring

/-- The odd imaginary part of the zero-time symmetric Cauchy window cancels. -/
theorem scalarFourierLaplacePlemelj_zero_odd_imaginary_integral_eq_zero
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    ∫ t in Set.Icc (-T) T,
      (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) = 0 := by
  let f : ℝ → ℂ :=
    fun t : ℝ => (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I)
  have hodd : ∀ t : ℝ, f (-t) = -f t := by
    intro t
    unfold f
    have hden :
        a ^ 2 + (-t) ^ 2 = a ^ 2 + t ^ 2 := by
      have hneg_sq : (-t) ^ 2 = t ^ 2 := by
        calc
          (-t) ^ 2 = (-t) * (-t) := pow_two (-t)
          _ = t * t := neg_mul_neg t t
          _ = t ^ 2 := (pow_two t).symm
      exact congrArg (fun y : ℝ => a ^ 2 + y) hneg_sq
    calc
      ((((-t) / (a ^ 2 + (-t) ^ 2) : ℝ) : ℂ) * Complex.I)
          =
          ((((-t) / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
            exact congrArg
              (fun y : ℝ => ((y : ℂ) * Complex.I))
              (congrArg (fun d : ℝ => (-t) / d) hden)
      _ =
          -(((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
            calc
              ((((-t) / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I)
                  =
                  (((-(t / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) * Complex.I) := by
                    exact congrArg
                      (fun y : ℝ => ((y : ℂ) * Complex.I))
                      (neg_div t (a ^ 2 + t ^ 2))
              _ =
                  (-(((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) * Complex.I) := by
                    exact congrArg
                      (fun z : ℂ => z * Complex.I)
                      (Complex.ofReal_neg (t / (a ^ 2 + t ^ 2)))
              _ =
                  -(((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
                    exact neg_mul (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) Complex.I
  have hcomp :
      (∫ t in (-T)..T, f (-t)) = ∫ t in (-T)..T, f t := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := T)).symm
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
  have htwo_ne : (2 : ℂ) ≠ 0 :=
    two_ne_zero
  exact mul_eq_zero.mp htwo_zero |>.resolve_left htwo_ne

/-- The even real part of the zero-time symmetric Cauchy window has the
arctangent primitive value. -/
theorem scalarFourierLaplacePlemelj_zero_real_kernel_integral_eq_arctan
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    ∫ t in Set.Icc (-T) T,
      ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) =
      (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hreal :
      (∫ t in (-T)..T, (-(a / (a ^ 2 + t ^ 2)) : ℝ)) =
        -(2 : ℝ) * Real.arctan (T / a) := by
    have hscale :
        (∫ u in (-(T / a))..(T / a),
          (-(1 : ℝ) / (1 + u ^ 2))) =
          -(2 : ℝ) * Real.arctan (T / a) := by
      calc
        (∫ u in (-(T / a))..(T / a),
          (-(1 : ℝ) / (1 + u ^ 2)))
            = -∫ u in (-(T / a))..(T / a),
                ((1 : ℝ) + u ^ 2)⁻¹ := by
              simp only [neg_div, one_div, intervalIntegral.integral_neg]
        _ = -(Real.arctan (T / a) - Real.arctan (-(T / a))) := by
              exact congrArg Neg.neg
                (Real.integral_inv_one_add_sq
                  (a := -(T / a)) (b := T / a))
        _ = -(2 : ℝ) * Real.arctan (T / a) := by
              rw [Real.arctan_neg]
              ring
    have hsub :
        (∫ t in (-T)..T, (-(a / (a ^ 2 + t ^ 2)) : ℝ)) =
          ∫ u in (-(T / a))..(T / a),
            (-(1 : ℝ) / (1 + u ^ 2)) := by
      have hcomp :=
        intervalIntegral.integral_comp_mul_left
          (f := fun t : ℝ => (-(a / (a ^ 2 + t ^ 2)) : ℝ))
          (a := -(T / a)) (b := T / a) ha_ne
      have hpoint :
          ∀ u : ℝ,
            (a⁻¹ : ℝ) • (-(a / (a ^ 2 + (a * u) ^ 2)) : ℝ) =
              (-(1 : ℝ) / (1 + u ^ 2)) := by
        intro u
        field_simp [ha_ne]
        ring
      calc
        (∫ t in (-T)..T, (-(a / (a ^ 2 + t ^ 2)) : ℝ))
            =
            (a⁻¹ : ℝ) •
              ∫ t in (a * (-(T / a)))..(a * (T / a)),
                (-(a / (a ^ 2 + t ^ 2)) : ℝ) := by
              rw [mul_neg, mul_div_cancel₀ T ha_ne,
                mul_div_cancel₀ T ha_ne]
              exact Eq.symm hcomp
        _ =
            ∫ u in (-(T / a))..(T / a),
              (a⁻¹ : ℝ) •
                (-(a / (a ^ 2 + (a * u) ^ 2)) : ℝ) := by
              rw [intervalIntegral.integral_smul]
        _ =
            ∫ u in (-(T / a))..(T / a),
              (-(1 : ℝ) / (1 + u ^ 2)) := by
              exact intervalIntegral.integral_congr
                (Filter.Eventually.of_forall hpoint)
    exact hsub.trans hscale
  calc
    (∫ t in Set.Icc (-T) T,
      ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ))
        =
        ∫ t in (-T)..T,
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) := by
          rfl
    _ =
        ((∫ t in (-T)..T,
          (-(a / (a ^ 2 + t ^ 2)) : ℝ)) : ℂ) := by
          exact intervalIntegral.integral_ofReal
    _ =
        (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
          exact congrArg (fun y : ℝ => (y : ℂ)) hreal

/-- Interval integrability of the even real part of the zero-time Cauchy
kernel on symmetric finite windows. -/
theorem scalarFourierLaplacePlemelj_zero_real_kernel_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hquot_cont : Continuous (fun t : ℝ => a / (a ^ 2 + t ^ 2)) :=
    continuous_const.div hden_cont
      (scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha)
  have hreal_cont :
      Continuous (fun t : ℝ => (-(a / (a ^ 2 + t ^ 2)) : ℝ)) :=
    hquot_cont.neg
  exact (Complex.continuous_ofReal.comp hreal_cont).intervalIntegrable (-T) T

/-- Interval integrability of the odd imaginary part of the zero-time Cauchy
kernel on symmetric finite windows. -/
theorem scalarFourierLaplacePlemelj_zero_odd_imaginary_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hquot_cont : Continuous (fun t : ℝ => t / (a ^ 2 + t ^ 2)) :=
    continuous_id.div hden_cont
      (scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha)
  have hcomplex_cont :
      Continuous
        (fun t : ℝ => ((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hquot_cont
  exact (hcomplex_cont.mul continuous_const).intervalIntegrable (-T) T

/-- Zero-time symmetric Cauchy window before multiplying by the trivial
endpoint exponential factors. -/
theorem scalarFourierLaplacePlemelj_zero_raw_window_eq_arctan
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    ∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) =
      (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
  calc
    ∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I))
        =
        ∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) +
            (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
          exact intervalIntegral.integral_congr
            (Filter.Eventually.of_forall
              (fun t : ℝ =>
                scalarFourierLaplacePlemelj_zero_kernel_pointwise_decomposition
                  a ha t))
    _ =
        (∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ)) +
          ∫ t in Set.Icc (-T) T,
            (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
          exact intervalIntegral.integral_add
            (scalarFourierLaplacePlemelj_zero_real_kernel_intervalIntegrable
              a ha T)
            (scalarFourierLaplacePlemelj_zero_odd_imaginary_intervalIntegrable
              a ha T)
    _ =
        (∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ)) + 0 := by
          exact congrArg
            (fun z : ℂ =>
              (∫ t in Set.Icc (-T) T,
                ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ)) + z)
            (scalarFourierLaplacePlemelj_zero_odd_imaginary_integral_eq_zero
              a ha T)
    _ =
        ∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) := by
          exact add_zero _
    _ =
        (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
          exact
            scalarFourierLaplacePlemelj_zero_real_kernel_integral_eq_arctan
              a ha T

/-- Zero-time symmetric Cauchy window has the elementary arctangent value. -/
theorem scalarFourierLaplacePlemelj_zero_window_eq_arctan
    (a : ℝ) (ha : 0 < a) (T x : ℝ) (hx : x = 0) :
    (∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp ((a : ℂ) * (x : ℂ)) =
      (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
  have hinner :
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) =
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) := by
    exact intervalIntegral.integral_congr
      (Filter.Eventually.of_forall
        (fun t : ℝ =>
          congrArg
            (fun z : ℂ =>
              (-1 / ((a : ℂ) + t * Complex.I)) *
                Complex.exp z)
            (calc
              Complex.I * (t : ℂ) * (x : ℂ) =
                  Complex.I * (t : ℂ) * (0 : ℂ) := by
                exact congrArg
                  (fun y : ℂ => Complex.I * (t : ℂ) * y)
                  (congrArg (fun y : ℝ => (y : ℂ)) hx)
              _ = 0 := by
                exact mul_zero (Complex.I * (t : ℂ)))))
  have houter :
      Complex.exp ((a : ℂ) * (x : ℂ)) = 1 := by
    exact congrArg Complex.exp
      (calc
        (a : ℂ) * (x : ℂ) = (a : ℂ) * (0 : ℂ) := by
          exact congrArg
            (fun y : ℂ => (a : ℂ) * y)
            (congrArg (fun y : ℝ => (y : ℂ)) hx)
        _ = 0 := by
          exact mul_zero (a : ℂ))
  calc
    (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp ((a : ℂ) * (x : ℂ))
        =
        (∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I))) *
          Complex.exp ((a : ℂ) * (x : ℂ)) := by
          exact congrArg
            (fun z : ℂ => z * Complex.exp ((a : ℂ) * (x : ℂ)))
            hinner
    _ =
        (∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I))) * 1 := by
          exact congrArg
            (fun z : ℂ =>
              (∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I))) * z)
            houter
    _ =
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) := by
          exact mul_one _
    _ =
        (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
          exact scalarFourierLaplacePlemelj_zero_raw_window_eq_arctan
            a ha T

/-- The zero-time arctangent window is bounded by the scalar Plemelj constant. -/
theorem scalarFourierLaplacePlemelj_zero_arctan_bound
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    ‖((-(2 : ℝ) * Real.arctan (T / a) : ℝ) : ℂ)‖
      ≤ 2 * (Real.pi + 1) := by
  let y : ℝ := T / a
  let u : ℝ := Real.arctan y
  have hhalf_lt_pi : Real.pi / 2 < Real.pi :=
    half_lt_self Real.pi_pos
  have hupper : u ≤ Real.pi := by
    exact le_of_lt
      ((Real.arctan_lt_pi_div_two y).trans hhalf_lt_pi)
  have hneg_pi_lt_neg_half : -Real.pi < -(Real.pi / 2) :=
    neg_lt_neg hhalf_lt_pi
  have hlower : -Real.pi ≤ u := by
    exact le_of_lt
      (hneg_pi_lt_neg_half.trans
        (Real.neg_pi_div_two_lt_arctan y))
  have habs : |u| ≤ Real.pi :=
    abs_le.mpr ⟨hlower, hupper⟩
  have hnorm :
      ‖((-(2 : ℝ) * Real.arctan (T / a) : ℝ) : ℂ)‖ =
        |(-(2 : ℝ) * u)| := by
    unfold u
    unfold y
    exact RCLike.norm_ofReal (K := ℂ) (-(2 : ℝ) * Real.arctan (T / a))
  have habs_neg :
      |(-(2 : ℝ) * u)| = |(2 : ℝ) * u| := by
    have hneg_mul : (-(2 : ℝ) * u) = -((2 : ℝ) * u) :=
      neg_mul (2 : ℝ) u
    exact (congrArg abs hneg_mul).trans (abs_neg ((2 : ℝ) * u))
  have habs_mul :
      |(2 : ℝ) * u| = (2 : ℝ) * |u| := by
    calc
      |(2 : ℝ) * u| = |(2 : ℝ)| * |u| := by
        exact abs_mul (2 : ℝ) u
      _ = (2 : ℝ) * |u| := by
        exact congrArg (fun r : ℝ => r * |u|)
          (abs_of_nonneg zero_le_two)
  have htwo_abs_le : (2 : ℝ) * |u| ≤ 2 * Real.pi :=
    mul_le_mul_of_nonneg_left habs zero_le_two
  have hpi_le_pi_add_one : Real.pi ≤ Real.pi + 1 :=
    le_add_of_nonneg_right zero_le_one
  have htwo_pi_le : 2 * Real.pi ≤ 2 * (Real.pi + 1) :=
    mul_le_mul_of_nonneg_left hpi_le_pi_add_one zero_le_two
  exact
    (le_of_eq hnorm).trans
      ((le_of_eq habs_neg).trans
        ((le_of_eq habs_mul).trans
          (htwo_abs_le.trans htwo_pi_le)))

/-- Zero-time uniform finite-window bound for the normalized scalar Cauchy
kernel. -/
theorem scalarFourierLaplacePlemelj_unweighted_window_mul_exp_uniform_bound_zero
    (a : ℝ) (ha : 0 < a) (T x : ℝ) (hx : x = 0) :
    ‖(∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp ((a : ℂ) * (x : ℂ))‖
      ≤ 2 * (Real.pi + 1) := by
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ 2 * (Real.pi + 1))
    (scalarFourierLaplacePlemelj_zero_window_eq_arctan a ha T x hx)
    (scalarFourierLaplacePlemelj_zero_arctan_bound a ha T)

/-- Normalized scalar Fourier-Laplace Plemelj package.

For `a > 0`, the symmetric Fourier windows of
`-exp(a x)/(a + i t)` converge to the open half-line multiplier. -/
theorem scalarFourierLaplacePlemelj_openHalfLine
    (a : ℝ) (ha : 0 < a) :
    ∀ x : ℝ, x ≠ 0 →
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / ((a : ℂ) + t * Complex.I)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp ((a : ℂ) * (x : ℂ)))
        atTop
        (𝓝
          (Set.indicator (Set.Ioi (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) :=
  fun x hx0 =>
    scalarFourierLaplacePlemelj_pointwise_openHalfLine a ha x hx0

/-- The fixed-right-line scalar Cauchy window is the normalized
Fourier-Laplace Plemelj window with `a = c - 1`. -/
theorem fixedRightLine_scalarCauchyWindow_eq_normalizedLaplaceWindow
    (c : ℝ) (x T : ℝ) :
    (∫ t in Set.Icc (-T) T,
      (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
    ∫ t in Set.Icc (-T) T,
      (-1 / (((c - 1 : ℝ) : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
  exact intervalIntegral.integral_congr
    (Filter.Eventually.of_forall
      (fun t : ℝ =>
        congrArg
          (fun z : ℂ =>
            (-1 / z) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
          (calc
            ((c : ℂ) + t * Complex.I) - 1 =
                ((c : ℂ) - 1) + t * Complex.I := by
              exact sub_add_eq_add_sub (c : ℂ) (t * Complex.I) 1
            _ = (((c - 1 : ℝ) : ℂ) + t * Complex.I) := by
              exact congrArg (fun z : ℂ => z + t * Complex.I)
                (Complex.ofReal_sub c 1).symm)))

/-- Scalar fixed-right-line Cauchy/Plemelj package.

This is the one-dimensional analytic owner theorem behind the fixed-right-line
Cauchy projection: finite symmetric Cauchy windows converge pointwise to the
open-half-line multiplier. -/
theorem fixedRightLine_scalarCauchyWindow_plemelj_openHalfLine
    (c : ℝ) (hc : 1 < c) :
    ∀ x : ℝ, x ≠ 0 →
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        atTop
        (𝓝
          (Set.indicator (Set.Ioi (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) := by
  have ha : 0 < c - 1 :=
    sub_pos.mpr hc
  have hbase :=
    scalarFourierLaplacePlemelj_openHalfLine
      (c - 1) ha
  intro x
  intro hx0
  have hfun :
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c - 1 : ℝ) : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
    funext T
    exact fixedRightLine_scalarCauchyWindow_eq_normalizedLaplaceWindow c x T
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop
        (𝓝
          (Set.indicator (Set.Ioi (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)))
    hfun.symm
    (hbase x hx0)

/-- Scalar fixed-right-line Plemelj theorem for finite symmetric Cauchy
windows, preserving the legacy theorem name while only asserting the
open-half-line pointwise limit. -/
theorem fixedRightLine_scalarCauchyWindow_plemelj_openHalfLine_with_uniform_bound
    (c : ℝ) (hc : 1 < c) (x : ℝ) (hx0 : x ≠ 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
      atTop
      (𝓝
        (Set.indicator (Set.Ioi (0 : ℝ))
          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) := by
  exact
    fixedRightLine_scalarCauchyWindow_plemelj_openHalfLine c hc x hx0

/-- Scalar fixed-right-line Plemelj theorem for finite symmetric Cauchy
windows, expressed as the open half-line multiplier. -/
theorem fixedRightLine_scalarCauchyWindow_pointwise_tendsto_openHalfLine
    (c : ℝ) (hc : 1 < c) (x : ℝ) (hx0 : x ≠ 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
      atTop
      (𝓝
        (Set.indicator (Set.Ioi (0 : ℝ))
          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) :=
  fixedRightLine_scalarCauchyWindow_plemelj_openHalfLine_with_uniform_bound
    c hc x hx0

/-- Pointwise positive-time Bromwich/Plemelj value for the fixed-right-line
finite scalar Cauchy windows. -/
theorem fixedRightLine_scalarCauchyWindow_pointwise_tendsto_positive
    (c : ℝ) (hc : 1 < c) (x : ℝ) (hx : 0 < x) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
      atTop
      (𝓝 (-2 * (Real.pi : ℂ))) := by
  have hbase :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        atTop
        (𝓝
          (Set.indicator (Set.Ioi (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) :=
    fixedRightLine_scalarCauchyWindow_pointwise_tendsto_openHalfLine c hc x
      (ne_of_gt hx)
  have hvalue :
      Set.indicator (Set.Ioi (0 : ℝ))
        (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x =
        (-2 * (Real.pi : ℂ)) :=
    indicator_of_mem hx
      (fun _ : ℝ => (-2 * (Real.pi : ℂ)))
  exact hvalue ▸ hbase

/-- Pointwise negative-time Bromwich/Plemelj value for the fixed-right-line
finite scalar Cauchy windows. -/
theorem fixedRightLine_scalarCauchyWindow_pointwise_tendsto_negative
    (c : ℝ) (hc : 1 < c) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
      atTop
      (𝓝 0) := by
  have hbase :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        atTop
        (𝓝
          (Set.indicator (Set.Ioi (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) :=
    fixedRightLine_scalarCauchyWindow_pointwise_tendsto_openHalfLine c hc x
      (ne_of_lt hx)
  have hnot : x ∉ Set.Ioi (0 : ℝ) :=
    fun hx_pos : 0 < x =>
      (not_lt_of_ge (le_of_lt hx)) hx_pos
  have hvalue :
      Set.indicator (Set.Ioi (0 : ℝ))
        (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x = 0 :=
    indicator_of_not_mem hnot
      (fun _ : ℝ => (-2 * (Real.pi : ℂ)))
  exact hvalue ▸ hbase

/-- The positive upper-arc Jordan majorant remains bounded after multiplication
by the compensating exponential on compact intervals away from zero. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_eventually_le
    (a : ℝ) :
    ∀ᶠ T in atTop,
      Real.pi * T / (T - a) ≤ Real.pi + 1 := by
  have hlimit :
      Tendsto
        (fun T : ℝ => Real.pi * T / (T - a))
        atTop
        (𝓝 Real.pi) :=
    scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_tendsto_pi a
  have hpi_lt : Real.pi < Real.pi + 1 :=
    lt_add_of_pos_right Real.pi zero_lt_one
  exact
    (hlimit (Set.Iio_mem_nhds hpi_lt)).mono
      (fun T hT => le_of_lt hT)

/-- Real exponential factor in the positive away-zero compact interval is
bounded by the endpoint exponential. -/
theorem scalarFourierLaplacePlemelj_positive_exp_norm_le_intervalEndpoint
    (a : ℝ) (ha : 0 < a) (R x : ℝ) (hxR : ‖x‖ ≤ R) :
    ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ Real.exp (a * R) := by
  have hx_le_R : x ≤ R :=
    (le_abs_self x).trans hxR
  have hax_le_aR : a * x ≤ a * R :=
    mul_le_mul_of_nonneg_left hx_le_R ha.le
  have hnorm_eq :
      ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ = Real.exp (a * x) := by
    calc
      ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ =
          Complex.abs (Complex.exp ((a : ℂ) * (x : ℂ))) := by
        exact Complex.norm_eq_abs (Complex.exp ((a : ℂ) * (x : ℂ)))
      _ =
          Real.exp (((a : ℂ) * (x : ℂ)).re) := by
        exact Complex.abs_exp ((a : ℂ) * (x : ℂ))
      _ =
          Real.exp
            ((a : ℂ).re * (x : ℂ).re -
              (a : ℂ).im * (x : ℂ).im) := by
        exact congrArg Real.exp (Complex.mul_re (a : ℂ) (x : ℂ))
      _ =
          Real.exp (a * (x : ℂ).re -
              (a : ℂ).im * (x : ℂ).im) := by
        exact congrArg
          (fun r : ℝ =>
            Real.exp
              (r * (x : ℂ).re - (a : ℂ).im * (x : ℂ).im))
          (Complex.ofReal_re a)
      _ =
          Real.exp (a * x -
              (a : ℂ).im * (x : ℂ).im) := by
        exact congrArg
          (fun r : ℝ =>
            Real.exp (a * r - (a : ℂ).im * (x : ℂ).im))
          (Complex.ofReal_re x)
      _ =
          Real.exp (a * x - 0 * (x : ℂ).im) := by
        exact congrArg
          (fun r : ℝ => Real.exp (a * x - r * (x : ℂ).im))
          (Complex.ofReal_im a)
      _ =
          Real.exp (a * x - 0) := by
        exact congrArg Real.exp (congrArg (fun r : ℝ => a * x - r)
          (zero_mul (x : ℂ).im))
      _ =
          Real.exp (a * x) := by
        exact congrArg Real.exp (sub_zero (a * x))
  exact (le_of_eq hnorm_eq).trans (Real.exp_le_exp.mpr hax_le_aR)

/-- Reciprocal factor in the positive away-zero Jordan majorant is bounded by
the away-from-zero threshold. -/
theorem scalarFourierLaplacePlemelj_positive_awayZero_reciprocal_le
    (T x δ : ℝ) (hT : 0 < T) (hδ : 0 < δ) (hδx : δ ≤ x) :
    (T * x)⁻¹ ≤ (T * δ)⁻¹ := by
  have hTδ_pos : 0 < T * δ :=
    mul_pos hT hδ
  have hTδ_le_Tx : T * δ ≤ T * x :=
    mul_le_mul_of_nonneg_left hδx hT.le
  exact inv_anti₀ hTδ_pos hTδ_le_Tx

/-- Product assembly for the positive upper-arc Jordan majorant away from
zero. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_awayZero_mulExp_bound_eventually_of_factors
    (a : ℝ) (ha : 0 < a) (R δ B : ℝ) (hδ : 0 < δ)
    (hB_nonneg : 0 ≤ B)
    (hpref :
      ∀ᶠ T in atTop,
        Real.pi * T / (T - a) ≤ B) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
                ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  let C : ℝ := B * δ⁻¹ * Real.exp (a * R)
  have hδ_inv_nonneg : 0 ≤ δ⁻¹ :=
    inv_nonneg_of_nonneg hδ.le
  have hexp_nonneg : 0 ≤ Real.exp (a * R) :=
    (Real.exp_pos (a * R)).le
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact mul_nonneg (mul_nonneg hB_nonneg hδ_inv_nonneg) hexp_nonneg
  refine ⟨C, hC_nonneg, ?_⟩
  exact
    (hpref.and (eventually_gt_atTop (max a 1))).mono
      (fun T hTpair =>
        fun x hδx hxR =>
          let Pref : ℝ := Real.pi * T / (T - a)
          let Rec : ℝ := (T * x)⁻¹
          let E : ℝ := ‖Complex.exp ((a : ℂ) * (x : ℂ))‖
          have hpref_le : Pref ≤ B := hTpair.1
          have hmax : max a 1 < T := hTpair.2
          have haT : a < T := (le_max_left a 1).trans_lt hmax
          have h_one_lt_T : 1 < T := (le_max_right a 1).trans_lt hmax
          have hT_pos : 0 < T := zero_lt_one.trans h_one_lt_T
          have hden_pos : 0 < T - a := sub_pos.mpr haT
          have hpref_nonneg : 0 ≤ Pref := by
            unfold Pref
            exact div_nonneg
              (mul_nonneg Real.pi_nonneg hT_pos.le)
              hden_pos.le
          have hrec_le_Tδ :
              Rec ≤ (T * δ)⁻¹ := by
            unfold Rec
            exact
              scalarFourierLaplacePlemelj_positive_awayZero_reciprocal_le
                T x δ hT_pos hδ hδx
          have hδ_le_Tδ : δ ≤ T * δ := by
            calc
              δ = 1 * δ := by
                exact (one_mul δ).symm
              _ ≤ T * δ := by
                exact mul_le_mul_of_nonneg_right h_one_lt_T.le hδ.le
          have hTδ_inv_le : (T * δ)⁻¹ ≤ δ⁻¹ :=
            inv_anti₀ hδ hδ_le_Tδ
          have hrec_le : Rec ≤ δ⁻¹ :=
            hrec_le_Tδ.trans hTδ_inv_le
          have hrec_nonneg : 0 ≤ Rec := by
            unfold Rec
            exact inv_nonneg_of_nonneg (mul_nonneg hT_pos.le (hδ.le.trans hδx))
          have hE_le : E ≤ Real.exp (a * R) := by
            unfold E
            exact
              scalarFourierLaplacePlemelj_positive_exp_norm_le_intervalEndpoint
                a ha R x hxR
          have hE_nonneg : 0 ≤ E := by
            unfold E
            exact norm_nonneg _
          have h_pref_rec :
              Pref * Rec ≤ B * δ⁻¹ :=
            mul_le_mul hpref_le hrec_le hrec_nonneg hB_nonneg
          have h_product :
              (Pref * Rec) * E ≤ (B * δ⁻¹) * Real.exp (a * R) :=
            mul_le_mul h_pref_rec hE_le hE_nonneg
              (mul_nonneg hB_nonneg hδ_inv_nonneg)
          calc
            scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
                ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ =
                (Pref * Rec) * E := by
              rfl
            _ ≤ (B * δ⁻¹) * Real.exp (a * R) := h_product
            _ = C := by
              rfl)

theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_awayZero_mulExp_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
                ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  let B : ℝ := Real.pi + 1
  have hB_nonneg : 0 ≤ B := by
    unfold B
    exact add_nonneg Real.pi_nonneg zero_le_one
  exact
    scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_awayZero_mulExp_bound_eventually_of_factors
      a ha R δ B hδ hB_nonneg
      (scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_eventually_le
        a)

/-- Positive upper-arc away-from-zero estimate from its Jordan majorant. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_awayZero_mulExp_norm_bound_eventually_of_jordan
    (a : ℝ) (ha : 0 < a) (R δ Cj : ℝ) (hδ : 0 < δ)
    (hCj_nonneg : 0 ≤ Cj)
    (hjordan :
      ∀ᶠ T in atTop,
        ∀ x : ℝ,
          δ ≤ x →
          ‖x‖ ≤ R →
            scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
              ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ Cj) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  exact
    ⟨Cj, hCj_nonneg,
      (hjordan.and (eventually_gt_atTop a)).mono
        (fun T hTpair =>
          fun x hδx hxR =>
            have hxpos : x ∈ Set.Ioi (0 : ℝ) :=
              hδ.trans_le hδx
            have harc :
                ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T‖ ≤
                  scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T :=
              (scalarFourierLaplacePlemelj_positiveUpperArc_norm_le_jordanDensity_integral
                a ha x hxpos T hTpair.2).trans
                (scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_le_majorant
                  a ha x hxpos T hTpair.2)
            have hexp_nonneg :
                0 ≤ ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ :=
              norm_nonneg _
            calc
              ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                  Complex.exp ((a : ℂ) * (x : ℂ))‖ =
                  ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T‖ *
                    ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
                exact norm_mul
                  (scalarFourierLaplacePlemelj_positiveUpperArc a x T)
                  (Complex.exp ((a : ℂ) * (x : ℂ)))
              _ ≤
                  scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
                    ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
                exact mul_le_mul_of_nonneg_right harc hexp_nonneg
              _ ≤ Cj := hTpair.1 x hδx hxR)⟩

theorem scalarFourierLaplacePlemelj_positiveUpperArc_awayZero_mulExp_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  match
    scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_awayZero_mulExp_bound_eventually
      a ha R δ hδ
  with
  | ⟨Cj, hCj_nonneg, hjordan⟩ =>
      exact
        scalarFourierLaplacePlemelj_positiveUpperArc_awayZero_mulExp_norm_bound_eventually_of_jordan
          a ha R δ Cj hδ hCj_nonneg hjordan

/-- Radius-qualified finite upper-half-plane residue identity for the
positive-time scalar window. -/
theorem scalarFourierLaplacePlemelj_positive_window_add_upperArc_eq_residueValue_of_radius
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) :
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) +
          scalarFourierLaplacePlemelj_positiveUpperArc a x T =
        (-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  have hclosed :
      scalarFourierLaplacePlemelj_positiveClosedContour a x T =
        (-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ)) :=
    scalarFourierLaplacePlemelj_positiveClosedContour_eq_residueValue_of_poleInside
      a ha x hx T hT
  exact
    (scalarFourierLaplacePlemelj_positiveClosedContour_eq_window_add_upperArc
      a x T).symm.trans hclosed

/-- After compensation by `exp (a x)`, the positive finite window and the
compensated upper arc add to the constant residue. -/
theorem scalarFourierLaplacePlemelj_positive_window_mul_exp_add_upperArc_mul_exp_eq_residue_of_radius
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) :
      ((∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp ((a : ℂ) * (x : ℂ))) +
        scalarFourierLaplacePlemelj_positiveUpperArc a x T *
          Complex.exp ((a : ℂ) * (x : ℂ)) =
      (-2 * (Real.pi : ℂ)) := by
  let W : ℂ :=
    ∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))
  let A : ℂ := scalarFourierLaplacePlemelj_positiveUpperArc a x T
  let E : ℂ := Complex.exp ((a : ℂ) * (x : ℂ))
  let R : ℂ := (-2 * (Real.pi : ℂ))
  have hraw :
      W + A =
        R * Complex.exp (-(a : ℂ) * (x : ℂ)) := by
    exact
      scalarFourierLaplacePlemelj_positive_window_add_upperArc_eq_residueValue_of_radius
        a ha x hx T hT
  have hmul :
      (W + A) * E =
        (R * Complex.exp (-(a : ℂ) * (x : ℂ))) * E := by
    exact congrArg (fun z : ℂ => z * E) hraw
  have hcollapse :
      (R * Complex.exp (-(a : ℂ) * (x : ℂ))) * E = R := by
    exact
      scalarFourierLaplacePlemelj_positive_laplaceJump_mul_eq_constant
        a x
  calc
    W * E + A * E = (W + A) * E := by
      exact (add_mul W A E).symm
    _ = (R * Complex.exp (-(a : ℂ) * (x : ℂ))) * E := hmul
    _ = R := hcollapse

/-- Exact radius-qualified positive finite-window formula after moving the
compensating exponential inside the window. -/
theorem scalarFourierLaplacePlemelj_positive_window_with_exp_eq_residue_sub_upperArc_mul_exp_of_radius
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) :
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ))) =
      (-2 * (Real.pi : ℂ)) -
        scalarFourierLaplacePlemelj_positiveUpperArc a x T *
          Complex.exp ((a : ℂ) * (x : ℂ)) := by
  let W : ℂ :=
    ∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))
  let A : ℂ := scalarFourierLaplacePlemelj_positiveUpperArc a x T
  let E : ℂ := Complex.exp ((a : ℂ) * (x : ℂ))
  let R : ℂ := (-2 * (Real.pi : ℂ))
  have hadd :
      W * E + A * E = R :=
    scalarFourierLaplacePlemelj_positive_window_mul_exp_add_upperArc_mul_exp_eq_residue_of_radius
      a ha x hx T hT
  have hsub :
      W * E = R - A * E := by
    calc
      W * E = (W * E + A * E) - A * E := by
        exact (add_sub_cancel_right (W * E) (A * E)).symm
      _ = R - A * E := by
        exact congrArg (fun z : ℂ => z - A * E) hadd
  have hwindow :
      W * E =
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)) :=
    scalarFourierLaplacePlemelj_positive_window_mul_exp_eq_window_with_exp
      a x T
  exact hwindow.symm.trans hsub

/-- Radius-qualified positive finite-window norm estimate from the compensated
upper-arc norm. -/
theorem scalarFourierLaplacePlemelj_positive_window_with_exp_norm_le_residue_add_upperArc_of_radius
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) :
      ‖(∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ)))‖
      ≤ ‖(-2 * (Real.pi : ℂ))‖ +
          ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
            Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
  let A : ℂ := scalarFourierLaplacePlemelj_positiveUpperArc a x T
  let E : ℂ := Complex.exp ((a : ℂ) * (x : ℂ))
  let R : ℂ := (-2 * (Real.pi : ℂ))
  let Wexp : ℂ :=
    ∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp ((a : ℂ) * (x : ℂ))
  have heq :
      Wexp = R - A * E :=
    scalarFourierLaplacePlemelj_positive_window_with_exp_eq_residue_sub_upperArc_mul_exp_of_radius
      a ha x hx T hT
  calc
    ‖Wexp‖ = ‖R - A * E‖ := by
      exact congrArg norm heq
    _ ≤ ‖R‖ + ‖A * E‖ := by
      exact norm_sub_le R (A * E)

/-- Positive away-from-zero window bound from the upper-arc bound and the
positive residue identity. -/
theorem scalarFourierLaplacePlemelj_compactInterval_positive_awayZero_norm_bound_eventually_of_arc
    (a : ℝ) (ha : 0 < a) (R δ Carc : ℝ) (hδ : 0 < δ)
    (hCarc_nonneg : 0 ≤ Carc)
    (harc :
      ∀ᶠ T in atTop,
        ∀ x : ℝ,
          δ ≤ x →
          ‖x‖ ≤ R →
            ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
              Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ Carc) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  let Cresidue : ℝ := ‖(-2 * (Real.pi : ℂ))‖
  let C : ℝ := Cresidue + Carc
  have hCresidue_nonneg : 0 ≤ Cresidue := by
    unfold Cresidue
    exact norm_nonneg _
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact add_nonneg hCresidue_nonneg hCarc_nonneg
  have hresidue_norm :
      ‖(-2 * (Real.pi : ℂ))‖ = Cresidue := by
    rfl
  exact
    ⟨C, hC_nonneg,
      (harc.and (eventually_gt_atTop a)).mono
        (fun T hTpair x hδx hxR =>
          have hxpos : x ∈ Set.Ioi (0 : ℝ) :=
            lt_of_lt_of_le hδ hδx
          have hwindow :
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ ‖(-2 * (Real.pi : ℂ))‖ +
                  ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                    Complex.exp ((a : ℂ) * (x : ℂ))‖ :=
            scalarFourierLaplacePlemelj_positive_window_with_exp_norm_le_residue_add_upperArc_of_radius
              a ha x hxpos T hTpair.2
          calc
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + t * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))‖
                ≤ ‖(-2 * (Real.pi : ℂ))‖ +
                    ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                      Complex.exp ((a : ℂ) * (x : ℂ))‖ := hwindow
            _ ≤ ‖(-2 * (Real.pi : ℂ))‖ + Carc := by
                exact add_le_add_left (hTpair.1 x hδx hxR)
                  ‖(-2 * (Real.pi : ℂ))‖
            _ = C := by
                exact congrArg (fun r : ℝ => r + Carc) hresidue_norm)⟩

theorem scalarFourierLaplacePlemelj_compactInterval_positive_awayZero_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  match scalarFourierLaplacePlemelj_positiveUpperArc_awayZero_mulExp_norm_bound_eventually
    a ha R δ hδ with
  | ⟨Carc, hCarc_nonneg, harc⟩ =>
      exact
        scalarFourierLaplacePlemelj_compactInterval_positive_awayZero_norm_bound_eventually_of_arc
          a ha R δ Carc hδ hCarc_nonneg harc

/-- Even-cosine real part of the uncompensated Cauchy Fourier window. -/

end FixedLineCauchyProjection

end
end Boundary
