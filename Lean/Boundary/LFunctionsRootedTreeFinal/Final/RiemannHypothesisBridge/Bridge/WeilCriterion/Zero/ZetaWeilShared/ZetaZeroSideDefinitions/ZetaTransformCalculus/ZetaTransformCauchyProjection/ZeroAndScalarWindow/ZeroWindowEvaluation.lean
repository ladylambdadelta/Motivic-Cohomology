import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.ZeroAndScalarWindow.ZeroKernel

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

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
end FixedLineCauchyProjection

end
end Boundary
