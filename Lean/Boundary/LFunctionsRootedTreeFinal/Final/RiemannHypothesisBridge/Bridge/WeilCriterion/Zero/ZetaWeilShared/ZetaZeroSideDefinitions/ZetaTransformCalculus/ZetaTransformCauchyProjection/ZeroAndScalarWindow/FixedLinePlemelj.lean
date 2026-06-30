import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.ZeroAndScalarWindow.ZeroWindowEvaluation

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

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
end FixedLineCauchyProjection

end
end Boundary
