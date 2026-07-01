import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.ZeroAndScalarWindow.PositiveArcBounds

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

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

end FixedLineCauchyProjection

end
end Boundary
