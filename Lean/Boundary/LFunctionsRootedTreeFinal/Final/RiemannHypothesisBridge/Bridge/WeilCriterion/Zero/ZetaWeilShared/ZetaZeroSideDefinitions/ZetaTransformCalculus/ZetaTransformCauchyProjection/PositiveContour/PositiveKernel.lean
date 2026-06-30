import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.PositiveContour.CauchyKernel
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RemovableSingularity

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection
theorem scalarFourierLaplacePlemelj_neg_one_div_I_mul_eq_I_div
    (D : ℂ) :
    (-1 : ℂ) / (Complex.I * D) = Complex.I / D := by
  calc
    (-1 : ℂ) / (Complex.I * D) =
        (-1 : ℂ) * (Complex.I * D)⁻¹ := by
      rfl
    _ = (-1 : ℂ) * (D⁻¹ * Complex.I⁻¹) := by
      exact congrArg (fun W : ℂ => (-1 : ℂ) * W)
        (mul_inv_rev Complex.I D)
    _ = (-1 : ℂ) * (D⁻¹ * (-Complex.I)) := by
      exact congrArg
        (fun W : ℂ => (-1 : ℂ) * (D⁻¹ * W))
        Complex.inv_I
    _ = ((-1 : ℂ) * D⁻¹) * (-Complex.I) := by
      exact mul_assoc (-1 : ℂ) D⁻¹ (-Complex.I)
    _ = (-(D⁻¹)) * (-Complex.I) := by
      exact congrArg
        (fun W : ℂ => W * (-Complex.I))
        (neg_one_mul D⁻¹)
    _ = D⁻¹ * Complex.I := by
      exact neg_mul_neg D⁻¹ Complex.I
    _ = Complex.I * D⁻¹ := by
      exact mul_comm D⁻¹ Complex.I
    _ = Complex.I / D := by
      rfl

/-- Moving the exponential factor into the numerator of the normalized Cauchy
kernel. -/
theorem scalarFourierLaplacePlemelj_I_div_mul_exp_eq_I_mul_exp_div
    (D E : ℂ) :
    (Complex.I / D) * E = (Complex.I * E) / D := by
  calc
    (Complex.I / D) * E =
        (Complex.I * D⁻¹) * E := by
      rfl
    _ = Complex.I * (D⁻¹ * E) := by
      exact mul_assoc Complex.I D⁻¹ E
    _ = Complex.I * (E * D⁻¹) := by
      exact congrArg
        (fun W : ℂ => Complex.I * W)
        (mul_comm D⁻¹ E)
    _ = (Complex.I * E) * D⁻¹ := by
      exact (mul_assoc Complex.I E D⁻¹).symm
    _ = (Complex.I * E) / D := by
      rfl

/-- The positive scalar kernel is the upper-pole Cauchy kernel with analytic
numerator `scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator`. -/
theorem scalarFourierLaplacePlemelj_positiveKernel_eq_analyticNumerator_div_upperPole
    (a x : ℝ) (z : ℂ) :
    scalarFourierLaplacePlemelj_positiveKernel a x z =
      scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator x z /
        (z - scalarFourierLaplacePlemelj_upperPole a) := by
  let D : ℂ := z - scalarFourierLaplacePlemelj_upperPole a
  let E : ℂ := Complex.exp (Complex.I * z * (x : ℂ))
  unfold scalarFourierLaplacePlemelj_positiveKernel
  unfold scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator
  change (-1 / ((a : ℂ) + z * Complex.I)) * E =
    (Complex.I * E) / D
  have hden :
      (a : ℂ) + z * Complex.I = Complex.I * D :=
    scalarFourierLaplacePlemelj_positiveKernel_denominator_factor_upperPole
      a z
  exact
    Eq.subst
      (motive := fun W : ℂ =>
        (-1 / W) * E = (Complex.I * E) / D)
      hden.symm
      ((congrArg (fun Q : ℂ => Q * E)
        (scalarFourierLaplacePlemelj_neg_one_div_I_mul_eq_I_div D)).trans
        (scalarFourierLaplacePlemelj_I_div_mul_exp_eq_I_mul_exp_div
          D E))

/-- The positive analytic numerator is complex differentiable on the closed
upper half-disk. -/
theorem scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator_differentiableOn_upperHalfDisk
    (x : ℝ) (T : ℝ) :
    DifferentiableOn ℂ
      (scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator x)
      (scalarFourierLaplacePlemelj_upperHalfDisk T) := by
  unfold scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator
  let L : ℂ → ℂ := fun z : ℂ => Complex.I * z * (x : ℂ)
  have hL : Differentiable ℂ L := by
    exact
      (differentiable_id.const_mul Complex.I).mul_const
        (x : ℂ)
  have hExp :
      Differentiable ℂ (NormedSpace.exp ℂ : ℂ → ℂ) := by
    exact
      fun z : ℂ =>
        (NormedSpace.hasFDerivAt_exp (𝕂 := ℂ) (𝔸 := ℂ)).differentiableAt
  have hComp :
      DifferentiableOn ℂ
        ((NormedSpace.exp ℂ : ℂ → ℂ) ∘ L)
        (scalarFourierLaplacePlemelj_upperHalfDisk T) := by
    exact hExp.comp_differentiableOn hL.differentiableOn
  have hComplexExp :
      DifferentiableOn ℂ
        (Complex.exp ∘ L)
        (scalarFourierLaplacePlemelj_upperHalfDisk T) := by
    exact
      Eq.subst
        (motive := fun E : ℂ → ℂ =>
          DifferentiableOn ℂ
            (E ∘ L)
            (scalarFourierLaplacePlemelj_upperHalfDisk T))
        Complex.exp_eq_exp_ℂ.symm
        hComp
  exact hComplexExp.const_mul Complex.I

/-- The positive analytic numerator is entire, hence analytic at every point of
the closed upper half-disk. -/
theorem scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator_analyticAt_upperHalfDisk
    (x : ℝ) (T : ℝ) :
    ∀ z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
      AnalyticAt ℂ
        (scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator x)
        z := by
  intro z _hz
  unfold scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator
  let L : ℂ → ℂ := fun w : ℂ => Complex.I * w * (x : ℂ)
  have hL : Differentiable ℂ L := by
    exact
      (differentiable_id.const_mul Complex.I).mul_const
        (x : ℂ)
  have hExp :
      Differentiable ℂ (NormedSpace.exp ℂ : ℂ → ℂ) := by
    exact
      fun w : ℂ =>
        (NormedSpace.hasFDerivAt_exp (𝕂 := ℂ) (𝔸 := ℂ)).differentiableAt
  have hComp :
      Differentiable ℂ ((NormedSpace.exp ℂ : ℂ → ℂ) ∘ L) :=
    hExp.comp hL
  have hComplexExp :
      Differentiable ℂ (Complex.exp ∘ L) :=
    Eq.subst
      (motive := fun E : ℂ → ℂ =>
        Differentiable ℂ (E ∘ L))
      Complex.exp_eq_exp_ℂ.symm
      hComp
  exact (hComplexExp.const_mul Complex.I).analyticAt z

/-- Half-disk Cauchy integral formula for the positive-time analytic numerator
and the upper-pole denominator. -/
theorem scalarFourierLaplacePlemelj_positiveKernelUpperHalfDisk_cauchyIntegralFormula
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ)
    (_hpole : ‖scalarFourierLaplacePlemelj_upperPole a‖ < T) :
    scalarFourierLaplacePlemelj_positiveKernelUpperSemicircleBoundaryIntegral
        a x T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
        scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator
          x (scalarFourierLaplacePlemelj_upperPole a) := by
  have hT : 0 < T :=
    lt_of_le_of_lt (norm_nonneg (scalarFourierLaplacePlemelj_upperPole a))
      _hpole
  have hboundary :
      scalarFourierLaplacePlemelj_positiveKernelUpperSemicircleBoundaryIntegral
          a x T =
        scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
          (fun z : ℂ =>
            scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator x z /
              (z - scalarFourierLaplacePlemelj_upperPole a)) T := by
    exact
      (scalarFourierLaplacePlemelj_positiveKernelUpperSemicircleBoundaryIntegral_eq_upperHalfDiskBoundaryIntegral
        a x T).trans
        (congrArg
          (fun G : ℂ → ℂ =>
            scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral G T)
          (funext
            (fun z : ℂ =>
              scalarFourierLaplacePlemelj_positiveKernel_eq_analyticNumerator_div_upperPole
                a x z)))
  exact
    hboundary.trans
      (scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral_cauchyIntegralFormula
        (scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator x)
        T hT
        (scalarFourierLaplacePlemelj_upperPole a)
        _hpole
        (scalarFourierLaplacePlemelj_upperPole_im_pos a ha)
        (scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator_differentiableOn_upperHalfDisk
          x T)
        (scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator_analyticAt_upperHalfDisk
          x T))

/-- Cauchy's residue theorem for the positive-time scalar kernel boundary
integral over the finite upper semicircle. -/
theorem scalarFourierLaplacePlemelj_positiveKernelUpperSemicircleBoundaryIntegral_cauchyResidue
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ)
    (_hpole : ‖scalarFourierLaplacePlemelj_upperPole a‖ < T) :
    scalarFourierLaplacePlemelj_positiveKernelUpperSemicircleBoundaryIntegral
        a x T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
        scalarFourierLaplacePlemelj_positiveUpperPoleResidueCoefficient a x := by
  exact
    (scalarFourierLaplacePlemelj_positiveKernelUpperHalfDisk_cauchyIntegralFormula
      a ha x hx T _hpole).trans
      (congrArg
        (fun R : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * R)
        (scalarFourierLaplacePlemelj_positiveUpperPoleResidueCoefficient_eq_analyticNumerator
          a x).symm)

/-- Cauchy's residue theorem for the positive-time scalar Fourier-Laplace
kernel on the finite upper semicircle.

This is the genuine complex-analysis source: the real segment plus the
parametrized upper semicircle is the integral of
`scalarFourierLaplacePlemelj_positiveKernel a x`, and the only enclosed pole is
`scalarFourierLaplacePlemelj_upperPole a`. -/
theorem scalarFourierLaplacePlemelj_positiveKernel_upperSemicircle_cauchyResidue
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ)
    (_hpole : ‖scalarFourierLaplacePlemelj_upperPole a‖ < T) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
        scalarFourierLaplacePlemelj_positiveUpperPoleResidueCoefficient a x := by
  exact
    (scalarFourierLaplacePlemelj_positiveClosedContour_eq_positiveKernelUpperSemicircleBoundaryIntegral
      a x T).trans
      (scalarFourierLaplacePlemelj_positiveKernelUpperSemicircleBoundaryIntegral_cauchyResidue
        a ha x hx T _hpole)

/-- Upper-half-plane residue theorem for the positive-time scalar contour,
using the local residue of the named meromorphic kernel. -/
theorem scalarFourierLaplacePlemelj_upperHalfPlaneResidueTheorem_closedContour_eq_two_pi_i_kernelResidue
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ)
    (_hpole : ‖scalarFourierLaplacePlemelj_upperPole a‖ < T) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
        (Complex.I *
          Complex.exp
            (Complex.I * scalarFourierLaplacePlemelj_upperPole a * (x : ℂ))) := by
  exact
    (scalarFourierLaplacePlemelj_positiveKernel_upperSemicircle_cauchyResidue
      a ha x hx T _hpole).trans
      (congrArg
        (fun R : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * R)
        (scalarFourierLaplacePlemelj_positiveKernel_upperPole_residueCoefficient
          a x))

/-- Upper-half-plane residue theorem for the positive-time scalar contour:
the closed contour is `2πi` times the explicit upper-pole residue coefficient. -/
theorem scalarFourierLaplacePlemelj_upperHalfPlaneResidueTheorem_closedContour_eq_two_pi_i_residueCoefficient
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ)
    (_hpole : ‖scalarFourierLaplacePlemelj_upperPole a‖ < T) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
        scalarFourierLaplacePlemelj_positiveUpperPoleResidueCoefficient a x := by
  exact
    (scalarFourierLaplacePlemelj_upperHalfPlaneResidueTheorem_closedContour_eq_two_pi_i_kernelResidue
      a ha x hx T _hpole).trans
      (congrArg
        (fun R : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * R)
        (scalarFourierLaplacePlemelj_positiveKernel_upperPole_residueCoefficient
          a x).symm)

/-- Upper-half-plane residue theorem for the positive-time scalar contour:
the closed contour is the residue contribution of the enclosed upper pole. -/
theorem scalarFourierLaplacePlemelj_upperHalfPlaneResidueTheorem_closedContour_eq_upperPoleResidue
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ)
    (_hpole : ‖scalarFourierLaplacePlemelj_upperPole a‖ < T) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution a x := by
  exact
    (scalarFourierLaplacePlemelj_upperHalfPlaneResidueTheorem_closedContour_eq_two_pi_i_residueCoefficient
      a ha x hx T _hpole).trans
      (scalarFourierLaplacePlemelj_two_pi_i_mul_positiveUpperPoleResidueCoefficient_eq_contribution
        a x)

/-- Owner residue theorem for the positive-time upper semicircle contour. -/
theorem scalarFourierLaplacePlemelj_positiveClosedContour_eq_residueValue_owner
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ)
    (_hpole : ‖scalarFourierLaplacePlemelj_upperPole a‖ < T) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      (-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  exact
    (scalarFourierLaplacePlemelj_upperHalfPlaneResidueTheorem_closedContour_eq_upperPoleResidue
      a ha x hx T _hpole).trans
      (scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution_eq
        a ha x hx)

/-- Upper semicircle contour integral equals the abstract upper-pole residue contribution. -/
theorem scalarFourierLaplacePlemelj_positiveClosedContour_eq_upperPoleResidueContribution
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ)
    (_hpole : ‖scalarFourierLaplacePlemelj_upperPole a‖ < T) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution a x := by
  exact
    (scalarFourierLaplacePlemelj_positiveClosedContour_eq_residueValue_owner
      a ha x hx T _hpole).trans
      (scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution_eq
        a ha x hx).symm

/-- Upper semicircle contour integral equals the residue contribution once the pole
is inside the contour. -/
theorem scalarFourierLaplacePlemelj_positiveClosedContour_eq_residue_of_upperPoleInside
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ)
    (_hpole : ‖scalarFourierLaplacePlemelj_upperPole a‖ < T) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      (-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  exact
    (scalarFourierLaplacePlemelj_positiveClosedContour_eq_upperPoleResidueContribution
      a ha x hx T _hpole).trans
      (scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution_eq
        a ha x hx)

/-- Radius-qualified upper-half-plane residue theorem for the positive-time scalar
closed contour. -/
theorem scalarFourierLaplacePlemelj_positiveClosedContour_eq_residueValue_of_poleInside
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      (-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  exact
    scalarFourierLaplacePlemelj_positiveClosedContour_eq_residue_of_upperPoleInside
      a ha x hx T
      (scalarFourierLaplacePlemelj_upperPole_mem_upperSemicircleInterior_of_radius
        a ha T hT)

/-- Upper-half-plane residue theorem for the positive-time scalar closed contour. -/
theorem scalarFourierLaplacePlemelj_positiveClosedContour_eq_residueValue_residueTheorem
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ∀ᶠ T in atTop,
      scalarFourierLaplacePlemelj_positiveClosedContour a x T =
        (-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  exact (eventually_gt_atTop a).mono
    (fun T hT =>
      scalarFourierLaplacePlemelj_positiveClosedContour_eq_residueValue_of_poleInside
        a ha x hx T hT)

/-- Finite upper-half-plane residue identity for the positive-time scalar
Fourier-Laplace contour. -/
theorem scalarFourierLaplacePlemelj_positive_window_add_upperArc_eq_residueValue
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ∀ᶠ T in atTop,
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) +
          scalarFourierLaplacePlemelj_positiveUpperArc a x T =
        (-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  have hclosed :
      ∀ᶠ T in atTop,
        scalarFourierLaplacePlemelj_positiveClosedContour a x T =
          (-2 * (Real.pi : ℂ)) *
            Complex.exp (-(a : ℂ) * (x : ℂ)) :=
    scalarFourierLaplacePlemelj_positiveClosedContour_eq_residueValue_residueTheorem
      a ha x hx
  exact hclosed.mono
    (fun T hT =>
      (scalarFourierLaplacePlemelj_positiveClosedContour_eq_window_add_upperArc
        a x T).symm.trans hT)

/-- Positive upper-arc Jordan majorant. -/


end FixedLineCauchyProjection

end
end Boundary
