import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.PositiveJordan.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.LowerHalfDiskPrimitive.Owner

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

noncomputable def scalarFourierLaplacePlemelj_negativeLowerArc
    (a x T : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(-Real.pi),
    let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
    (-1 / ((a : ℂ) + z * Complex.I)) *
      Complex.exp (Complex.I * z * (x : ℂ)) *
      (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Integrand of the negative lower semicircle correction. -/
noncomputable def scalarFourierLaplacePlemelj_negativeLowerArcIntegrand
    (a x T θ : ℝ) : ℂ :=
  let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  (-1 / ((a : ℂ) + z * Complex.I)) *
    Complex.exp (Complex.I * z * (x : ℂ)) *
    (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- The negative lower arc is the interval integral of its named integrand. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_eq_integral_integrand
    (a x T : ℝ) :
    scalarFourierLaplacePlemelj_negativeLowerArc a x T =
      ∫ θ in (0 : ℝ)..(-Real.pi),
        scalarFourierLaplacePlemelj_negativeLowerArcIntegrand a x T θ := by
  rfl

/-- Real Jordan density for the negative lower semicircle estimate. -/
noncomputable def scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity
    (a x T θ : ℝ) : ℝ :=
  (T / (T - a)) * Real.exp (-(T * x * Real.sin θ))

/-- Closed lower-half-plane scalar contour integral for the negative-time
Fourier-Laplace denominator. -/
noncomputable def scalarFourierLaplacePlemelj_negativeClosedContour
    (a x T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-T) T,
    (-1 / ((a : ℂ) + t * Complex.I)) *
      Complex.exp
        (Complex.I * (t : ℂ) * (x : ℂ))) +
    scalarFourierLaplacePlemelj_negativeLowerArc a x T

/-- The negative closed contour unfolds to its real segment plus lower arc. -/
theorem scalarFourierLaplacePlemelj_negativeClosedContour_eq_window_add_lowerArc
    (a x T : ℝ) :
    scalarFourierLaplacePlemelj_negativeClosedContour a x T =
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) +
          scalarFourierLaplacePlemelj_negativeLowerArc a x T := by
  rfl

/-- The upper scalar pole is outside the lower half-plane contour. -/
theorem scalarFourierLaplacePlemelj_upperPole_not_mem_lowerSemicircleInterior
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : 0 < T) :
    ¬ scalarFourierLaplacePlemelj_upperPole a =
        (-(a : ℂ)) * Complex.I := by
  intro hpole
  have him :
      Complex.im (scalarFourierLaplacePlemelj_upperPole a) =
        Complex.im ((-(a : ℂ)) * Complex.I) :=
    congrArg Complex.im hpole
  have hleft :
      Complex.im (scalarFourierLaplacePlemelj_upperPole a) = a := by
    calc
      Complex.im (scalarFourierLaplacePlemelj_upperPole a) =
          Complex.im ((a : ℂ) * Complex.I) := by
        exact congrArg Complex.im
          (scalarFourierLaplacePlemelj_upperPole_eq a)
      _ = (a : ℂ).re * Complex.I.im + (a : ℂ).im * Complex.I.re := by
        exact Complex.mul_im (a : ℂ) Complex.I
      _ = a * 1 + 0 * 0 := by
        exact congrArg₂ HAdd.hAdd
          (congrArg₂ HMul.hMul
            (Complex.ofReal_re a)
            Complex.I_im)
          (congrArg₂ HMul.hMul
            (Complex.ofReal_im a)
            Complex.I_re)
      _ = a * 1 := by
        exact add_zero (a * 1)
      _ = a := by
        exact mul_one a
  have hright :
      Complex.im ((-(a : ℂ)) * Complex.I) = -a := by
    calc
      Complex.im ((-(a : ℂ)) * Complex.I) =
          (-(a : ℂ)).re * Complex.I.im + (-(a : ℂ)).im * Complex.I.re := by
        exact Complex.mul_im (-(a : ℂ)) Complex.I
      _ = (-(a : ℂ)).re * 1 + (-(a : ℂ)).im * 0 := by
        exact congrArg₂ HAdd.hAdd
          (congrArg₂ HMul.hMul
            rfl
            Complex.I_im)
          (congrArg₂ HMul.hMul
            rfl
            Complex.I_re)
      _ = (-(a : ℂ)).re * 1 + 0 := by
        exact congrArg
          (fun y : ℝ => (-(a : ℂ)).re * 1 + y)
          (mul_zero (-(a : ℂ)).im)
      _ = (-(a : ℂ)).re * 1 := by
        exact add_zero ((-(a : ℂ)).re * 1)
      _ = (-(a : ℂ)).re := by
        exact mul_one (-(a : ℂ)).re
      _ = -a := by
        exact (Complex.neg_re (a : ℂ)).trans
          (congrArg Neg.neg (Complex.ofReal_re a))
  have ha_eq_neg : a = -a :=
    hleft.symm.trans (him.trans hright)
  have htwo_zero : (2 : ℝ) * a = 0 := by
    have hadd : a + a = 0 :=
      eq_neg_iff_add_eq_zero.mp ha_eq_neg
    exact (two_mul a).symm.trans hadd
  have ha_zero : a = 0 :=
    (mul_eq_zero.mp htwo_zero).resolve_left two_ne_zero
  exact (ne_of_gt ha) ha_zero

/-- The lower-half-plane residue sum for the negative-time scalar contour is
zero because the pole is not enclosed. -/
noncomputable def scalarFourierLaplacePlemelj_negativeLowerHalfPlaneResidueSum
    (_a _x : ℝ) : ℂ :=
  0

/-- Negative-time scalar Fourier-Laplace meromorphic kernel. -/
noncomputable def scalarFourierLaplacePlemelj_negativeKernel
    (a x : ℝ) (z : ℂ) : ℂ :=
  (-1 / ((a : ℂ) + z * Complex.I)) *
    Complex.exp (Complex.I * z * (x : ℂ))

/-- Boundary integral of the negative-time scalar kernel over the finite lower
semicircle contour, written directly in terms of the named meromorphic kernel. -/
noncomputable def scalarFourierLaplacePlemelj_negativeKernelLowerSemicircleBoundaryIntegral
    (a x T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-T) T,
    scalarFourierLaplacePlemelj_negativeKernel a x (t : ℂ)) +
    ∫ θ in (0 : ℝ)..(-Real.pi),
      let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      scalarFourierLaplacePlemelj_negativeKernel a x z *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Analytic numerator of the negative-time scalar Cauchy kernel after factoring
the simple upper-pole denominator. -/
noncomputable def scalarFourierLaplacePlemelj_negativeKernelAnalyticNumerator
    (x : ℝ) (z : ℂ) : ℂ :=
  Complex.I * Complex.exp (Complex.I * z * (x : ℂ))

/-- Closed lower half-disk used by the negative-time scalar contour. -/
    ∫ θ in (0 : ℝ)..(-Real.pi),
      let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      F z *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- The upper pole is not in any closed lower half-disk. -/
theorem scalarFourierLaplacePlemelj_upperPole_not_mem_lowerHalfDisk
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    scalarFourierLaplacePlemelj_upperPole a ∉
      scalarFourierLaplacePlemelj_lowerHalfDisk T := by
  intro hpole
  have him_le :
      Complex.im (scalarFourierLaplacePlemelj_upperPole a) ≤ 0 :=
    hpole.2
  have him_eq :
      Complex.im (scalarFourierLaplacePlemelj_upperPole a) = a := by
    calc
      Complex.im (scalarFourierLaplacePlemelj_upperPole a) =
          Complex.im ((a : ℂ) * Complex.I) := by
        exact congrArg Complex.im
          (scalarFourierLaplacePlemelj_upperPole_eq a)
      _ = (a : ℂ).re * Complex.I.im + (a : ℂ).im * Complex.I.re := by
        exact Complex.mul_im (a : ℂ) Complex.I
      _ = a * 1 + 0 * 0 := by
        exact congrArg₂ HAdd.hAdd
          (congrArg₂ HMul.hMul
            (Complex.ofReal_re a)
            Complex.I_im)
          (congrArg₂ HMul.hMul
            (Complex.ofReal_im a)
            Complex.I_re)
      _ = a * 1 + 0 := by
        exact congrArg
          (fun r : ℝ => a * 1 + r)
          (zero_mul (0 : ℝ))
      _ = a * 1 := by
        exact add_zero (a * 1)
      _ = a := by
        exact mul_one a
  exact (not_le_of_gt ha) (him_eq ▸ him_le)

/-- The scalar Cauchy denominator is nonzero on the lower half-disk. -/
theorem scalarFourierLaplacePlemelj_negativeKernel_denominator_ne_zero_on_lowerHalfDisk
    (a : ℝ) (ha : 0 < a) (T : ℝ) {z : ℂ}
    (hz : z ∈ scalarFourierLaplacePlemelj_lowerHalfDisk T) :
    (a : ℂ) + z * Complex.I ≠ 0 := by
  intro hzero
  have hfactor_zero :
      Complex.I * (z - scalarFourierLaplacePlemelj_upperPole a) = 0 :=
    (scalarFourierLaplacePlemelj_positiveKernel_denominator_factor_upperPole
      a z).symm.trans hzero
  have hsub_zero : z - scalarFourierLaplacePlemelj_upperPole a = 0 :=
    (mul_eq_zero.mp hfactor_zero).resolve_left Complex.I_ne_zero
  have hz_eq_pole : z = scalarFourierLaplacePlemelj_upperPole a :=
    sub_eq_zero.mp hsub_zero
  exact
    scalarFourierLaplacePlemelj_upperPole_not_mem_lowerHalfDisk
      a ha T
      (hz_eq_pole ▸ hz)

/-- The affine denominator of the scalar Cauchy kernel is complex differentiable. -/
theorem scalarFourierLaplacePlemelj_negativeKernel_denominator_differentiableOn_lowerHalfDisk
    (a : ℝ) (T : ℝ) :
    DifferentiableOn ℂ
      (fun z : ℂ => (a : ℂ) + z * Complex.I)
      (scalarFourierLaplacePlemelj_lowerHalfDisk T) := by
  exact
    (differentiable_id.mul_const Complex.I).differentiableOn.const_add
      (a : ℂ)

/-- The reciprocal denominator of the scalar Cauchy kernel is complex
differentiable on the lower half-disk. -/
theorem scalarFourierLaplacePlemelj_negativeKernel_reciprocalDenominator_differentiableOn_lowerHalfDisk
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    DifferentiableOn ℂ
      (fun z : ℂ => ((a : ℂ) + z * Complex.I)⁻¹)
      (scalarFourierLaplacePlemelj_lowerHalfDisk T) := by
  exact
    (scalarFourierLaplacePlemelj_negativeKernel_denominator_differentiableOn_lowerHalfDisk
      a T).inv
      (fun z hz =>
        scalarFourierLaplacePlemelj_negativeKernel_denominator_ne_zero_on_lowerHalfDisk
          a ha T hz)

/-- The normalized reciprocal denominator `-1 / ((a : ℂ) + z * I)` is complex
differentiable on the lower half-disk. -/
theorem scalarFourierLaplacePlemelj_negativeKernel_normalizedReciprocalDenominator_differentiableOn_lowerHalfDisk
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    DifferentiableOn ℂ
      (fun z : ℂ => -1 / ((a : ℂ) + z * Complex.I))
      (scalarFourierLaplacePlemelj_lowerHalfDisk T) := by
  exact
    (scalarFourierLaplacePlemelj_negativeKernel_reciprocalDenominator_differentiableOn_lowerHalfDisk
      a ha T).const_mul
      (-1 : ℂ)

/-- The exponential numerator of the scalar Cauchy kernel is complex
differentiable on the lower half-disk. -/
theorem scalarFourierLaplacePlemelj_negativeKernel_exponentialNumerator_differentiableOn_lowerHalfDisk
    (x : ℝ) (T : ℝ) :
    DifferentiableOn ℂ
      (fun z : ℂ => Complex.exp (Complex.I * z * (x : ℂ)))
      (scalarFourierLaplacePlemelj_lowerHalfDisk T) := by
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
        (scalarFourierLaplacePlemelj_lowerHalfDisk T) := by
    exact hExp.comp_differentiableOn hL.differentiableOn
  exact
    Eq.subst
      (motive := fun E : ℂ → ℂ =>
        DifferentiableOn ℂ
          (E ∘ L)
          (scalarFourierLaplacePlemelj_lowerHalfDisk T))
      Complex.exp_eq_exp_ℂ.symm
      hComp

/-- The negative lower-half-plane kernel has zero enclosed residue sum. -/
theorem scalarFourierLaplacePlemelj_negativeKernel_lowerHalfPlaneResidueSum_eq_zero
    (a x : ℝ) :
    scalarFourierLaplacePlemelj_negativeLowerHalfPlaneResidueSum a x = 0 := by
  rfl

theorem scalarFourierLaplacePlemelj_two_pi_i_mul_negativeLowerHalfPlaneResidueSum_eq_zero
    (a x : ℝ) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
        scalarFourierLaplacePlemelj_negativeLowerHalfPlaneResidueSum a x = 0 := by
  unfold scalarFourierLaplacePlemelj_negativeLowerHalfPlaneResidueSum
  exact mul_zero ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)

/-- The negative closed contour is the named kernel boundary integral. -/
theorem scalarFourierLaplacePlemelj_negativeClosedContour_eq_negativeKernelLowerSemicircleBoundaryIntegral
    (a x T : ℝ) :
    scalarFourierLaplacePlemelj_negativeClosedContour a x T =
      scalarFourierLaplacePlemelj_negativeKernelLowerSemicircleBoundaryIntegral
        a x T := by
  rfl

/-- The negative lower semicircle boundary integral is the generic lower
half-disk boundary integral specialized to the negative scalar kernel. -/
theorem scalarFourierLaplacePlemelj_negativeKernelLowerSemicircleBoundaryIntegral_eq_lowerHalfDiskBoundaryIntegral
    (a x T : ℝ) :
    scalarFourierLaplacePlemelj_negativeKernelLowerSemicircleBoundaryIntegral
        a x T =
      scalarFourierLaplacePlemelj_lowerHalfDiskBoundaryIntegral
        (scalarFourierLaplacePlemelj_negativeKernel a x) T := by
  rfl

/-- The negative-time scalar kernel is complex differentiable on the closed
lower half-disk because its only pole is the upper pole. -/
theorem scalarFourierLaplacePlemelj_negativeKernel_differentiableOn_lowerHalfDisk
    (a : ℝ) (ha : 0 < a) (x : ℝ) (T : ℝ) :
    DifferentiableOn ℂ
      (scalarFourierLaplacePlemelj_negativeKernel a x)
      (scalarFourierLaplacePlemelj_lowerHalfDisk T) := by
  unfold scalarFourierLaplacePlemelj_negativeKernel
  exact
    (scalarFourierLaplacePlemelj_negativeKernel_normalizedReciprocalDenominator_differentiableOn_lowerHalfDisk
      a ha T).mul
      (scalarFourierLaplacePlemelj_negativeKernel_exponentialNumerator_differentiableOn_lowerHalfDisk
        x T)

/-- The negative-time scalar kernel is analytic at every point of the lower
half-disk. -/
theorem scalarFourierLaplacePlemelj_negativeKernel_analyticAt_lowerHalfDisk
    (a : ℝ) (ha : 0 < a) (x : ℝ) (T : ℝ) :
    ∀ z ∈ scalarFourierLaplacePlemelj_lowerHalfDisk T,
      AnalyticAt ℂ (scalarFourierLaplacePlemelj_negativeKernel a x) z := by
  intro z hz
  unfold scalarFourierLaplacePlemelj_negativeKernel
  have hden :
      AnalyticAt ℂ (fun w : ℂ => (a : ℂ) + w * Complex.I) z :=
    analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hden_ne :
      (a : ℂ) + z * Complex.I ≠ 0 :=
    scalarFourierLaplacePlemelj_negativeKernel_denominator_ne_zero_on_lowerHalfDisk
      a ha T hz
  have hnorm_rec :
      AnalyticAt ℂ (fun w : ℂ => -1 / ((a : ℂ) + w * Complex.I)) z :=
    analyticAt_const.div hden hden_ne
  have harg :
      AnalyticAt ℂ (fun w : ℂ => Complex.I * w * (x : ℂ)) z :=
    (analyticAt_const.mul analyticAt_id).mul analyticAt_const
  have hexp_normed :
      AnalyticAt ℂ
        (fun w : ℂ =>
          NormedSpace.exp ℂ (Complex.I * w * (x : ℂ)))
        z :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) (𝔸 := ℂ)
      (Complex.I * z * (x : ℂ))).comp harg
  have hexp :
      AnalyticAt ℂ
        (fun w : ℂ =>
          Complex.exp (Complex.I * w * (x : ℂ)))
        z := by
    exact
      Eq.subst
        (motive := fun E : ℂ → ℂ =>
          AnalyticAt ℂ
            (fun w : ℂ => E (Complex.I * w * (x : ℂ)))
            z)
        Complex.exp_eq_exp_ℂ.symm
        hexp_normed
  exact hnorm_rec.mul hexp

/-- Primitive data for a function on the lower half-disk. -/
theorem scalarFourierLaplacePlemelj_negativeKernelLowerHalfDisk_cauchyGoursat
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T) :
    scalarFourierLaplacePlemelj_negativeKernelLowerSemicircleBoundaryIntegral
        a x T = 0 := by
  exact
    (scalarFourierLaplacePlemelj_negativeKernelLowerSemicircleBoundaryIntegral_eq_lowerHalfDiskBoundaryIntegral
      a x T).trans
      (scalarFourierLaplacePlemelj_lowerHalfDiskBoundaryIntegral_eq_zero_of_analyticAt
        (scalarFourierLaplacePlemelj_negativeKernel a x) T hT.le
        (scalarFourierLaplacePlemelj_negativeKernel_analyticAt_lowerHalfDisk
          a ha x T))

/-- Half-disk Cauchy theorem for the negative-time lower contour: the upper pole
is outside the lower half-disk, so the boundary integral is zero. -/
theorem scalarFourierLaplacePlemelj_negativeKernelLowerHalfDisk_cauchyIntegralFormula
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T)
    (_hpole :
      ¬ scalarFourierLaplacePlemelj_upperPole a =
          (-(a : ℂ)) * Complex.I) :
    scalarFourierLaplacePlemelj_negativeKernelLowerSemicircleBoundaryIntegral
        a x T = 0 := by
  exact
    scalarFourierLaplacePlemelj_negativeKernelLowerHalfDisk_cauchyGoursat
      a ha x hx T hT

/-- Cauchy's residue theorem for the negative-time scalar kernel boundary
integral over the finite lower semicircle. -/
theorem scalarFourierLaplacePlemelj_negativeKernelLowerSemicircleBoundaryIntegral_cauchyResidue
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T)
    (_hpole :
      ¬ scalarFourierLaplacePlemelj_upperPole a =
          (-(a : ℂ)) * Complex.I) :
    scalarFourierLaplacePlemelj_negativeKernelLowerSemicircleBoundaryIntegral
        a x T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
        scalarFourierLaplacePlemelj_negativeLowerHalfPlaneResidueSum a x := by
  exact
    (scalarFourierLaplacePlemelj_negativeKernelLowerHalfDisk_cauchyIntegralFormula
      a ha x hx T hT _hpole).trans
      (scalarFourierLaplacePlemelj_two_pi_i_mul_negativeLowerHalfPlaneResidueSum_eq_zero
        a x).symm

/-- Cauchy's residue theorem for the negative-time scalar Fourier-Laplace
kernel on the finite lower semicircle.

The upper pole is outside this contour, so the enclosed residue sum is the
named zero residue sum. -/
theorem scalarFourierLaplacePlemelj_negativeKernel_lowerSemicircle_cauchyResidue
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T)
    (_hpole :
      ¬ scalarFourierLaplacePlemelj_upperPole a =
          (-(a : ℂ)) * Complex.I) :
    scalarFourierLaplacePlemelj_negativeClosedContour a x T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
        scalarFourierLaplacePlemelj_negativeLowerHalfPlaneResidueSum a x := by
  exact
    (scalarFourierLaplacePlemelj_negativeClosedContour_eq_negativeKernelLowerSemicircleBoundaryIntegral
      a x T).trans
      (scalarFourierLaplacePlemelj_negativeKernelLowerSemicircleBoundaryIntegral_cauchyResidue
        a ha x hx T hT _hpole)

/-- Lower-half-plane pole-free residue theorem for the negative-time scalar
contour, in `2πi` times the named kernel residue-sum form. -/
theorem scalarFourierLaplacePlemelj_lowerHalfPlaneResidueTheorem_closedContour_eq_two_pi_i_kernelResidueSum
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T)
    (_hpole :
      ¬ scalarFourierLaplacePlemelj_upperPole a =
          (-(a : ℂ)) * Complex.I) :
    scalarFourierLaplacePlemelj_negativeClosedContour a x T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
        scalarFourierLaplacePlemelj_negativeLowerHalfPlaneResidueSum a x := by
  exact
    scalarFourierLaplacePlemelj_negativeKernel_lowerSemicircle_cauchyResidue
      a ha x hx T hT _hpole

/-- Lower-half-plane pole-free residue theorem for the negative-time scalar
contour, in `2πi` times residue-sum form. -/
theorem scalarFourierLaplacePlemelj_lowerHalfPlaneResidueTheorem_closedContour_eq_two_pi_i_zeroResidueSum
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T)
    (_hpole :
      ¬ scalarFourierLaplacePlemelj_upperPole a =
          (-(a : ℂ)) * Complex.I) :
    scalarFourierLaplacePlemelj_negativeClosedContour a x T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
        scalarFourierLaplacePlemelj_negativeLowerHalfPlaneResidueSum a x := by
  exact
    scalarFourierLaplacePlemelj_lowerHalfPlaneResidueTheorem_closedContour_eq_two_pi_i_kernelResidueSum
      a ha x hx T hT _hpole

/-- Lower-half-plane pole-free residue theorem for the negative-time scalar
contour. -/
theorem scalarFourierLaplacePlemelj_lowerHalfPlaneResidueTheorem_closedContour_eq_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T)
    (_hpole :
      ¬ scalarFourierLaplacePlemelj_upperPole a =
          (-(a : ℂ)) * Complex.I) :
    scalarFourierLaplacePlemelj_negativeClosedContour a x T = 0 := by
  exact
    (scalarFourierLaplacePlemelj_lowerHalfPlaneResidueTheorem_closedContour_eq_two_pi_i_zeroResidueSum
      a ha x hx T hT _hpole).trans
      (scalarFourierLaplacePlemelj_two_pi_i_mul_negativeLowerHalfPlaneResidueSum_eq_zero
        a x)

theorem scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_owner
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T)
    (_hpole :
      ¬ scalarFourierLaplacePlemelj_upperPole a =
          (-(a : ℂ)) * Complex.I) :
    scalarFourierLaplacePlemelj_negativeClosedContour a x T = 0 := by
  exact
    scalarFourierLaplacePlemelj_lowerHalfPlaneResidueTheorem_closedContour_eq_zero
      a ha x hx T hT _hpole

/-- Pole-free lower-half-plane contour integral for the negative-time scalar kernel. -/
theorem scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_of_noPole
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T)
    (_hpole :
      ¬ scalarFourierLaplacePlemelj_upperPole a =
          (-(a : ℂ)) * Complex.I) :
    scalarFourierLaplacePlemelj_negativeClosedContour a x T = 0 := by
  exact
    scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_owner
      a ha x hx T hT _hpole

/-- Radius-qualified lower-half-plane pole-free residue theorem for the negative-time
scalar closed contour. -/
theorem scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_of_poleOutside
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T) :
    scalarFourierLaplacePlemelj_negativeClosedContour a x T = 0 := by
  exact
    scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_of_noPole
      a ha x hx T hT
      (scalarFourierLaplacePlemelj_upperPole_not_mem_lowerSemicircleInterior
        a ha T hT)

/-- Lower-half-plane pole-free residue theorem for the negative-time scalar closed
contour. -/
theorem scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_residueTheorem
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    ∀ᶠ T in atTop,
      scalarFourierLaplacePlemelj_negativeClosedContour a x T = 0 := by
  exact (eventually_gt_atTop (0 : ℝ)).mono
    (fun T hT =>
      scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_of_poleOutside
        a ha x hx T hT)

/-- Finite lower-half-plane pole-free contour identity for the negative-time
scalar Fourier-Laplace contour. -/
theorem scalarFourierLaplacePlemelj_negative_window_add_lowerArc_eq_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    ∀ᶠ T in atTop,
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) +
          scalarFourierLaplacePlemelj_negativeLowerArc a x T =
        0 := by
  have hclosed :
      ∀ᶠ T in atTop,
        scalarFourierLaplacePlemelj_negativeClosedContour a x T = 0 :=
    scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_residueTheorem
      a ha x hx
  exact hclosed.mono
    (fun T hT =>
      (scalarFourierLaplacePlemelj_negativeClosedContour_eq_window_add_lowerArc
        a x T).symm.trans hT)

/-- Negative lower-arc Jordan majorant. -/
noncomputable def scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant
    (a x T : ℝ) : ℝ :=
  (Real.pi * T / (T - a)) * ((T * (-x))⁻¹)

/-- The negative lower-arc Jordan prefactor has a finite limit. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanPrefactor_tendsto_pi
    (a : ℝ) :
    Tendsto
      (fun T : ℝ => Real.pi * T / (T - a))
      atTop
      (𝓝 Real.pi) :=
  scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_tendsto_pi a

/-- The negative lower-arc reciprocal linear factor tends to zero. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanReciprocal_tendsto_zero
    (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ => (T * (-x))⁻¹)
      atTop
      (𝓝 0) := by
  have hneg : 0 < -x :=
    neg_pos.mpr hx
  exact
    tendsto_inv_atTop_zero.comp
      (Tendsto.atTop_mul_const
        hneg
        tendsto_id)

/-- The negative lower-arc Jordan majorant tends to zero. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant_tendsto_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ =>
        scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T)
      atTop
      (𝓝 0) := by
  exact
    (scalarFourierLaplacePlemelj_negativeLowerArcJordanPrefactor_tendsto_pi
      a).mul
      (scalarFourierLaplacePlemelj_negativeLowerArcJordanReciprocal_tendsto_zero
        x hx)

/-- Denominator part of the negative lower-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_denominator_norm_inv_le
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : a < T) (θ : ℝ) :
    ‖(-1 /
      ((a : ℂ) +
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I))‖ ≤
      (T - a)⁻¹ := by
  exact
    scalarFourierLaplacePlemelj_semicircleDenominator_inv_norm_le
      a ha T hT θ

/-- Exponential damping part of the negative lower-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_exponential_norm_eq_damping
    (x T θ : ℝ) :
    ‖Complex.exp
      (Complex.I *
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (x : ℂ))‖ =
      Real.exp (-(T * x * Real.sin θ)) := by
  exact
    scalarFourierLaplacePlemelj_positiveUpperArc_exponential_norm_eq_damping
      x T θ

/-- Velocity part of the negative lower-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_velocity_norm_eq_radius
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : a < T) (θ : ℝ) :
    ‖Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = T := by
  exact
    scalarFourierLaplacePlemelj_semicircleVelocity_norm_eq_radius
      T (ha.trans hT) θ

/-- Product assembly for the negative lower-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcIntegrand_norm_le_jordanDensity_of_factors
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : a < T) (θ : ℝ)
    (hden :
      ‖(-1 /
        ((a : ℂ) +
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I))‖ ≤
        (T - a)⁻¹)
    (hexp :
      ‖Complex.exp
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (x : ℂ))‖ =
        Real.exp (-(T * x * Real.sin θ)))
    (hvel :
      ‖Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = T) :
    ‖scalarFourierLaplacePlemelj_negativeLowerArcIntegrand a x T θ‖ ≤
      scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ := by
  let D : ℂ :=
    -1 /
      ((a : ℂ) +
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I)
  let E : ℂ :=
    Complex.exp
      (Complex.I *
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (x : ℂ))
  let V : ℂ :=
    Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  let R : ℝ :=
    Real.exp (-(T * x * Real.sin θ))
  have hER : ‖E‖ = R := by
    exact hexp
  have hVR : ‖V‖ = T := by
    exact hvel
  have hV_nonneg : 0 ≤ ‖V‖ :=
    norm_nonneg V
  have hstep :
      (‖D‖ * ‖E‖) * ‖V‖ ≤
        ((T - a)⁻¹ * ‖E‖) * ‖V‖ := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hden (norm_nonneg E))
      hV_nonneg
  calc
    ‖scalarFourierLaplacePlemelj_negativeLowerArcIntegrand a x T θ‖ =
        ‖D * E * V‖ := by
      exact rfl
    _ = ‖D * E‖ * ‖V‖ := by
      exact norm_mul (D * E) V
    _ = (‖D‖ * ‖E‖) * ‖V‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖V‖)
        (norm_mul D E)
    _ ≤ ((T - a)⁻¹ * ‖E‖) * ‖V‖ := by
      exact hstep
    _ = ((T - a)⁻¹ * R) * ‖V‖ := by
      exact congrArg
        (fun r : ℝ => ((T - a)⁻¹ * r) * ‖V‖)
        hER
    _ = ((T - a)⁻¹ * R) * T := by
      exact congrArg
        (fun r : ℝ => ((T - a)⁻¹ * R) * r)
        hVR
    _ = (T / (T - a)) * R := by
      exact
        (scalarFourierLaplacePlemelj_jordanDensity_eq_inv_mul_exp_mul_radius
          a T R).symm
    _ = scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ := by
      exact rfl

/-- Pointwise Jordan domination of the negative lower-arc integrand. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcIntegrand_norm_le_jordanDensity
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : a < T) (θ : ℝ) :
    ‖scalarFourierLaplacePlemelj_negativeLowerArcIntegrand a x T θ‖ ≤
      scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ := by
  exact
    scalarFourierLaplacePlemelj_negativeLowerArcIntegrand_norm_le_jordanDensity_of_factors
      a ha x hx T hT θ
      (scalarFourierLaplacePlemelj_negativeLowerArc_denominator_norm_inv_le
        a ha T hT θ)
      (scalarFourierLaplacePlemelj_negativeLowerArc_exponential_norm_eq_damping
        x T θ)
      (scalarFourierLaplacePlemelj_negativeLowerArc_velocity_norm_eq_radius
        a ha T hT θ)

/-- The negative lower-arc Jordan density is interval-integrable. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_intervalIntegrable
    (a x T : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ)
      MeasureTheory.volume
      (-Real.pi)
      (0 : ℝ) := by
  have harg :
      Continuous
        (fun θ : ℝ => -(T * x * Real.sin θ)) := by
    exact (continuous_const.mul Real.continuous_sin).neg
  have hexp :
      Continuous
        (fun θ : ℝ => Real.exp (-(T * x * Real.sin θ))) := by
    exact Real.continuous_exp.comp harg
  have hdensity :
      Continuous
        (fun θ : ℝ =>
          scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ) := by
    exact continuous_const.mul hexp
  exact hdensity.intervalIntegrable (-Real.pi) (0 : ℝ)

/-- The negative lower-arc Jordan density is nonnegative when the radius is
larger than the pole height. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_nonneg
    (a : ℝ) (ha : 0 < a) (x T θ : ℝ) (hT : a < T) :
    0 ≤ scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ := by
  have hTpos : 0 < T :=
    ha.trans hT
  have hdenpos : 0 < T - a :=
    sub_pos.mpr hT
  have hpref_nonneg : 0 ≤ T / (T - a) :=
    div_nonneg hTpos.le hdenpos.le
  exact mul_nonneg hpref_nonneg (Real.exp_pos _).le

/-- The negative Jordan density interval integral factors into the constant
prefactor times the scalar lower-arc sine-damping integral. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_integral_eq_prefactor_mul
    (a : ℝ) (T x : ℝ) :
    ∫ θ in (-Real.pi)..(0 : ℝ),
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ =
      (T / (T - a)) *
        ∫ θ in (-Real.pi)..(0 : ℝ),
          Real.exp (-(T * x * Real.sin θ)) := by
  exact intervalIntegral.integral_const_mul
    (T / (T - a))
    (fun θ : ℝ => Real.exp (-(T * x * Real.sin θ)))

/-- The lower-arc damping integrand after `θ ↦ -θ` is the upper-arc damping
integrand for `-x`. -/
theorem scalarFourierLaplacePlemelj_lowerSineDamping_negIntegrand_eq_upper
    (T x θ : ℝ) :
    Real.exp (-(T * x * Real.sin (-θ))) =
      Real.exp (-((T * (-x)) * Real.sin θ)) := by
  have hleft_arg :
      -(T * x * Real.sin (-θ)) =
        T * x * Real.sin θ := by
    calc
      -(T * x * Real.sin (-θ)) =
          -(T * x * (-Real.sin θ)) := by
        exact congrArg
          (fun r : ℝ => -(T * x * r))
          (Real.sin_neg θ)
      _ = -((T * x) * (-Real.sin θ)) := by
        exact rfl
      _ = -(-(T * x * Real.sin θ)) := by
        exact congrArg Neg.neg
          (mul_neg (T * x) (Real.sin θ))
      _ = T * x * Real.sin θ := by
        exact neg_neg (T * x * Real.sin θ)
  have hright_arg :
      -((T * (-x)) * Real.sin θ) =
        T * x * Real.sin θ := by
    calc
      -((T * (-x)) * Real.sin θ) =
          -((-(T * x)) * Real.sin θ) := by
        exact congrArg
          (fun r : ℝ => -(r * Real.sin θ))
          (mul_neg T x)
      _ = -(-(T * x * Real.sin θ)) := by
        exact congrArg Neg.neg
          (neg_mul (T * x) (Real.sin θ))
      _ = T * x * Real.sin θ := by
        exact neg_neg (T * x * Real.sin θ)
  exact congrArg Real.exp
    (hleft_arg.trans hright_arg.symm)

/-- Lower semicircle sine-damping integral is transported to the upper
semicircle by `θ ↦ -θ`. -/
theorem scalarFourierLaplacePlemelj_lowerSineDampingIntegral_eq_upper
    (T x : ℝ) :
    ∫ θ in (-Real.pi)..(0 : ℝ),
        Real.exp (-(T * x * Real.sin θ)) =
      ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-((T * (-x)) * Real.sin θ)) := by
  calc
    ∫ θ in (-Real.pi)..(0 : ℝ),
        Real.exp (-(T * x * Real.sin θ)) =
        ∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (-(T * x * Real.sin (-θ))) := by
      exact
        (intervalIntegral.integral_comp_neg
          (f := fun θ : ℝ => Real.exp (-(T * x * Real.sin θ)))
          (a := (0 : ℝ))
          (b := Real.pi)).symm
    _ = ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-((T * (-x)) * Real.sin θ)) := by
      exact intervalIntegral.integral_congr
        (fun θ _hθ =>
          scalarFourierLaplacePlemelj_lowerSineDamping_negIntegrand_eq_upper
            T x θ)

/-- Jordan's sine estimate for the negative lower-arc damping integral. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_sineDampingIntegral_le
    (T x : ℝ) (hTnegx : 0 < T * (-x)) :
    ∫ θ in (-Real.pi)..(0 : ℝ),
        Real.exp (-(T * x * Real.sin θ)) ≤
      Real.pi * (T * (-x))⁻¹ := by
  calc
    ∫ θ in (-Real.pi)..(0 : ℝ),
        Real.exp (-(T * x * Real.sin θ)) =
        ∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (-((T * (-x)) * Real.sin θ)) := by
      exact scalarFourierLaplacePlemelj_lowerSineDampingIntegral_eq_upper
        T x
    _ ≤ Real.pi * (T * (-x))⁻¹ := by
      exact scalarFourierLaplacePlemelj_upperSineDamping_integral_le
        (T * (-x)) hTnegx

/-- Multiplication by the positive Jordan prefactor transports the scalar
lower-arc sine-damping estimate to the full density. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_integral_le_majorant_of_sine
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : a < T)
    (hsine :
      ∫ θ in (-Real.pi)..(0 : ℝ),
          Real.exp (-(T * x * Real.sin θ)) ≤
        Real.pi * (T * (-x))⁻¹) :
    ∫ θ in (-Real.pi)..(0 : ℝ),
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ ≤
      scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T := by
  have hTpos : 0 < T :=
    ha.trans hT
  have hdenpos : 0 < T - a :=
    sub_pos.mpr hT
  have hpref_nonneg : 0 ≤ T / (T - a) :=
    div_nonneg hTpos.le hdenpos.le
  calc
    ∫ θ in (-Real.pi)..(0 : ℝ),
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ =
        (T / (T - a)) *
          ∫ θ in (-Real.pi)..(0 : ℝ),
            Real.exp (-(T * x * Real.sin θ)) := by
      exact
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_integral_eq_prefactor_mul
          a T x
    _ ≤ (T / (T - a)) * (Real.pi * (T * (-x))⁻¹) := by
      exact mul_le_mul_of_nonneg_left hsine hpref_nonneg
    _ = (Real.pi * T / (T - a)) * (T * (-x))⁻¹ := by
      exact
        scalarFourierLaplacePlemelj_jordanPrefactor_mul_pi_inv_eq_majorant
          a T (T * (-x))
    _ = scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T := by
      exact rfl

/-- Integral form of Jordan's sine estimate for the negative lower arc. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_integral_le_majorant
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : a < T) :
    ∫ θ in (-Real.pi)..(0 : ℝ),
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ ≤
      scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T := by
  have hTpos : 0 < T :=
    ha.trans hT
  have hnegx : 0 < -x :=
    neg_pos.mpr hx
  have hTnegx : 0 < T * (-x) :=
    mul_pos hTpos hnegx
  exact
    scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_integral_le_majorant_of_sine
      a ha x hx T hT
      (scalarFourierLaplacePlemelj_negativeLowerArc_sineDampingIntegral_le
        T x hTnegx)

/-- Interval-integral norm domination for the negative lower arc by the Jordan
density. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_norm_le_jordanDensity_integral
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : a < T) :
    ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T‖ ≤
      ∫ θ in (-Real.pi)..(0 : ℝ),
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ := by
  have hdensity_int :
      IntervalIntegrable
        (fun θ : ℝ =>
          scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ)
        MeasureTheory.volume
        (-Real.pi)
        (0 : ℝ) :=
    scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_intervalIntegrable
      a x T
  have hnorm_abs :
      ‖∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_negativeLowerArcIntegrand a x T θ‖ ≤
        |∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ| := by
    exact intervalIntegral.norm_integral_le_of_norm_le
      (Eventually.of_forall
        (fun θ _hθ =>
          scalarFourierLaplacePlemelj_negativeLowerArcIntegrand_norm_le_jordanDensity
            a ha x hx T hT θ))
      hdensity_int
  have hneg_pi_le_zero : -Real.pi ≤ (0 : ℝ) :=
    neg_nonpos.mpr Real.pi_nonneg
  have hnonneg_integral :
      0 ≤ ∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ := by
    exact intervalIntegral.integral_nonneg
      hneg_pi_le_zero
      (fun θ _hθ =>
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_nonneg
          a ha x T θ hT)
  calc
    ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T‖ =
        ‖∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_negativeLowerArcIntegrand a x T θ‖ := by
      exact congrArg norm
        (scalarFourierLaplacePlemelj_negativeLowerArc_eq_integral_integrand
          a x T)
    _ ≤ |∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ| := by
      exact hnorm_abs
    _ = ∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ := by
      exact abs_of_nonneg hnonneg_integral

/-- The negative lower arc is eventually bounded by the Jordan majorant. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_norm_eventually_le_jordanMajorant
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    ∀ᶠ T in atTop,
      ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T‖ ≤
        scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T := by
  exact
    (eventually_gt_atTop a).mono
      (fun T hT =>
        (scalarFourierLaplacePlemelj_negativeLowerArc_norm_le_jordanDensity_integral
          a ha x hx T hT).trans
          (scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_integral_le_majorant
            a ha x hx T hT))

/-- Jordan norm estimate for the negative lower semicircle correction. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_norm_tendsto_zero_jordanEstimate
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ => ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T‖)
      atTop
      (𝓝 0) := by
  exact squeeze_zero'
    (Eventually.of_forall
      (fun T : ℝ =>
        norm_nonneg (scalarFourierLaplacePlemelj_negativeLowerArc a x T)))
    (scalarFourierLaplacePlemelj_negativeLowerArc_norm_eventually_le_jordanMajorant
      a ha x hx)
    (scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant_tendsto_zero
      a ha x hx)

/-- The lower semicircle correction term vanishes for negative time. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_tendsto_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ => scalarFourierLaplacePlemelj_negativeLowerArc a x T)
      atTop
      (𝓝 0) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (scalarFourierLaplacePlemelj_negativeLowerArc_norm_tendsto_zero_jordanEstimate
      a ha x hx)

/-- Negative-time finite-window contour limit before multiplying by the
constant `exp (a x)`. -/
theorem scalarFourierLaplacePlemelj_negative_window_tendsto_zero_without_exp
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)))
      atTop
      (𝓝 0) := by
  let W : ℝ → ℂ :=
    fun T : ℝ =>
      ∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))
  let A : ℝ → ℂ :=
    fun T : ℝ => scalarFourierLaplacePlemelj_negativeLowerArc a x T
  have hsum_eventual :
      ∀ᶠ T in atTop, W T + A T = 0 := by
    unfold W
    unfold A
    exact
      scalarFourierLaplacePlemelj_negative_window_add_lowerArc_eq_zero
        a ha x hx
  have hsum :
      Tendsto (fun T : ℝ => W T + A T) atTop (𝓝 0) :=
    tendsto_nhds_of_eventually_eq hsum_eventual
  have hnegA :
      Tendsto (fun T : ℝ => -A T) atTop (𝓝 0) := by
    have hA :
        Tendsto A atTop (𝓝 0) := by
      unfold A
      exact
        scalarFourierLaplacePlemelj_negativeLowerArc_tendsto_zero
          a ha x hx
    exact Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun T : ℝ => -A T) atTop (𝓝 z))
      neg_zero
      hA.neg
  have hW :
      Tendsto (fun T : ℝ => W T + A T + -A T) atTop (𝓝 (0 + 0 : ℂ)) :=
    hsum.add hnegA
  have hpoint :
      (fun T : ℝ => W T + A T + -A T) = W := by
    funext T
    calc
      W T + A T + -A T = W T + (A T + -A T) := by
        exact add_assoc (W T) (A T) (-A T)
      _ = W T + 0 := by
        exact congrArg (fun z : ℂ => W T + z) (add_neg_cancel (A T))
      _ = W T := by
        exact add_zero (W T)
  have htarget : (0 : ℂ) + 0 = 0 :=
    add_zero (0 : ℂ)
  exact Eq.subst
    (motive := fun u : ℝ → ℂ => Tendsto u atTop (𝓝 0))
    hpoint
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun T : ℝ => W T + A T + -A T) atTop (𝓝 z))
      htarget
      hW)

/-- Multiplication by `exp (a x)` preserves the negative-time zero limit. -/
theorem scalarFourierLaplacePlemelj_negative_window_tendsto_zero_mul_exp
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ =>
        (∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ))) *
          Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝 0) := by
  have htarget :
      (0 : ℂ) * Complex.exp ((a : ℂ) * (x : ℂ)) = 0 :=
    zero_mul (Complex.exp ((a : ℂ) * (x : ℂ)))
  exact Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun T : ℝ =>
          (∫ t in Set.Icc (-T) T,
            (-1 / ((a : ℂ) + t * Complex.I)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ))) *
            Complex.exp ((a : ℂ) * (x : ℂ)))
        atTop
        (𝓝 z))
    htarget
    ((scalarFourierLaplacePlemelj_negative_window_tendsto_zero_without_exp
      a ha x hx).mul
      (tendsto_const_nhds :
        Tendsto
          (fun _T : ℝ => Complex.exp ((a : ℂ) * (x : ℂ)))
          atTop
          (𝓝 (Complex.exp ((a : ℂ) * (x : ℂ))))))

/-- Negative-time scalar Plemelj window after the Laplace denominator has been
closed on the pole-free side. -/
theorem scalarFourierLaplacePlemelj_negative_window_tendsto_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝 0) := by
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop (𝓝 0))
    (funext
      (fun T : ℝ =>
        scalarFourierLaplacePlemelj_positive_window_mul_exp_eq_window_with_exp
          a x T))
    (scalarFourierLaplacePlemelj_negative_window_tendsto_zero_mul_exp
      a ha x hx)

/-- Negative-time normalized Fourier-Laplace Plemelj value. -/
theorem scalarFourierLaplacePlemelj_pointwise_negative
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝 0) := by
  exact
    scalarFourierLaplacePlemelj_negative_window_tendsto_zero
      a ha x hx

/-- Off-endpoint pointwise normalized Fourier-Laplace Plemelj value.

For `a > 0`, the symmetric Fourier windows of
`-exp(a x)/(a + i t)` converge to the open half-line multiplier away from
the jump at `x = 0`. -/
theorem scalarFourierLaplacePlemelj_pointwise_openHalfLine
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : x ≠ 0) :
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
          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) := by
  by_cases hx : x ∈ Set.Ioi (0 : ℝ)
  · have htarget :
        Set.indicator (Set.Ioi (0 : ℝ))
          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x =
            (-2 * (Real.pi : ℂ)) :=
      Set.indicator_of_mem hx _
    exact Eq.subst
      (motive := fun y : ℂ =>
        Tendsto
          (fun T : ℝ =>
            ∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + t * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))
          atTop
          (𝓝 y))
      htarget.symm
      (scalarFourierLaplacePlemelj_pointwise_positive a ha x hx)
  · have htarget :
      Set.indicator (Set.Ioi (0 : ℝ))
          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x =
            0 :=
      Set.indicator_of_not_mem hx _
    have hxneg : x < 0 :=
      lt_of_le_of_ne (not_lt.mp hx) hx0
    exact Eq.subst
      (motive := fun y : ℂ =>
        Tendsto
          (fun T : ℝ =>
            ∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + t * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))
          atTop
          (𝓝 y))
      htarget.symm
      (scalarFourierLaplacePlemelj_pointwise_negative a ha x hxneg)

/-- Normalized scalar finite-window Cauchy integral after multiplication by
the compensating exponential. -/

end FixedLineCauchyProjection

end
end Boundary
