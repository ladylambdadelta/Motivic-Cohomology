import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.PositiveJordan.Owner

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
def scalarFourierLaplacePlemelj_lowerHalfDisk
    (T : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ ≤ T ∧ Complex.im z ≤ 0}

/-- Generic boundary integral over the finite lower half-disk contour: diameter
from `-T` to `T`, then the lower semicircle returning from `T` to `-T`. -/
noncomputable def scalarFourierLaplacePlemelj_lowerHalfDiskBoundaryIntegral
    (F : ℂ → ℂ) (T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-T) T, F (t : ℂ)) +
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
def scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk
    (F G : ℂ → ℂ) (T : ℝ) : Prop :=
  ContinuousOn F (scalarFourierLaplacePlemelj_lowerHalfDisk T) ∧
    ∀ z ∈ scalarFourierLaplacePlemelj_lowerHalfDisk T,
      HasDerivWithinAt G (F z) (scalarFourierLaplacePlemelj_lowerHalfDisk T) z

/-- The lower half-disk is the intersection of the closed radius disk and the
closed lower half-plane. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_eq_closedBall_inter_lowerHalfPlane
    (T : ℝ) :
    scalarFourierLaplacePlemelj_lowerHalfDisk T =
      Metric.closedBall (0 : ℂ) T ∩ {z : ℂ | Complex.im z ≤ 0} := by
  exact
    Set.ext
      (fun z : ℂ =>
        Iff.intro
          (fun hz =>
            And.intro
              (mem_closedBall_zero_iff.mpr hz.1)
              hz.2)
          (fun hz =>
            And.intro
              (mem_closedBall_zero_iff.mp hz.1)
              hz.2))

/-- The origin lies in every nonnegative lower half-disk. -/
theorem scalarFourierLaplacePlemelj_zero_mem_lowerHalfDisk
    (T : ℝ) (_hT : 0 ≤ T) :
    (0 : ℂ) ∈ scalarFourierLaplacePlemelj_lowerHalfDisk T := by
  exact
    And.intro
      (Eq.subst
        (motive := fun r : ℝ => r ≤ T)
        norm_zero
        _hT)
      (le_of_eq Complex.zero_im)

/-- The lower half-disk is star-convex from the origin. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_starConvex
    (T : ℝ) (_hT : 0 ≤ T) :
    StarConvex ℝ (0 : ℂ) (scalarFourierLaplacePlemelj_lowerHalfDisk T) := by
  have hconv_closedBall :
      Convex ℝ (Metric.closedBall (0 : ℂ) T) :=
    convex_closedBall (0 : ℂ) T
  have hconv_lower :
      Convex ℝ {z : ℂ | Complex.im z ≤ 0} :=
    Complex.convex_halfSpace_im_le 0
  have hconv :
      Convex ℝ (Metric.closedBall (0 : ℂ) T ∩ {z : ℂ | Complex.im z ≤ 0}) :=
    hconv_closedBall.inter hconv_lower
  have hzero :
      (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) T ∩ {z : ℂ | Complex.im z ≤ 0} := by
    exact
      Eq.subst
        (motive := fun S : Set ℂ => (0 : ℂ) ∈ S)
        (scalarFourierLaplacePlemelj_lowerHalfDisk_eq_closedBall_inter_lowerHalfPlane T)
        (scalarFourierLaplacePlemelj_zero_mem_lowerHalfDisk T _hT)
  exact
    Eq.subst
      (motive := fun S : Set ℂ => StarConvex ℝ (0 : ℂ) S)
      (scalarFourierLaplacePlemelj_lowerHalfDisk_eq_closedBall_inter_lowerHalfPlane T).symm
      (hconv.starConvex hzero)

/-- Holomorphicity on the lower half-disk supplies primitive data on that
star-convex contour domain. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_hasPrimitive_of_analyticAt
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hanalytic :
      ∀ z ∈ scalarFourierLaplacePlemelj_lowerHalfDisk T,
        AnalyticAt ℂ F z) :
    ∃ G : ℂ → ℂ,
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T := by
  let G : ℂ → ℂ := LFunctions.complex_centerSegmentIntegral F
  have hprimitive :
      ∀ z : ℂ,
        z ∈ scalarFourierLaplacePlemelj_lowerHalfDisk T →
          AnalyticAt ℂ G z ∧ HasDerivAt G (F z) z := by
    exact
      LFunctions.complex_centerSegmentIntegral_parametricPrimitive_of_holomorphicOn_starConvex
        F
        (scalarFourierLaplacePlemelj_lowerHalfDisk_starConvex T _hT)
        _hanalytic
  exact
    Exists.intro G
      (And.intro
        (fun z hz => (_hanalytic z hz).continuousAt.continuousWithinAt)
        (fun z hz => (hprimitive z hz).2.hasDerivWithinAt))

/-- The unoriented real set integral on the lower half-disk diameter is the
usual oriented interval integral when `0 ≤ T`. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_setIntegral_eq_intervalIntegral
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T) :
    (∫ t in Set.Icc (-T) T, F (t : ℂ)) =
      ∫ t in (-T)..T, F (t : ℂ) := by
  have hle : -T ≤ T := by
    exact neg_le_self _hT
  exact
    Eq.trans
      MeasureTheory.integral_Icc_eq_integral_Ioc
      (intervalIntegral.integral_of_le
        (f := fun t : ℝ => F (t : ℂ))
        hle).symm

/-- The real diameter maps into the lower half-disk. -/
theorem scalarFourierLaplacePlemelj_realSegment_mapsTo_lowerHalfDisk
    (T : ℝ) (_hT : 0 ≤ T) :
    Set.MapsTo
      (fun x : ℝ => (x : ℂ))
      (Set.Icc (-T) T)
      (scalarFourierLaplacePlemelj_lowerHalfDisk T) := by
  intro x hx
  have hnorm : ‖(x : ℂ)‖ ≤ T := by
    calc
      ‖(x : ℂ)‖ = ‖x‖ := by
        exact Complex.norm_real x
      _ = |x| := by
        exact Real.norm_eq_abs x
      _ ≤ T := by
        exact abs_le.mpr hx
  have him : Complex.im (x : ℂ) ≤ 0 := by
    exact le_of_eq (Complex.ofReal_im x)
  exact ⟨hnorm, him⟩

/-- Around an interior diameter point, the closed diameter interval is a
neighborhood inside the right ray. -/
theorem scalarFourierLaplacePlemelj_realSegment_Icc_mem_nhdsWithin_Ioi
    (T t : ℝ) (_ht : t ∈ Set.Ioo (-T) T) :
    Set.Icc (-T) T ∈ 𝓝[Set.Ioi t] t := by
  exact
    Icc_mem_nhdsWithin_Ioi
      ⟨le_of_lt _ht.1, _ht.2⟩

/-- The local right-diameter derivative can be enlarged to the right-ray germ,
because near an interior point the right ray remains inside the diameter. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_rightLocalDerivative_to_rightRay
    (F G : ℂ → ℂ) (T t : ℝ) (_ht : t ∈ Set.Ioo (-T) T)
    (_hlocal :
      HasDerivWithinAt
        (fun x : ℝ => G (x : ℂ))
        (F (t : ℂ))
        (Set.Ioi t ∩ Set.Icc (-T) T)
        t) :
    HasDerivWithinAt
      (fun x : ℝ => G (x : ℂ))
      (F (t : ℂ))
      (Set.Ioi t)
      t := by
  exact
    _hlocal.mono_of_mem_nhdsWithin
      (inter_mem
        self_mem_nhdsWithin
        (scalarFourierLaplacePlemelj_realSegment_Icc_mem_nhdsWithin_Ioi
          T t _ht))

/-- Complex primitive data restricts to the local right-diameter derivative
inside the closed diameter. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_hasRightLocalDerivWithinAt_of_complexPrimitive
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T)
    (t : ℝ) (_ht : t ∈ Set.Ioo (-T) T)
    (_ht_lower :
      (t : ℂ) ∈ scalarFourierLaplacePlemelj_lowerHalfDisk T)
    (_hderiv :
      HasDerivWithinAt G (F (t : ℂ))
        (scalarFourierLaplacePlemelj_lowerHalfDisk T) (t : ℂ)) :
    HasDerivWithinAt
      (fun x : ℝ => G (x : ℂ))
      (F (t : ℂ))
      (Set.Ioi t ∩ Set.Icc (-T) T)
      t := by
  let s : Set ℝ := Set.Ioi t ∩ Set.Icc (-T) T
  let ofRealLine : ℝ → ℂ := fun x : ℝ => (x : ℂ)
  have hinner :
      HasDerivWithinAt ofRealLine (1 : ℂ) s t := by
    exact Complex.ofRealCLM.hasDerivAt.hasDerivWithinAt
  have hmaps :
      Set.MapsTo ofRealLine s
        (scalarFourierLaplacePlemelj_lowerHalfDisk T) := by
    intro x hx
    exact
      scalarFourierLaplacePlemelj_realSegment_mapsTo_lowerHalfDisk
        T _hT hx.2
  have houter :
      HasFDerivWithinAt G
        ((F (t : ℂ)) • (1 : ℂ →L[ℝ] ℂ))
        (scalarFourierLaplacePlemelj_lowerHalfDisk T)
        (ofRealLine t) := by
    exact _hderiv.complexToReal_fderiv
  have hcomp :
      HasDerivWithinAt
        (G ∘ ofRealLine)
        (((F (t : ℂ)) • (1 : ℂ →L[ℝ] ℂ)) (1 : ℂ))
        s
        t := by
    exact houter.comp_hasDerivWithinAt t hinner hmaps
  have hvalue :
      (((F (t : ℂ)) • (1 : ℂ →L[ℝ] ℂ)) (1 : ℂ)) =
        F (t : ℂ) := by
    calc
      (((F (t : ℂ)) • (1 : ℂ →L[ℝ] ℂ)) (1 : ℂ)) =
          (F (t : ℂ)) * ((1 : ℂ →L[ℝ] ℂ) (1 : ℂ)) := by
        rfl
      _ = (F (t : ℂ)) * (1 : ℂ) := by
        rfl
      _ = F (t : ℂ) := by
        exact mul_one (F (t : ℂ))
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        HasDerivWithinAt
          (G ∘ ofRealLine)
          z
          s
          t)
      hvalue
      hcomp

/-- Transport a complex lower-half-disk primitive derivative at a real interior
point to the right real derivative along the diameter. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_hasRightDerivWithinAt_point_of_complexPrimitive
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T)
    (t : ℝ) (_ht : t ∈ Set.Ioo (-T) T)
    (_ht_lower :
      (t : ℂ) ∈ scalarFourierLaplacePlemelj_lowerHalfDisk T)
    (_hderiv :
      HasDerivWithinAt G (F (t : ℂ))
        (scalarFourierLaplacePlemelj_lowerHalfDisk T) (t : ℂ)) :
    HasDerivWithinAt
      (fun x : ℝ => G (x : ℂ))
      (F (t : ℂ))
      (Set.Ioi t)
      t := by
  exact
    scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_rightLocalDerivative_to_rightRay
      F G T t _ht
      (scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_hasRightLocalDerivWithinAt_of_complexPrimitive
        F G T _hT _hprimitive t _ht _ht_lower _hderiv)

/-- Pointwise right-derivative transport from lower half-disk primitive data to
the real diameter. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_hasRightDerivWithinAt_point
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T)
    (t : ℝ) (_ht : t ∈ Set.Ioo (-T) T) :
    HasDerivWithinAt
      (fun x : ℝ => G (x : ℂ))
      (F (t : ℂ))
      (Set.Ioi t)
      t := by
  have ht_closed : t ∈ Set.Icc (-T) T :=
    Set.mem_Icc_of_Ioo _ht
  have ht_lower :
      (t : ℂ) ∈ scalarFourierLaplacePlemelj_lowerHalfDisk T :=
    scalarFourierLaplacePlemelj_realSegment_mapsTo_lowerHalfDisk
      T _hT ht_closed
  exact
    scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_hasRightDerivWithinAt_point_of_complexPrimitive
      F G T _hT _hprimitive t _ht ht_lower (_hprimitive.2 (t : ℂ) ht_lower)

/-- Restricting lower half-disk primitive data to the real diameter gives the
right-derivative on the open interval needed by the fundamental theorem of
calculus. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_hasRightDerivWithinAt
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T) :
    ∀ t ∈ Set.Ioo (-T) T,
      HasDerivWithinAt
        (fun x : ℝ => G (x : ℂ))
        (F (t : ℂ))
        (Set.Ioi t)
        t := by
  intro t ht
  exact
    scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_hasRightDerivWithinAt_point
      F G T _hT _hprimitive t ht

/-- Primitive data makes the primitive function continuous on the lower
half-disk. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_primitiveFunction_continuousOn
    (F G : ℂ → ℂ) (T : ℝ)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T) :
    ContinuousOn G (scalarFourierLaplacePlemelj_lowerHalfDisk T) := by
  intro z hz
  exact (_hprimitive.2 z hz).continuousWithinAt

/-- Primitive data on the lower half-disk makes the real-diameter primitive
continuous on the closed diameter. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_realSegmentPrimitive_continuousOn
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T) :
    ContinuousOn (fun x : ℝ => G (x : ℂ)) (Set.Icc (-T) T) := by
  exact
    (scalarFourierLaplacePlemelj_lowerHalfDisk_primitiveFunction_continuousOn
      F G T _hprimitive).comp
      Complex.continuous_ofReal.continuousOn
      (scalarFourierLaplacePlemelj_realSegment_mapsTo_lowerHalfDisk T _hT)

/-- The real-diameter integrand is continuous on the closed diameter. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_realSegmentIntegrand_continuousOn
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T) :
    ContinuousOn (fun x : ℝ => F (x : ℂ)) (Set.Icc (-T) T) := by
  exact
    _hprimitive.1.comp
      Complex.continuous_ofReal.continuousOn
      (scalarFourierLaplacePlemelj_realSegment_mapsTo_lowerHalfDisk T _hT)

/-- The real-diameter integrand is interval-integrable on the diameter. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_intervalIntegrable
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T) :
    IntervalIntegrable (fun x : ℝ => F (x : ℂ)) MeasureTheory.volume (-T) T := by
  have hle : -T ≤ T := by
    exact neg_le_self _hT
  exact
    ContinuousOn.intervalIntegrable_of_Icc hle
      (scalarFourierLaplacePlemelj_lowerHalfDisk_realSegmentIntegrand_continuousOn
        F G T _hT _hprimitive)

/-- The interval integral over the real diameter evaluates to the primitive
endpoint difference. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_intervalIntegral_eq_primitiveEndpointSub
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T) :
    (∫ t in (-T)..T, F (t : ℂ)) =
      G (T : ℂ) - G ((-T : ℝ) : ℂ) := by
  have hle : -T ≤ T := by
    exact neg_le_self _hT
  exact
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      hle
      (scalarFourierLaplacePlemelj_lowerHalfDisk_realSegmentPrimitive_continuousOn
        F G T _hT _hprimitive)
      (scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_hasRightDerivWithinAt
        F G T _hT _hprimitive)
      (scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_intervalIntegrable
        F G T _hT _hprimitive)

/-- The real diameter part of the lower half-disk boundary integral is the
primitive endpoint difference. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_realSegmentIntegral_eq_primitiveEndpointSub
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T) :
    (∫ t in Set.Icc (-T) T, F (t : ℂ)) =
      G (T : ℂ) - G ((-T : ℝ) : ℂ) := by
  exact
    Eq.trans
      (scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_setIntegral_eq_intervalIntegral
        F T _hT)
      (scalarFourierLaplacePlemelj_lowerHalfDisk_realSegment_intervalIntegral_eq_primitiveEndpointSub
        F G T _hT _hprimitive)

/-- The lower semicircle parametrization. -/
noncomputable def scalarFourierLaplacePlemelj_lowerArcParam
    (T : ℝ) (θ : ℝ) : ℂ :=
  (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))

/-- The derivative of the lower semicircle parametrization. -/
theorem scalarFourierLaplacePlemelj_lowerArcParam_hasDerivAt
    (T θ : ℝ) :
    HasDerivAt
      (scalarFourierLaplacePlemelj_lowerArcParam T)
      (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
      θ := by
  unfold scalarFourierLaplacePlemelj_lowerArcParam
  have hraw :
      HasDerivAt
        (fun u : ℝ => (T : ℂ) * Complex.exp (Complex.I * (u : ℂ)))
        ((T : ℂ) *
          (Complex.exp (Complex.I * (θ : ℂ)) * Complex.I))
        θ := by
    exact
      (((Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul Complex.I).cexp).const_mul
        (T : ℂ)
  have hvalue :
      (T : ℂ) * (Complex.exp (Complex.I * (θ : ℂ)) * Complex.I) =
        Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
    exact
      Eq.trans
        (congrArg
          (fun w : ℂ => (T : ℂ) * w)
          (mul_comm (Complex.exp (Complex.I * (θ : ℂ))) Complex.I))
        (Eq.trans
          (mul_assoc (T : ℂ) Complex.I
            (Complex.exp (Complex.I * (θ : ℂ))))
          (congrArg
            (fun w : ℂ => w * Complex.exp (Complex.I * (θ : ℂ)))
            (mul_comm (T : ℂ) Complex.I)))
  exact
    Eq.subst
      (motive := fun v : ℂ =>
        HasDerivAt
          (fun u : ℝ => (T : ℂ) * Complex.exp (Complex.I * (u : ℂ)))
          v
          θ)
      hvalue
      hraw

/-- The lower arc point has radius bounded by the contour radius. -/
theorem scalarFourierLaplacePlemelj_lowerArcParam_norm_le_radius
    (T : ℝ) (_hT : 0 ≤ T) (θ : ℝ) :
    ‖scalarFourierLaplacePlemelj_lowerArcParam T θ‖ ≤ T := by
  unfold scalarFourierLaplacePlemelj_lowerArcParam
  have hexp_arg :
      Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I :=
    mul_comm Complex.I (θ : ℂ)
  have hexp_norm :
      ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
    exact
      (congrArg
        (fun z : ℂ => ‖Complex.exp z‖)
        hexp_arg).trans
        (Complex.norm_exp_ofReal_mul_I θ)
  have hTnorm :
      ‖(T : ℂ)‖ = T := by
    exact (RCLike.norm_ofReal (K := ℂ) T).trans
      (abs_of_nonneg _hT)
  have hnorm :
      ‖(T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = T := by
    calc
      ‖(T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ =
          ‖(T : ℂ)‖ * ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
        exact norm_mul (T : ℂ)
          (Complex.exp (Complex.I * (θ : ℂ)))
      _ = T * ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
        exact congrArg
          (fun r : ℝ => r * ‖Complex.exp (Complex.I * (θ : ℂ))‖)
          hTnorm
      _ = T * 1 := by
        exact congrArg
          (fun r : ℝ => T * r)
          hexp_norm
      _ = T := by
        exact mul_one T
  exact le_of_eq hnorm

/-- The sine factor on the lower returning angular interval is nonpositive. -/
theorem scalarFourierLaplacePlemelj_lowerArc_sin_nonpos
    (θ : ℝ) (_hθ : θ ∈ Set.uIcc (0 : ℝ) (-Real.pi)) :
    Real.sin θ ≤ 0 := by
  have hneg_pi_le : -Real.pi ≤ θ :=
    (mem_uIcc.mp _hθ).1
  have hle_zero : θ ≤ (0 : ℝ) :=
    (mem_uIcc.mp _hθ).2
  exact Real.sin_nonpos_of_nonnpos_of_neg_pi_le hle_zero hneg_pi_le

/-- The lower arc point has nonpositive imaginary coordinate. -/
theorem scalarFourierLaplacePlemelj_lowerArcParam_im_nonpos
    (T : ℝ) (_hT : 0 ≤ T) (θ : ℝ)
    (_hθ : θ ∈ Set.uIcc (0 : ℝ) (-Real.pi)) :
    (scalarFourierLaplacePlemelj_lowerArcParam T θ).im ≤ 0 := by
  unfold scalarFourierLaplacePlemelj_lowerArcParam
  exact
    Eq.subst
      (motive := fun r : ℝ => r ≤ 0)
      (scalarFourierLaplacePlemelj_semicirclePoint_im T θ)
      (mul_nonpos_of_nonneg_of_nonpos
        _hT
        (scalarFourierLaplacePlemelj_lowerArc_sin_nonpos θ _hθ))

/-- The lower semicircle parametrization maps its angular interval into the
lower half-disk. -/
theorem scalarFourierLaplacePlemelj_lowerArcParam_mapsTo_lowerHalfDisk
    (T : ℝ) (_hT : 0 ≤ T) :
    Set.MapsTo
      (scalarFourierLaplacePlemelj_lowerArcParam T)
      (Set.uIcc (0 : ℝ) (-Real.pi))
      (scalarFourierLaplacePlemelj_lowerHalfDisk T) := by
  intro θ hθ
  exact
    And.intro
      (scalarFourierLaplacePlemelj_lowerArcParam_norm_le_radius T _hT θ)
      (scalarFourierLaplacePlemelj_lowerArcParam_im_nonpos T _hT θ hθ)

/-- Along the lower arc, the primitive is continuous on the angular interval. -/
theorem scalarFourierLaplacePlemelj_lowerArcPrimitive_continuousOn
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T) :
    ContinuousOn
      (fun θ : ℝ => G (scalarFourierLaplacePlemelj_lowerArcParam T θ))
      (Set.uIcc (0 : ℝ) (-Real.pi)) := by
  have hparam_continuous : Continuous (scalarFourierLaplacePlemelj_lowerArcParam T) := by
    exact fun θ : ℝ =>
      (scalarFourierLaplacePlemelj_lowerArcParam_hasDerivAt T θ).continuousAt
  exact
    (scalarFourierLaplacePlemelj_lowerHalfDisk_primitiveFunction_continuousOn
      F G T _hprimitive).comp
      hparam_continuous.continuousOn
      (scalarFourierLaplacePlemelj_lowerArcParam_mapsTo_lowerHalfDisk T _hT)

/-- On the open lower arc, the primitive has the displayed one-sided
parametrized derivative. -/
theorem scalarFourierLaplacePlemelj_lowerArcPrimitive_hasRightDerivWithinAt
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T) :
    ∀ θ ∈ Set.Ioo (-Real.pi) (0 : ℝ),
      HasDerivWithinAt
        (fun u : ℝ => G (scalarFourierLaplacePlemelj_lowerArcParam T u))
        (F (scalarFourierLaplacePlemelj_lowerArcParam T θ) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (Set.Ioi θ)
        θ := by
  intro θ hθ
  let s : Set ℝ := Set.Ioi θ ∩ Set.Ioo (-Real.pi) (0 : ℝ)
  have hθ_uIcc : θ ∈ Set.uIcc (0 : ℝ) (-Real.pi) :=
    mem_uIcc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hθ_lower :
      scalarFourierLaplacePlemelj_lowerArcParam T θ ∈
        scalarFourierLaplacePlemelj_lowerHalfDisk T :=
    scalarFourierLaplacePlemelj_lowerArcParam_mapsTo_lowerHalfDisk
      T _hT hθ_uIcc
  have hinner :
      HasDerivWithinAt
        (scalarFourierLaplacePlemelj_lowerArcParam T)
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        s
        θ := by
    exact
      (scalarFourierLaplacePlemelj_lowerArcParam_hasDerivAt T θ).hasDerivWithinAt
  have hmaps :
      Set.MapsTo
        (scalarFourierLaplacePlemelj_lowerArcParam T)
        s
        (scalarFourierLaplacePlemelj_lowerHalfDisk T) := by
    intro u hu
    have hu_uIcc : u ∈ Set.uIcc (0 : ℝ) (-Real.pi) :=
      mem_uIcc.mpr ⟨le_of_lt hu.2.1, le_of_lt hu.2.2⟩
    exact
      scalarFourierLaplacePlemelj_lowerArcParam_mapsTo_lowerHalfDisk
        T _hT hu_uIcc
  have houter :
      HasFDerivWithinAt G
        ((F (scalarFourierLaplacePlemelj_lowerArcParam T θ)) •
          (1 : ℂ →L[ℝ] ℂ))
        (scalarFourierLaplacePlemelj_lowerHalfDisk T)
        (scalarFourierLaplacePlemelj_lowerArcParam T θ) := by
    exact (_hprimitive.2
      (scalarFourierLaplacePlemelj_lowerArcParam T θ)
      hθ_lower).complexToReal_fderiv
  have hcomp :
      HasDerivWithinAt
        (G ∘ scalarFourierLaplacePlemelj_lowerArcParam T)
        (((F (scalarFourierLaplacePlemelj_lowerArcParam T θ)) •
          (1 : ℂ →L[ℝ] ℂ))
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        s
        θ := by
    exact houter.comp_hasDerivWithinAt θ hinner hmaps
  have hvalue :
      (((F (scalarFourierLaplacePlemelj_lowerArcParam T θ)) •
          (1 : ℂ →L[ℝ] ℂ))
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        F (scalarFourierLaplacePlemelj_lowerArcParam T θ) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
    calc
      (((F (scalarFourierLaplacePlemelj_lowerArcParam T θ)) •
          (1 : ℂ →L[ℝ] ℂ))
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
          F (scalarFourierLaplacePlemelj_lowerArcParam T θ) *
            ((1 : ℂ →L[ℝ] ℂ)
              (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
        rfl
      _ =
          F (scalarFourierLaplacePlemelj_lowerArcParam T θ) *
            (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
        rfl
  have hlocal :
      HasDerivWithinAt
        (fun u : ℝ => G (scalarFourierLaplacePlemelj_lowerArcParam T u))
        (F (scalarFourierLaplacePlemelj_lowerArcParam T θ) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        s
        θ := by
    exact
      Eq.subst
        (motive := fun v : ℂ =>
          HasDerivWithinAt
            (G ∘ scalarFourierLaplacePlemelj_lowerArcParam T)
            v
            s
            θ)
        hvalue
        hcomp
  have hIoo_mem :
      Set.Ioo (-Real.pi) (0 : ℝ) ∈ 𝓝[Set.Ioi θ] θ :=
    Ioo_mem_nhdsWithin_Ioi ⟨le_of_lt hθ.1, hθ.2⟩
  exact
    hlocal.mono_of_mem_nhdsWithin
      (inter_mem self_mem_nhdsWithin hIoo_mem)

/-- The lower arc integrand is interval-integrable over the returning arc. -/
theorem scalarFourierLaplacePlemelj_lowerArc_intervalIntegrable
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T) :
    IntervalIntegrable
      (fun θ : ℝ =>
        F (scalarFourierLaplacePlemelj_lowerArcParam T θ) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      MeasureTheory.volume
      (0 : ℝ)
      (-Real.pi) := by
  have hparam_continuous : Continuous (scalarFourierLaplacePlemelj_lowerArcParam T) := by
    exact fun θ : ℝ =>
      (scalarFourierLaplacePlemelj_lowerArcParam_hasDerivAt T θ).continuousAt
  have hintegrand_continuous :
      ContinuousOn
        (fun θ : ℝ =>
          F (scalarFourierLaplacePlemelj_lowerArcParam T θ) *
            (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (Set.uIcc (0 : ℝ) (-Real.pi)) := by
    have hF_continuous :
        ContinuousOn
          (fun θ : ℝ => F (scalarFourierLaplacePlemelj_lowerArcParam T θ))
          (Set.uIcc (0 : ℝ) (-Real.pi)) := by
      exact
        _hprimitive.1.comp
          hparam_continuous.continuousOn
          (scalarFourierLaplacePlemelj_lowerArcParam_mapsTo_lowerHalfDisk T _hT)
    have hexp_continuous :
        Continuous
          (fun θ : ℝ =>
            Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
      exact
        (continuous_const.mul continuous_const).mul
          (Complex.continuous_exp.comp
            (continuous_const.mul Complex.continuous_ofReal))
    exact hF_continuous.mul hexp_continuous.continuousOn
  exact ContinuousOn.intervalIntegrable hintegrand_continuous

/-- The lower arc parametrization starts at the right endpoint of the
diameter. -/
theorem scalarFourierLaplacePlemelj_lowerArcParam_zero
    (T : ℝ) :
    scalarFourierLaplacePlemelj_lowerArcParam T 0 = (T : ℂ) := by
  unfold scalarFourierLaplacePlemelj_lowerArcParam
  exact
    Eq.trans
      (congrArg
        (fun w : ℂ => (T : ℂ) * Complex.exp w)
        (mul_zero Complex.I))
      (Eq.trans
        (congrArg (fun w : ℂ => (T : ℂ) * w) Complex.exp_zero)
        (mul_one (T : ℂ)))

/-- The lower arc parametrization ends at the left endpoint of the diameter. -/
theorem scalarFourierLaplacePlemelj_lowerArcParam_neg_pi
    (T : ℝ) :
    scalarFourierLaplacePlemelj_lowerArcParam T (-Real.pi) =
      ((-T : ℝ) : ℂ) := by
  unfold scalarFourierLaplacePlemelj_lowerArcParam
  have harg :
      Complex.I * (((-Real.pi : ℝ) : ℂ)) =
        -((Real.pi : ℂ) * Complex.I) := by
    exact
      Eq.trans
        (mul_comm Complex.I (((-Real.pi : ℝ) : ℂ)))
        (Eq.trans
          (congrArg (fun w : ℂ => w * Complex.I)
            (Complex.ofReal_neg Real.pi))
          (neg_mul_eq_neg_mul (Real.pi : ℂ) Complex.I).symm)
  have hexp :
      Complex.exp (Complex.I * (((-Real.pi : ℝ) : ℂ))) = (-1 : ℂ) := by
    exact
      Eq.trans
        (congrArg Complex.exp harg)
        (Eq.trans
          (Complex.exp_neg ((Real.pi : ℂ) * Complex.I))
          (Eq.trans
            (congrArg Inv.inv Complex.exp_pi_mul_I)
            (inv_neg_one : (-1 : ℂ)⁻¹ = -1)))
  exact
    Eq.trans
      (congrArg (fun w : ℂ => (T : ℂ) * w) hexp)
      (Eq.trans
        (mul_neg_one (T : ℂ))
        (Complex.ofReal_neg T).symm)

/-- The open angular interval for the lower returning arc is `(-π,0)`. -/
theorem scalarFourierLaplacePlemelj_lowerArc_openInterval_normalize :
    Set.Ioo (min (0 : ℝ) (-Real.pi)) (max (0 : ℝ) (-Real.pi)) =
      Set.Ioo (-Real.pi) (0 : ℝ) := by
  have hneg : -Real.pi ≤ (0 : ℝ) :=
    neg_nonpos.mpr Real.pi_pos.le
  have hmin : min (0 : ℝ) (-Real.pi) = -Real.pi :=
    min_eq_right hneg
  have hmax : max (0 : ℝ) (-Real.pi) = (0 : ℝ) :=
    max_eq_left hneg
  exact congrArg₂ Set.Ioo hmin hmax

/-- The path-FTC derivative hypothesis in the exact interval orientation. -/
theorem scalarFourierLaplacePlemelj_lowerArcPrimitive_hasRightDerivWithinAt_minMax
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T) :
    ∀ θ ∈ Set.Ioo (min (0 : ℝ) (-Real.pi)) (max (0 : ℝ) (-Real.pi)),
      HasDerivWithinAt
        (fun u : ℝ => G (scalarFourierLaplacePlemelj_lowerArcParam T u))
        (F (scalarFourierLaplacePlemelj_lowerArcParam T θ) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (Set.Ioi θ)
        θ := by
  intro θ hθ
  exact
    scalarFourierLaplacePlemelj_lowerArcPrimitive_hasRightDerivWithinAt
      F G T _hT _hprimitive
      θ
      (Eq.subst
        (fun S : Set ℝ => θ ∈ S)
        scalarFourierLaplacePlemelj_lowerArc_openInterval_normalize
        hθ)

/-- The path-FTC form of the lower arc endpoint calculation. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_lowerArcIntegral_eq_primitiveEndpointSub_of_pathFTC
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T) :
    (∫ θ in (0 : ℝ)..(-Real.pi),
      let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      F z *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      G ((-T : ℝ) : ℂ) - G (T : ℂ) := by
  have hftc :
      (∫ θ in (0 : ℝ)..(-Real.pi),
        F (scalarFourierLaplacePlemelj_lowerArcParam T θ) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        G (scalarFourierLaplacePlemelj_lowerArcParam T (-Real.pi)) -
          G (scalarFourierLaplacePlemelj_lowerArcParam T 0) :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right
      (scalarFourierLaplacePlemelj_lowerArcPrimitive_continuousOn
        F G T _hT _hprimitive)
      (scalarFourierLaplacePlemelj_lowerArcPrimitive_hasRightDerivWithinAt_minMax
        F G T _hT _hprimitive)
      (scalarFourierLaplacePlemelj_lowerArc_intervalIntegrable
        F G T _hT _hprimitive)
  have hleft :
      (∫ θ in (0 : ℝ)..(-Real.pi),
        let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
        F z *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      (∫ θ in (0 : ℝ)..(-Real.pi),
        F (scalarFourierLaplacePlemelj_lowerArcParam T θ) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
    rfl
  have hend :
      G (scalarFourierLaplacePlemelj_lowerArcParam T (-Real.pi)) -
          G (scalarFourierLaplacePlemelj_lowerArcParam T 0) =
        G ((-T : ℝ) : ℂ) - G (T : ℂ) := by
    exact
      congrArg₂ HSub.hSub
        (congrArg G (scalarFourierLaplacePlemelj_lowerArcParam_neg_pi T))
        (congrArg G (scalarFourierLaplacePlemelj_lowerArcParam_zero T))
  exact Eq.trans hleft (Eq.trans hftc hend)

/-- The lower semicircle part of the boundary integral is the returning
primitive endpoint difference. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_lowerArcIntegral_eq_primitiveEndpointSub
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T) :
    (∫ θ in (0 : ℝ)..(-Real.pi),
      let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      F z *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      G ((-T : ℝ) : ℂ) - G (T : ℂ) := by
  exact
    scalarFourierLaplacePlemelj_lowerHalfDisk_lowerArcIntegral_eq_primitiveEndpointSub_of_pathFTC
      F G T _hT _hprimitive

/-- Adding the two primitive endpoint differences around the lower half-disk
boundary gives zero. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDisk_primitiveEndpointSub_add_return_eq_zero
    (G : ℂ → ℂ) (T : ℝ) :
    (G (T : ℂ) - G ((-T : ℝ) : ℂ)) +
        (G ((-T : ℝ) : ℂ) - G (T : ℂ)) =
      0 := by
  calc
    (G (T : ℂ) - G ((-T : ℝ) : ℂ)) +
        (G ((-T : ℝ) : ℂ) - G (T : ℂ)) =
      (G (T : ℂ) + -G ((-T : ℝ) : ℂ)) +
        (G ((-T : ℝ) : ℂ) + -G (T : ℂ)) := by
        exact congrArg₂ HAdd.hAdd
          (sub_eq_add_neg (G (T : ℂ)) (G ((-T : ℝ) : ℂ)))
          (sub_eq_add_neg (G ((-T : ℝ) : ℂ)) (G (T : ℂ)))
    _ =
      G (T : ℂ) +
        (-G ((-T : ℝ) : ℂ) +
          (G ((-T : ℝ) : ℂ) + -G (T : ℂ))) := by
        exact add_assoc
          (G (T : ℂ))
          (-G ((-T : ℝ) : ℂ))
          (G ((-T : ℝ) : ℂ) + -G (T : ℂ))
    _ =
      G (T : ℂ) +
        ((-G ((-T : ℝ) : ℂ) + G ((-T : ℝ) : ℂ)) +
          -G (T : ℂ)) := by
        exact congrArg
          (fun z : ℂ => G (T : ℂ) + z)
          (add_assoc
            (-G ((-T : ℝ) : ℂ))
            (G ((-T : ℝ) : ℂ))
            (-G (T : ℂ))).symm
    _ =
      G (T : ℂ) + (0 + -G (T : ℂ)) := by
        exact congrArg
          (fun z : ℂ => G (T : ℂ) + (z + -G (T : ℂ)))
          (neg_add_cancel (G ((-T : ℝ) : ℂ)))
    _ = G (T : ℂ) + -G (T : ℂ) := by
        exact congrArg
          (fun z : ℂ => G (T : ℂ) + z)
          (zero_add (-G (T : ℂ)))
    _ = 0 := by
        exact add_neg_cancel (G (T : ℂ))

/-- The boundary integral of a derivative around the lower half-disk contour is
zero. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDiskBoundaryIntegral_eq_zero_of_hasPrimitive
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      ∃ G : ℂ → ℂ,
        scalarFourierLaplacePlemelj_hasPrimitiveOnLowerHalfDisk F G T) :
    scalarFourierLaplacePlemelj_lowerHalfDiskBoundaryIntegral F T = 0 := by
  match _hprimitive with
  | ⟨G, hG⟩ =>
    unfold scalarFourierLaplacePlemelj_lowerHalfDiskBoundaryIntegral
    exact
      Eq.trans
        (congrArg₂ HAdd.hAdd
          (scalarFourierLaplacePlemelj_lowerHalfDisk_realSegmentIntegral_eq_primitiveEndpointSub
            F G T _hT hG)
          (scalarFourierLaplacePlemelj_lowerHalfDisk_lowerArcIntegral_eq_primitiveEndpointSub
            F G T _hT hG))
        (scalarFourierLaplacePlemelj_lowerHalfDisk_primitiveEndpointSub_add_return_eq_zero
          G T)

/-- Cauchy-Goursat for a generic analytic function on the lower half-disk
boundary. -/
theorem scalarFourierLaplacePlemelj_lowerHalfDiskBoundaryIntegral_eq_zero_of_analyticAt
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hanalytic :
      ∀ z ∈ scalarFourierLaplacePlemelj_lowerHalfDisk T,
        AnalyticAt ℂ F z) :
    scalarFourierLaplacePlemelj_lowerHalfDiskBoundaryIntegral F T = 0 := by
  exact
    scalarFourierLaplacePlemelj_lowerHalfDiskBoundaryIntegral_eq_zero_of_hasPrimitive
      F T _hT
      (scalarFourierLaplacePlemelj_lowerHalfDisk_hasPrimitive_of_analyticAt
        F T _hT _hanalytic)

/-- Cauchy-Goursat for the negative-time scalar kernel on the lower half-disk
boundary. -/
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
