import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.FixedLineTails.Owner
import Mathlib.Analysis.Complex.RemovableSingularity

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

theorem scalarFourierLaplacePlemelj_positive_residue_value
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    (-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) =
      (-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  exact rfl

/-- Upper semicircle correction term for the positive-time scalar
Fourier-Laplace contour.  The real segment runs from `-T` to `T`, and this arc
returns from `T` to `-T` through the upper half-plane. -/
noncomputable def scalarFourierLaplacePlemelj_positiveUpperArc
    (a x T : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
    (-1 / ((a : ℂ) + z * Complex.I)) *
      Complex.exp (Complex.I * z * (x : ℂ)) *
      (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Integrand of the positive upper semicircle correction. -/
noncomputable def scalarFourierLaplacePlemelj_positiveUpperArcIntegrand
    (a x T θ : ℝ) : ℂ :=
  let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  (-1 / ((a : ℂ) + z * Complex.I)) *
    Complex.exp (Complex.I * z * (x : ℂ)) *
    (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- The positive upper arc is the interval integral of its named integrand. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_eq_integral_integrand
    (a x T : ℝ) :
    scalarFourierLaplacePlemelj_positiveUpperArc a x T =
      ∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_positiveUpperArcIntegrand a x T θ := by
  rfl

/-- Real Jordan density for the positive upper semicircle estimate. -/
noncomputable def scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity
    (a x T θ : ℝ) : ℝ :=
  (T / (T - a)) * Real.exp (-(T * x * Real.sin θ))

/-- Closed upper-half-plane scalar contour integral for the positive-time
Fourier-Laplace denominator. -/
noncomputable def scalarFourierLaplacePlemelj_positiveClosedContour
    (a x T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-T) T,
    (-1 / ((a : ℂ) + t * Complex.I)) *
      Complex.exp
        (Complex.I * (t : ℂ) * (x : ℂ))) +
    scalarFourierLaplacePlemelj_positiveUpperArc a x T

/-- The positive closed contour unfolds to its real segment plus upper arc. -/
theorem scalarFourierLaplacePlemelj_positiveClosedContour_eq_window_add_upperArc
    (a x T : ℝ) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) +
          scalarFourierLaplacePlemelj_positiveUpperArc a x T := by
  rfl

/-- The pole of the scalar Fourier-Laplace denominator in the upper half-plane. -/
noncomputable def scalarFourierLaplacePlemelj_upperPole
    (a : ℝ) : ℂ :=
  (a : ℂ) * Complex.I

/-- The scalar upper pole lies on the positive imaginary axis. -/
theorem scalarFourierLaplacePlemelj_upperPole_eq
    (a : ℝ) :
    scalarFourierLaplacePlemelj_upperPole a = (a : ℂ) * Complex.I := by
  rfl

/-- The upper pole is inside the positive semicircle once the radius exceeds `a`. -/
theorem scalarFourierLaplacePlemelj_upperPole_mem_upperSemicircleInterior_of_radius
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : a < T) :
    ‖scalarFourierLaplacePlemelj_upperPole a‖ < T := by
  have hpole_norm :
      ‖scalarFourierLaplacePlemelj_upperPole a‖ = a := by
    calc
      ‖scalarFourierLaplacePlemelj_upperPole a‖ =
          ‖(a : ℂ) * Complex.I‖ := by
        exact congrArg norm
          (scalarFourierLaplacePlemelj_upperPole_eq a)
      _ = ‖(a : ℂ)‖ * ‖Complex.I‖ := by
        exact norm_mul (a : ℂ) Complex.I
      _ = |a| * ‖Complex.I‖ := by
        exact congrArg
          (fun r : ℝ => r * ‖Complex.I‖)
          (RCLike.norm_ofReal (K := ℂ) a)
      _ = a * ‖Complex.I‖ := by
        exact congrArg
          (fun r : ℝ => r * ‖Complex.I‖)
          (abs_of_pos ha)
      _ = a * 1 := by
        exact congrArg
          (fun r : ℝ => a * r)
          Complex.norm_I
      _ = a := by
        exact mul_one a
  exact hpole_norm.trans_lt hT

/-- Residue of the positive-time normalized scalar kernel at the upper pole. -/
noncomputable def scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution
    (a x : ℝ) : ℂ :=
  (-2 * (Real.pi : ℂ)) *
    Complex.exp (-(a : ℂ) * (x : ℂ))

/-- Positive-time scalar Fourier-Laplace meromorphic kernel. -/
noncomputable def scalarFourierLaplacePlemelj_positiveKernel
    (a x : ℝ) (z : ℂ) : ℂ :=
  (-1 / ((a : ℂ) + z * Complex.I)) *
    Complex.exp (Complex.I * z * (x : ℂ))

/-- Boundary integral of the positive-time scalar kernel over the finite upper
semicircle contour, written directly in terms of the named meromorphic kernel. -/
noncomputable def scalarFourierLaplacePlemelj_positiveKernelUpperSemicircleBoundaryIntegral
    (a x T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-T) T,
    scalarFourierLaplacePlemelj_positiveKernel a x (t : ℂ)) +
    ∫ θ in (0 : ℝ)..Real.pi,
      let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      scalarFourierLaplacePlemelj_positiveKernel a x z *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Generic boundary integral over the finite upper half-disk contour: diameter
from `-T` to `T`, then the upper semicircle returning from `T` to `-T`. -/
noncomputable def scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
    (F : ℂ → ℂ) (T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-T) T, F (t : ℂ)) +
    ∫ θ in (0 : ℝ)..Real.pi,
      let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      F z *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Closed upper half-disk used by the positive-time scalar contour. -/
def scalarFourierLaplacePlemelj_upperHalfDisk
    (T : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ ≤ T ∧ 0 ≤ Complex.im z}

/-- The real diameter segment lies in the closed upper half-disk. -/
theorem scalarFourierLaplacePlemelj_realDiameter_mapsTo_upperHalfDisk
    (T : ℝ) (t : ℝ) (_ht : t ∈ Set.Icc (-T) T) :
    (t : ℂ) ∈ scalarFourierLaplacePlemelj_upperHalfDisk T := by
  unfold scalarFourierLaplacePlemelj_upperHalfDisk
  have habs : |t| ≤ T := by
    exact abs_le.mpr _ht
  have hnorm : ‖(t : ℂ)‖ ≤ T := by
    exact
      Eq.subst
        (motive := fun r : ℝ => r ≤ T)
        (RCLike.norm_ofReal (K := ℂ) t).symm
        habs
  have him : 0 ≤ Complex.im (t : ℂ) := by
    exact
      Eq.subst
        (motive := fun r : ℝ => 0 ≤ r)
        (Complex.ofReal_im t).symm
        (le_refl (0 : ℝ))
  exact And.intro hnorm him

/-- Analytic numerator of the positive-time scalar Cauchy kernel after factoring
the simple upper-pole denominator. -/
noncomputable def scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator
    (x : ℝ) (z : ℂ) : ℂ :=
  Complex.I * Complex.exp (Complex.I * z * (x : ℂ))

/-- Point residue coefficient of the positive-time normalized scalar kernel at
the upper pole, before multiplication by `2πi`. -/
noncomputable def scalarFourierLaplacePlemelj_positiveUpperPoleResidueCoefficient
    (a x : ℝ) : ℂ :=
  Complex.I * Complex.exp (-(a : ℂ) * (x : ℂ))

/-- The positive kernel denominator factors through the upper-pole local
coordinate. -/
theorem scalarFourierLaplacePlemelj_positiveKernel_denominator_factor_upperPole
    (a : ℝ) (z : ℂ) :
    (a : ℂ) + z * Complex.I =
      Complex.I * (z - scalarFourierLaplacePlemelj_upperPole a) := by
  unfold scalarFourierLaplacePlemelj_upperPole
  calc
    (a : ℂ) + z * Complex.I =
        z * Complex.I + (a : ℂ) := by
      exact add_comm (a : ℂ) (z * Complex.I)
    _ = Complex.I * z + (a : ℂ) := by
      exact congrArg (fun w : ℂ => w + (a : ℂ)) (mul_comm z Complex.I)
    _ = Complex.I * z - ((a : ℂ) * (Complex.I * Complex.I)) := by
      have hi2 : (a : ℂ) * (Complex.I * Complex.I) = -(a : ℂ) := by
        calc
          (a : ℂ) * (Complex.I * Complex.I) =
              (a : ℂ) * (-1 : ℂ) := by
            exact congrArg (fun w : ℂ => (a : ℂ) * w) Complex.I_mul_I
          _ = -(a : ℂ) := by
            exact mul_neg_one (a : ℂ)
      exact Eq.subst
        (motive := fun w : ℂ => z * Complex.I + (a : ℂ) = Complex.I * z - w)
        hi2.symm
        (calc
          z * Complex.I + (a : ℂ) =
              Complex.I * z + (a : ℂ) := by
            exact congrArg (fun w : ℂ => w + (a : ℂ)) (mul_comm z Complex.I)
          _ = Complex.I * z - (-(a : ℂ)) := by
            exact (sub_neg_eq_add (Complex.I * z) (a : ℂ)).symm)
    _ = Complex.I * z - Complex.I * ((a : ℂ) * Complex.I) := by
      exact congrArg (fun w : ℂ => Complex.I * z - w)
        (mul_assoc Complex.I (a : ℂ) Complex.I |>.trans
          (congrArg (fun w : ℂ => w * Complex.I)
            (mul_comm Complex.I (a : ℂ))))
    _ = Complex.I * (z - (a : ℂ) * Complex.I) := by
      exact (mul_sub Complex.I z ((a : ℂ) * Complex.I)).symm

/-- Evaluating the exponential factor at the upper pole. -/
theorem scalarFourierLaplacePlemelj_positiveKernel_upperPole_exponential
    (a x : ℝ) :
    Complex.exp
      (Complex.I * scalarFourierLaplacePlemelj_upperPole a * (x : ℂ)) =
      Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  unfold scalarFourierLaplacePlemelj_upperPole
  exact congrArg Complex.exp
    (calc
      Complex.I * ((a : ℂ) * Complex.I) * (x : ℂ) =
          ((Complex.I * (a : ℂ)) * Complex.I) * (x : ℂ) := by
        exact congrArg (fun w : ℂ => w * (x : ℂ))
          (mul_assoc Complex.I (a : ℂ) Complex.I)
      _ = (((a : ℂ) * Complex.I) * Complex.I) * (x : ℂ) := by
        exact congrArg (fun w : ℂ => (w * Complex.I) * (x : ℂ))
          (mul_comm Complex.I (a : ℂ))
      _ = ((a : ℂ) * (Complex.I * Complex.I)) * (x : ℂ) := by
        exact congrArg (fun w : ℂ => w * (x : ℂ))
          (mul_assoc (a : ℂ) Complex.I Complex.I)
      _ = ((a : ℂ) * (-1 : ℂ)) * (x : ℂ) := by
        exact congrArg (fun w : ℂ => ((a : ℂ) * w) * (x : ℂ))
          Complex.I_mul_I
      _ = (-(a : ℂ)) * (x : ℂ) := by
        exact congrArg (fun w : ℂ => w * (x : ℂ))
          (mul_neg_one (a : ℂ)))

/-- Local residue coefficient of the positive kernel at the upper pole. -/
theorem scalarFourierLaplacePlemelj_positiveKernel_upperPole_residueCoefficient
    (a x : ℝ) :
    scalarFourierLaplacePlemelj_positiveUpperPoleResidueCoefficient a x =
      Complex.I *
        Complex.exp
          (Complex.I * scalarFourierLaplacePlemelj_upperPole a * (x : ℂ)) := by
  unfold scalarFourierLaplacePlemelj_positiveUpperPoleResidueCoefficient
  exact congrArg (fun E : ℂ => Complex.I * E)
    (scalarFourierLaplacePlemelj_positiveKernel_upperPole_exponential
      a x).symm

/-- Multiplying the positive upper-pole residue coefficient by `2πi` gives the
normalized residue contribution. -/
theorem scalarFourierLaplacePlemelj_two_pi_i_mul_positiveUpperPoleResidueCoefficient_eq_contribution
    (a x : ℝ) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
        scalarFourierLaplacePlemelj_positiveUpperPoleResidueCoefficient a x =
      scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution a x := by
  let E : ℂ := Complex.exp (-(a : ℂ) * (x : ℂ))
  unfold scalarFourierLaplacePlemelj_positiveUpperPoleResidueCoefficient
  unfold scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution
  change ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (Complex.I * E) =
    (-2 * (Real.pi : ℂ)) * E
  calc
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (Complex.I * E) =
        (((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * Complex.I) * E := by
      exact mul_assoc ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) Complex.I E
    _ = (((2 : ℂ) * (Real.pi : ℂ)) * (Complex.I * Complex.I)) * E := by
      exact congrArg (fun z : ℂ => z * E)
        (mul_assoc ((2 : ℂ) * (Real.pi : ℂ)) Complex.I Complex.I).symm
    _ = (((2 : ℂ) * (Real.pi : ℂ)) * (-1 : ℂ)) * E := by
      exact congrArg
        (fun z : ℂ => (((2 : ℂ) * (Real.pi : ℂ)) * z) * E)
        Complex.I_mul_I
    _ = (-((2 : ℂ) * (Real.pi : ℂ))) * E := by
      exact congrArg (fun z : ℂ => z * E)
        (mul_neg_one ((2 : ℂ) * (Real.pi : ℂ)))
    _ = ((-2 : ℂ) * (Real.pi : ℂ)) * E := by
      exact congrArg (fun z : ℂ => z * E)
        (neg_mul (2 : ℂ) (Real.pi : ℂ)).symm
    _ = (-2 * (Real.pi : ℂ)) * E := by
      rfl

/-- Evaluation of the positive-time normalized scalar residue at the upper pole. -/
theorem scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution_eq
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution a x =
      (-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  exact rfl

/-- The positive closed contour is the named kernel boundary integral. -/
theorem scalarFourierLaplacePlemelj_positiveClosedContour_eq_positiveKernelUpperSemicircleBoundaryIntegral
    (a x T : ℝ) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      scalarFourierLaplacePlemelj_positiveKernelUpperSemicircleBoundaryIntegral
        a x T := by
  rfl

/-- The positive upper semicircle boundary integral is the generic upper
half-disk boundary integral specialized to the positive scalar kernel. -/
theorem scalarFourierLaplacePlemelj_positiveKernelUpperSemicircleBoundaryIntegral_eq_upperHalfDiskBoundaryIntegral
    (a x T : ℝ) :
    scalarFourierLaplacePlemelj_positiveKernelUpperSemicircleBoundaryIntegral
        a x T =
      scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (scalarFourierLaplacePlemelj_positiveKernel a x) T := by
  rfl

/-- The positive upper-pole residue coefficient is the analytic numerator
evaluated at the upper pole. -/
theorem scalarFourierLaplacePlemelj_positiveUpperPoleResidueCoefficient_eq_analyticNumerator
    (a x : ℝ) :
    scalarFourierLaplacePlemelj_positiveUpperPoleResidueCoefficient a x =
      scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator
        x (scalarFourierLaplacePlemelj_upperPole a) := by
  unfold scalarFourierLaplacePlemelj_positiveKernelAnalyticNumerator
  exact
    scalarFourierLaplacePlemelj_positiveKernel_upperPole_residueCoefficient
      a x

/-- Imaginary coordinate of the scalar upper pole. -/
theorem scalarFourierLaplacePlemelj_upperPole_im
    (a : ℝ) :
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

/-- The scalar upper pole lies strictly in the upper half-plane for `0 < a`. -/
theorem scalarFourierLaplacePlemelj_upperPole_im_pos
    (a : ℝ) (ha : 0 < a) :
    0 < Complex.im (scalarFourierLaplacePlemelj_upperPole a) := by
  exact
    Eq.subst
      (motive := fun r : ℝ => 0 < r)
      (scalarFourierLaplacePlemelj_upperPole_im a).symm
      ha

/-- Residue contribution of a simple pole inside the upper half-disk.  This is
the local small-circle value produced by the indentation around `p`. -/
noncomputable def scalarFourierLaplacePlemelj_upperHalfDiskSimplePoleResidueContribution
    (F : ℂ → ℂ) (p : ℂ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * F p

/-- Regular part of the Cauchy kernel after subtracting its value at the pole.
This is the canonical removable quotient: away from the pole it is the ordinary
difference quotient, and at the pole it is the complex derivative. -/
noncomputable def scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart
    (F : ℂ → ℂ) (p : ℂ) : ℂ → ℂ :=
  dslope F p

/-- Away from the pole, the removable Cauchy regular part is the ordinary
difference quotient. -/
theorem scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart_eq_quotient_of_ne
    (F : ℂ → ℂ) (p z : ℂ) (hz : z ≠ p) :
    scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p z =
      (F z - F p) / (z - p) := by
  calc
    scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p z =
        dslope F p z := by
      rfl
    _ = slope F p z := by
      exact dslope_of_ne F hz
    _ = (F z - F p) / (z - p) := by
      exact slope_def_field F p z

/-- Away from the pole, the Cauchy kernel splits into the removable regular
part plus the scalar pole kernel. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_cauchyKernel_pointwise_decompose
    (F : ℂ → ℂ) (p z : ℂ) (hz : z ≠ p) :
    F z / (z - p) =
      scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p z +
        F p * (z - p)⁻¹ := by
  have hregular :
      scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p z =
        (F z - F p) / (z - p) :=
    scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart_eq_quotient_of_ne
      F p z hz
  calc
    F z / (z - p) =
        (F z) * (z - p)⁻¹ := by
      rfl
    _ = ((F z - F p) + F p) * (z - p)⁻¹ := by
      exact congrArg
        (fun w : ℂ => w * (z - p)⁻¹)
        (sub_add_cancel (F z) (F p)).symm
    _ = (F z - F p) * (z - p)⁻¹ + F p * (z - p)⁻¹ := by
      exact add_mul (F z - F p) (F p) (z - p)⁻¹
    _ = (F z - F p) / (z - p) + F p * (z - p)⁻¹ := by
      rfl
    _ =
        scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p z +
          F p * (z - p)⁻¹ := by
      exact congrArg
        (fun w : ℂ => w + F p * (z - p)⁻¹)
        hregular.symm

/-- A point in the open upper half-plane cannot lie on the real diameter of
the upper half-disk contour. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_ne_pole
    (p : ℂ) (_hp_upper : 0 < Complex.im p) (t : ℝ) :
    (t : ℂ) ≠ p := by
  intro ht
  have him_eq_zero : Complex.im p = 0 := by
    exact
      Eq.trans
        (congrArg Complex.im ht.symm)
        (Complex.ofReal_im t)
  have hzero_lt_zero : (0 : ℝ) < 0 := by
    exact
      Eq.subst
        (motive := fun r : ℝ => 0 < r)
        him_eq_zero
        _hp_upper
  exact (lt_irrefl (0 : ℝ)) hzero_lt_zero

/-- The upper semicircle parametrization has norm equal to the contour radius. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_arcPoint_norm_eq_radius
    (T : ℝ) (_hT : 0 < T) (θ : ℝ) :
    ‖(T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = T := by
  have harg :
      Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I :=
    mul_comm Complex.I (θ : ℂ)
  have hexp_norm :
      ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 :=
    (congrArg
      (fun z : ℂ => ‖Complex.exp z‖)
      harg).trans
      (Complex.norm_exp_ofReal_mul_I θ)
  have hTnorm :
      ‖(T : ℂ)‖ = T :=
    (RCLike.norm_ofReal (K := ℂ) T).trans
      (abs_of_pos _hT)
  calc
    ‖(T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ =
        ‖(T : ℂ)‖ * ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact norm_mul (T : ℂ) (Complex.exp (Complex.I * (θ : ℂ)))
    _ = T * ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖Complex.exp (Complex.I * (θ : ℂ))‖)
        hTnorm
    _ = T * 1 := by
      exact congrArg (fun r : ℝ => T * r) hexp_norm
    _ = T := by
      exact mul_one T

/-- A point strictly inside the radius-`T` disk cannot lie on the radius-`T`
upper semicircle. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_arcPoint_ne_pole
    (T : ℝ) (_hT : 0 < T) (p : ℂ) (_hp : ‖p‖ < T) (θ : ℝ) :
    (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ≠ p := by
  intro hp_eq
  have hpoint_norm :
      ‖(T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = T :=
    scalarFourierLaplacePlemelj_upperHalfDisk_arcPoint_norm_eq_radius
      T _hT θ
  have hp_norm_eq_T : ‖p‖ = T := by
    exact (congrArg norm hp_eq.symm).trans hpoint_norm
  have hT_le_normp : T ≤ ‖p‖ := by
    exact Eq.subst
      (motive := fun r : ℝ => T ≤ r)
      hp_norm_eq_T.symm
      (le_refl T)
  exact (not_lt_of_ge hT_le_normp) _hp

/-- Pointwise Cauchy-kernel decomposition on the real diameter of the upper
half-disk contour. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_cauchyKernel_decompose
    (F : ℂ → ℂ) (p : ℂ) (_hp_upper : 0 < Complex.im p) (t : ℝ) :
    F (t : ℂ) / ((t : ℂ) - p) =
      scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p (t : ℂ) +
        F p * (((t : ℂ) - p)⁻¹) := by
  exact
    scalarFourierLaplacePlemelj_upperHalfDisk_cauchyKernel_pointwise_decompose
      F p (t : ℂ)
      (scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_ne_pole
        p _hp_upper t)

/-- Pointwise Cauchy-kernel decomposition on the real diameter, expressed as
the exact integrand split used by the diameter integral. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_integrand_decompose
    (F : ℂ → ℂ) (p : ℂ) (_hp_upper : 0 < Complex.im p) (t : ℝ) :
    (fun z : ℂ => F z / (z - p)) (t : ℂ) =
      scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p (t : ℂ) +
        (fun z : ℂ => F p * (z - p)⁻¹) (t : ℂ) := by
  exact
    scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_cauchyKernel_decompose
      F p _hp_upper t

/-- Pointwise Cauchy-kernel decomposition on the upper semicircle of the upper
half-disk contour. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_arc_cauchyKernel_decompose
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ) (_hp : ‖p‖ < T)
    (θ : ℝ) :
    F ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
        (((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p) =
      scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
        F p *
          ((((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p)⁻¹) := by
  exact
    scalarFourierLaplacePlemelj_upperHalfDisk_cauchyKernel_pointwise_decompose
      F p ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
      (scalarFourierLaplacePlemelj_upperHalfDisk_arcPoint_ne_pole
        T _hT p _hp θ)

/-- Pointwise Cauchy-kernel decomposition on the upper semicircle after
multiplication by the circular velocity. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_arc_integrand_decompose
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ) (_hp : ‖p‖ < T)
    (θ : ℝ) :
    (F ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
        (((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p)) *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
        (F p *
          ((((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p)⁻¹)) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  exact
    congrArg
      (fun w : ℂ =>
        w * (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (scalarFourierLaplacePlemelj_upperHalfDisk_arc_cauchyKernel_decompose
        F T _hT p _hp θ)

/-- Primitive data for a function on the upper half-disk. -/
def scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk
    (F G : ℂ → ℂ) (T : ℝ) : Prop :=
  ContinuousOn F (scalarFourierLaplacePlemelj_upperHalfDisk T) ∧
    ∀ z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
      HasDerivWithinAt G (F z) (scalarFourierLaplacePlemelj_upperHalfDisk T) z

/-- The upper half-disk is the intersection of the closed radius disk and the
closed upper half-plane. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_eq_closedBall_inter_upperHalfPlane
    (T : ℝ) :
    scalarFourierLaplacePlemelj_upperHalfDisk T =
      Metric.closedBall (0 : ℂ) T ∩ {z : ℂ | 0 ≤ Complex.im z} := by
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

/-- The origin lies in every nonnegative upper half-disk. -/
theorem scalarFourierLaplacePlemelj_zero_mem_upperHalfDisk
    (T : ℝ) (_hT : 0 ≤ T) :
    (0 : ℂ) ∈ scalarFourierLaplacePlemelj_upperHalfDisk T := by
  exact
    And.intro
      (Eq.subst
        (motive := fun r : ℝ => r ≤ T)
        norm_zero
        _hT)
      (le_of_eq Complex.zero_im.symm)

/-- The upper half-disk is star-convex from the origin. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_starConvex
    (T : ℝ) (_hT : 0 ≤ T) :
    StarConvex ℝ (0 : ℂ) (scalarFourierLaplacePlemelj_upperHalfDisk T) := by
  have hconv_closedBall :
      Convex ℝ (Metric.closedBall (0 : ℂ) T) :=
    convex_closedBall (0 : ℂ) T
  have hconv_upper :
      Convex ℝ {z : ℂ | 0 ≤ Complex.im z} :=
    Complex.convex_halfSpace_im_ge 0
  have hconv :
      Convex ℝ (Metric.closedBall (0 : ℂ) T ∩ {z : ℂ | 0 ≤ Complex.im z}) :=
    hconv_closedBall.inter hconv_upper
  have hzero :
      (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) T ∩ {z : ℂ | 0 ≤ Complex.im z} := by
    exact
      Eq.subst
        (motive := fun S : Set ℂ => (0 : ℂ) ∈ S)
        (scalarFourierLaplacePlemelj_upperHalfDisk_eq_closedBall_inter_upperHalfPlane T)
        (scalarFourierLaplacePlemelj_zero_mem_upperHalfDisk T _hT)
  exact
    Eq.subst
      (motive := fun S : Set ℂ => StarConvex ℝ (0 : ℂ) S)
      (scalarFourierLaplacePlemelj_upperHalfDisk_eq_closedBall_inter_upperHalfPlane T).symm
      (hconv.starConvex hzero)

/-- Holomorphicity on the upper half-disk supplies primitive data on that
star-convex contour domain. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_hasPrimitive_of_analyticAt
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hanalytic :
      ∀ z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
        AnalyticAt ℂ F z) :
    ∃ G : ℂ → ℂ,
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk F G T := by
  let G : ℂ → ℂ := LFunctions.complex_centerSegmentIntegral F
  have hprimitive :
      ∀ z : ℂ,
        z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T →
          AnalyticAt ℂ G z ∧ HasDerivAt G (F z) z := by
    exact
      LFunctions.complex_centerSegmentIntegral_parametricPrimitive_of_holomorphicOn_starConvex
        F
        (scalarFourierLaplacePlemelj_upperHalfDisk_starConvex T _hT)
        _hanalytic
  exact
    Exists.intro G
      (And.intro
        (fun z hz => (_hanalytic z hz).continuousAt.continuousWithinAt)
        (fun z hz => (hprimitive z hz).2.hasDerivWithinAt))

/-- A point strictly inside the radius disk and strictly above the real axis
has the closed upper half-disk as a neighborhood. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_mem_nhds_of_norm_lt_im_pos
    (T : ℝ) (p : ℂ) (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p) :
    scalarFourierLaplacePlemelj_upperHalfDisk T ∈ 𝓝 p := by
  have hp_ball : p ∈ Metric.ball (0 : ℂ) T := by
    exact
      Eq.subst
        (motive := fun r : ℝ => r < T)
        (dist_zero_right p).symm
        _hp
  have hclosed_ball :
      Metric.closedBall (0 : ℂ) T ∈ 𝓝 p :=
    Metric.closedBall_mem_nhds_of_mem hp_ball
  have him_upper :
      {z : ℂ | 0 ≤ Complex.im z} ∈ 𝓝 p :=
    (Complex.continuous_im.continuousAt
      (x := p)).preimage_mem_nhds
      (Ici_mem_nhds _hp_upper)
  have hinter :
      Metric.closedBall (0 : ℂ) T ∩ {z : ℂ | 0 ≤ Complex.im z} ∈ 𝓝 p :=
    inter_mem hclosed_ball him_upper
  exact
    Eq.subst
      (motive := fun S : Set ℂ => S ∈ 𝓝 p)
      (scalarFourierLaplacePlemelj_upperHalfDisk_eq_closedBall_inter_upperHalfPlane
        T).symm
      hinter

/-- The unoriented real set integral on the upper half-disk diameter is the
usual oriented interval integral when `0 ≤ T`. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_realSegment_setIntegral_eq_intervalIntegral
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

/-- Primitive data on the upper half-disk makes the primitive function
continuous on the closed diameter. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_realSegmentPrimitive_continuousOn
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk F G T) :
    ContinuousOn (fun x : ℝ => G (x : ℂ)) (Set.Icc (-T) T) := by
  have hG_continuous :
      ContinuousOn G (scalarFourierLaplacePlemelj_upperHalfDisk T) := by
    intro z hz
    exact (_hprimitive.2 z hz).continuousWithinAt
  exact
    hG_continuous.comp
      Complex.continuous_ofReal.continuousOn
      (fun x hx =>
        scalarFourierLaplacePlemelj_realDiameter_mapsTo_upperHalfDisk
          T x hx)

/-- The upper real-diameter integrand is continuous on the closed diameter. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_realSegmentIntegrand_continuousOn
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk F G T) :
    ContinuousOn (fun x : ℝ => F (x : ℂ)) (Set.Icc (-T) T) := by
  exact
    _hprimitive.1.comp
      Complex.continuous_ofReal.continuousOn
      (fun x hx =>
        scalarFourierLaplacePlemelj_realDiameter_mapsTo_upperHalfDisk
          T x hx)

/-- The upper real-diameter integrand is interval-integrable on the diameter. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_realSegment_intervalIntegrable
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk F G T) :
    IntervalIntegrable (fun x : ℝ => F (x : ℂ)) MeasureTheory.volume (-T) T := by
  have hle : -T ≤ T := by
    exact neg_le_self _hT
  exact
    ContinuousOn.intervalIntegrable_of_Icc hle
      (scalarFourierLaplacePlemelj_upperHalfDisk_realSegmentIntegrand_continuousOn
        F G T _hT _hprimitive)

/-- Pointwise right-derivative transport from upper half-disk primitive data to
the real diameter. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_realSegment_hasRightDerivWithinAt
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk F G T) :
    ∀ t ∈ Set.Ioo (-T) T,
      HasDerivWithinAt
        (fun x : ℝ => G (x : ℂ))
        (F (t : ℂ))
        (Set.Ioi t)
        t := by
  intro t ht
  let s : Set ℝ := Set.Ioi t ∩ Set.Icc (-T) T
  let ofRealLine : ℝ → ℂ := fun x : ℝ => (x : ℂ)
  have ht_closed : t ∈ Set.Icc (-T) T :=
    Set.mem_Icc_of_Ioo ht
  have ht_upper :
      (t : ℂ) ∈ scalarFourierLaplacePlemelj_upperHalfDisk T :=
    scalarFourierLaplacePlemelj_realDiameter_mapsTo_upperHalfDisk
      T t ht_closed
  have hinner :
      HasDerivWithinAt ofRealLine (1 : ℂ) s t := by
    exact Complex.ofRealCLM.hasDerivAt.hasDerivWithinAt
  have hmaps :
      Set.MapsTo ofRealLine s
        (scalarFourierLaplacePlemelj_upperHalfDisk T) := by
    intro x hx
    exact
      scalarFourierLaplacePlemelj_realDiameter_mapsTo_upperHalfDisk
        T x hx.2
  have houter :
      HasFDerivWithinAt G
        ((F (t : ℂ)) • (1 : ℂ →L[ℝ] ℂ))
        (scalarFourierLaplacePlemelj_upperHalfDisk T)
        (ofRealLine t) := by
    exact (_hprimitive.2 (t : ℂ) ht_upper).complexToReal_fderiv
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
  have hlocal :
      HasDerivWithinAt
        (G ∘ ofRealLine)
        (F (t : ℂ))
        s
        t := by
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
  have hIcc_mem :
      Set.Icc (-T) T ∈ 𝓝[Set.Ioi t] t :=
    Icc_mem_nhdsWithin_Ioi
      ⟨le_of_lt ht.1, ht.2⟩
  exact
    hlocal.mono_of_mem_nhdsWithin
      (inter_mem self_mem_nhdsWithin hIcc_mem)

/-- The interval integral over the upper real diameter evaluates to the
primitive endpoint difference. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_realSegment_intervalIntegral_eq_primitiveEndpointSub
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk F G T) :
    (∫ t in (-T)..T, F (t : ℂ)) =
      G (T : ℂ) - G ((-T : ℝ) : ℂ) := by
  have hle : -T ≤ T := by
    exact neg_le_self _hT
  exact
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      hle
      (scalarFourierLaplacePlemelj_upperHalfDisk_realSegmentPrimitive_continuousOn
        F G T _hT _hprimitive)
      (scalarFourierLaplacePlemelj_upperHalfDisk_realSegment_hasRightDerivWithinAt
        F G T _hT _hprimitive)
      (scalarFourierLaplacePlemelj_upperHalfDisk_realSegment_intervalIntegrable
        F G T _hT _hprimitive)

/-- The real diameter part of the upper half-disk boundary integral is the
primitive endpoint difference. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_realSegmentIntegral_eq_primitiveEndpointSub
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 < T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk F G T) :
    (∫ t in Set.Icc (-T) T, F (t : ℂ)) =
      G (T : ℂ) - G ((-T : ℝ) : ℂ) := by
  exact
    Eq.trans
      (scalarFourierLaplacePlemelj_upperHalfDisk_realSegment_setIntegral_eq_intervalIntegral
        F T _hT.le)
      (scalarFourierLaplacePlemelj_upperHalfDisk_realSegment_intervalIntegral_eq_primitiveEndpointSub
        F G T _hT.le _hprimitive)

/-- The upper semicircle parametrization. -/
noncomputable def scalarFourierLaplacePlemelj_upperArcParam
    (T : ℝ) (θ : ℝ) : ℂ :=
  (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))

/-- The derivative of the upper semicircle parametrization. -/
theorem scalarFourierLaplacePlemelj_upperArcParam_hasDerivAt
    (T θ : ℝ) :
    HasDerivAt
      (scalarFourierLaplacePlemelj_upperArcParam T)
      (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
      θ := by
  unfold scalarFourierLaplacePlemelj_upperArcParam
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

/-- The upper arc parametrization starts at the right endpoint of the diameter. -/
theorem scalarFourierLaplacePlemelj_upperArcParam_zero
    (T : ℝ) :
    scalarFourierLaplacePlemelj_upperArcParam T 0 = (T : ℂ) := by
  unfold scalarFourierLaplacePlemelj_upperArcParam
  exact
    Eq.trans
      (congrArg
        (fun w : ℂ => (T : ℂ) * Complex.exp w)
        (mul_zero Complex.I))
      (Eq.trans
        (congrArg (fun w : ℂ => (T : ℂ) * w) Complex.exp_zero)
        (mul_one (T : ℂ)))

/-- The upper arc parametrization ends at the left endpoint of the diameter. -/
theorem scalarFourierLaplacePlemelj_upperArcParam_pi
    (T : ℝ) :
    scalarFourierLaplacePlemelj_upperArcParam T Real.pi =
      ((-T : ℝ) : ℂ) := by
  unfold scalarFourierLaplacePlemelj_upperArcParam
  have harg :
      Complex.I * ((Real.pi : ℝ) : ℂ) =
        (Real.pi : ℂ) * Complex.I := by
    exact mul_comm Complex.I (Real.pi : ℂ)
  have hexp :
      Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ)) = (-1 : ℂ) := by
    exact (congrArg Complex.exp harg).trans Complex.exp_pi_mul_I
  exact
    Eq.trans
      (congrArg (fun w : ℂ => (T : ℂ) * w) hexp)
      (Eq.trans
        (mul_neg_one (T : ℂ))
        (Complex.ofReal_neg T).symm)

/-- Along the upper arc, the primitive is continuous on the angular interval. -/
theorem scalarFourierLaplacePlemelj_upperArcPrimitive_continuousOn
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 < T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk F G T) :
    ContinuousOn
      (fun θ : ℝ => G (scalarFourierLaplacePlemelj_upperArcParam T θ))
      (Set.uIcc (0 : ℝ) Real.pi) := by
  have hparam_continuous : Continuous (scalarFourierLaplacePlemelj_upperArcParam T) := by
    exact fun θ : ℝ =>
      (scalarFourierLaplacePlemelj_upperArcParam_hasDerivAt T θ).continuousAt
  have hmaps :
      Set.MapsTo
        (scalarFourierLaplacePlemelj_upperArcParam T)
        (Set.uIcc (0 : ℝ) Real.pi)
        (scalarFourierLaplacePlemelj_upperHalfDisk T) := by
    intro θ hθ
    unfold scalarFourierLaplacePlemelj_upperArcParam
    exact
      scalarFourierLaplacePlemelj_upperArc_mapsTo_upperHalfDisk
        T _hT θ hθ
  have hG_continuous :
      ContinuousOn G (scalarFourierLaplacePlemelj_upperHalfDisk T) := by
    intro z hz
    exact (_hprimitive.2 z hz).continuousWithinAt
  exact
    hG_continuous.comp
      hparam_continuous.continuousOn
      hmaps

/-- On the open upper arc, the primitive has the displayed one-sided
parametrized derivative. -/
theorem scalarFourierLaplacePlemelj_upperArcPrimitive_hasRightDerivWithinAt
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 < T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk F G T) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi,
      HasDerivWithinAt
        (fun u : ℝ => G (scalarFourierLaplacePlemelj_upperArcParam T u))
        (F (scalarFourierLaplacePlemelj_upperArcParam T θ) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (Set.Ioi θ)
        θ := by
  intro θ hθ
  let s : Set ℝ := Set.Ioi θ ∩ Set.Ioo (0 : ℝ) Real.pi
  have hθ_uIcc : θ ∈ Set.uIcc (0 : ℝ) Real.pi :=
    mem_uIcc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hθ_upper :
      scalarFourierLaplacePlemelj_upperArcParam T θ ∈
        scalarFourierLaplacePlemelj_upperHalfDisk T := by
    unfold scalarFourierLaplacePlemelj_upperArcParam
    exact
      scalarFourierLaplacePlemelj_upperArc_mapsTo_upperHalfDisk
        T _hT θ hθ_uIcc
  have hinner :
      HasDerivWithinAt
        (scalarFourierLaplacePlemelj_upperArcParam T)
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        s
        θ := by
    exact
      (scalarFourierLaplacePlemelj_upperArcParam_hasDerivAt T θ).hasDerivWithinAt
  have hmaps :
      Set.MapsTo
        (scalarFourierLaplacePlemelj_upperArcParam T)
        s
        (scalarFourierLaplacePlemelj_upperHalfDisk T) := by
    intro u hu
    have hu_uIcc : u ∈ Set.uIcc (0 : ℝ) Real.pi :=
      mem_uIcc.mpr ⟨le_of_lt hu.2.1, le_of_lt hu.2.2⟩
    unfold scalarFourierLaplacePlemelj_upperArcParam
    exact
      scalarFourierLaplacePlemelj_upperArc_mapsTo_upperHalfDisk
        T _hT u hu_uIcc
  have houter :
      HasFDerivWithinAt G
        ((F (scalarFourierLaplacePlemelj_upperArcParam T θ)) •
          (1 : ℂ →L[ℝ] ℂ))
        (scalarFourierLaplacePlemelj_upperHalfDisk T)
        (scalarFourierLaplacePlemelj_upperArcParam T θ) := by
    exact (_hprimitive.2
      (scalarFourierLaplacePlemelj_upperArcParam T θ)
      hθ_upper).complexToReal_fderiv
  have hcomp :
      HasDerivWithinAt
        (G ∘ scalarFourierLaplacePlemelj_upperArcParam T)
        (((F (scalarFourierLaplacePlemelj_upperArcParam T θ)) •
          (1 : ℂ →L[ℝ] ℂ))
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        s
        θ := by
    exact houter.comp_hasDerivWithinAt θ hinner hmaps
  have hvalue :
      (((F (scalarFourierLaplacePlemelj_upperArcParam T θ)) •
          (1 : ℂ →L[ℝ] ℂ))
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        F (scalarFourierLaplacePlemelj_upperArcParam T θ) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
    calc
      (((F (scalarFourierLaplacePlemelj_upperArcParam T θ)) •
          (1 : ℂ →L[ℝ] ℂ))
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
          F (scalarFourierLaplacePlemelj_upperArcParam T θ) *
            ((1 : ℂ →L[ℝ] ℂ)
              (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
        rfl
      _ =
          F (scalarFourierLaplacePlemelj_upperArcParam T θ) *
            (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
        rfl
  have hlocal :
      HasDerivWithinAt
        (fun u : ℝ => G (scalarFourierLaplacePlemelj_upperArcParam T u))
        (F (scalarFourierLaplacePlemelj_upperArcParam T θ) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        s
        θ := by
    exact
      Eq.subst
        (motive := fun v : ℂ =>
          HasDerivWithinAt
            (G ∘ scalarFourierLaplacePlemelj_upperArcParam T)
            v
            s
            θ)
        hvalue
        hcomp
  have hIoo_mem :
      Set.Ioo (0 : ℝ) Real.pi ∈ 𝓝[Set.Ioi θ] θ :=
    Ioo_mem_nhdsWithin_Ioi ⟨le_of_lt hθ.1, hθ.2⟩
  exact
    hlocal.mono_of_mem_nhdsWithin
      (inter_mem self_mem_nhdsWithin hIoo_mem)

/-- The upper arc integrand is interval-integrable over the returning arc. -/
theorem scalarFourierLaplacePlemelj_upperArc_intervalIntegrable
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 < T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk F G T) :
    IntervalIntegrable
      (fun θ : ℝ =>
        F (scalarFourierLaplacePlemelj_upperArcParam T θ) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      MeasureTheory.volume
      (0 : ℝ)
      Real.pi := by
  have hparam_continuous : Continuous (scalarFourierLaplacePlemelj_upperArcParam T) := by
    exact fun θ : ℝ =>
      (scalarFourierLaplacePlemelj_upperArcParam_hasDerivAt T θ).continuousAt
  have hmaps :
      Set.MapsTo
        (scalarFourierLaplacePlemelj_upperArcParam T)
        (Set.uIcc (0 : ℝ) Real.pi)
        (scalarFourierLaplacePlemelj_upperHalfDisk T) := by
    intro θ hθ
    unfold scalarFourierLaplacePlemelj_upperArcParam
    exact
      scalarFourierLaplacePlemelj_upperArc_mapsTo_upperHalfDisk
        T _hT θ hθ
  have hF_continuous :
      ContinuousOn
        (fun θ : ℝ => F (scalarFourierLaplacePlemelj_upperArcParam T θ))
        (Set.uIcc (0 : ℝ) Real.pi) := by
    exact
      _hprimitive.1.comp
        hparam_continuous.continuousOn
        hmaps
  have hvelocity_continuous :
      Continuous
        (fun θ : ℝ =>
          Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
    exact
      (continuous_const.mul continuous_const).mul
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))
  have hintegrand_continuous :
      ContinuousOn
        (fun θ : ℝ =>
          F (scalarFourierLaplacePlemelj_upperArcParam T θ) *
            (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (Set.uIcc (0 : ℝ) Real.pi) :=
    hF_continuous.mul hvelocity_continuous.continuousOn
  exact ContinuousOn.intervalIntegrable hintegrand_continuous

/-- The path-FTC form of the upper arc endpoint calculation. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_upperArcIntegral_eq_primitiveEndpointSub_of_pathFTC
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 < T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk F G T) :
    (∫ θ in (0 : ℝ)..Real.pi,
      let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      F z *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      G ((-T : ℝ) : ℂ) - G (T : ℂ) := by
  have hftc :
      (∫ θ in (0 : ℝ)..Real.pi,
        F (scalarFourierLaplacePlemelj_upperArcParam T θ) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        G (scalarFourierLaplacePlemelj_upperArcParam T Real.pi) -
          G (scalarFourierLaplacePlemelj_upperArcParam T 0) :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right
      (scalarFourierLaplacePlemelj_upperArcPrimitive_continuousOn
        F G T _hT _hprimitive)
      (scalarFourierLaplacePlemelj_upperArcPrimitive_hasRightDerivWithinAt
        F G T _hT _hprimitive)
      (scalarFourierLaplacePlemelj_upperArc_intervalIntegrable
        F G T _hT _hprimitive)
  have hleft :
      (∫ θ in (0 : ℝ)..Real.pi,
        let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
        F z *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      (∫ θ in (0 : ℝ)..Real.pi,
        F (scalarFourierLaplacePlemelj_upperArcParam T θ) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
    rfl
  have hend :
      G (scalarFourierLaplacePlemelj_upperArcParam T Real.pi) -
          G (scalarFourierLaplacePlemelj_upperArcParam T 0) =
        G ((-T : ℝ) : ℂ) - G (T : ℂ) := by
    exact
      congrArg₂ HSub.hSub
        (congrArg G (scalarFourierLaplacePlemelj_upperArcParam_pi T))
        (congrArg G (scalarFourierLaplacePlemelj_upperArcParam_zero T))
  exact Eq.trans hleft (Eq.trans hftc hend)

/-- The upper semicircle part of the boundary integral is the returning
primitive endpoint difference. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_upperArcIntegral_eq_primitiveEndpointSub
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 < T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk F G T) :
    (∫ θ in (0 : ℝ)..Real.pi,
      let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      F z *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      G ((-T : ℝ) : ℂ) - G (T : ℂ) := by
  exact
    scalarFourierLaplacePlemelj_upperHalfDisk_upperArcIntegral_eq_primitiveEndpointSub_of_pathFTC
      F G T _hT _hprimitive

/-- Adding the two primitive endpoint differences around the upper half-disk
boundary gives zero. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_primitiveEndpointSub_add_return_eq_zero
    (G : ℂ → ℂ) (T : ℝ) :
    (G (T : ℂ) - G ((-T : ℝ) : ℂ)) +
        (G ((-T : ℝ) : ℂ) - G (T : ℂ)) =
      0 := by
  exact
    scalarFourierLaplacePlemelj_lowerHalfDisk_primitiveEndpointSub_add_return_eq_zero
      G T

/-- Upper-half-disk primitive data makes the boundary integral vanish. -/
theorem scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral_eq_zero_of_hasPrimitive
    (F G : ℂ → ℂ) (T : ℝ) (_hT : 0 < T)
    (_hprimitive :
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk F G T) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral F T = 0 := by
  unfold scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
  exact
    Eq.trans
      (congrArg₂ HAdd.hAdd
        (scalarFourierLaplacePlemelj_upperHalfDisk_realSegmentIntegral_eq_primitiveEndpointSub
          F G T _hT _hprimitive)
        (scalarFourierLaplacePlemelj_upperHalfDisk_upperArcIntegral_eq_primitiveEndpointSub
          F G T _hT _hprimitive))
      (scalarFourierLaplacePlemelj_upperHalfDisk_primitiveEndpointSub_add_return_eq_zero
        G T)

/-- Domain-relative Cauchy--FTC for the center-segment primitive on the closed
upper half-disk.  This is the within-domain form needed at boundary points:
continuity on the closed star-convex set and complex differentiability within
that set are enough to differentiate the center-segment integral within the
same set. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_centerSegmentIntegral_hasDerivWithinAt_of_differentiableOn
    (φ : ℂ → ℂ) (T : ℝ) (_hT : 0 < T)
    (_hcont : ContinuousOn φ (scalarFourierLaplacePlemelj_upperHalfDisk T))
    (_hdiff : DifferentiableOn ℂ φ
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    ∀ z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
      HasDerivWithinAt
        (LFunctions.complex_centerSegmentIntegral φ)
        (φ z)
        (scalarFourierLaplacePlemelj_upperHalfDisk T)
        z := by
  sorry

/-- Continuity of the removable Cauchy regular part on the upper half-disk. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_continuousOn
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    ContinuousOn
      (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p)
      (scalarFourierLaplacePlemelj_upperHalfDisk T) := by
  have hdomain :
      scalarFourierLaplacePlemelj_upperHalfDisk T ∈ 𝓝 p :=
    scalarFourierLaplacePlemelj_upperHalfDisk_mem_nhds_of_norm_lt_im_pos
      T p _hp _hp_upper
  have hF_continuous :
      ContinuousOn F (scalarFourierLaplacePlemelj_upperHalfDisk T) :=
    _hdiff.continuousOn
  have hF_differentiableAt :
      DifferentiableAt ℂ F p :=
    _hdiff.differentiableAt hdomain
  exact
    Iff.mpr
      (continuousOn_dslope hdomain)
      (And.intro hF_continuous hF_differentiableAt)

/-- The center-segment primitive differentiates to the removable Cauchy regular
part within the upper half-disk. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_centerSegmentPrimitive_hasDerivWithinAt
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    ∀ z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
      HasDerivWithinAt
        (LFunctions.complex_centerSegmentIntegral
          (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p))
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p z)
        (scalarFourierLaplacePlemelj_upperHalfDisk T)
        z := by
  have hdomain :
      scalarFourierLaplacePlemelj_upperHalfDisk T ∈ 𝓝 p :=
    scalarFourierLaplacePlemelj_upperHalfDisk_mem_nhds_of_norm_lt_im_pos
      T p _hp _hp_upper
  have hregular_continuous :
      ContinuousOn
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p)
        (scalarFourierLaplacePlemelj_upperHalfDisk T) :=
    scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_continuousOn
      F T _hT p _hp _hp_upper _hdiff
  have hregular_differentiable :
      DifferentiableOn ℂ
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p)
        (scalarFourierLaplacePlemelj_upperHalfDisk T) :=
    Iff.mpr
      (Complex.differentiableOn_dslope hdomain)
      _hdiff
  exact
    scalarFourierLaplacePlemelj_upperHalfDisk_centerSegmentIntegral_hasDerivWithinAt_of_differentiableOn
      (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p)
      T _hT hregular_continuous hregular_differentiable

/-- The center-segment integral is primitive data for the removable Cauchy
regular part on the upper half-disk. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_centerSegmentPrimitive
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk
      (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p)
      (LFunctions.complex_centerSegmentIntegral
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p))
      T := by
  exact
    And.intro
      (scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_continuousOn
        F T _hT p _hp _hp_upper _hdiff)
      (scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_centerSegmentPrimitive_hasDerivWithinAt
        F T _hT p _hp _hp_upper _hdiff)

/-- The regular part of the Cauchy kernel has primitive data on the upper
half-disk. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_hasPrimitive
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    ∃ G : ℂ → ℂ,
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p)
        G T := by
  exact
    Exists.intro
      (LFunctions.complex_centerSegmentIntegral
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p))
      (scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_centerSegmentPrimitive
        F T _hT p _hp _hp_upper _hdiff)

/-- The regular part of the simple-pole Cauchy kernel has zero boundary
integral on the upper half-disk.  This is the removable-singularity branch of
the residue proof: after subtracting `F p`, the numerator vanishes at `p`, so
the quotient extends holomorphically through the pole and has a primitive on
the star-convex upper half-disk. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_boundaryIntegral_eq_zero
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p) T = 0 := by
  match
    scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_hasPrimitive
      F T _hT p _hp _hp_upper _hdiff with
  | ⟨G, hprimitive⟩ =>
      exact
        scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral_eq_zero_of_hasPrimitive
          (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p)
          G T _hT hprimitive

/-- The upper half-disk boundary has winding number one around any point in
the strict upper half-disk. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_boundary_winding_one
    (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (fun z : ℂ => (z - p)⁻¹) T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  sorry

/-- The raw scalar simple-pole kernel has winding number one around a pole in
the upper half-disk boundary contour. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_simplePoleKernel_boundaryIntegral_eq_two_pi_i
    (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (fun z : ℂ => (z - p)⁻¹) T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  exact
    scalarFourierLaplacePlemelj_upperHalfDisk_boundary_winding_one
      T _hT p _hp _hp_upper

/-- Pull a constant residue coefficient out of the upper half-disk scalar
pole-kernel boundary integral. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_const_mul_simplePoleKernel_boundaryIntegral
    (c : ℂ) (T : ℝ) (p : ℂ) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (fun z : ℂ => c * (z - p)⁻¹) T =
      c *
        scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
          (fun z : ℂ => (z - p)⁻¹) T := by
  unfold scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
  let A : ℂ := ∫ t in Set.Icc (-T) T, (((t : ℂ) - p)⁻¹)
  let B : ℂ :=
    ∫ θ in (0 : ℝ)..Real.pi,
      let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      ((z - p)⁻¹) *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  have hreal :
      (∫ t in Set.Icc (-T) T, c * (((t : ℂ) - p)⁻¹)) = c * A := by
    exact integral_mul_left c (fun t : ℝ => (((t : ℂ) - p)⁻¹))
  have harc :
      (∫ θ in (0 : ℝ)..Real.pi,
        let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
        (c * ((z - p)⁻¹)) *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        c * B := by
    have hcongr :
        (∫ θ in (0 : ℝ)..Real.pi,
          let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
          (c * ((z - p)⁻¹)) *
            (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
          ∫ θ in (0 : ℝ)..Real.pi,
            c *
              (let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
              ((z - p)⁻¹) *
                (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
      exact
        intervalIntegral.integral_congr
          (fun θ _hθ =>
            let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
            mul_assoc c ((z - p)⁻¹)
              (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
    exact
      hcongr.trans
        (intervalIntegral.integral_const_mul c
          (fun θ : ℝ =>
            let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
            ((z - p)⁻¹) *
              (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))))
  calc
    (∫ t in Set.Icc (-T) T, c * (((t : ℂ) - p)⁻¹)) +
        (∫ θ in (0 : ℝ)..Real.pi,
          let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
          (c * ((z - p)⁻¹)) *
            (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        c * A + c * B := by
      exact congrArg₂ HAdd.hAdd hreal harc
    _ = c * (A + B) := by
      exact (mul_add c A B).symm

/-- Interval integrability of the regular removable part on the real diameter. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_regularPart_intervalIntegrable
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    IntervalIntegrable
      (fun t : ℝ =>
        scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p (t : ℂ))
      MeasureTheory.volume (-T) T := by
  have hle : -T ≤ T := by
    exact neg_le_self _hT.le
  have hmaps :
      Set.MapsTo
        (fun t : ℝ => (t : ℂ))
        (Set.Icc (-T) T)
        (scalarFourierLaplacePlemelj_upperHalfDisk T) := by
    intro t ht
    exact scalarFourierLaplacePlemelj_realDiameter_mapsTo_upperHalfDisk T t ht
  have hFline :
      ContinuousOn (fun t : ℝ => F (t : ℂ)) (Set.Icc (-T) T) :=
    _hdiff.continuousOn.comp
      Complex.continuous_ofReal.continuousOn
      hmaps
  have hnum :
      ContinuousOn
        (fun t : ℝ => F (t : ℂ) - F p)
        (Set.Icc (-T) T) :=
    hFline.sub continuousOn_const
  have hden :
      ContinuousOn
        (fun t : ℝ => ((t : ℂ) - p))
        (Set.Icc (-T) T) :=
    (Complex.continuous_ofReal.sub continuous_const).continuousOn
  have hden_ne_zero :
      ∀ t : ℝ, t ∈ Set.Icc (-T) T → ((t : ℂ) - p) ≠ 0 := by
    intro t _ht
    exact
      sub_ne_zero.mpr
        (scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_ne_pole
          p _hp_upper t)
  have hinv :
      ContinuousOn
        (fun t : ℝ => (((t : ℂ) - p)⁻¹))
        (Set.Icc (-T) T) :=
    hden.inv₀ hden_ne_zero
  have hquot :
      ContinuousOn
        (fun t : ℝ => (F (t : ℂ) - F p) * (((t : ℂ) - p)⁻¹))
        (Set.Icc (-T) T) :=
    hnum.mul hinv
  have hregular_eq :
      Set.EqOn
        (fun t : ℝ =>
          scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p
            (t : ℂ))
        (fun t : ℝ => (F (t : ℂ) - F p) * (((t : ℂ) - p)⁻¹))
        (Set.Icc (-T) T) := by
    intro t ht
    unfold scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart
    have hneq :
        (t : ℂ) ≠ p :=
      scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_ne_pole
        p _hp_upper t
    have hif :
        (if (t : ℂ) = p then 0 else (F (t : ℂ) - F p) / ((t : ℂ) - p)) =
          (F (t : ℂ) - F p) / ((t : ℂ) - p) := by
      exact if_neg hneq
    exact hif.trans rfl
  exact
    ((ContinuousOn.congr hquot hregular_eq).intervalIntegrable_of_Icc hle)

/-- Interval integrability of the scalar pole part on the real diameter. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_simplePolePart_intervalIntegrable
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    IntervalIntegrable
      (fun t : ℝ => (fun z : ℂ => F p * (z - p)⁻¹) (t : ℂ))
      MeasureTheory.volume (-T) T := by
  have hden :
      Continuous (fun t : ℝ => ((t : ℂ) - p)) :=
    Complex.continuous_ofReal.sub continuous_const
  have hden_ne_zero :
      ∀ t : ℝ, ((t : ℂ) - p) ≠ 0 := by
    intro t
    exact
      sub_ne_zero.mpr
        (scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_ne_pole
          p _hp_upper t)
  have hinv :
      Continuous (fun t : ℝ => (((t : ℂ) - p)⁻¹)) :=
    hden.inv₀ hden_ne_zero
  have hintegrand :
      Continuous
        (fun t : ℝ => (fun z : ℂ => F p * (z - p)⁻¹) (t : ℂ)) :=
    continuous_const.mul hinv
  exact hintegrand.intervalIntegrable (-T) T

/-- Diameter contribution to the boundary-integral Cauchy-kernel split. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_integral_decompose
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    (∫ t in Set.Icc (-T) T, (fun z : ℂ => F z / (z - p)) (t : ℂ)) =
      (∫ t in Set.Icc (-T) T,
        scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p (t : ℂ)) +
        ∫ t in Set.Icc (-T) T,
          (fun z : ℂ => F p * (z - p)⁻¹) (t : ℂ) := by
  calc
    (∫ t in Set.Icc (-T) T, (fun z : ℂ => F z / (z - p)) (t : ℂ)) =
        ∫ t in Set.Icc (-T) T,
          scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p (t : ℂ) +
            (fun z : ℂ => F p * (z - p)⁻¹) (t : ℂ) := by
      exact
        intervalIntegral.integral_congr
          (Filter.Eventually.of_forall
            (fun t : ℝ =>
              scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_integrand_decompose
                F p _hp_upper t))
    _ =
        (∫ t in Set.Icc (-T) T,
          scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p (t : ℂ)) +
          ∫ t in Set.Icc (-T) T,
            (fun z : ℂ => F p * (z - p)⁻¹) (t : ℂ) := by
      exact
        intervalIntegral.integral_add
          (scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_regularPart_intervalIntegrable
            F T _hT p _hp _hp_upper _hdiff)
          (scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_simplePolePart_intervalIntegrable
            F T _hT p _hp _hp_upper _hdiff)

/-- The upper semicircle parametrization lies in the closed upper half-disk on
the angular interval `[0, π]`. -/
theorem scalarFourierLaplacePlemelj_upperArc_mapsTo_upperHalfDisk
    (T : ℝ) (_hT : 0 < T) :
    Set.MapsTo
      (fun θ : ℝ => (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
      (Set.Icc (0 : ℝ) Real.pi)
      (scalarFourierLaplacePlemelj_upperHalfDisk T) := by
  intro θ hθ
  unfold scalarFourierLaplacePlemelj_upperHalfDisk
  have hnorm_eq :
      ‖(T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = T :=
    scalarFourierLaplacePlemelj_upperHalfDisk_arcPoint_norm_eq_radius
      T _hT θ
  have hnorm : ‖(T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ ≤ T := by
    exact
      Eq.subst
        (motive := fun r : ℝ => r ≤ T)
        hnorm_eq.symm
        (le_refl T)
  have harg :
      Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I :=
    mul_comm Complex.I (θ : ℂ)
  have hexp_re :
      (Complex.exp (Complex.I * (θ : ℂ))).re = Real.cos θ :=
    (congrArg
      (fun z : ℂ => (Complex.exp z).re)
      harg).trans
      (Complex.exp_ofReal_mul_I_re θ)
  have hexp_im :
      (Complex.exp (Complex.I * (θ : ℂ))).im = Real.sin θ :=
    (congrArg
      (fun z : ℂ => (Complex.exp z).im)
      harg).trans
      (Complex.exp_ofReal_mul_I_im θ)
  have him_eq :
      ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
        T * Real.sin θ := by
    calc
      ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
          (T : ℂ).re * (Complex.exp (Complex.I * (θ : ℂ))).im +
            (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).re := by
        exact Complex.mul_im (T : ℂ)
          (Complex.exp (Complex.I * (θ : ℂ)))
      _ =
          T * (Complex.exp (Complex.I * (θ : ℂ))).im +
            (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).re := by
        exact congrArg
          (fun r : ℝ =>
            r * (Complex.exp (Complex.I * (θ : ℂ))).im +
              (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).re)
          (Complex.ofReal_re T)
      _ =
          T * (Complex.exp (Complex.I * (θ : ℂ))).im +
            0 * (Complex.exp (Complex.I * (θ : ℂ))).re := by
        exact congrArg
          (fun r : ℝ =>
            T * (Complex.exp (Complex.I * (θ : ℂ))).im +
              r * (Complex.exp (Complex.I * (θ : ℂ))).re)
          (Complex.ofReal_im T)
      _ =
          T * (Complex.exp (Complex.I * (θ : ℂ))).im + 0 := by
        exact congrArg
          (fun r : ℝ =>
            T * (Complex.exp (Complex.I * (θ : ℂ))).im + r)
          (zero_mul (Complex.exp (Complex.I * (θ : ℂ))).re)
      _ = T * (Complex.exp (Complex.I * (θ : ℂ))).im := by
        exact add_zero (T * (Complex.exp (Complex.I * (θ : ℂ))).im)
      _ = T * Real.sin θ := by
        exact congrArg (fun r : ℝ => T * r) hexp_im
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc hθ
  have him : 0 ≤ ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im := by
    exact
      Eq.subst
        (motive := fun r : ℝ => 0 ≤ r)
        him_eq.symm
        (mul_nonneg _hT.le hsin)
  exact And.intro hnorm him

/-- Interval integrability of the regular removable part on the upper
semicircle parametrization. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_arc_regularPart_intervalIntegrable
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    IntervalIntegrable
      (fun θ : ℝ =>
        let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
        scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p z *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      MeasureTheory.volume (0 : ℝ) Real.pi := by
  have harg :
      Continuous (fun θ : ℝ => Complex.I * (θ : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  have hexp :
      Continuous (fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ))) :=
    Complex.continuous_exp.comp harg
  have hpoint :
      Continuous
        (fun θ : ℝ => (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    continuous_const.mul hexp
  have hmaps :
      Set.MapsTo
        (fun θ : ℝ => (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Set.Icc (0 : ℝ) Real.pi)
        (scalarFourierLaplacePlemelj_upperHalfDisk T) :=
    scalarFourierLaplacePlemelj_upperArc_mapsTo_upperHalfDisk T _hT
  have hFarc :
      ContinuousOn
        (fun θ : ℝ =>
          F ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (Set.Icc (0 : ℝ) Real.pi) :=
    _hdiff.continuousOn.comp hpoint.continuousOn hmaps
  have hnum :
      ContinuousOn
        (fun θ : ℝ =>
          F ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - F p)
        (Set.Icc (0 : ℝ) Real.pi) :=
    hFarc.sub continuousOn_const
  have hden :
      ContinuousOn
        (fun θ : ℝ =>
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p)
        (Set.Icc (0 : ℝ) Real.pi) :=
    (hpoint.sub continuous_const).continuousOn
  have hden_ne_zero :
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) Real.pi →
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p ≠ 0 := by
    intro θ _hθ
    exact
      sub_ne_zero.mpr
        (scalarFourierLaplacePlemelj_upperHalfDisk_arcPoint_ne_pole
          T _hT p _hp θ)
  have hinv :
      ContinuousOn
        (fun θ : ℝ =>
          ((((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p)⁻¹))
        (Set.Icc (0 : ℝ) Real.pi) :=
    hden.inv₀ hden_ne_zero
  have hquot :
      ContinuousOn
        (fun θ : ℝ =>
          (F ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - F p) *
            ((((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p)⁻¹))
        (Set.Icc (0 : ℝ) Real.pi) :=
    hnum.mul hinv
  have hregular_eq :
      Set.EqOn
        (fun θ : ℝ =>
          scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (fun θ : ℝ =>
          (F ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - F p) *
            ((((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p)⁻¹))
        (Set.Icc (0 : ℝ) Real.pi) := by
    intro θ _hθ
    unfold scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart
    have hneq :
        (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ≠ p :=
      scalarFourierLaplacePlemelj_upperHalfDisk_arcPoint_ne_pole
        T _hT p _hp θ
    have hif :
        (if (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) = p
          then 0
          else
            (F ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - F p) /
              (((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p)) =
          (F ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - F p) /
            (((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p) := by
      exact if_neg hneq
    exact hif.trans rfl
  have hregular :
      ContinuousOn
        (fun θ : ℝ =>
          scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (Set.Icc (0 : ℝ) Real.pi) :=
    ContinuousOn.congr hquot hregular_eq
  have hvelocity :
      ContinuousOn
        (fun θ : ℝ =>
          Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Set.Icc (0 : ℝ) Real.pi) :=
    ((continuous_const.mul continuous_const).mul hexp).continuousOn
  exact
    (hregular.mul hvelocity).intervalIntegrable_of_Icc Real.pi_pos.le

/-- Interval integrability of the scalar pole part on the upper semicircle
parametrization. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_arc_simplePolePart_intervalIntegrable
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    IntervalIntegrable
      (fun θ : ℝ =>
        let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
        (fun z : ℂ => F p * (z - p)⁻¹) z *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      MeasureTheory.volume (0 : ℝ) Real.pi := by
  have harg :
      Continuous (fun θ : ℝ => Complex.I * (θ : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  have hexp :
      Continuous (fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ))) :=
    Complex.continuous_exp.comp harg
  have hpoint :
      Continuous
        (fun θ : ℝ => (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    continuous_const.mul hexp
  have hden :
      Continuous
        (fun θ : ℝ =>
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p) :=
    hpoint.sub continuous_const
  have hden_ne_zero :
      ∀ θ : ℝ,
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p ≠ 0 := by
    intro θ
    exact
      sub_ne_zero.mpr
        (scalarFourierLaplacePlemelj_upperHalfDisk_arcPoint_ne_pole
          T _hT p _hp θ)
  have hinv :
      Continuous
        (fun θ : ℝ =>
          ((((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p)⁻¹)) :=
    hden.inv₀ hden_ne_zero
  have hscalar :
      Continuous
        (fun θ : ℝ =>
          F p *
            ((((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p)⁻¹)) :=
    continuous_const.mul hinv
  have hvelocity :
      Continuous
        (fun θ : ℝ =>
          Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    (continuous_const.mul continuous_const).mul hexp
  have hintegrand :
      Continuous
        (fun θ : ℝ =>
          let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
          (fun z : ℂ => F p * (z - p)⁻¹) z *
            (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :=
    hscalar.mul hvelocity
  exact hintegrand.intervalIntegrable (0 : ℝ) Real.pi

/-- Arc contribution to the boundary-integral Cauchy-kernel split. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_arc_integral_decompose
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    (∫ θ in (0 : ℝ)..Real.pi,
      let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      (fun z : ℂ => F z / (z - p)) z *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      (∫ θ in (0 : ℝ)..Real.pi,
        let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
        scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p z *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) +
        ∫ θ in (0 : ℝ)..Real.pi,
          let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
          (fun z : ℂ => F p * (z - p)⁻¹) z *
            (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  calc
    (∫ θ in (0 : ℝ)..Real.pi,
      let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      (fun z : ℂ => F z / (z - p)) z *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      ∫ θ in (0 : ℝ)..Real.pi,
        (let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
        scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p z *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) +
          (let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
          (fun z : ℂ => F p * (z - p)⁻¹) z *
            (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
      exact
        intervalIntegral.integral_congr
          (fun θ _hθ =>
            scalarFourierLaplacePlemelj_upperHalfDisk_arc_integrand_decompose
              F T _hT p _hp θ)
    _ =
      (∫ θ in (0 : ℝ)..Real.pi,
        let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
        scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p z *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) +
        ∫ θ in (0 : ℝ)..Real.pi,
          let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
          (fun z : ℂ => F p * (z - p)⁻¹) z *
            (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
      exact
        intervalIntegral.integral_add
          (scalarFourierLaplacePlemelj_upperHalfDisk_arc_regularPart_intervalIntegrable
            F T _hT p _hp _hp_upper _hdiff)
          (scalarFourierLaplacePlemelj_upperHalfDisk_arc_simplePolePart_intervalIntegrable
            F T _hT p _hp _hp_upper _hdiff)

/-- Boundary integral decomposition before pulling the residue coefficient
outside the scalar winding integral. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_cauchyKernel_boundaryIntegral_decompose_raw
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (fun z : ℂ => F z / (z - p)) T =
      scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p) T +
        scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
          (fun z : ℂ => F p * (z - p)⁻¹) T := by
  unfold scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
  let A : ℂ :=
    ∫ t in Set.Icc (-T) T,
      scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p (t : ℂ)
  let B : ℂ :=
    ∫ t in Set.Icc (-T) T,
      (fun z : ℂ => F p * (z - p)⁻¹) (t : ℂ)
  let C : ℂ :=
    ∫ θ in (0 : ℝ)..Real.pi,
      let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p z *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  let D : ℂ :=
    ∫ θ in (0 : ℝ)..Real.pi,
      let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      (fun z : ℂ => F p * (z - p)⁻¹) z *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  have hreal :
      (∫ t in Set.Icc (-T) T, (fun z : ℂ => F z / (z - p)) (t : ℂ)) =
        A + B :=
    scalarFourierLaplacePlemelj_upperHalfDisk_realDiameter_integral_decompose
      F T _hT p _hp _hp_upper _hdiff
  have harc :
      (∫ θ in (0 : ℝ)..Real.pi,
        let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
        (fun z : ℂ => F z / (z - p)) z *
          (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        C + D :=
    scalarFourierLaplacePlemelj_upperHalfDisk_arc_integral_decompose
      F T _hT p _hp _hp_upper _hdiff
  calc
    (∫ t in Set.Icc (-T) T, (fun z : ℂ => F z / (z - p)) (t : ℂ)) +
        (∫ θ in (0 : ℝ)..Real.pi,
          let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
          (fun z : ℂ => F z / (z - p)) z *
            (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        (A + B) + (C + D) := by
      exact congrArg₂ HAdd.hAdd hreal harc
    _ = (A + C) + (B + D) := by
      exact
        Eq.trans
          (add_assoc A B (C + D))
          (Eq.trans
            (congrArg (fun W : ℂ => A + W)
              (Eq.trans
                (add_assoc B C D).symm
                (congrArg (fun W : ℂ => W + D) (add_comm B C))))
            (add_assoc A C (B + D)).symm)

/-- Boundary integral decomposition of a Cauchy kernel into its regular
removable part and its scalar winding part. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_cauchyKernel_boundaryIntegral_decompose
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (fun z : ℂ => F z / (z - p)) T =
      scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p) T +
        F p *
          scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
            (fun z : ℂ => (z - p)⁻¹) T := by
  exact
    (scalarFourierLaplacePlemelj_upperHalfDisk_cauchyKernel_boundaryIntegral_decompose_raw
      F T _hT p _hp _hp_upper _hdiff).trans
      (congrArg
        (fun W : ℂ =>
          scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
            (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p) T + W)
        (scalarFourierLaplacePlemelj_upperHalfDisk_const_mul_simplePoleKernel_boundaryIntegral
          (F p) T p))

/-- Multiplying the scalar winding value by the residue coefficient gives the
named simple-pole residue contribution. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_regular_zero_add_winding_eq_residue
    (F : ℂ → ℂ) (p : ℂ) :
    0 + F p * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) =
      scalarFourierLaplacePlemelj_upperHalfDiskSimplePoleResidueContribution
        F p := by
  unfold scalarFourierLaplacePlemelj_upperHalfDiskSimplePoleResidueContribution
  calc
    0 + F p * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) =
        F p * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
      exact zero_add (F p * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))
    _ = ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * F p := by
      exact mul_comm (F p) ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)

/-- Cauchy-Goursat on the upper half-disk punctured at the enclosed pole
reduces the boundary integral to the local simple-pole residue contribution. -/
theorem scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral_eq_simplePoleResidueContribution
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (fun z : ℂ => F z / (z - p)) T =
      scalarFourierLaplacePlemelj_upperHalfDiskSimplePoleResidueContribution
        F p := by
  exact
    (scalarFourierLaplacePlemelj_upperHalfDisk_cauchyKernel_boundaryIntegral_decompose
      F T _hT p _hp _hp_upper _hdiff).trans
      ((congrArg₂ HAdd.hAdd
        (scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_boundaryIntegral_eq_zero
          F T _hT p _hp _hp_upper _hdiff)
        (congrArg
          (fun W : ℂ => F p * W)
          (scalarFourierLaplacePlemelj_upperHalfDisk_simplePoleKernel_boundaryIntegral_eq_two_pi_i
            T _hT p _hp _hp_upper))).trans
        (scalarFourierLaplacePlemelj_upperHalfDisk_regular_zero_add_winding_eq_residue
          F p))

/-- The named upper simple-pole residue contribution unfolds to `2πi F p`. -/
theorem scalarFourierLaplacePlemelj_upperHalfDiskSimplePoleResidueContribution_eq
    (F : ℂ → ℂ) (p : ℂ) :
    scalarFourierLaplacePlemelj_upperHalfDiskSimplePoleResidueContribution
        F p =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * F p := by
  rfl

/-- Cauchy's integral formula for a generic upper half-disk boundary integral
with one enclosed pole. -/
theorem scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral_cauchyIntegralFormula
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hdiff : DifferentiableOn ℂ F
      (scalarFourierLaplacePlemelj_upperHalfDisk T)) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (fun z : ℂ => F z / (z - p)) T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * F p := by
  exact
    Eq.trans
      (scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral_eq_simplePoleResidueContribution
        F T _hT p _hp _hp_upper _hdiff)
      (scalarFourierLaplacePlemelj_upperHalfDiskSimplePoleResidueContribution_eq
        F p)

/-- Scalar complex algebra behind the normalized Cauchy denominator:
`-1 / (I * D) = I / D`. -/
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
