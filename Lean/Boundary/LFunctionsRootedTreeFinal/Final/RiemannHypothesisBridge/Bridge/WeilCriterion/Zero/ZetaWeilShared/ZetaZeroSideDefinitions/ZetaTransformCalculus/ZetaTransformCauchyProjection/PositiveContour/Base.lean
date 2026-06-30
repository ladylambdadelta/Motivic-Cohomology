import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.FixedLineTails.Owner
import Mathlib.Analysis.Analytic.IsolatedZeros
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
      calc
        Complex.I * z + (a : ℂ) =
            Complex.I * z - (-(a : ℂ)) := by
          exact (sub_neg_eq_add (Complex.I * z) (a : ℂ)).symm
        _ = Complex.I * z - ((a : ℂ) * (Complex.I * Complex.I)) := by
          exact congrArg (fun w : ℂ => Complex.I * z - w) hi2.symm
    _ = Complex.I * z - Complex.I * ((a : ℂ) * Complex.I) := by
      exact congrArg (fun w : ℂ => Complex.I * z - w)
        (calc
          (a : ℂ) * (Complex.I * Complex.I) =
              ((a : ℂ) * Complex.I) * Complex.I := by
            exact (mul_assoc (a : ℂ) Complex.I Complex.I).symm
          _ = (Complex.I * (a : ℂ)) * Complex.I := by
            exact congrArg (fun w : ℂ => w * Complex.I)
              (mul_comm Complex.I (a : ℂ)).symm
          _ = Complex.I * ((a : ℂ) * Complex.I) := by
            exact mul_assoc Complex.I (a : ℂ) Complex.I)
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
          (mul_assoc Complex.I (a : ℂ) Complex.I).symm
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
      exact (mul_assoc ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) Complex.I E).symm
    _ = (((2 : ℂ) * (Real.pi : ℂ)) * (Complex.I * Complex.I)) * E := by
      exact congrArg (fun z : ℂ => z * E)
        (mul_assoc ((2 : ℂ) * (Real.pi : ℂ)) Complex.I Complex.I)
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
  let V : ℂ := Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  let R : ℂ :=
    scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p
      ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  let S : ℂ :=
    F p * ((((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p)⁻¹)
  calc
    (F ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
        (((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - p)) * V =
        (R + S) * V := by
      exact
        congrArg
          (fun w : ℂ => w * V)
          (scalarFourierLaplacePlemelj_upperHalfDisk_arc_cauchyKernel_decompose
            F T _hT p _hp θ)
    _ = R * V + S * V := by
      show (R + S) * V = R * V + S * V
      exact add_mul R S V

/-- Imaginary coordinate of the scalar semicircle point. -/
theorem scalarFourierLaplacePlemelj_semicirclePoint_im
    (T θ : ℝ) :
    ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
      T * Real.sin θ := by
  have harg :
      Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I :=
    mul_comm Complex.I (θ : ℂ)
  have hexp_im :
      (Complex.exp (Complex.I * (θ : ℂ))).im = Real.sin θ :=
    (congrArg
      (fun z : ℂ => (Complex.exp z).im)
      harg).trans
      (Complex.exp_ofReal_mul_I_im θ)
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
  have him_eq :
      ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
        T * Real.sin θ := by
    exact scalarFourierLaplacePlemelj_semicirclePoint_im T θ
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc hθ
  have him : 0 ≤ ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im := by
    exact
      Eq.subst
        (motive := fun r : ℝ => 0 ≤ r)
        him_eq.symm
        (mul_nonneg _hT.le hsin)
  exact And.intro hnorm him

end FixedLineCauchyProjection

end
end Boundary
