import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaCore
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Upper residual API for the finite Abel-Plana vertical side

This file owns the upper endpoint residual integrability API shared by the
finite asymptotic estimates and the vertical-limit passage.  It sits directly
over `BinetAbelPlanaCore`, so `BinetAbelPlanaVerticalLimits` can consume these
facts without importing the downstream asymptotic file.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter MeasureTheory

/-- The upper endpoint vertical line lies in the principal logarithm slit
plane. -/
theorem Complex.binetAbelPlanaUpperEndpointLine_mem_slitPlane_shared
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (s : ℝ) :
    w + (N + 1 : ℂ) + (s : ℂ) * Complex.I ∈ Complex.slitPlane := by
  have hre_pos :
      0 < (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re :=
    Complex.binetAbelPlanaUpperLogJumpSegmentDenominator_re_pos hw N s
  exact Or.inl hre_pos

/-- Real derivative of the principal logarithm along the upper endpoint
vertical line. -/
theorem Complex.hasDerivAt_binetAbelPlanaUpperEndpointLine_log_shared
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (s : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        Complex.log (w + (N + 1 : ℂ) + (u : ℂ) * Complex.I))
      (Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s)
      s := by
  have hline :
      HasDerivAt
        (fun u : ℝ => w + (N + 1 : ℂ) + (u : ℂ) * Complex.I)
        ((1 : ℂ) * Complex.I)
        s := by
    have hcomplex :
        HasDerivAt
          (fun z : ℂ => w + (N + 1 : ℂ) + z * Complex.I)
          (1 * Complex.I)
          (s : ℂ) :=
      ((hasDerivAt_id (s : ℂ)).mul_const Complex.I).const_add
        (w + (N + 1 : ℂ))
    exact hcomplex.comp_ofReal
  have hslit :
      w + (N + 1 : ℂ) + (s : ℂ) * Complex.I ∈ Complex.slitPlane :=
    Complex.binetAbelPlanaUpperEndpointLine_mem_slitPlane_shared hw N s
  have hlog :
      HasDerivAt
        (fun u : ℝ =>
          Complex.log (w + (N + 1 : ℂ) + (u : ℂ) * Complex.I))
        (Complex.I /
          (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I))
        s := by
    have hlog_raw :
        HasDerivAt
          (fun u : ℝ =>
            Complex.log (w + (N + 1 : ℂ) + (u : ℂ) * Complex.I))
          (((1 : ℂ) * Complex.I) /
            (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I))
          s :=
      hline.clog_real hslit
    have hderiv :
        ((1 : ℂ) * Complex.I) /
            (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I) =
          Complex.I / (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I) := by
      exact congrArg
        (fun u : ℂ => u / (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I))
        (one_mul Complex.I)
    exact hderiv ▸ hlog_raw
  exact hlog

/-- The upper endpoint differential-log integrand is interval-integrable on
every finite segment. -/
theorem Complex.intervalIntegrable_binetAbelPlanaUpperLogJumpSegmentIntegrand_shared
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (a b : ℝ) :
    IntervalIntegrable
      (fun s : ℝ =>
        Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s)
      volume
      a
      b := by
  show
    IntervalIntegrable
      (fun s : ℝ =>
        Complex.I / (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I))
      volume
      a
      b
  have hden_cont :
      Continuous
        (fun s : ℝ => w + (N + 1 : ℂ) + (s : ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hinv_cont :
      Continuous
        (fun s : ℝ => (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I)⁻¹) :=
    hden_cont.inv₀
      (fun s =>
        Complex.binetAbelPlanaUpperLogJumpSegmentDenominator_ne_zero hw N s)
  exact (continuous_const.mul hinv_cont).intervalIntegrable a b

/-- Fundamental theorem of calculus for the upper endpoint logarithmic line. -/
theorem Complex.integral_binetAbelPlanaUpperLogJumpSegmentIntegrand_eq_log_sub_shared
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (a b : ℝ) :
    ∫ s : ℝ in a..b,
        Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s =
      Complex.log (w + (N + 1 : ℂ) + (b : ℂ) * Complex.I) -
        Complex.log (w + (N + 1 : ℂ) + (a : ℂ) * Complex.I) := by
  exact
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _hs =>
        Complex.hasDerivAt_binetAbelPlanaUpperEndpointLine_log_shared hw N s)
      (Complex.intervalIntegrable_binetAbelPlanaUpperLogJumpSegmentIntegrand_shared
        hw N a b)

/-- The scalar exponential kernel controlling the upper vertical Abel-Plana
residual. -/
noncomputable def Complex.binetAbelPlanaVerticalKernelMajorant
    (t : ℝ) : ℝ :=
  t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)

/-- The finite mass of the Abel-Plana vertical kernel. -/
noncomputable def Complex.binetAbelPlanaVerticalKernelMass : ℝ :=
  ∫ t : ℝ in Set.Ioi (0 : ℝ),
    Complex.binetAbelPlanaVerticalKernelMajorant t

/-- Unfolding of the Abel-Plana vertical kernel majorant. -/
theorem Complex.binetAbelPlanaVerticalKernelMajorant_unfold
    (t : ℝ) :
    Complex.binetAbelPlanaVerticalKernelMajorant t =
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  rfl

/-- Unfolding of the Abel-Plana vertical kernel mass. -/
theorem Complex.binetAbelPlanaVerticalKernelMass_unfold :
    Complex.binetAbelPlanaVerticalKernelMass =
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
        Complex.binetAbelPlanaVerticalKernelMajorant t := by
  rfl

/-- Unfolding of the upper finite Abel-Plana residual integrand. -/
theorem Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand_unfold
    (N : ℕ)
    (w : ℂ)
    (t : ℝ) :
    Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t =
      Complex.I *
        (Complex.binetAbelPlanaFiniteUpperLogJump N w t /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
  rfl

/-- The Abel-Plana vertical kernel is the existing Binet real majorant. -/
theorem Complex.binetAbelPlanaVerticalKernelMajorant_eq_binetMajorant
    (t : ℝ) :
    Complex.binetAbelPlanaVerticalKernelMajorant t =
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  rfl

/-- The Abel-Plana vertical kernel is nonnegative on the positive half-line. -/
theorem Complex.binetAbelPlanaVerticalKernelMajorant_nonneg_on_Ioi :
    ∀ t : ℝ,
      t ∈ Set.Ioi (0 : ℝ) →
        0 ≤ Complex.binetAbelPlanaVerticalKernelMajorant t := by
  intro t ht
  exact
    (Complex.binetAbelPlanaVerticalKernelMajorant_unfold t).symm ▸
      Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t ht

/-- The Abel-Plana vertical kernel is integrable on the positive half-line. -/
theorem Complex.binetAbelPlanaVerticalKernelMajorant_integrableOn :
    IntegrableOn
      (fun t : ℝ => Complex.binetAbelPlanaVerticalKernelMajorant t)
      (Set.Ioi (0 : ℝ)) := by
  have hsource :
      (fun t : ℝ =>
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) =
      (fun t : ℝ =>
        Complex.binetAbelPlanaVerticalKernelMajorant t) := by
    funext t
    exact (Complex.binetAbelPlanaVerticalKernelMajorant_unfold t).symm
  exact hsource ▸ Real.binetSecondFormula_kernel_majorant_integrableOn

/-- The Abel-Plana vertical kernel mass is nonnegative. -/
theorem Complex.binetAbelPlanaVerticalKernelMass_nonneg :
    0 ≤ Complex.binetAbelPlanaVerticalKernelMass := by
  have hmass :
      0 ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ),
          Complex.binetAbelPlanaVerticalKernelMajorant t :=
    setIntegral_nonneg
      measurableSet_Ioi
      Complex.binetAbelPlanaVerticalKernelMajorant_nonneg_on_Ioi
  exact Complex.binetAbelPlanaVerticalKernelMass_unfold.symm ▸ hmass

/-- The upper finite Abel-Plana residual integrand is measurable. -/
theorem Complex.measurable_binetAbelPlanaFiniteUpperContourResidualIntegrand
    (N : ℕ)
    (w : ℂ) :
    Measurable
      (fun t : ℝ =>
        Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t) := by
  show
    Measurable
      (fun t : ℝ =>
        Complex.I *
          (Complex.binetAbelPlanaFiniteUpperLogJump N w t /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)))
  have hplus_line :
      Measurable
        (fun t : ℝ => w + ((N + 1 : ℕ) : ℂ) + (t : ℂ) * Complex.I) :=
    measurable_const.add ((Complex.measurable_ofReal.comp measurable_id).mul measurable_const)
  have hminus_line :
      Measurable
        (fun t : ℝ => w + ((N + 1 : ℕ) : ℂ) - (t : ℂ) * Complex.I) :=
    measurable_const.sub ((Complex.measurable_ofReal.comp measurable_id).mul measurable_const)
  have hjump :
      Measurable
        (fun t : ℝ =>
          Complex.log (w + ((N + 1 : ℕ) : ℂ) + (t : ℂ) * Complex.I) -
            Complex.log (w + ((N + 1 : ℕ) : ℂ) - (t : ℂ) * Complex.I)) :=
    hplus_line.clog.sub hminus_line.clog
  have hden :
      Measurable
        (fun t : ℝ => Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
    ((Complex.measurable_ofReal.comp
      (measurable_const.mul measurable_id)).cexp).sub measurable_const
  exact measurable_const.mul (hjump.div hden)

/-- The norm of the upper finite Abel-Plana residual integrand is measurable
on the positive vertical half-line. -/
theorem Complex.aestronglyMeasurable_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand
    (N : ℕ)
    (w : ℂ) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  exact
    ((Complex.measurable_binetAbelPlanaFiniteUpperContourResidualIntegrand
      N w).norm).aestronglyMeasurable

/-- Integrability of the upper-contour residual integrand norm follows from
the vertical-kernel majorant. -/
theorem Complex.integrableOn_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand_of_majorant
    {w : ℂ}
    {N : ℕ}
    (hmajorant :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t) :
    IntegrableOn
      (fun t : ℝ =>
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖)
      (Set.Ioi (0 : ℝ)) := by
  let c : ℝ := 4 * (1 + ‖w‖) / (N + 1 : ℝ)
  let K : ℝ → ℝ := fun t : ℝ =>
    ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖
  let M : ℝ → ℝ := fun t : ℝ =>
    Complex.binetAbelPlanaVerticalKernelMajorant t
  have hmajorant_integrable :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Complex.binetAbelPlanaVerticalKernelMajorant_integrableOn.const_mul c
  have hK_meas :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Complex.aestronglyMeasurable_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand
      N w
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖K t‖ ≤ c * M t := by
    filter_upwards [hmajorant] with t ht
    have hK_nonneg : 0 ≤ K t :=
      norm_nonneg
        (Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t)
    have hK_norm : ‖K t‖ = K t := by
      exact Real.norm_of_nonneg hK_nonneg
    calc
      ‖K t‖ = K t := hK_norm
      _ ≤ c * M t := ht
  exact
    hmajorant_integrable.mono' hK_meas hpointwise

/-- The upper endpoint logarithmic jump is the integral of the differential
logarithm along the vertical segment from `-t` to `t`. -/
theorem Complex.binetAbelPlanaFiniteUpperLogJump_eq_segmentIntegral_shared
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Complex.binetAbelPlanaFiniteUpperLogJump N w t =
        ∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s := by
  filter_upwards with t
  have hftc :
      ∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s =
        Complex.log (w + (N + 1 : ℂ) + (t : ℂ) * Complex.I) -
          Complex.log (w + (N + 1 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) :=
    Complex.integral_binetAbelPlanaUpperLogJumpSegmentIntegrand_eq_log_sub_shared
      hw N (-t) t
  have hneg :
      w + (N + 1 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I =
        w + (N + 1 : ℂ) - (t : ℂ) * Complex.I := by
    have hcast : ((-t : ℝ) : ℂ) = -(t : ℂ) :=
      Complex.ofReal_neg t
    have hmul : ((-t : ℝ) : ℂ) * Complex.I = -((t : ℂ) * Complex.I) := by
      calc
        ((-t : ℝ) : ℂ) * Complex.I = (-(t : ℂ)) * Complex.I := by
          exact congrArg (fun u : ℂ => u * Complex.I) hcast
        _ = -((t : ℂ) * Complex.I) := by
          exact neg_mul (t : ℂ) Complex.I
    calc
      w + (N + 1 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I =
          w + (N + 1 : ℂ) + -((t : ℂ) * Complex.I) := by
        exact congrArg (fun u : ℂ => w + (N + 1 : ℂ) + u) hmul
      _ = w + (N + 1 : ℂ) - (t : ℂ) * Complex.I := by
        exact (sub_eq_add_neg (w + (N + 1 : ℂ)) ((t : ℂ) * Complex.I)).symm
  calc
    Complex.binetAbelPlanaFiniteUpperLogJump N w t =
        Complex.log (w + (N + 1 : ℂ) + (t : ℂ) * Complex.I) -
          Complex.log (w + (N + 1 : ℂ) - (t : ℂ) * Complex.I) := by
      have hcast : ((N + 1 : ℕ) : ℂ) = (N + 1 : ℂ) :=
        Nat.cast_add_one N
      calc
        Complex.binetAbelPlanaFiniteUpperLogJump N w t =
            Complex.log (w + ((N + 1 : ℕ) : ℂ) + (t : ℂ) * Complex.I) -
              Complex.log (w + ((N + 1 : ℕ) : ℂ) - (t : ℂ) * Complex.I) := by
          rfl
        _ = Complex.log (w + (N + 1 : ℂ) + (t : ℂ) * Complex.I) -
              Complex.log (w + ((N + 1 : ℕ) : ℂ) - (t : ℂ) * Complex.I) := by
          exact congrArg
            (fun u : ℂ =>
              Complex.log u -
                Complex.log (w + ((N + 1 : ℕ) : ℂ) - (t : ℂ) * Complex.I))
            (congrArg (fun u : ℂ => w + u + (t : ℂ) * Complex.I) hcast)
        _ = Complex.log (w + (N + 1 : ℂ) + (t : ℂ) * Complex.I) -
              Complex.log (w + (N + 1 : ℂ) - (t : ℂ) * Complex.I) := by
          exact congrArg
            (fun u : ℂ =>
              Complex.log (w + (N + 1 : ℂ) + (t : ℂ) * Complex.I) -
                Complex.log u)
            (congrArg (fun u : ℂ => w + u - (t : ℂ) * Complex.I) hcast)
    _ =
        Complex.log (w + (N + 1 : ℂ) + (t : ℂ) * Complex.I) -
          Complex.log (w + (N + 1 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) := by
      exact congrArg
        (fun z : ℂ =>
          Complex.log (w + (N + 1 : ℂ) + (t : ℂ) * Complex.I) -
            Complex.log z)
        hneg.symm
    _ =
        ∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s := by
      exact hftc.symm

/-- Norm bound for the upper endpoint logarithmic-jump segment integral. -/
theorem Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegral_le_two_mul_t_div_endpoint_re_shared
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
        (2 * t) / (w.re + (N + 1 : ℝ)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht_nonneg : 0 ≤ t := le_of_lt ht
  have hpoint :
      ∀ s : ℝ,
        ‖Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
          (w.re + (N + 1 : ℝ))⁻¹ :=
    fun s =>
      Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegrand_le_endpoint_re_inv_core
        hw N s
  have hinterval :
      ‖∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
        (w.re + (N + 1 : ℝ))⁻¹ * |t - (-t)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun s hs => hpoint s)
  have habs : |t - (-t)| = 2 * t := by
    have hsub : t - (-t) = 2 * t := by
      calc
        t - (-t) = t + t := by
          exact sub_neg_eq_add t t
        _ = (1 : ℝ) * t + (1 : ℝ) * t := by
          exact congrArg₂ HAdd.hAdd (one_mul t).symm (one_mul t).symm
        _ = ((1 : ℝ) + 1) * t := by
          exact (add_mul (1 : ℝ) 1 t).symm
        _ = 2 * t := by
          exact congrArg (fun u : ℝ => u * t) one_add_one_eq_two
    calc
      |t - (-t)| = |2 * t| := by
        exact congrArg abs hsub
      _ = 2 * t :=
        abs_of_nonneg (mul_nonneg zero_le_two ht_nonneg)
  calc
    ‖∫ s : ℝ in (-t)..t,
        Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖
        ≤ (w.re + (N + 1 : ℝ))⁻¹ * |t - (-t)| :=
      hinterval
    _ = (w.re + (N + 1 : ℝ))⁻¹ * (2 * t) := by
      exact congrArg
        (fun x : ℝ => (w.re + (N + 1 : ℝ))⁻¹ * x)
        habs
    _ = (2 * t) / (w.re + (N + 1 : ℝ)) := by
      calc
        (w.re + (N + 1 : ℝ))⁻¹ * (2 * t) =
            (2 * t) * (w.re + (N + 1 : ℝ))⁻¹ := by
          exact mul_comm (w.re + (N + 1 : ℝ))⁻¹ (2 * t)
        _ = (2 * t) / (w.re + (N + 1 : ℝ)) := by
          exact (div_eq_mul_inv (2 * t) (w.re + (N + 1 : ℝ))).symm

/-- Upper endpoint logarithmic-jump bound at fixed `N`. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperLogJump_le_endpoint_kernel_fixed
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
        (4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t := by
  have hidentity :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        Complex.binetAbelPlanaFiniteUpperLogJump N w t =
          ∫ s : ℝ in (-t)..t,
            Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s :=
    Complex.binetAbelPlanaFiniteUpperLogJump_eq_segmentIntegral_shared
      hw N
  have hsegment :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
          (2 * t) / (w.re + (N + 1 : ℝ)) :=
    Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegral_le_two_mul_t_div_endpoint_re_shared
      hw N
  filter_upwards [hidentity, hsegment, ae_restrict_mem measurableSet_Ioi] with
    t ht_identity ht_segment ht_mem
  have hN_pos : 0 < (N + 1 : ℝ) := by
    have hN_nonneg : 0 ≤ (N : ℝ) :=
      Nat.cast_nonneg N
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hN_nonneg)
  have hone_le : 1 ≤ 1 + ‖w‖ :=
    le_add_of_nonneg_right (norm_nonneg w)
  have hbase :
      (2 : ℝ) / (w.re + (N + 1 : ℝ)) ≤
        4 * (1 + ‖w‖) / (N + 1 : ℝ) := by
    have hden_le :
        (N + 1 : ℝ) ≤ w.re + (N + 1 : ℝ) :=
      le_add_of_nonneg_left hw.le
    have hrecip :
        (1 : ℝ) / (w.re + (N + 1 : ℝ)) ≤
          1 / (N + 1 : ℝ) :=
      one_div_le_one_div_of_le hN_pos hden_le
    have hrecip_inv :
        (w.re + (N + 1 : ℝ))⁻¹ ≤
          (N + 1 : ℝ)⁻¹ := by
      calc
        (w.re + (N + 1 : ℝ))⁻¹ =
            (1 : ℝ) / (w.re + (N + 1 : ℝ)) := by
          exact inv_eq_one_div (w.re + (N + 1 : ℝ))
        _ ≤ 1 / (N + 1 : ℝ) := hrecip
        _ = (N + 1 : ℝ)⁻¹ := by
          exact (inv_eq_one_div (N + 1 : ℝ)).symm
    have htwo :
        (2 : ℝ) / (w.re + (N + 1 : ℝ)) ≤
          2 / (N + 1 : ℝ) :=
      calc
        (2 : ℝ) / (w.re + (N + 1 : ℝ)) =
            2 * (w.re + (N + 1 : ℝ))⁻¹ := by
          exact div_eq_mul_inv 2 (w.re + (N + 1 : ℝ))
        _ ≤ 2 * (N + 1 : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hrecip_inv zero_le_two
        _ = 2 / (N + 1 : ℝ) := by
          exact (div_eq_mul_inv 2 (N + 1 : ℝ)).symm
    have htwo_le_four :
        (2 : ℝ) / (N + 1 : ℝ) ≤
          4 * (1 + ‖w‖) / (N + 1 : ℝ) := by
      have hnum : (2 : ℝ) ≤ 4 * (1 + ‖w‖) := by
        have htwo_mul : (2 : ℝ) * 1 ≤ 2 * (1 + ‖w‖) :=
          mul_le_mul_of_nonneg_left hone_le zero_le_two
        have htwo_le_four : (2 : ℝ) * (1 + ‖w‖) ≤
            4 * (1 + ‖w‖) := by
          have htwo_le_four_scalar : (2 : ℝ) ≤ 4 := by
            calc
              (2 : ℝ) ≤ 2 + 2 := by
                exact le_add_of_nonneg_right zero_le_two
              _ = 4 := by
                exact two_add_two_eq_four
          exact mul_le_mul_of_nonneg_right htwo_le_four_scalar (zero_le_one.trans hone_le)
        exact (show (2 : ℝ) = 2 * 1 from (mul_one 2).symm) ▸
          htwo_mul.trans htwo_le_four
      exact div_le_div_of_nonneg_right hnum hN_pos.le
    exact htwo.trans htwo_le_four
  calc
    ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ =
        ‖∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ := by
      exact congrArg norm ht_identity
    _ ≤ (2 * t) / (w.re + (N + 1 : ℝ)) :=
      ht_segment
    _ = ((2 : ℝ) / (w.re + (N + 1 : ℝ))) * t := by
      calc
        (2 * t) / (w.re + (N + 1 : ℝ)) =
            (2 * t) * (w.re + (N + 1 : ℝ))⁻¹ := by
          exact div_eq_mul_inv (2 * t) (w.re + (N + 1 : ℝ))
        _ = (2 * (w.re + (N + 1 : ℝ))⁻¹) * t := by
          calc
            2 * t * (w.re + (N + 1 : ℝ))⁻¹ =
                2 * (t * (w.re + (N + 1 : ℝ))⁻¹) := by
              exact mul_assoc 2 t (w.re + (N + 1 : ℝ))⁻¹
            _ = 2 * ((w.re + (N + 1 : ℝ))⁻¹ * t) := by
              exact congrArg (fun u : ℝ => 2 * u)
                (mul_comm t (w.re + (N + 1 : ℝ))⁻¹)
            _ = (2 * (w.re + (N + 1 : ℝ))⁻¹) * t := by
              exact (mul_assoc 2 (w.re + (N + 1 : ℝ))⁻¹ t).symm
        _ = ((2 : ℝ) / (w.re + (N + 1 : ℝ))) * t := by
          exact congrArg (fun u : ℝ => u * t)
            (div_eq_mul_inv 2 (w.re + (N + 1 : ℝ))).symm
    _ ≤ (4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t :=
      mul_le_mul_of_nonneg_right hbase ht_mem.le

/-- Fixed-index pointwise majorization of the upper-contour residual
integrand.

This is the upper endpoint logarithmic-jump estimate for the vertical
Abel-Plana side: write the jump as an integral of the differential logarithm
along the segment `[-t,t]`, bound that differential logarithm by the inverse
real part of the endpoint line, and divide by the positive exponential
denominator. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperContourResidual_integrand_le_majorant_fixed
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
        (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMajorant t := by
  have hjump :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t :=
    Complex.norm_binetAbelPlanaFiniteUpperLogJump_le_endpoint_kernel_fixed
      hw N
  filter_upwards [hjump, ae_restrict_mem measurableSet_Ioi] with
    t ht_jump ht_mem
  have ht_pos : 0 < t := ht_mem
  have hden_pos :
      0 < Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
    Real.binetSecondFormula_exp_denominator_pos ht_pos
  calc
    ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ =
        ‖Complex.I *
          (Complex.binetAbelPlanaFiniteUpperLogJump N w t /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ := by
      exact congrArg norm
        (Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand_unfold N w t)
    _ =
        ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
      calc
        ‖Complex.I *
            (Complex.binetAbelPlanaFiniteUpperLogJump N w t /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ =
            ‖Complex.I‖ *
              ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
          exact norm_mul _ _
        _ =
            ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
          calc
            ‖Complex.I‖ *
                ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ =
                1 *
                ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
              exact congrArg
                (fun u : ℝ =>
                  u *
                    ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖)
                Complex.norm_I
            _ =
                ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
              exact one_mul _
        _ =
            ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
              ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
          exact norm_div _ _
        _ =
            ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
              ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ := by
          exact congrArg
            (fun x : ℝ =>
              ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ / x)
            (Complex.binetSecondFormula_exp_denominator_norm_eq t)
        _ =
            ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
              (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
          exact congrArg
            (fun x : ℝ =>
              ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ / x)
            (Real.binetSecondFormula_exp_denominator_norm_eq ht_pos)
    _ ≤
        ((4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
      div_le_div_of_nonneg_right ht_jump hden_pos.le
    _ =
        (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMajorant t := by
      calc
        ((4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t) /
            (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
            ((4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t) *
              (Real.exp ((2 : ℝ) * Real.pi * t) - 1)⁻¹ := by
          exact div_eq_mul_inv
            ((4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t)
            (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
        _ = (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            (t * (Real.exp ((2 : ℝ) * Real.pi * t) - 1)⁻¹) := by
          exact mul_assoc
            (4 * (1 + ‖w‖) / (N + 1 : ℝ))
            t
            (Real.exp ((2 : ℝ) * Real.pi * t) - 1)⁻¹
        _ = (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
          exact congrArg
            (fun u : ℝ => (4 * (1 + ‖w‖) / (N + 1 : ℝ)) * u)
            (div_eq_mul_inv t (Real.exp ((2 : ℝ) * Real.pi * t) - 1)).symm

/-- Integrability of the concrete upper vertical Abel-Plana integrand on
`(0,∞)`. -/
theorem Complex.finiteAbelPlana_log_upperVerticalIntegrand_integrableOn_Ioi
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    IntegrableOn
      (fun t : ℝ => Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t)
      (Set.Ioi (0 : ℝ)) := by
  have hmajorant :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t :=
    Complex.norm_binetAbelPlanaFiniteUpperContourResidual_integrand_le_majorant_fixed
      hw N
  have hnorm :
      Integrable
        (fun t : ℝ =>
          ‖Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t‖)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hresidual_on :
        IntegrableOn
          (fun t : ℝ =>
            ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖)
          (Set.Ioi (0 : ℝ)) :=
      Complex.integrableOn_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand_of_majorant
        (w := w)
        (N := N)
        hmajorant
    have hresidual_integrable :
        Integrable
        (fun t : ℝ =>
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      hresidual_on
    have hfun :
        (fun t : ℝ =>
            ‖Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t‖) =
          (fun t : ℝ =>
            ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖) := by
      funext t
      exact congrArg norm
        (Complex.finiteAbelPlana_log_upperVerticalIntegrand_eq_binet N w t)
    exact Eq.subst
      (motive := fun f : ℝ → ℝ =>
        Integrable f (volume.restrict (Set.Ioi (0 : ℝ))))
      hfun.symm
      hresidual_integrable
  show
    Integrable
      (fun t : ℝ => Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t)
      (volume.restrict (Set.Ioi (0 : ℝ)))
  have hmeas :
      AEStronglyMeasurable
        (fun t : ℝ => Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hmeas_global :
        Measurable
          (fun t : ℝ => Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t) := by
      show
        Measurable
          (fun t : ℝ =>
            Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t)
      exact
        Complex.measurable_binetAbelPlanaFiniteUpperContourResidualIntegrand
          N w
    exact hmeas_global.aestronglyMeasurable
  exact (integrable_norm_iff hmeas).mp hnorm

end

end LFunctions
end Boundary
