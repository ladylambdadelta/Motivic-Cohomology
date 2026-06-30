import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.PositiveContour.RegularPart
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.LowerHalfDiskPrimitive.Owner
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RemovableSingularity

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection
noncomputable def scalarFourierLaplacePlemelj_upperWinding_lowerHalfDiskBoundaryIntegral
    (p : ℂ) (T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-T) T, (((t : ℂ) - p)⁻¹)) +
    ∫ θ in (0 : ℝ)..(-Real.pi),
      let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      ((z - p)⁻¹) *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Full positively oriented circle integral of the scalar Cauchy kernel,
using mathlib's circle-integral owner normalization. -/
noncomputable def scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral
    (p : ℂ) (T : ℝ) : ℂ :=
  ∮ z in C((0 : ℂ), T), (z - p)⁻¹

/-- Counterclockwise lower semicircle arc of the scalar Cauchy kernel, from
`-T` to `T`. -/
noncomputable def scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral
    (p : ℂ) (T : ℝ) : ℂ :=
  ∫ θ in (-Real.pi)..(0 : ℝ),
    let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
    ((z - p)⁻¹) *
      (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Upper semicircle arc of the scalar Cauchy kernel, from `T` to `-T`. -/
noncomputable def scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral
    (p : ℂ) (T : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
    ((z - p)⁻¹) *
      (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Clockwise lower semicircle arc of the scalar Cauchy kernel, from `T` to
`-T`, matching the lower half-disk boundary parametrization. -/
noncomputable def scalarFourierLaplacePlemelj_upperWinding_lowerClockwiseArcIntegral
    (p : ℂ) (T : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(-Real.pi),
    let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
    ((z - p)⁻¹) *
      (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Real diameter contribution of the scalar Cauchy kernel. -/
noncomputable def scalarFourierLaplacePlemelj_upperWinding_realDiameterIntegral
    (p : ℂ) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-T) T, (((t : ℂ) - p)⁻¹)

/-- Mathlib's circle-integral integrand for the scalar Cauchy kernel. -/
noncomputable def scalarFourierLaplacePlemelj_upperWinding_circleIntegrand
    (p : ℂ) (T : ℝ) (θ : ℝ) : ℂ :=
  deriv (circleMap (0 : ℂ) T) θ *
    ((circleMap (0 : ℂ) T θ - p)⁻¹)

/-- The scalar arc integrand used in this file agrees pointwise with
mathlib's circle-integral integrand. -/
theorem scalarFourierLaplacePlemelj_upperWinding_arcIntegrand_eq_circleIntegrand
    (T : ℝ) (p : ℂ) (θ : ℝ) :
    (let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      ((z - p)⁻¹) *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ := by
  let z₁ : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  let z₂ : ℂ := circleMap (0 : ℂ) T θ
  have hexp :
      Complex.exp (Complex.I * (θ : ℂ)) =
        Complex.exp ((θ : ℂ) * Complex.I) := by
    exact congrArg Complex.exp (mul_comm Complex.I (θ : ℂ))
  have hz :
      z₁ = z₂ := by
    calc
      z₁ = (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
        rfl
      _ = (T : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
        exact congrArg (fun W : ℂ => (T : ℂ) * W) hexp
      _ = circleMap (0 : ℂ) T θ := by
        exact (circleMap_zero T θ).symm
  have hderiv :
      deriv (circleMap (0 : ℂ) T) θ =
        z₂ * Complex.I := by
    exact deriv_circleMap (0 : ℂ) T θ
  calc
    (let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      ((z - p)⁻¹) *
        (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        (z₁ - p)⁻¹ * (Complex.I * z₁) := by
      rfl
    _ = (z₂ - p)⁻¹ * (Complex.I * z₂) := by
      exact congrArg
        (fun W : ℂ => (W - p)⁻¹ * (Complex.I * W))
        hz
    _ = (z₂ * Complex.I) * ((z₂ - p)⁻¹) := by
      calc
        (z₂ - p)⁻¹ * (Complex.I * z₂) =
            (z₂ - p)⁻¹ * (z₂ * Complex.I) := by
          exact congrArg (fun W : ℂ => (z₂ - p)⁻¹ * W)
            (mul_comm Complex.I z₂)
        _ = (z₂ * Complex.I) * ((z₂ - p)⁻¹) := by
          exact mul_comm (z₂ - p)⁻¹ (z₂ * Complex.I)
    _ = deriv (circleMap (0 : ℂ) T) θ * ((circleMap (0 : ℂ) T θ - p)⁻¹) := by
      exact congrArg
        (fun W : ℂ => W * ((circleMap (0 : ℂ) T θ - p)⁻¹))
        hderiv.symm
    _ = scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ := by
      rfl

/-- The upper arc integrand is mathlib's scalar circle-integral integrand on
`0..π`. -/
theorem scalarFourierLaplacePlemelj_upperWinding_upperArc_eq_circleIntegrand
    (T : ℝ) (p : ℂ) :
    scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral p T =
      ∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ := by
  unfold scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral
  exact
    intervalIntegral.integral_congr
      (fun θ _hθ =>
        scalarFourierLaplacePlemelj_upperWinding_arcIntegrand_eq_circleIntegrand
          T p θ)

/-- The lower counterclockwise arc integrand is mathlib's scalar
circle-integral integrand on `-π..0`. -/
theorem scalarFourierLaplacePlemelj_upperWinding_lowerCounterArc_eq_circleIntegrand
    (T : ℝ) (p : ℂ) :
    scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral p T =
      ∫ θ in (-Real.pi)..(0 : ℝ),
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ := by
  unfold scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral
  exact
    intervalIntegral.integral_congr
      (fun θ _hθ =>
        scalarFourierLaplacePlemelj_upperWinding_arcIntegrand_eq_circleIntegrand
          T p θ)

/-- The full circle integral is the circle-integral integrand over `0..2π`. -/
theorem scalarFourierLaplacePlemelj_upperWinding_fullCircle_eq_integral_zero_two_pi
    (T : ℝ) (p : ℂ) :
    scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral p T =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ := by
  unfold scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral
  unfold scalarFourierLaplacePlemelj_upperWinding_circleIntegrand
  rfl

/-- The scalar circle-integral integrand is `2π`-periodic. -/
theorem scalarFourierLaplacePlemelj_upperWinding_circleIntegrand_periodic_two_pi
    (T : ℝ) (p : ℂ) :
    Function.Periodic
      (fun θ : ℝ =>
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ)
      (2 * Real.pi) := by
  intro θ
  let z₀ : ℂ := circleMap (0 : ℂ) T θ
  let z₁ : ℂ := circleMap (0 : ℂ) T (θ + 2 * Real.pi)
  have hz : z₁ = z₀ :=
    periodic_circleMap (0 : ℂ) T θ
  have hderiv₁ :
      deriv (circleMap (0 : ℂ) T) (θ + 2 * Real.pi) =
        z₁ * Complex.I := by
    exact deriv_circleMap (0 : ℂ) T (θ + 2 * Real.pi)
  have hderiv₀ :
      deriv (circleMap (0 : ℂ) T) θ =
        z₀ * Complex.I := by
    exact deriv_circleMap (0 : ℂ) T θ
  calc
    scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T
        (θ + 2 * Real.pi) =
        deriv (circleMap (0 : ℂ) T) (θ + 2 * Real.pi) *
          ((circleMap (0 : ℂ) T (θ + 2 * Real.pi) - p)⁻¹) := by
      rfl
    _ = (z₁ * Complex.I) * ((z₁ - p)⁻¹) := by
      exact congrArg₂ HMul.hMul hderiv₁
        (congrArg (fun W : ℂ => (W - p)⁻¹) rfl)
    _ = (z₀ * Complex.I) * ((z₀ - p)⁻¹) := by
      exact congrArg
        (fun W : ℂ => (W * Complex.I) * ((W - p)⁻¹))
        hz
    _ = deriv (circleMap (0 : ℂ) T) θ *
          ((circleMap (0 : ℂ) T θ - p)⁻¹) := by
      exact congrArg₂ HMul.hMul hderiv₀.symm
        (congrArg (fun W : ℂ => (W - p)⁻¹) rfl)
    _ =
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ := by
      rfl

/-- The `π..2π` part of the circle integral is the shifted lower
counterclockwise arc. -/
theorem scalarFourierLaplacePlemelj_upperWinding_integral_pi_two_pi_eq_lowerCounter
    (T : ℝ) (_hT : 0 < T) (p : ℂ) (_hp : ‖p‖ < T) :
    (∫ θ in Real.pi..(2 * Real.pi),
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ) =
      scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral p T := by
  have hshift :
      (∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T
            (θ + 2 * Real.pi)) =
        ∫ θ in Real.pi..(2 * Real.pi),
          scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ := by
    exact
      intervalIntegral.integral_comp_add_right
        (fun θ : ℝ =>
          scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ)
        (2 * Real.pi)
  have hperiodic :
      (∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T
            (θ + 2 * Real.pi)) =
        ∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ :=
    intervalIntegral.integral_congr
      (fun θ _hθ =>
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand_periodic_two_pi
          T p θ)
  calc
    (∫ θ in Real.pi..(2 * Real.pi),
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ) =
        (∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T
            (θ + 2 * Real.pi)) := by
      exact hshift.symm
    _ =
        ∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ := by
      exact hperiodic
    _ = scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral p T := by
      exact
        (scalarFourierLaplacePlemelj_upperWinding_lowerCounterArc_eq_circleIntegrand
          T p).symm

/-- The `0..π` part of the circle integral is the upper arc. -/
theorem scalarFourierLaplacePlemelj_upperWinding_integral_zero_pi_eq_upperArc
    (T : ℝ) (p : ℂ) :
    (∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ) =
      scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral p T := by
  exact
    (scalarFourierLaplacePlemelj_upperWinding_upperArc_eq_circleIntegrand
      T p).symm

/-- The scalar circle-integral integrand is continuous on every real interval
when the pole lies strictly inside the radius-`T` circle. -/
theorem scalarFourierLaplacePlemelj_upperWinding_circleIntegrand_continuousOn_Icc
    (T : ℝ) (_hT : 0 < T) (p : ℂ) (_hp : ‖p‖ < T)
    (a b : ℝ) :
    ContinuousOn
      (fun θ : ℝ =>
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ)
      (Set.Icc a b) := by
  have hp_ball : p ∈ Metric.ball (0 : ℂ) T := by
    exact
      Eq.subst
        (motive := fun r : ℝ => r < T)
        (dist_zero_right p).symm
        _hp
  have hcircle :
      Continuous
        (fun θ : ℝ => circleMap (0 : ℂ) T θ * Complex.I) :=
    (continuous_circleMap (0 : ℂ) T).mul continuous_const
  have hinv :
      Continuous
        (fun θ : ℝ => (circleMap (0 : ℂ) T θ - p)⁻¹) :=
    continuous_circleMap_inv hp_ball
  have hprod :
      Continuous
        (fun θ : ℝ =>
          (circleMap (0 : ℂ) T θ * Complex.I) *
            (circleMap (0 : ℂ) T θ - p)⁻¹) :=
    hcircle.mul hinv
  have heq :
      (fun θ : ℝ =>
        (circleMap (0 : ℂ) T θ * Complex.I) *
          (circleMap (0 : ℂ) T θ - p)⁻¹) =
        fun θ : ℝ =>
          scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ :=
    funext
      (fun θ : ℝ =>
        Eq.trans
          (congrArg
            (fun W : ℂ => W * (circleMap (0 : ℂ) T θ - p)⁻¹)
            (deriv_circleMap (0 : ℂ) T θ).symm)
          (show
            deriv (circleMap (0 : ℂ) T) θ *
                (circleMap (0 : ℂ) T θ - p)⁻¹ =
              scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ
            from rfl))
  exact
    Eq.subst
      (motive := fun f : ℝ → ℂ => ContinuousOn f (Set.Icc a b))
      heq
      hprod.continuousOn

/-- The scalar circle-integral integrand is interval-integrable on the upper
semicircle. -/
theorem scalarFourierLaplacePlemelj_upperWinding_circleIntegrand_intervalIntegrable_zero_pi
    (T : ℝ) (_hT : 0 < T) (p : ℂ) (_hp : ‖p‖ < T) :
    IntervalIntegrable
      (fun θ : ℝ =>
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ)
      MeasureTheory.volume
      (0 : ℝ)
      Real.pi := by
  exact
    ContinuousOn.intervalIntegrable_of_Icc
      (show (0 : ℝ) ≤ Real.pi from Real.pi_nonneg)
      (scalarFourierLaplacePlemelj_upperWinding_circleIntegrand_continuousOn_Icc
        T _hT p _hp (0 : ℝ) Real.pi)

/-- The scalar circle-integral integrand is interval-integrable on the shifted
lower semicircle. -/
theorem scalarFourierLaplacePlemelj_upperWinding_circleIntegrand_intervalIntegrable_pi_two_pi
    (T : ℝ) (_hT : 0 < T) (p : ℂ) (_hp : ‖p‖ < T) :
    IntervalIntegrable
      (fun θ : ℝ =>
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ)
      MeasureTheory.volume
      Real.pi
      (2 * Real.pi) := by
  exact
    ContinuousOn.intervalIntegrable_of_Icc
      (show Real.pi ≤ 2 * Real.pi from
        le_mul_of_one_le_left Real.pi_nonneg (one_le_two : (1 : ℝ) ≤ 2))
      (scalarFourierLaplacePlemelj_upperWinding_circleIntegrand_continuousOn_Icc
        T _hT p _hp Real.pi (2 * Real.pi))

/-- Interval additivity splits the full circle integral at `π`. -/
theorem scalarFourierLaplacePlemelj_upperWinding_integral_zero_two_pi_split_at_pi
    (T : ℝ) (_hT : 0 < T) (p : ℂ) (_hp : ‖p‖ < T) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ) =
      (∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ) +
      (∫ θ in Real.pi..(2 * Real.pi),
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ) := by
  exact
    (intervalIntegral.integral_add_adjacent_intervals
      (scalarFourierLaplacePlemelj_upperWinding_circleIntegrand_intervalIntegrable_zero_pi
        T _hT p _hp)
      (scalarFourierLaplacePlemelj_upperWinding_circleIntegrand_intervalIntegrable_pi_two_pi
        T _hT p _hp)).symm

/-- Splitting the full circle integral at `π` gives the upper and shifted
lower semicircles. -/
theorem scalarFourierLaplacePlemelj_upperWinding_integral_zero_two_pi_eq_upper_add_lowerCounter
    (T : ℝ) (_hT : 0 < T) (p : ℂ) (_hp : ‖p‖ < T) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ) =
      scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral p T +
        scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral p T := by
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ) =
        (∫ θ in (0 : ℝ)..Real.pi,
          scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ) +
        (∫ θ in Real.pi..(2 * Real.pi),
          scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ) := by
      exact
        scalarFourierLaplacePlemelj_upperWinding_integral_zero_two_pi_split_at_pi
          T _hT p _hp
    _ =
        scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral p T +
          (∫ θ in Real.pi..(2 * Real.pi),
            scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ) := by
      exact congrArg
        (fun W : ℂ =>
          W +
          (∫ θ in Real.pi..(2 * Real.pi),
            scalarFourierLaplacePlemelj_upperWinding_circleIntegrand p T θ))
        (scalarFourierLaplacePlemelj_upperWinding_integral_zero_pi_eq_upperArc
          T p)
    _ =
        scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral p T +
          scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral p T := by
      exact congrArg
        (fun W : ℂ =>
          scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral p T + W)
        (scalarFourierLaplacePlemelj_upperWinding_integral_pi_two_pi_eq_lowerCounter
          T _hT p _hp)

/-- The upper-winding auxiliary lower boundary is the generic lower half-disk
boundary integral specialized to the scalar Cauchy kernel. -/
theorem scalarFourierLaplacePlemelj_upperWinding_lowerBoundary_eq_lowerHalfDiskBoundaryIntegral
    (T : ℝ) (p : ℂ) :
    scalarFourierLaplacePlemelj_upperWinding_lowerHalfDiskBoundaryIntegral p T =
      scalarFourierLaplacePlemelj_lowerHalfDiskBoundaryIntegral
        (fun z : ℂ => (z - p)⁻¹) T := by
  rfl

/-- A point in the closed lower half-disk cannot equal a point strictly above
the real axis. -/
theorem scalarFourierLaplacePlemelj_upperWinding_lowerHalfDisk_point_ne_upperPole
    (T : ℝ) (p z : ℂ)
    (_hz : z ∈ scalarFourierLaplacePlemelj_lowerHalfDisk T)
    (_hp_upper : 0 < Complex.im p) :
    z ≠ p := by
  intro hzp
  have hp_im_le_zero : Complex.im p ≤ 0 := by
    exact
      Eq.subst
        (motive := fun w : ℂ => Complex.im w ≤ 0)
        hzp
        _hz.2
  exact (not_le_of_gt _hp_upper) hp_im_le_zero

/-- The scalar Cauchy kernel has no pole on the closed lower half-disk when
the pole lies strictly in the upper half-plane. -/
theorem scalarFourierLaplacePlemelj_upperWinding_cauchyKernel_analyticAt_lowerHalfDisk
    (T : ℝ) (p : ℂ) (_hp_upper : 0 < Complex.im p) :
    ∀ z ∈ scalarFourierLaplacePlemelj_lowerHalfDisk T,
      AnalyticAt ℂ (fun w : ℂ => (w - p)⁻¹) z := by
  intro z hz
  have hden :
      AnalyticAt ℂ (fun w : ℂ => w - p) z :=
    analyticAt_id.sub analyticAt_const
  have hden_ne :
      (fun w : ℂ => w - p) z ≠ 0 := by
    exact
      sub_ne_zero.mpr
        (scalarFourierLaplacePlemelj_upperWinding_lowerHalfDisk_point_ne_upperPole
          T p z hz _hp_upper)
  exact hden.inv hden_ne

/-- The scalar Cauchy kernel has zero lower half-disk boundary integral when
the pole lies strictly in the upper half-disk. -/
theorem scalarFourierLaplacePlemelj_upperWinding_lowerHalfDiskBoundaryIntegral_eq_zero
    (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p) :
    scalarFourierLaplacePlemelj_upperWinding_lowerHalfDiskBoundaryIntegral p T = 0 := by
  exact
    (scalarFourierLaplacePlemelj_upperWinding_lowerBoundary_eq_lowerHalfDiskBoundaryIntegral
      T p).trans
      (scalarFourierLaplacePlemelj_lowerHalfDiskBoundaryIntegral_eq_zero_of_analyticAt
        (fun z : ℂ => (z - p)⁻¹)
        T
        _hT.le
        (scalarFourierLaplacePlemelj_upperWinding_cauchyKernel_analyticAt_lowerHalfDisk
          T p _hp_upper))

/-- The full circle boundary integral of the scalar Cauchy kernel is `2πi`
for a pole inside the radius-`T` circle. -/
theorem scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral_eq_two_pi_i
    (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) :
    scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral p T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  unfold scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral
  have hp_ball : p ∈ Metric.ball (0 : ℂ) T := by
    exact
      Eq.subst
        (motive := fun r : ℝ => r < T)
        (dist_zero_right p).symm
        _hp
  exact circleIntegral.integral_sub_inv_of_mem_ball hp_ball

/-- The mathlib full circle integral splits into the lower counterclockwise
semicircle plus the upper semicircle. -/
theorem scalarFourierLaplacePlemelj_upperWinding_fullCircle_eq_upperArc_add_shiftedLowerArc
    (T : ℝ) (_hT : 0 < T) (p : ℂ) (_hp : ‖p‖ < T) :
    scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral p T =
      scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral p T +
        scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral p T := by
  exact
    (scalarFourierLaplacePlemelj_upperWinding_fullCircle_eq_integral_zero_two_pi
      T p).trans
      (scalarFourierLaplacePlemelj_upperWinding_integral_zero_two_pi_eq_upper_add_lowerCounter
        T _hT p _hp)

/-- Reordering of the two semicircle contributions in the full-circle split. -/
theorem scalarFourierLaplacePlemelj_upperWinding_upper_add_lowerCounter_eq_lowerCounter_add_upper
    (T : ℝ) (p : ℂ) :
    scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral p T +
        scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral p T =
      scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral p T +
        scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral p T := by
  exact
    add_comm
      (scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral p T)
      (scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral p T)

/-- The mathlib full circle integral splits into the lower counterclockwise
semicircle plus the upper semicircle. -/
theorem scalarFourierLaplacePlemelj_upperWinding_fullCircle_eq_lowerCounter_add_upperArc
    (T : ℝ) (_hT : 0 < T) (p : ℂ) (_hp : ‖p‖ < T) :
    scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral p T =
      scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral p T +
        scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral p T := by
  exact
    (scalarFourierLaplacePlemelj_upperWinding_fullCircle_eq_upperArc_add_shiftedLowerArc
      T _hT p _hp).trans
      (scalarFourierLaplacePlemelj_upperWinding_upper_add_lowerCounter_eq_lowerCounter_add_upper
        T p)

/-- The counterclockwise lower arc is the negative of the clockwise lower arc
with the same parametrized integrand. -/
theorem scalarFourierLaplacePlemelj_upperWinding_lowerCounterArc_eq_neg_lowerClockwiseArc
    (T : ℝ) (p : ℂ) :
    scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral p T =
      -scalarFourierLaplacePlemelj_upperWinding_lowerClockwiseArcIntegral p T := by
  unfold scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral
  unfold scalarFourierLaplacePlemelj_upperWinding_lowerClockwiseArcIntegral
  exact intervalIntegral.integral_symm (0 : ℝ) (-Real.pi)

/-- The scalar lower half-disk boundary is the real diameter plus the clockwise
lower semicircle. -/
theorem scalarFourierLaplacePlemelj_upperWinding_lowerBoundary_eq_real_add_lowerClockwise
    (T : ℝ) (p : ℂ) :
    scalarFourierLaplacePlemelj_upperWinding_lowerHalfDiskBoundaryIntegral p T =
      scalarFourierLaplacePlemelj_upperWinding_realDiameterIntegral p T +
        scalarFourierLaplacePlemelj_upperWinding_lowerClockwiseArcIntegral p T := by
  rfl

/-- The scalar upper half-disk boundary is the real diameter plus the upper
semicircle. -/
theorem scalarFourierLaplacePlemelj_upperWinding_upperBoundary_eq_real_add_upperArc
    (T : ℝ) (p : ℂ) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (fun z : ℂ => (z - p)⁻¹) T =
      scalarFourierLaplacePlemelj_upperWinding_realDiameterIntegral p T +
        scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral p T := by
  rfl

/-- Algebraic assembly of the upper boundary from the full circle and lower
clockwise boundary, once the full circle has been split into semicircles. -/
theorem scalarFourierLaplacePlemelj_upperWinding_boundary_assembly_algebra
    (R U Lc : ℂ) :
    R + U = ((-Lc) + U) + (R + Lc) := by
  calc
    R + U = U + R := by
      exact add_comm R U
    _ = U + (R + (Lc + -Lc)) := by
      exact congrArg (fun W : ℂ => U + (R + W)) (add_right_neg Lc).symm
    _ = U + ((R + Lc) + -Lc) := by
      exact congrArg (fun W : ℂ => U + W) (add_assoc R Lc (-Lc)).symm
    _ = (U + -Lc) + (R + Lc) := by
      exact
        Eq.trans
          (add_assoc U (R + Lc) (-Lc))
          (Eq.trans
            (congrArg (fun W : ℂ => W + -Lc) (add_comm U (R + Lc)))
            (add_assoc (R + Lc) U (-Lc)).symm)
    _ = ((-Lc) + U) + (R + Lc) := by
      exact congrArg
        (fun W : ℂ => W + (R + Lc))
        (add_comm U (-Lc))

/-- The upper half-disk boundary integral is the full circle integral plus the
clockwise lower no-pole boundary contribution.  The sign comes from the lower
arc parametrization `0` to `-π`. -/
theorem scalarFourierLaplacePlemelj_upperWinding_boundaryIntegral_eq_fullCircle_add_lower
    (T : ℝ) (p : ℂ) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (fun z : ℂ => (z - p)⁻¹) T =
      scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral p T +
        scalarFourierLaplacePlemelj_upperWinding_lowerHalfDiskBoundaryIntegral p T := by
  let R : ℂ := scalarFourierLaplacePlemelj_upperWinding_realDiameterIntegral p T
  let U : ℂ := scalarFourierLaplacePlemelj_upperWinding_upperArcIntegral p T
  let Lc : ℂ := scalarFourierLaplacePlemelj_upperWinding_lowerClockwiseArcIntegral p T
  let Lccw : ℂ := scalarFourierLaplacePlemelj_upperWinding_lowerCounterArcIntegral p T
  have hupper :
      scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
          (fun z : ℂ => (z - p)⁻¹) T =
        R + U :=
    scalarFourierLaplacePlemelj_upperWinding_upperBoundary_eq_real_add_upperArc
      T p
  have hfull :
    scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral p T =
        Lccw + U :=
    scalarFourierLaplacePlemelj_upperWinding_fullCircle_eq_lowerCounter_add_upperArc
      T _hT p _hp
  have hlowerCounter :
      Lccw = -Lc :=
    scalarFourierLaplacePlemelj_upperWinding_lowerCounterArc_eq_neg_lowerClockwiseArc
      T p
  have hlower :
      scalarFourierLaplacePlemelj_upperWinding_lowerHalfDiskBoundaryIntegral p T =
        R + Lc :=
    scalarFourierLaplacePlemelj_upperWinding_lowerBoundary_eq_real_add_lowerClockwise
      T p
  calc
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (fun z : ℂ => (z - p)⁻¹) T =
        R + U := by
      exact hupper
    _ = ((-Lc) + U) + (R + Lc) := by
      exact scalarFourierLaplacePlemelj_upperWinding_boundary_assembly_algebra
        R U Lc
    _ = (Lccw + U) + (R + Lc) := by
      exact congrArg
        (fun W : ℂ => (W + U) + (R + Lc))
        hlowerCounter.symm
    _ =
        scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral p T +
          (R + Lc) := by
      exact congrArg
        (fun W : ℂ => W + (R + Lc))
        hfull.symm
    _ =
        scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral p T +
          scalarFourierLaplacePlemelj_upperWinding_lowerHalfDiskBoundaryIntegral p T := by
      exact congrArg
        (fun W : ℂ =>
          scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral p T + W)
        hlower.symm

/-- The upper half-disk boundary has winding number one around any point in
the strict upper half-disk. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_boundary_winding_one
    (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (fun z : ℂ => (z - p)⁻¹) T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  calc
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (fun z : ℂ => (z - p)⁻¹) T =
        scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral p T +
          scalarFourierLaplacePlemelj_upperWinding_lowerHalfDiskBoundaryIntegral p T := by
      exact
        scalarFourierLaplacePlemelj_upperWinding_boundaryIntegral_eq_fullCircle_add_lower
          T p
    _ =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) +
          scalarFourierLaplacePlemelj_upperWinding_lowerHalfDiskBoundaryIntegral p T := by
      exact congrArg
        (fun W : ℂ =>
          W + scalarFourierLaplacePlemelj_upperWinding_lowerHalfDiskBoundaryIntegral p T)
        (scalarFourierLaplacePlemelj_upperWinding_fullCircleBoundaryIntegral_eq_two_pi_i
          T _hT p _hp)
    _ = ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) + 0 := by
      exact congrArg
        (fun W : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) + W)
        (scalarFourierLaplacePlemelj_upperWinding_lowerHalfDiskBoundaryIntegral_eq_zero
          T _hT p _hp _hp_upper)
    _ = ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
      exact add_zero ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)

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

end FixedLineCauchyProjection

end
end Boundary
