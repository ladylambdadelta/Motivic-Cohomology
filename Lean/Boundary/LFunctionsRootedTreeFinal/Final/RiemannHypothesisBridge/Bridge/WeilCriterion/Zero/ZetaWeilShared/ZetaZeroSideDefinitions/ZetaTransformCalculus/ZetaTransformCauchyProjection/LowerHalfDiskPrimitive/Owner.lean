import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.FixedLineTails.Owner

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection
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

end FixedLineCauchyProjection

end
end Boundary
