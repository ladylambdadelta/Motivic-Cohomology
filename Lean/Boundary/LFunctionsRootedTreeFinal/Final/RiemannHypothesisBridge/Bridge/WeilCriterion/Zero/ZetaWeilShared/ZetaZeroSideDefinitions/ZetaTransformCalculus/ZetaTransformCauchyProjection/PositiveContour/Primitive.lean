import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.PositiveContour.Base
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RemovableSingularity

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection
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

/-- Strict interior of the upper half-disk, expressed by the two strict
inequalities that make the closed constraints neighborhoods. -/

end FixedLineCauchyProjection

end
end Boundary
