import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.PositiveContour.Winding
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RemovableSingularity

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection
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
      (scalarFourierLaplacePlemelj_upperHalfDisk T))
    (_hanalytic :
      ∀ z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
        AnalyticAt ℂ F z) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (fun z : ℂ => F z / (z - p)) T =
      scalarFourierLaplacePlemelj_upperHalfDiskSimplePoleResidueContribution
        F p := by
  exact
    (scalarFourierLaplacePlemelj_upperHalfDisk_cauchyKernel_boundaryIntegral_decompose
      F T _hT p _hp _hp_upper _hdiff).trans
      ((congrArg₂ HAdd.hAdd
        (scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_boundaryIntegral_eq_zero
          F T _hT p _hp _hp_upper _hanalytic)
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
      (scalarFourierLaplacePlemelj_upperHalfDisk T))
    (_hanalytic :
      ∀ z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
        AnalyticAt ℂ F z) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (fun z : ℂ => F z / (z - p)) T =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * F p := by
  exact
    Eq.trans
      (scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral_eq_simplePoleResidueContribution
        F T _hT p _hp _hp_upper _hdiff _hanalytic)
      (scalarFourierLaplacePlemelj_upperHalfDiskSimplePoleResidueContribution_eq
        F p)

/-- Scalar complex algebra behind the normalized Cauchy denominator:
`-1 / (I * D) = I / D`. -/

end FixedLineCauchyProjection

end
end Boundary
