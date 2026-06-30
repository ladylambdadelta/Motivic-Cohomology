import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.PositiveContour.Primitive
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RemovableSingularity

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection
def scalarFourierLaplacePlemelj_upperHalfDiskStrictInterior
    (T : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ < T ∧ 0 < Complex.im z}

/-- Points in the strict upper half-disk belong to the closed upper half-disk. -/
theorem scalarFourierLaplacePlemelj_upperHalfDiskStrictInterior_subset_upperHalfDisk
    (T : ℝ) :
    scalarFourierLaplacePlemelj_upperHalfDiskStrictInterior T ⊆
      scalarFourierLaplacePlemelj_upperHalfDisk T := by
  intro z hz
  exact
    And.intro
      (le_of_lt hz.1)
      (le_of_lt hz.2)

/-- A strict-interior point has the closed upper half-disk as a neighborhood. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_mem_nhds_of_strictInterior
    (T : ℝ) (z : ℂ)
    (_hz : z ∈ scalarFourierLaplacePlemelj_upperHalfDiskStrictInterior T) :
    scalarFourierLaplacePlemelj_upperHalfDisk T ∈ 𝓝 z := by
  exact
    scalarFourierLaplacePlemelj_upperHalfDisk_mem_nhds_of_norm_lt_im_pos
      T z _hz.1 _hz.2

/-- The removable Cauchy regular part is analytic on the closed upper
half-disk when the numerator is analytic there. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_analyticAt
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hanalytic :
      ∀ z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
        AnalyticAt ℂ F z) :
    ∀ z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
      AnalyticAt ℂ
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p)
        z := by
  intro z hz
  match Classical.em (z = p) with
  | Or.inl hzp =>
      have hp_mem :
          p ∈ scalarFourierLaplacePlemelj_upperHalfDisk T :=
        And.intro
          (le_of_lt _hp)
          (le_of_lt _hp_upper)
      match _hanalytic p hp_mem with
      | ⟨P, hP⟩ =>
          exact
            Eq.subst
              (motive := fun q : ℂ =>
                AnalyticAt ℂ
                  (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p)
                  q)
              hzp.symm
              ((HasFPowerSeriesAt.has_fpower_series_dslope_fslope hP).analyticAt)
  | Or.inr hzp =>
      have hquot_analytic :
          AnalyticAt ℂ (fun w : ℂ => (F w - F p) / (w - p)) z := by
        have hnum :
            AnalyticAt ℂ (fun w : ℂ => F w - F p) z :=
          (_hanalytic z hz).sub analyticAt_const
        have hden :
            AnalyticAt ℂ (fun w : ℂ => w - p) z :=
          analyticAt_id.sub analyticAt_const
        have hden_ne :
            (fun w : ℂ => w - p) z ≠ 0 :=
          sub_ne_zero.mpr hzp
        exact hnum.div hden hden_ne
      have hlocal :
          (fun w : ℂ => (F w - F p) / (w - p)) =ᶠ[𝓝 z]
            scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p := by
        exact
          (dslope_eventuallyEq_slope_of_ne (f := F) hzp).mono
            (fun w hw =>
              Eq.trans
                (slope_def_field F p w).symm
                hw.symm)
      exact hquot_analytic.congr hlocal

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
    (_hanalytic :
      ∀ z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
        AnalyticAt ℂ F z) :
    ∀ z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
      HasDerivWithinAt
        (LFunctions.complex_centerSegmentIntegral
          (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p))
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p z)
        (scalarFourierLaplacePlemelj_upperHalfDisk T)
        z := by
  intro z hz
  let R : ℂ → ℂ :=
    scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p
  let G : ℂ → ℂ := LFunctions.complex_centerSegmentIntegral R
  have hregular_analytic :
      ∀ w ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
        AnalyticAt ℂ R w :=
    scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_analyticAt
      F T _hT p _hp _hp_upper _hanalytic
  have hprimitive :
      ∀ w : ℂ,
        w ∈ scalarFourierLaplacePlemelj_upperHalfDisk T →
          AnalyticAt ℂ G w ∧ HasDerivAt G (R w) w := by
    exact
      LFunctions.complex_centerSegmentIntegral_parametricPrimitive_of_holomorphicOn_starConvex
        R
        (scalarFourierLaplacePlemelj_upperHalfDisk_starConvex T (le_of_lt _hT))
        hregular_analytic
  exact
    (hprimitive z hz).2.hasDerivWithinAt

/-- The center-segment integral is primitive data for the removable Cauchy
regular part on the upper half-disk. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_centerSegmentPrimitive
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hanalytic :
      ∀ z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
        AnalyticAt ℂ F z) :
    scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk
      (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p)
      (LFunctions.complex_centerSegmentIntegral
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p))
      T := by
  exact
    And.intro
      (scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_continuousOn
        F T _hT p _hp _hp_upper
        (fun z hz => (_hanalytic z hz).differentiableAt.differentiableWithinAt))
      (scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_centerSegmentPrimitive_hasDerivWithinAt
        F T _hT p _hp _hp_upper _hanalytic)

/-- The regular part of the Cauchy kernel has primitive data on the upper
half-disk. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_hasPrimitive
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hanalytic :
      ∀ z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
        AnalyticAt ℂ F z) :
    ∃ G : ℂ → ℂ,
      scalarFourierLaplacePlemelj_hasPrimitiveOnUpperHalfDisk
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p)
        G T := by
  exact
    Exists.intro
      (LFunctions.complex_centerSegmentIntegral
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p))
      (scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_centerSegmentPrimitive
        F T _hT p _hp _hp_upper _hanalytic)

/-- The regular part of the simple-pole Cauchy kernel has zero boundary
integral on the upper half-disk.  This is the removable-singularity branch of
the residue proof: after subtracting `F p`, the numerator vanishes at `p`, so
the quotient extends holomorphically through the pole and has a primitive on
the star-convex upper half-disk. -/
theorem scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_boundaryIntegral_eq_zero
    (F : ℂ → ℂ) (T : ℝ) (_hT : 0 < T) (p : ℂ)
    (_hp : ‖p‖ < T) (_hp_upper : 0 < Complex.im p)
    (_hanalytic :
      ∀ z ∈ scalarFourierLaplacePlemelj_upperHalfDisk T,
        AnalyticAt ℂ F z) :
    scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral
        (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p) T = 0 := by
  match
    scalarFourierLaplacePlemelj_upperHalfDisk_regularPart_hasPrimitive
      F T _hT p _hp _hp_upper _hanalytic with
  | ⟨G, hprimitive⟩ =>
      exact
        scalarFourierLaplacePlemelj_upperHalfDiskBoundaryIntegral_eq_zero_of_hasPrimitive
          (scalarFourierLaplacePlemelj_upperHalfDiskCauchyRegularPart F p)
          G T _hT hprimitive

end FixedLineCauchyProjection

end
end Boundary
