import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.VerticalChannels.Owner

/-!
# Explicit-formula contour assembly

This owner layer contains final contour identity compatibility wrappers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The completed zeta contour integrand is compatible with the rectangle theorem
surface once differentiability hypotheses are supplied. -/
theorem zetaCompletedExplicitFormulaRectangleBoundaryIdentity
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (f' : ℂ → (ℂ →L[ℝ] ℂ))
    (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (Set.uIcc (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re ×ℂ
        Set.uIcc (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im))
    (Hd : ∀ x, x ∈ Set.Ioo (min (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re)
        (max (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re) ×ℂ
        Set.Ioo (min (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im)
          (max (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im) \ s →
        HasFDerivAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) (f' x) x)
    (Hi : IntegrableOn
      (fun z => Complex.I • ⇑(f' z) 1 - ⇑(f' z) Complex.I)
      (Set.uIcc (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re ×ℂ
        Set.uIcc (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im) volume) :
    (((∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (r.c + (-r.T) * Complex.I).im * Complex.I)) -
        ∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (r.c + (r.T) * Complex.I).im * Complex.I)) +
      Complex.I • ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
        zetaCompletedExplicitFormulaContourIntegrand f
          ((r.c + (r.T) * Complex.I).re + y * Complex.I)) -
      Complex.I • ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
        zetaCompletedExplicitFormulaContourIntegrand f
          ((r.c + (-r.T) * Complex.I).re + y * Complex.I)
      =
      ∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
        ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
          Complex.I • ⇑(f' (x + y * Complex.I)) 1 - ⇑(f' (x + y * Complex.I)) Complex.I :=
  Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable
    (f := fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
    (f' := f') (z := r.c + (-r.T) * Complex.I) (w := r.c + (r.T) * Complex.I)
    (s := s) (hs := hs) (Hc := Hc) (Hd := Hd) (Hi := Hi)

/-- Four-side contour algebra: the signed rectangle integral is the vertical difference
plus the horizontal difference. -/
theorem complex_four_side_contour_split
    (R L T B : ℂ) :
    R - L + T - B = (R - L) + (T - B) := by
  calc
    R - L + T - B = (R - L + T) + -B := by
      exact sub_eq_add_neg (R - L + T) B
    _ = (R - L) + (T + -B) := by
      exact add_assoc (R - L) T (-B)
    _ = (R - L) + (T - B) := by
      exact congrArg (fun z : ℂ => (R - L) + z)
        (sub_eq_add_neg T B).symm

/-- The contour integral splits into vertical and horizontal signed contributions. -/
theorem zetaCompletedExplicitFormulaContourIntegral_eq_vertical_add_horizontal
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaContourIntegral f r =
      (zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r) +
      (zetaCompletedExplicitFormulaTopLineIntegral f r -
        zetaCompletedExplicitFormulaBottomLineIntegral f r) := by
  change
    zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r +
        zetaCompletedExplicitFormulaTopLineIntegral f r -
          zetaCompletedExplicitFormulaBottomLineIntegral f r =
      (zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r) +
      (zetaCompletedExplicitFormulaTopLineIntegral f r -
        zetaCompletedExplicitFormulaBottomLineIntegral f r)
  exact complex_four_side_contour_split
    (zetaCompletedExplicitFormulaRightLineIntegral f r)
    (zetaCompletedExplicitFormulaLeftLineIntegral f r)
    (zetaCompletedExplicitFormulaTopLineIntegral f r)
    (zetaCompletedExplicitFormulaBottomLineIntegral f r)

/-- If residue calculus identifies the contour limit with the completed zero side, while
vertical and horizontal assembly identify the same contour limit with the analytic boundary
sum, then the analytic boundary sum is the completed zero-side residue sum. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_zeroSideComplex_of_contour_vertical_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hcontour :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)))
    (hvertical :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
    (hhorizontal :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
        atTop
        (𝓝 0)) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic f =
      zetaCompletedZeroSideComplex f := by
  have hsum :
      Tendsto
        (fun T : ℝ =>
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)) +
            (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
              zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f + 0)) :=
    hvertical.add hhorizontal
  have htarget :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f + 0 =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
    add_zero _
  have hboundary :
      Tendsto
        (fun T : ℝ =>
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)) +
            (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
              zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
                zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)) +
              (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
                zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)))
          atTop
          (𝓝 z))
      htarget
      hsum
  have hpointwise :
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T)) =
      (fun T : ℝ =>
        (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)) +
          (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))) := by
    funext T
    exact zetaCompletedExplicitFormulaContourIntegral_eq_vertical_add_horizontal
      f (F.rectangle T)
  have hcontourBoundary :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
      hpointwise.symm
      hboundary
  exact tendsto_nhds_unique hcontourBoundary hcontour

/-- Real-valued owner form of the completed explicit-formula assembly. -/
theorem zetaCompletedZeroKreinGram_eq_boundarySumAnalytic_re_of_contour_vertical_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hcontour :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)))
    (hvertical :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
    (hhorizontal :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
        atTop
        (𝓝 0)) :
    zetaCompletedZeroKreinGram f =
      Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
  have hcomplex :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        zetaCompletedZeroSideComplex f :=
    zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_zeroSideComplex_of_contour_vertical_horizontal
      f F hcontour hvertical hhorizontal
  calc
    zetaCompletedZeroKreinGram f =
        Complex.re (zetaCompletedZeroSideComplex f) := by
      rfl
    _ = Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
      exact congrArg Complex.re hcomplex.symm

/-- Scheduled contour assembly: if residue calculus, vertical decomposition, and
horizontal decay hold along the same height schedule, then the analytic boundary sum is
the completed zero-side residue sum. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_zeroSideComplex_of_scheduled_contour_vertical_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (height : ℝ → ℝ)
    (hcontour :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f (F.rectangle (height u)))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)))
    (hvertical :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle (height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle (height u)))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle (height u)) -
            zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle (height u)))
        atTop
        (𝓝 0)) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic f =
      zetaCompletedZeroSideComplex f := by
  have hsum :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle (height u)) -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle (height u))) +
            (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle (height u)) -
              zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle (height u))))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f + 0)) :=
    hvertical.add hhorizontal
  have htarget :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f + 0 =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
    add_zero _
  have hboundary :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle (height u)) -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle (height u))) +
            (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle (height u)) -
              zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle (height u))))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle (height u)) -
                zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle (height u))) +
              (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle (height u)) -
                zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle (height u))))
          atTop
          (𝓝 z))
      htarget
      hsum
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral f (F.rectangle (height u))) =
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle (height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle (height u))) +
          (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle (height u)) -
            zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle (height u)))) := by
    funext u
    exact zetaCompletedExplicitFormulaContourIntegral_eq_vertical_add_horizontal
      f (F.rectangle (height u))
  have hcontourBoundary :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f (F.rectangle (height u)))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
      hpointwise.symm
      hboundary
  exact tendsto_nhds_unique hcontourBoundary hcontour

/-- Real-valued scheduled owner form of the completed explicit-formula assembly. -/
theorem zetaCompletedZeroKreinGram_eq_boundarySumAnalytic_re_of_scheduled_contour_vertical_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (height : ℝ → ℝ)
    (hcontour :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f (F.rectangle (height u)))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)))
    (hvertical :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle (height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle (height u)))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle (height u)) -
            zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle (height u)))
        atTop
        (𝓝 0)) :
    zetaCompletedZeroKreinGram f =
      Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
  have hcomplex :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        zetaCompletedZeroSideComplex f :=
    zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_zeroSideComplex_of_scheduled_contour_vertical_horizontal
      f F height hcontour hvertical hhorizontal
  calc
    zetaCompletedZeroKreinGram f =
        Complex.re (zetaCompletedZeroSideComplex f) := by
      rfl
    _ = Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
      exact congrArg Complex.re hcomplex.symm

/-- Scheduled-carrier autocorrelation completed explicit-formula assembly: residue calculus,
vertical-channel decomposition, and scheduled horizontal decay identify the completed Weil
form with the completed boundary channel once the scheduled horizontal edge family has a
shared zero-excised carrier. -/
theorem zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_of_scheduledHorizontalCarrier_ownerContourAssembly
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f))
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u))
        atTop
        (𝓝 0))
    (hcontourScheduled :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral (convolutionAutocorrelation f)
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f schedule hPhi hLog).height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex (convolutionAutocorrelation f))))
    (E : CompletedZetaZeroExcisedStrip
      (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
      (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)))
    (hTopMem :
      ∀ (u x : ℝ),
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ),
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u)) x ∈ E.carrier) :
    zetaWeilFormCompleted (convolutionAutocorrelation f) =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  let g : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let F : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let h : ExplicitFormulaFamilyAnalyticPackage g F :=
    zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f schedule hPhi hLog
  have hweil :
      zetaWeilFormCompleted g =
        zetaCompletedZeroKreinGram g :=
    zetaWeilFormCompleted_eq_zeroKreinGram g
  have hverticalScheduled :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral g
              (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral g
              (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic g)) :=
    zetaCompletedExplicitFormula_autocorrelation_scheduledVertical_tendsto_boundarySum
      f schedule hPhi hLog hone
  have hhorizontalScheduled :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaTopLineIntegral g
              (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaBottomLineIntegral g
              (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormula_autocorrelation_horizontal_tendsto_zero_scheduled
      f h E hTopMem hBottomMem
  have hzero :
      zetaCompletedZeroKreinGram g =
        Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic g) :=
    zetaCompletedZeroKreinGram_eq_boundarySumAnalytic_re_of_scheduled_contour_vertical_horizontal
      g
      F
      h.height_schedule.height
      hcontourScheduled
      hverticalScheduled
      hhorizontalScheduled
  have hanalytic :
      zetaCompletedExplicitFormulaBoundarySumAnalytic g =
        zetaCompletedExplicitFormulaBoundarySumCore g :=
    zetaCompletedExplicitFormulaBoundarySumAnalytic_eq g
  have hchannel :
      zetaCompletedExplicitFormulaBoundarySumCore g =
        completedBoundaryChannel g :=
    (completedBoundaryChannel_unfold g).symm
  calc
    zetaWeilFormCompleted (convolutionAutocorrelation f) =
        zetaWeilFormCompleted g := by
      rfl
    _ = zetaCompletedZeroKreinGram g := by
      exact hweil
    _ = Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic g) := by
      exact hzero
    _ = Complex.re (zetaCompletedExplicitFormulaBoundarySumCore g) := by
      exact congrArg Complex.re hanalytic
    _ = Complex.re (completedBoundaryChannel g) := by
      exact congrArg Complex.re hchannel
    _ = Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
      rfl

/-- Autocorrelation completed explicit-formula assembly using the scheduled horizontal
carrier constructed by the analytic package. -/
theorem zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_of_constructedScheduledHorizontalCarrier_ownerContourAssembly
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f))
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u))
        atTop
        (𝓝 0))
    (hcontourScheduled :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral (convolutionAutocorrelation f)
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f schedule hPhi hLog).height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex (convolutionAutocorrelation f)))) :
    zetaWeilFormCompleted (convolutionAutocorrelation f) =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  let g : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let F : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let h : ExplicitFormulaFamilyAnalyticPackage g F :=
    zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f schedule hPhi hLog
  have hweil :
      zetaWeilFormCompleted g =
        zetaCompletedZeroKreinGram g :=
    zetaWeilFormCompleted_eq_zeroKreinGram g
  have hverticalScheduled :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral g
              (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral g
              (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic g)) :=
    zetaCompletedExplicitFormula_autocorrelation_scheduledVertical_tendsto_boundarySum
      f schedule hPhi hLog hone
  have hhorizontalScheduled :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaTopLineIntegral g
              (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaBottomLineIntegral g
              (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormula_autocorrelation_horizontal_tendsto_zero_of_scheduledCarrier
      f h
  have hzero :
      zetaCompletedZeroKreinGram g =
        Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic g) :=
    zetaCompletedZeroKreinGram_eq_boundarySumAnalytic_re_of_scheduled_contour_vertical_horizontal
      g
      F
      h.height_schedule.height
      hcontourScheduled
      hverticalScheduled
      hhorizontalScheduled
  have hanalytic :
      zetaCompletedExplicitFormulaBoundarySumAnalytic g =
        zetaCompletedExplicitFormulaBoundarySumCore g :=
    zetaCompletedExplicitFormulaBoundarySumAnalytic_eq g
  have hchannel :
      zetaCompletedExplicitFormulaBoundarySumCore g =
        completedBoundaryChannel g :=
    (completedBoundaryChannel_unfold g).symm
  calc
    zetaWeilFormCompleted (convolutionAutocorrelation f) =
        zetaWeilFormCompleted g := by
      rfl
    _ = zetaCompletedZeroKreinGram g := by
      exact hweil
    _ = Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic g) := by
      exact hzero
    _ = Complex.re (zetaCompletedExplicitFormulaBoundarySumCore g) := by
      exact congrArg Complex.re hanalytic
    _ = Complex.re (completedBoundaryChannel g) := by
      exact congrArg Complex.re hchannel
    _ = Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
      rfl

/-- Autocorrelation completed explicit-formula assembly using constructed scheduled
horizontal carrier and the finite-rectangle residue-calculus contour limit. -/
theorem zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_of_constructedScheduledContour_ownerContourAssembly
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f))
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u))
        atTop
        (𝓝 0))
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral (convolutionAutocorrelation f)
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f schedule hPhi hLog).height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum
            (convolutionAutocorrelation f)
            ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u))
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f))) :
    zetaWeilFormCompleted (convolutionAutocorrelation f) =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  let g : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let F : ExplicitFormulaVerticallyRegularContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily f
  let h : ExplicitFormulaFamilyAnalyticPackage g F.toContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f schedule hPhi hLog
  have hcontourScheduled :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral g
            (F.toContourFamily.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex g)) :=
    zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_of_scheduledCarrier_ownerResidueCalculus
      g F h N hfinite hsum
  exact
    zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_of_constructedScheduledHorizontalCarrier_ownerContourAssembly
      f schedule hPhi hLog hone hcontourScheduled

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
