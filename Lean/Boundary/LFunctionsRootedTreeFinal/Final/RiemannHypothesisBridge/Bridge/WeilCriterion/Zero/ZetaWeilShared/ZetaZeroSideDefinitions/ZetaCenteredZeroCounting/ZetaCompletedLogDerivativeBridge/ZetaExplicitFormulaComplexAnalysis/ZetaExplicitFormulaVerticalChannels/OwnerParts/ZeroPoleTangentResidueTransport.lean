import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleTangentBoundaryAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightOnePoleTangentCancellation

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Corrected standard-contour residue transport from the finite rectangle
Cauchy convention to the scheduled left zero-pole face. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_standardBoundaryResidue_and_orientationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A : ℂ)
    (hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 A))
    (B : ℂ)
    (hcancel : A + B * Complex.I = 0)
    (hstandard :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u) = B)
    (horientation :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_standardBoundaryResidue_and_orientationDefect_ownerZeroPoleAlgebra
      f F h A B hright hcancel hstandard horientation
      (zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero_ownerZeroPoleHorizontal
        f F h)

/-- Eventual constant-value transport for the corrected standard rectangle
Cauchy boundary convention at positive scheduled heights. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_standardBoundaryResidueValue_of_positiveHeight
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F T = B) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u) = B := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      hpositive (h.height_schedule.height u) hu)

/-- Positive-height raw standard-contour Cauchy transport for the isolated
zero-pole local residue.  The raw contour value carries the usual `2πi` factor;
the cancellation identity must therefore be stated for that raw value. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_positiveHeight_rawStandardLocalResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A : ℂ)
    (hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 A))
    (hcancel :
      A +
        ((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I = 0)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F T =
            (2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_standardBoundaryResidue_and_orientationDefect
      f F h A hright
      ((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))))
      hcancel
      (zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_standardBoundaryResidueValue_of_positiveHeight
        f F h
        ((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))))
        hpositive)
      (zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect_tendsto_zero
        f F h)

/-- A positive-height raw standard Cauchy theorem gives the normalized `s = 1`
standard boundary value equal to its local residue. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_eventually_normalizedStandardBoundaryResidueValue_of_positiveHeight_rawCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F T =
            (2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionOnePoleNormalizedStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
        -zetaCompletedExplicitFormulaPhi f (1 / 2) := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      zetaCompletedExplicitFormulaCorrectionOnePoleNormalizedStandardRectangleBoundaryIntegral_eq_residue_of_rawCauchy
        f F (h.height_schedule.height u)
        (hpositive (h.height_schedule.height u) hu))

/-- Constant-valued finite tangent residue transport for the genuine zero-pole
tangent defect.  The residue theorem only has to provide a constant boundary
value whose tangent contribution cancels the right-face limit. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_tendsto_zero_of_eventually_tangentBoundaryResidueValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℂ)
    (hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 A))
    (hcancel :
      A + B * Complex.I = 0)
    (hboundary :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) = B) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
      atTop
      (𝓝 0) := by
  have hboundary_event :
      Filter.EventuallyEq atTop
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
        (fun _u : ℝ => B * Complex.I) := by
    exact hboundary.mono
      (fun u hC =>
        congrArg (fun z : ℂ => z * Complex.I) hC)
  have hboundary_tendsto :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I)) :=
    Tendsto.congr' hboundary_event.symm tendsto_const_nhds
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (A + B * Complex.I)) :=
    hright.add hboundary_tendsto
  exact Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 z))
    hcancel
    hsum

/-- Constant-valued finite tangent residue transport to the scheduled left
zero-pole face. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_eventually_tangentBoundaryResidueValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℂ)
    (hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 A))
    (hcancel :
      A + B * Complex.I = 0)
    (hboundary :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) = B) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_tangentBoundaryDefect
      f F h
      (zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_tendsto_zero_of_eventually_tangentBoundaryResidueValue
        f F h A B hright hcancel hboundary)

/-- A positive-height finite tangent residue theorem with value `B` supplies
that scheduled zero-pole tangent residue value eventually. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_tangentBoundaryResidueValue_of_positiveHeight
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F T = B) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) = B := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      hpositive (h.height_schedule.height u) hu)

/-- Positive-height finite residue transport from the genuine tangent rectangle
to the scheduled left zero-pole face, with the residue value and cancellation
identity kept explicit. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_positiveHeight_tangentBoundaryResidueValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℂ)
    (hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 A))
    (hcancel :
      A + B * Complex.I = 0)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F T = B) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_eventually_tangentBoundaryResidueValue
      f F h A B hright hcancel
      (zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_tangentBoundaryResidueValue_of_positiveHeight
        f F h B hpositive)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
