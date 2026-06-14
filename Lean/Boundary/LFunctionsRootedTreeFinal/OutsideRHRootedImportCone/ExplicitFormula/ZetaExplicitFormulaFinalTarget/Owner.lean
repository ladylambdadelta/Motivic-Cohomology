import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.Owner
import Boundary.LFunctionsRootedTreeFinal.OutsideRHRootedImportCone.ExplicitFormula.ZetaExplicitFormulaFinalTarget.ZetaExplicitFormulaVerticalTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.OutsideRHRootedImportCone.ExplicitFormula.ZetaExplicitFormulaFinalTarget.ZetaExplicitFormulaResidueBridge.Owner

/-!
# Boundary explicit-formula final target

This file owns the final zero-side contour-shift target. The pure contour
geometry file intentionally does not import the zero-side Krein form, because
the zero-side chain already depends downstream on the complex-analysis contour
layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The full contour-shift target for the explicit formula. -/
def explicitFormulaContourShiftTarget
    (f : ZetaAdmissibleFunction) (_r : ExplicitFormulaRectangle) : Prop :=
  zetaCompletedResidueBoundarySumComplex f =
    zetaCompletedExplicitFormulaBoundarySumAnalytic f

/-- The contour-shift target is the final public explicit-formula statement. -/
theorem explicitFormulaContourShiftTarget_iff
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaContourShiftTarget f r ↔
      zetaCompletedResidueBoundarySumComplex f =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
  Iff.rfl

/-- The complex zero-side residue sum is the completed residue boundary sum. -/
theorem zetaCompletedZeroSideComplex_eq_completedResidueBoundarySumComplex
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaCompletedZeroSideComplex f =
      zetaCompletedResidueBoundarySumComplex f := by
  rfl

/-- The horizontal side difference along a contour family. -/
noncomputable def explicitFormulaFamilyHorizontalDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)

/-- The contour-family integral is the sum of the vertical and horizontal differences. -/
theorem explicitFormulaFamilyContourIntegral_eq_vertical_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyContourIntegral f F T =
      explicitFormulaFamilyVerticalDifference f F T +
        explicitFormulaFamilyHorizontalDifference f F T := by
  let R : ℂ := zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T)
  let L : ℂ := zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)
  let U : ℂ := zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)
  let B : ℂ := zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)
  unfold explicitFormulaFamilyContourIntegral
  unfold zetaCompletedExplicitFormulaContourIntegral
  unfold explicitFormulaFamilyVerticalDifference
  unfold explicitFormulaFamilyHorizontalDifference
  change R - L + U - B = (R - L) + (U - B)
  calc
    R - L + U - B = (R - L + U) + -B := by
      exact sub_eq_add_neg (R - L + U) B
    _ = ((R - L) + U) + -B := by
      rfl
    _ = (R - L) + (U + -B) := by
      exact add_assoc (R - L) U (-B)
    _ = (R - L) + (U - B) := by
      exact congrArg (fun x : ℂ => (R - L) + x) (sub_eq_add_neg U B).symm

/-- The vertical family is the contour family with the horizontal difference subtracted. -/
theorem explicitFormulaFamilyVerticalDifference_eq_contour_sub_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyVerticalDifference f F T =
      explicitFormulaFamilyContourIntegral f F T -
        explicitFormulaFamilyHorizontalDifference f F T := by
  let V : ℂ := explicitFormulaFamilyVerticalDifference f F T
  let H : ℂ := explicitFormulaFamilyHorizontalDifference f F T
  have hcontour :
      explicitFormulaFamilyContourIntegral f F T = V + H :=
    explicitFormulaFamilyContourIntegral_eq_vertical_add_horizontal f F T
  calc
    explicitFormulaFamilyVerticalDifference f F T = V := by
      rfl
    _ = (V + H) - H := by
      exact (add_sub_cancel_right V H).symm
    _ = explicitFormulaFamilyContourIntegral f F T - H := by
      exact congrArg (fun x : ℂ => x - H) hcontour.symm
    _ =
        explicitFormulaFamilyContourIntegral f F T -
          explicitFormulaFamilyHorizontalDifference f F T := by
      rfl

/-- The horizontal contour sides vanish along every vertically regular contour family using
the supplied cofinal schedule. -/
theorem explicitFormulaFamilyHorizontalDifference_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyHorizontalDifference f F.toContourFamily T)
      atTop
      (𝓝 0) := by
  exact
    ExplicitFormulaFamilyAnalyticPackage.horizontalDecay
      (f := f) (F := F.toContourFamily)
      (h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule)
      1

/-- Historical name for the owner residue-limit theorem. -/
theorem explicitFormulaFamilyContourIntegral_tendsto_residueBoundarySum_ownerResidueLimit
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyContourIntegral f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedResidueBoundarySumComplex f)) := by
  dsimp
  exact explicitFormulaFamilyContourIntegral_tendsto_residueBoundarySum_ownerResidueTheorem
    f F hSchedule

/-- The residue theorem reconstructs the limiting contour integral from the zero-side
completed residue boundary. -/
theorem explicitFormulaFamilyContourIntegral_tendsto_residueBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyContourIntegral f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedResidueBoundarySumComplex f)) := by
  dsimp
  exact explicitFormulaFamilyContourIntegral_tendsto_residueBoundarySum_ownerResidueLimit
    f F hSchedule

/-- Residue reconstruction plus horizontal decay identifies the limit of the vertical
family with the completed residue boundary sum. -/
theorem explicitFormulaFamilyVerticalDifference_tendsto_residueBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalDifference f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedResidueBoundarySumComplex f)) := by
  dsimp
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hcontour :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyContourIntegral f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedResidueBoundarySumComplex f)) :=
    explicitFormulaFamilyContourIntegral_tendsto_residueBoundarySum f F hSchedule
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalDifference f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (0 : ℂ)) :=
    (explicitFormulaFamilyHorizontalDifference_tendsto_zero f F hSchedule).comp
      h.height_schedule.cofinal
  have hdiff :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyContourIntegral f F.toContourFamily
              (h.height_schedule.height u) -
            explicitFormulaFamilyHorizontalDifference f F.toContourFamily
              (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedResidueBoundarySumComplex f - 0)) :=
    hcontour.sub hhorizontal
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalDifference f F.toContourFamily
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyContourIntegral f F.toContourFamily
              (h.height_schedule.height u) -
            explicitFormulaFamilyHorizontalDifference f F.toContourFamily
              (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaFamilyVerticalDifference_eq_contour_sub_horizontal
      f F.toContourFamily (h.height_schedule.height u)
  have htarget :
      zetaCompletedResidueBoundarySumComplex f - 0 =
        zetaCompletedResidueBoundarySumComplex f :=
    sub_zero _
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedResidueBoundarySumComplex f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            explicitFormulaFamilyContourIntegral f F.toContourFamily
                (h.height_schedule.height T) -
              explicitFormulaFamilyHorizontalDifference f F.toContourFamily
                (h.height_schedule.height T))
          atTop
          (𝓝 z))
      htarget
      hdiff)

/-- The vertical channel transport identifies the vertical-family limit with the analytic
prime/archimedean/correction boundary sum. -/
theorem explicitFormulaFamilyVerticalTransport_tendsto_boundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalDifference f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  dsimp
  exact explicitFormulaFamilyVerticalDifference_tendsto_boundarySum_ownerVerticalTransport
    f F hSchedule

/-- The vertical channel transport identifies the limit of the vertical family with the
analytic prime/archimedean/correction boundary sum. -/
theorem explicitFormulaFamilyVerticalDifference_tendsto_boundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalDifference f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
  explicitFormulaFamilyVerticalTransport_tendsto_boundarySum f F hSchedule

/-- The complex zero side equals the analytic boundary sum by uniqueness of the completed
vertical family limit. -/
theorem zetaCompletedResidueBoundarySumComplex_eq_boundarySum_of_familyContourShift
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    zetaCompletedResidueBoundarySumComplex f =
      zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hresidue :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalDifference f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedResidueBoundarySumComplex f)) :=
    explicitFormulaFamilyVerticalDifference_tendsto_residueBoundarySum f F hSchedule
  have hboundary :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalDifference f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    explicitFormulaFamilyVerticalDifference_tendsto_boundarySum f F hSchedule
  exact tendsto_nhds_unique hresidue hboundary

/-- The completed contour-shift theorem in the repository's analytic normalization.

This is a rectangle-indexed wrapper around the family/limit theorem above; the target itself
does not depend on the finite rectangle parameter. -/
theorem explicitFormulaContourShiftTarget_of_rectangle
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    explicitFormulaContourShiftTarget f r := by
  have htarget :
      zetaCompletedResidueBoundarySumComplex f =
      zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
    zetaCompletedResidueBoundarySumComplex_eq_boundarySum_of_familyContourShift
      f F hSchedule
  exact htarget

/-- A complex contour-shift target gives a real Krein equality after the analytic boundary
sum has been normalized to a real scalar. -/
theorem zetaCompletedZeroKreinGram_eq_realBoundary_of_contourShiftTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (R : ℝ)
    (hshift : explicitFormulaContourShiftTarget f r)
    (hboundary :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f = (R : ℂ)) :
    zetaCompletedZeroKreinGram f = R := by
  have hcomplex :
      zetaCompletedResidueBoundarySumComplex f = (R : ℂ) :=
    Eq.trans hshift hboundary
  have hre :
      Complex.re (zetaCompletedResidueBoundarySumComplex f) =
        Complex.re (R : ℂ) :=
    congrArg Complex.re hcomplex
  have hzero :
      zetaCompletedZeroKreinGram f =
        Complex.re (zetaCompletedResidueBoundarySumComplex f) := by
    rfl
  have hR :
      Complex.re (R : ℂ) = R :=
    Complex.ofReal_re R
  exact hzero.trans (hre.trans hR)

/-- A complex zero statement for the real zero-side Krein form descends to a real zero statement. -/
theorem zetaCompletedZeroKreinGram_eq_zero_of_complex_zero
    (f : ZetaAdmissibleFunction)
    (h : (zetaCompletedZeroKreinGram f : ℂ) = 0) :
    zetaCompletedZeroKreinGram f = 0 :=
  Complex.ofReal_injective h

/-- A real zero statement for the zero-side Krein form ascends to a complex zero statement. -/
theorem zetaCompletedZeroKreinGram_complex_zero_of_eq_zero
    (f : ZetaAdmissibleFunction)
    (h : zetaCompletedZeroKreinGram f = 0) :
    (zetaCompletedZeroKreinGram f : ℂ) = 0 :=
  congrArg (fun x : ℝ => (x : ℂ)) h

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
