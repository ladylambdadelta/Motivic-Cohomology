import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleResidues

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

/-- The scheduled right-face off-pole `s = 1` correction integral, isolated as
the object controlled by the contour-cancellation argument. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  ∫ t in
      Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      (-1 /
          (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)

/-- Definition transport from the explicit right-face off-pole correction
integral to its scheduled owner name. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledOscillatoryIntegral_eq_named
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (∫ t in
        Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        (-1 /
            (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
        f F h u :=
  rfl

/-- Direct residue-free inverse-quadratic estimate for the scheduled right
`s = 1` correction face.

This theorem belongs with the scheduled oscillatory integral itself.  Its proof
is the residue-free right-contour estimate, using the fixed off-pole
displacement from `s = 1`, the finite horizontal-edge decay, and the
scheduled height normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_eventual_inverseQuadratic_ownerOscillatory
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
              f F h u‖
            ≤ MR *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  sorry

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
