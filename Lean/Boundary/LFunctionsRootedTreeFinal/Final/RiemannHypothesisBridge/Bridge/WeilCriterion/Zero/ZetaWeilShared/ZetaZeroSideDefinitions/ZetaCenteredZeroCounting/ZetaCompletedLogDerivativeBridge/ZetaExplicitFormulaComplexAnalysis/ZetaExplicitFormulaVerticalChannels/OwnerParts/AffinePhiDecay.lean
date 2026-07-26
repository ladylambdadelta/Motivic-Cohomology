import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineVerticalKernels

/-!
# Fixed affine-line decay for the test transform

This file specializes the vertical-strip rapid decay of `Φ_f` to the two
centered affine vertical lines used by the vertical-channel kernels.
-/

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

/-- Rapid decay of `Φ_f` on the shifted right affine line
`(F.c - 1/2) + i t`. -/
theorem zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_decay_bound_of_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (N : ℕ) (t : ℝ) :
    ‖zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖
      ≤ hPhi.verticalStripRapidDecayConstant
          (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) N *
        (1 + ‖t‖) ^ (-(N : ℤ)) := by
  let z : ℂ := zetaCompletedExplicitFormulaRightCenteredAffineLine F t
  let a : ℝ := F.c - (1 / 2 : ℝ)
  have hre : z.re = a :=
    zetaCompletedExplicitFormulaRightCenteredAffineLine_re F t
  have him : z.im = t :=
    zetaCompletedExplicitFormulaRightCenteredAffineLine_im F t
  have ha : a ≤ z.re :=
    le_of_eq hre.symm
  have hb : z.re ≤ a :=
    le_of_eq hre
  have hraw :
      ‖zetaCompletedExplicitFormulaPhi f z‖
        ≤ hPhi.verticalStripRapidDecayConstant a a N *
          (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
    hPhi.verticalStripRapidDecayConstant_bound a a N z ha hb
  have him_norm : ‖z.im‖ = ‖t‖ :=
    congrArg norm him
  have hweight :
      (1 + ‖z.im‖) ^ (-(N : ℤ)) =
        (1 + ‖t‖) ^ (-(N : ℤ)) :=
    congrArg (fun x : ℝ => (1 + x) ^ (-(N : ℤ))) him_norm
  exact hraw.trans_eq
    (congrArg
      (fun x : ℝ =>
        hPhi.verticalStripRapidDecayConstant a a N * x)
      hweight)

/-- Rapid decay of `Φ_f` on the shifted right affine line
`(F.c - 1/2) + i t`. -/
theorem zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_decay_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (t : ℝ) :
    ‖zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖
      ≤ h.phi_control.verticalStripRapidDecayConstant
          (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) N *
        (1 + ‖t‖) ^ (-(N : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_decay_bound_of_phiControl
      f F h.phi_control N t

/-- Rapid decay of `Φ_f` on the shifted left affine line
`(1 - F.c - 1/2) + i t`. -/
theorem zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_decay_bound_of_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (N : ℕ) (t : ℝ) :
    ‖zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖
      ≤ hPhi.verticalStripRapidDecayConstant
          ((1 : ℝ) - F.c - (1 / 2 : ℝ))
          ((1 : ℝ) - F.c - (1 / 2 : ℝ)) N *
        (1 + ‖t‖) ^ (-(N : ℤ)) := by
  let z : ℂ := zetaCompletedExplicitFormulaLeftCenteredAffineLine F t
  let a : ℝ := (1 : ℝ) - F.c - (1 / 2 : ℝ)
  have hre : z.re = a :=
    zetaCompletedExplicitFormulaLeftCenteredAffineLine_re F t
  have him : z.im = t :=
    zetaCompletedExplicitFormulaLeftCenteredAffineLine_im F t
  have ha : a ≤ z.re :=
    le_of_eq hre.symm
  have hb : z.re ≤ a :=
    le_of_eq hre
  have hraw :
      ‖zetaCompletedExplicitFormulaPhi f z‖
        ≤ hPhi.verticalStripRapidDecayConstant a a N *
          (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
    hPhi.verticalStripRapidDecayConstant_bound a a N z ha hb
  have him_norm : ‖z.im‖ = ‖t‖ :=
    congrArg norm him
  have hweight :
      (1 + ‖z.im‖) ^ (-(N : ℤ)) =
        (1 + ‖t‖) ^ (-(N : ℤ)) :=
    congrArg (fun x : ℝ => (1 + x) ^ (-(N : ℤ))) him_norm
  exact hraw.trans_eq
    (congrArg
      (fun x : ℝ =>
        hPhi.verticalStripRapidDecayConstant a a N * x)
      hweight)

/-- Rapid decay of `Φ_f` on the shifted left affine line
`(1 - F.c - 1/2) + i t`. -/
theorem zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_decay_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (t : ℝ) :
    ‖zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖
      ≤ h.phi_control.verticalStripRapidDecayConstant
          ((1 : ℝ) - F.c - (1 / 2 : ℝ))
          ((1 : ℝ) - F.c - (1 / 2 : ℝ)) N *
        (1 + ‖t‖) ^ (-(N : ℤ)) :=
  zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_decay_bound_of_phiControl
    f F h.phi_control N t

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
