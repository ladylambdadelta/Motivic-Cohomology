import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineVerticalTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineIntegralZero
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RealLineQuantitativeTails

/-!
# Quantitative tails for the right one-pole affine kernel

This file owns the measure-theoretic tail estimate for the right one-pole
affine kernel.  The analytic input is high-order Paley-Wiener decay of the
affine kernel plus a zero whole-line value; the output is the scheduled
inverse-quadratic bound needed by the residue-tail layer.
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

/-- Owner analytic tail leaf: if the right one-pole affine kernel has zero
whole-line value, then its rectangle-window truncations decay
inverse-quadratically.

The proof should use the `N = 4` (or stronger) affine kernel majorant, express
the window integral as the negative complement of the whole-line integral, and
bound the two tails by integrating `(1 + ‖t‖)^{-4}` outside the window. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelInterval_eventual_inverseQuadratic_of_integral_zero_ownerOnePoleTail
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hzero :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) =
        0) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t‖
            ≤ MR *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  let φ : ℝ → ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F
  let A : ℝ :=
    ((1 : ℝ) / (F.c - 1)) *
      h.phi_control.verticalStripRapidDecayConstant
        (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 4
  have hφ_integrable :
      Integrable φ (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integrable_ownerBounds
      f F h
  have hA_nonneg : 0 ≤ A := by
    have hcoeff_nonneg : 0 ≤ (1 : ℝ) / (F.c - 1) :=
      le_of_lt (div_pos zero_lt_one (sub_pos.mpr F.c_gt_one))
    have hdecay_nonneg :
        0 ≤
          h.phi_control.verticalStripRapidDecayConstant
            (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 4 :=
      h.phi_control.verticalStripRapidDecayConstant_nonneg
        (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 4
    exact mul_nonneg hcoeff_nonneg hdecay_nonneg
  have hmajorant :
      ∀ t : ℝ,
        ‖φ t‖ ≤ A * (1 + ‖t‖) ^ (-(4 : ℤ)) := by
    intro t
    exact
      zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_norm_le_majorant
        f F h 4 t
  match
    realLine_intervalIntegral_eventually_inverseQuadratic_of_integral_zero_norm_le_zpow_four
      φ hφ_integrable hzero A hA_nonneg hmajorant with
  | ⟨M, hMpos, hM⟩ =>
      exact
        ⟨M, hMpos,
          (h.height_schedule.cofinal.eventually hM).mono
            (fun u hu => hu)⟩

/-- Scheduled vertical one-pole tail bound obtained by transporting the
vertical integral to the affine-kernel rectangle integral. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eventual_inverseQuadratic_of_affineKernelInterval_ownerOnePoleTail
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hinterval :
      ∃ MR : ℝ,
        0 < MR ∧
          ∀ᶠ u in atTop,
            ‖∫ t in Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
                zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t‖
              ≤ MR *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u)‖
            ≤ MR *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match hinterval with
  | ⟨MR, hMRpos, hMR⟩ =>
      exact
        ⟨MR, hMRpos,
          hMR.mono
            (fun u hu =>
              Eq.subst
                (motive := fun z : ℂ =>
                  ‖z‖ ≤
                    MR *
                      (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^
                        (-(2 : ℤ)))
                (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_affineKernelIntegral_ownerOnePoleVerticalTransport
                  f F (h.height_schedule.height u)).symm
                hu)⟩

/-- Owner quantitative tail theorem for scheduled truncations of the right
`s = 1` correction affine kernel, assuming the whole-line value is zero.

This is a measure/decay consequence of the affine-kernel rapid decay bounds,
the rectangle-window transport, and the zero whole-line value. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eventual_inverseQuadratic_of_affineIntegral_zero_ownerOnePoleTail
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hzero :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) =
        0) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u)‖
            ≤ MR *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eventual_inverseQuadratic_of_affineKernelInterval_ownerOnePoleTail
      f F h
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelInterval_eventual_inverseQuadratic_of_integral_zero_ownerOnePoleTail
        f F h hzero)

/-- Public tail consequence of the right one-pole affine zero value. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eventual_inverseQuadratic_ownerOnePoleTail
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u)‖
            ≤ MR *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eventual_inverseQuadratic_of_affineIntegral_zero_ownerOnePoleTail
      f F h
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integral_eq_zero_ownerOnePoleAffine
        f F h)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
