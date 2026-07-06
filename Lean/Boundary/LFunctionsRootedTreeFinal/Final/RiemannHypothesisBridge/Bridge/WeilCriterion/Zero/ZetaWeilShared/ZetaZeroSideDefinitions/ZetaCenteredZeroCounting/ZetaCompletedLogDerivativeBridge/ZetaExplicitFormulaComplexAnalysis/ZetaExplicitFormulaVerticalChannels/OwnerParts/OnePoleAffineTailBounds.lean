import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineVerticalTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineIntegralZero
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RealLineQuantitativeTails

/-!
# Quantitative tails for the right one-pole affine kernel

This file owns the measure-theoretic tail estimate for the right one-pole
affine kernel.  The analytic input is high-order Paley-Wiener decay of the
affine kernel plus its projection whole-line value; the output is the scheduled
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

/-- Owner analytic tail leaf: if the right one-pole affine kernel has
projection whole-line value, then its rectangle-window truncations converge to
that value inverse-quadratically.

The proof should use the `N = 4` (or stronger) affine kernel majorant, express
the window integral as the negative complement of the whole-line integral, and
bound the two tails by integrating `(1 + ‖t‖)^{-4}` outside the window. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelInterval_eventual_inverseQuadratic_of_integral_projection_ownerOnePoleTail
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) =
        zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖(∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) -
              zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c‖
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
      le_of_lt
        (h.phi_control.verticalStripRapidDecayConstant_pos
          (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 4)
    exact mul_nonneg hcoeff_nonneg hdecay_nonneg
  have hmajorant :
      ∀ t : ℝ,
        ‖φ t‖ ≤ A * (1 + ‖t‖) ^ (-(4 : ℤ)) := by
    intro t
    exact
      zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_norm_le_majorant
        f F h 4 t
  match
    realLine_intervalIntegral_eventually_inverseQuadratic_of_integral_value_norm_le_zpow_four
      φ hφ_integrable
      (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)
      hvalue A hA_nonneg hmajorant with
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
            ‖(∫ t in Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
                zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) -
                zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c‖
              ≤ MR *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c‖
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
                (congrArg
                  (fun z : ℂ =>
                    z -
                      zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)
                  (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_affineKernelIntegral_ownerOnePoleVerticalTransport
                    f F (h.height_schedule.height u))).symm
                hu)⟩

/-- Owner quantitative tail theorem for scheduled truncations of the right
`s = 1` correction affine kernel, assuming the whole-line projection value.

This is a measure/decay consequence of the affine-kernel rapid decay bounds,
the rectangle-window transport, and the zero whole-line value. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eventual_inverseQuadratic_of_affineIntegral_projection_ownerOnePoleTail
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) =
        zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c‖
            ≤ MR *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eventual_inverseQuadratic_of_affineKernelInterval_ownerOnePoleTail
      f F h
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelInterval_eventual_inverseQuadratic_of_integral_projection_ownerOnePoleTail
        f F h hvalue)

/-- Public tail consequence of the right one-pole affine projection value. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eventual_inverseQuadratic_ownerOnePoleTail
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c‖
            ≤ MR *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eventual_inverseQuadratic_of_affineIntegral_projection_ownerOnePoleTail
      f F h
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integral_eq_projection_ownerOnePoleAffine
        f F h)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
