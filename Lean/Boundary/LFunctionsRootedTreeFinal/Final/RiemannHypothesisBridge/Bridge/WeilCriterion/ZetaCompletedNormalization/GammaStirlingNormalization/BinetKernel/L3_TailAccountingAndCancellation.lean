import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.A_RealAnalysisBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.I_LocalIndentationAbsorption
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.J_ContourKernelAccounting
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.H_TailRemainderEstimates
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.K_BranchCoherence

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.L2_AbelPlanaDecomposition

import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.SetIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteFormula
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetTailContour
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.FiniteOrderAlgebra.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.RightCriticalStripCompact.Owner

/-!
# Binet kernel and sectorial Gamma seed estimates

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.GammaStirlingNormalization.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter

theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_eventually_lowerVerticalUpTo_decay
    (hfinite :
      ∃ R : ℝ, ∃ C : ℝ,
        0 < R ∧
        0 < C ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∀ᶠ T : ℝ in atTop,
              ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                  Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                (C / ‖w‖) *
                  Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  match hfinite with
  | ⟨R, C, hR_pos, hC_pos, hfinite_bound⟩ =>
      exact
        ⟨R, C, hR_pos, hC_pos,
          fun w hw_re_pos hRle =>
            Complex.binetSecondFormula_tailRemainder_norm_le_of_eventually_lowerVerticalUpTo_sub_initialWindow_norm_le_owner
              hw_re_pos
              (hfinite_bound w hw_re_pos hRle)⟩

/-- Constructor from separate finite-height bounds for the solved static
boundary term and for the contour error.

This is the finite-height estimate in the exact form produced by the solved
boundary equation: the static boundary expression and the paired contour error
are bounded separately, then combined by the triangle estimate for the lower
vertical tail. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_boundarySolvedStatic_and_contourError_decay
    (hfinite :
      ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
        0 < R ∧
        0 < Cstatic ∧
        0 < Cerror ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∃ N : ℕ,
              (∀ᶠ T : ℝ in atTop,
                ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                  Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                  Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                  Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                  (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    (Cstatic / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w) ∧
              (∀ᶠ T : ℝ in atTop,
                ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
                    (Cerror / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w)) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  match hfinite with
  | ⟨R, Cstatic, Cerror, hR_pos, hCstatic_pos, hCerror_pos, hbounds⟩ =>
      let C : ℝ := Cstatic + Cerror
      have hC_pos : 0 < C :=
        add_pos hCstatic_pos hCerror_pos
      have hfinite_lower :
          ∃ R : ℝ, ∃ C : ℝ,
            0 < R ∧
            0 < C ∧
            ∀ w : ℂ,
              0 < w.re →
              R ≤ ‖w‖ →
                ∀ᶠ T : ℝ in atTop,
                  ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                    (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    (C / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w := by
        exact
          ⟨R, C, hR_pos, hC_pos,
            fun w hw_re_pos hRle =>
              match hbounds w hw_re_pos hRle with
              | ⟨N, hstatic, herror⟩ =>
                  (hstatic.and herror).mono
                    (fun T hpair =>
                      let J : ℝ :=
                        Complex.binetSecondFormulaDecayingTailIntegral w
                      let S : ℂ :=
                        ((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                          Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)
                      let E : ℂ :=
                        Complex.finiteAbelPlanaLogFiniteHeightContourError N w T
                      have htriangle :
                          ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                            (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                              Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                            ‖S‖ + ‖E‖ :=
                        Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_contourError_owner
                          N w T
                      have hstatic_T :
                          ‖S‖ ≤ (Cstatic / ‖w‖) * J :=
                        hpair.1
                      have herror_T :
                          ‖E‖ ≤ (Cerror / ‖w‖) * J :=
                        hpair.2
                      have hsum :
                          ‖S‖ + ‖E‖ ≤
                            (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J :=
                        add_le_add hstatic_T herror_T
                      have hcombine :
                          (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J =
                            (C / ‖w‖) * J := by
                        calc
                          (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J =
                              (Cstatic / ‖w‖ + Cerror / ‖w‖) * J := by
                            exact
                              (right_distrib (Cstatic / ‖w‖)
                                (Cerror / ‖w‖) J).symm
                          _ = ((Cstatic + Cerror) / ‖w‖) * J := by
                            exact
                              congrArg (fun x : ℝ => x * J)
                                (add_div Cstatic Cerror ‖w‖).symm
                          _ = (C / ‖w‖) * J := by
                            rfl
                      le_trans htriangle
                        (le_trans hsum (le_of_eq hcombine)))⟩
      exact
        Complex.binetSecondFormula_branchTail_wallCancellation_of_eventually_lowerVerticalUpTo_decay
          hfinite_lower

/-- Constructor reducing branch-wall cancellation to the solved static
boundary decay estimate.

The contour-error part is discharged here from the finite-height owner
boundary target and the paired contour-error theorem.  Thus the only
quantitative input left to this constructor is the decay of the solved static
boundary expression. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_boundarySolvedStatic_decay
    (hfinite :
      ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
        0 < R ∧
        2 ≤ R ∧
        0 < Cstatic ∧
        0 < Cerror ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∃ N : ℕ,
              (∀ᶠ T : ℝ in atTop,
                (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                      (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                        Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                    (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
                  ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                      (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                        Complex.I *
                          Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                    (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
                  Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T) ∧
              (∀ᶠ T : ℝ in atTop,
                ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                  Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                  Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                  Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                  (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    (Cstatic / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w)) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  match hfinite with
  | ⟨R, Cstatic, Cerror, hR_pos, hR_two, hCstatic_pos, hCerror_pos, hbounds⟩ =>
      have hwith_error :
          ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
            0 < R ∧
            0 < Cstatic ∧
            0 < Cerror ∧
            ∀ w : ℂ,
              0 < w.re →
              R ≤ ‖w‖ →
                ∃ N : ℕ,
                  (∀ᶠ T : ℝ in atTop,
                    ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                      Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                        (Cstatic / ‖w‖) *
                          Complex.binetSecondFormulaDecayingTailIntegral w) ∧
                  (∀ᶠ T : ℝ in atTop,
                    ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
                        (Cerror / ‖w‖) *
                          Complex.binetSecondFormulaDecayingTailIntegral w) := by
        exact
          ⟨R, Cstatic, Cerror, hR_pos, hCstatic_pos, hCerror_pos,
            fun w hw_re_pos hRle =>
              match hbounds w hw_re_pos hRle with
              | ⟨N, hboundary, hstatic⟩ =>
                  have hw_norm_two : 2 ≤ ‖w‖ :=
                    le_trans hR_two hRle
                  have herror :
                      ∀ᶠ T : ℝ in atTop,
                        ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
                          (Cerror / ‖w‖) *
                            Complex.binetSecondFormulaDecayingTailIntegral w :=
                    Complex.binetSecondFormula_finiteHeightContourError_eventually_scaled_decayingTail_of_boundaryTarget_owner
                      hw_re_pos hw_norm_two N hboundary hCerror_pos
                  ⟨N, hstatic, herror⟩⟩
      exact
        Complex.binetSecondFormula_branchTail_wallCancellation_of_boundarySolvedStatic_and_contourError_decay
          hwith_error

/-- Constructor from the lower-vertical cancellation-difference estimate to
the public branch-wall tail-absorption theorem.

This is a pure transport lemma from the contour-cancelled difference
`lowerVerticalFullIntegral - initialWindow` to the public tail-remainder
form. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_lowerVerticalDifference_decay
    (hdifference :
      Complex.BinetSecondFormulaLowerVerticalDifferenceDecay) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  match hdifference with
  | ⟨R, C, hR_pos, hC_pos, hdifference_bound⟩ =>
      exact
        ⟨R, C, hR_pos, hC_pos,
          fun w hw_re_pos hRle =>
            have hnorm :
                ‖Complex.binetSecondFormulaTailRemainder w‖ =
                  ‖Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
                    (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ :=
              Complex.binetSecondFormula_tailRemainder_norm_eq_lowerVerticalFullIntegral_sub_initialWindow_norm_owner
                hw_re_pos
            Eq.subst
              (motive := fun x : ℝ =>
                x ≤
                  (C / ‖w‖) *
                    Complex.binetSecondFormulaDecayingTailIntegral w)
              hnorm.symm
              (hdifference_bound w hw_re_pos hRle)⟩

/-- Closure from finite-height lower-vertical decay to the full lower-vertical
difference decay.

This is the lower-vertical version of the tail closure theorem: once the
finite-height cancelled lower side is eventually bounded at the decaying-tail
scale, its limit, the full lower-vertical difference, has the same bound. -/
theorem Complex.binetSecondFormula_lowerVerticalDifference_decay_of_eventually_lowerVerticalUpTo_decay
    (hfinite :
      ∃ R : ℝ, ∃ C : ℝ,
        0 < R ∧
        0 < C ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∀ᶠ T : ℝ in atTop,
              ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                  Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                (C / ‖w‖) *
                  Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaLowerVerticalDifferenceDecay := by
  match hfinite with
  | ⟨R, C, hR_pos, hC_pos, hfinite_bound⟩ =>
      exact
        ⟨R, C, hR_pos, hC_pos,
          fun w hw_re_pos hRle =>
            have htail_bound :
                ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
                  (C / ‖w‖) *
                    Complex.binetSecondFormulaDecayingTailIntegral w :=
              Complex.binetSecondFormula_tailRemainder_norm_le_of_eventually_lowerVerticalUpTo_sub_initialWindow_norm_le_owner
                hw_re_pos
                (hfinite_bound w hw_re_pos hRle)
            have hnorm :
                ‖Complex.binetSecondFormulaTailRemainder w‖ =
                  ‖Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
                    (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ :=
              Complex.binetSecondFormula_tailRemainder_norm_eq_lowerVerticalFullIntegral_sub_initialWindow_norm_owner
                hw_re_pos
            Eq.subst
              (motive := fun x : ℝ =>
                x ≤
                  (C / ‖w‖) *
                    Complex.binetSecondFormulaDecayingTailIntegral w)
              hnorm
              htail_bound⟩

/-- Finite-height lower-vertical decay from full lower-vertical decay.

This is the reverse convergence transport to
`binetSecondFormula_lowerVerticalDifference_decay_of_eventually_lowerVerticalUpTo_decay`.
The full lower-vertical estimate supplies the limit bound; positivity of the
decaying tail integral gives strict room after doubling the constant, so the
finite-height family is eventually bounded at the doubled scale. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_lowerVerticalDifference_decay
    (hdifference :
      Complex.BinetSecondFormulaLowerVerticalDifferenceDecay) :
    Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay := by
  match hdifference with
  | ⟨R, C, hR_pos, hC_pos, hdifference_bound⟩ =>
      let Rfinite : ℝ := max R 2
      let Cfinite : ℝ := 2 * C
      have hRfinite_pos : 0 < Rfinite :=
        lt_of_lt_of_le hR_pos (le_max_left R 2)
      have hCfinite_pos : 0 < Cfinite :=
        mul_pos two_pos hC_pos
      exact
        ⟨Rfinite, Cfinite, hRfinite_pos, hCfinite_pos,
          fun w hw_re_pos hRfinite_le =>
            let J : ℝ := Complex.binetSecondFormulaDecayingTailIntegral w
            let S : ℝ := (C / ‖w‖) * J
            let B : ℝ := (Cfinite / ‖w‖) * J
            have hnorm_pos : 0 < ‖w‖ :=
              Complex.norm_pos_of_re_pos hw_re_pos
            have hRle : R ≤ ‖w‖ :=
              le_trans (le_max_left R 2) hRfinite_le
            have htwo_le_norm : 2 ≤ ‖w‖ :=
              le_trans (le_max_right R 2) hRfinite_le
            have hJ_pos : 0 < J := by
              match Complex.binetSecondFormula_decayingTailIntegral_expLower_owner with
              | ⟨c, hc_pos, htail_lower⟩ =>
                  have hcE_pos :
                      0 < c * ‖w‖ * Real.exp (-Real.pi * ‖w‖) :=
                    mul_pos (mul_pos hc_pos hnorm_pos)
                      (Real.exp_pos (-Real.pi * ‖w‖))
                  exact lt_of_lt_of_le hcE_pos (htail_lower w htwo_le_norm)
            have htail_bound :
                ‖Complex.binetSecondFormulaTailRemainder w‖ ≤ S := by
              have hdiff_bound :
                  ‖Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
                    (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    S :=
                hdifference_bound w hw_re_pos hRle
              have hnorm :
                  ‖Complex.binetSecondFormulaTailRemainder w‖ =
                    ‖Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
                      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ :=
                Complex.binetSecondFormula_tailRemainder_norm_eq_lowerVerticalFullIntegral_sub_initialWindow_norm_owner
                  hw_re_pos
              exact
                Eq.subst
                  (motive := fun x : ℝ => x ≤ S)
                  hnorm.symm
                  hdiff_bound
            have htail_lt :
                ‖Complex.binetSecondFormulaTailRemainder w‖ < B := by
              have hscale_pos : 0 < (1 / ‖w‖) * J :=
                mul_pos (one_div_pos.mpr hnorm_pos) hJ_pos
              have hS_eq : S = C * ((1 / ‖w‖) * J) := by
                calc
                  S = (C / ‖w‖) * J := by
                    rfl
                  _ = (C * (1 / ‖w‖)) * J := by
                    exact congrArg (fun x : ℝ => x * J)
                      (div_eq_mul_one_div C ‖w‖)
                  _ = C * ((1 / ‖w‖) * J) := by
                    exact mul_assoc C (1 / ‖w‖) J
              have hB_eq : B = (2 * C) * ((1 / ‖w‖) * J) := by
                calc
                  B = (Cfinite / ‖w‖) * J := by
                    rfl
                  _ = ((2 * C) / ‖w‖) * J := by
                    rfl
                  _ = ((2 * C) * (1 / ‖w‖)) * J := by
                    exact congrArg (fun x : ℝ => x * J)
                      (div_eq_mul_one_div (2 * C) ‖w‖)
                  _ = (2 * C) * ((1 / ‖w‖) * J) := by
                    exact mul_assoc (2 * C) (1 / ‖w‖) J
              have htail_le_scaled :
                  ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
                    C * ((1 / ‖w‖) * J) :=
                Eq.subst
                  (motive := fun x : ℝ =>
                    ‖Complex.binetSecondFormulaTailRemainder w‖ ≤ x)
                  hS_eq
                  htail_bound
              have hlt :
                  ‖Complex.binetSecondFormulaTailRemainder w‖ <
                    (2 * C) * ((1 / ‖w‖) * J) :=
                Real.le_mul_pos_scale_lt_two_mul
                  htail_le_scaled hC_pos hscale_pos
              exact
                Eq.subst
                  (motive := fun x : ℝ =>
                    ‖Complex.binetSecondFormulaTailRemainder w‖ < x)
                  hB_eq.symm
                  hlt
            Complex.eventually_norm_le_of_tendsto_norm_lt
              (Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_tendsto_tailRemainder_owner
                hw_re_pos)
              htail_lt⟩

/-- Finite-height lower-vertical decay from separate static-boundary and
contour-error estimates.

This is the finite-height triangle step in owner form.  The lower vertical
side solved from the Abel-Plana boundary equation is bounded by the solved
static expression plus the paired contour error. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_boundarySolvedStatic_and_contourError_decay
    (hfinite :
      ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
        0 < R ∧
        0 < Cstatic ∧
        0 < Cerror ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∃ N : ℕ,
              (∀ᶠ T : ℝ in atTop,
                ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                  Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                  Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                  Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                  (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    (Cstatic / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w) ∧
              (∀ᶠ T : ℝ in atTop,
                ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
                    (Cerror / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w)) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∀ᶠ T : ℝ in atTop,
            ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
              (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
              (C / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w := by
  match hfinite with
  | ⟨R, Cstatic, Cerror, hR_pos, hCstatic_pos, hCerror_pos, hbounds⟩ =>
      let C : ℝ := Cstatic + Cerror
      have hC_pos : 0 < C :=
        add_pos hCstatic_pos hCerror_pos
      exact
        ⟨R, C, hR_pos, hC_pos,
          fun w hw_re_pos hRle =>
            match hbounds w hw_re_pos hRle with
            | ⟨N, hstatic, herror⟩ =>
                (hstatic.and herror).mono
                  (fun T hpair =>
                    let J : ℝ :=
                      Complex.binetSecondFormulaDecayingTailIntegral w
                    let S : ℂ :=
                      ((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)
                    let E : ℂ :=
                      Complex.finiteAbelPlanaLogFiniteHeightContourError N w T
                    have htriangle :
                        ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                          ‖S‖ + ‖E‖ :=
                      Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_contourError_owner
                        N w T
                    have hstatic_T :
                        ‖S‖ ≤ (Cstatic / ‖w‖) * J :=
                      hpair.1
                    have herror_T :
                        ‖E‖ ≤ (Cerror / ‖w‖) * J :=
                      hpair.2
                    have hsum :
                        ‖S‖ + ‖E‖ ≤
                          (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J :=
                      add_le_add hstatic_T herror_T
                    have hcombine :
                        (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J =
                          (C / ‖w‖) * J := by
                      calc
                        (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J =
                            (Cstatic / ‖w‖ + Cerror / ‖w‖) * J := by
                          exact
                            (right_distrib (Cstatic / ‖w‖)
                              (Cerror / ‖w‖) J).symm
                        _ = ((Cstatic + Cerror) / ‖w‖) * J := by
                          exact
                            congrArg (fun x : ℝ => x * J)
                              (add_div Cstatic Cerror ‖w‖).symm
                        _ = (C / ‖w‖) * J := by
                          rfl
                    le_trans htriangle
                      (le_trans hsum (le_of_eq hcombine)))⟩

/-- Compatibility triangle from separate endpoint-restored static-boundary and
endpoint-restored contour-error estimates.

This constructor is useful only if such separate estimates are independently
available.  It is not the canonical owner route for the endpoint-restored wall
cancellation, because the restored static limit carries a half-endpoint defect
while the restored contour error tends to zero.  The canonical endpoint
bookkeeping route is
`binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_endpointReturnedRestoredPair_decay`. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_boundarySolvedStatic_and_endpointRestoredContourError_decay
    (hfinite :
      ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
        0 < R ∧
        0 < Cstatic ∧
        0 < Cerror ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∃ N : ℕ,
              (∀ᶠ T : ℝ in atTop,
                ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
                  Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                  Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                  (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    (Cstatic / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w) ∧
              (∀ᶠ T : ℝ in atTop,
                ‖Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T‖ ≤
                    (Cerror / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w)) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∀ᶠ T : ℝ in atTop,
            ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
              (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
              (C / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w := by
  match hfinite with
  | ⟨R, Cstatic, Cerror, hR_pos, hCstatic_pos, hCerror_pos, hbounds⟩ =>
      let C : ℝ := Cstatic + Cerror
      have hC_pos : 0 < C :=
        add_pos hCstatic_pos hCerror_pos
      exact
        ⟨R, C, hR_pos, hC_pos,
          fun w hw_re_pos hRle =>
            match hbounds w hw_re_pos hRle with
            | ⟨N, hstatic, herror⟩ =>
                (hstatic.and herror).mono
                  (fun T hpair =>
                    let J : ℝ :=
                      Complex.binetSecondFormulaDecayingTailIntegral w
                    let S : ℂ :=
                      ((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
                        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)
                    let E : ℂ :=
                      Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T
                    have htriangle :
                        ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                          ‖S‖ + ‖E‖ :=
                      Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_endpointRestoredContourError_owner
                        N w T
                    have hstatic_T :
                        ‖S‖ ≤ (Cstatic / ‖w‖) * J :=
                      hpair.1
                    have herror_T :
                        ‖E‖ ≤ (Cerror / ‖w‖) * J :=
                      hpair.2
                    have hsum :
                        ‖S‖ + ‖E‖ ≤
                          (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J :=
                      add_le_add hstatic_T herror_T
                    have hcombine :
                        (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J =
                          (C / ‖w‖) * J := by
                      calc
                        (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J =
                            (Cstatic / ‖w‖ + Cerror / ‖w‖) * J := by
                          exact
                            (right_distrib (Cstatic / ‖w‖)
                              (Cerror / ‖w‖) J).symm
                        _ = ((Cstatic + Cerror) / ‖w‖) * J := by
                          exact
                            congrArg (fun x : ℝ => x * J)
                              (add_div Cstatic Cerror ‖w‖).symm
                        _ = (C / ‖w‖) * J := by
                          rfl
                    le_trans htriangle
                      (le_trans hsum (le_of_eq hcombine)))⟩

/-- Endpoint-returned restored pair decay from a finite-height cancelled lower
vertical estimate.

This is the reverse bookkeeping direction to the consumption theorem below.
The endpoint-returned expression is not a new analytic object: by the
endpoint-returned norm identity it is exactly the finite-height lower vertical
side after subtracting the fixed initial Binet window. -/
theorem Complex.binetSecondFormula_endpointReturnedRestoredPair_decay_of_finiteHeightLowerVerticalDifference_decay
    (hfinite :
      Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay) :
    Complex.BinetSecondFormulaEndpointReturnedRestoredPairDecay := by
  match hfinite with
  | ⟨R, C, hR_pos, hC_pos, hbounds⟩ =>
      exact
        ⟨R, C, hR_pos, hC_pos,
          fun w hw_re_pos hRle =>
            ⟨0,
              (hbounds w hw_re_pos hRle).mono
                (fun T hlower_T =>
                  let P : ℂ :=
                    (((((∫ x : ℝ in (0 : ℝ)..((0 + 1 : ℕ) : ℝ),
                        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
                      Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo 0 w T -
                      Complex.finiteAbelPlanaLogPVIntegerResidueContribution 0 w) -
                      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
                      Complex.finiteAbelPlanaLogSummandHalfEndpoints 0 w) -
                      (Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError 0 w T +
                        Complex.finiteAbelPlanaLogSummandHalfEndpoints 0 w))
                  have hnorm :
                      ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ =
                        ‖P‖ :=
                    Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_eq_endpointReturnedRestoredPair_norm_owner
                      0 w T
                  Eq.subst
                    (motive := fun x : ℝ =>
                      x ≤
                        (C / ‖w‖) *
                          Complex.binetSecondFormulaDecayingTailIntegral w)
                    hnorm
                    hlower_T)⟩⟩

/-- Finite-height lower-vertical decay from the endpoint-returned restored
paired estimate.

This is the canonical endpoint-restored consumption surface.  The restored
static expression and restored contour error are not bounded separately;
instead the half-endpoint term is returned to both sides of their paired
difference, where it cancels algebraically before the finite-height lower side
is identified. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_endpointReturnedRestoredPair_decay
    (hfinite : Complex.BinetSecondFormulaEndpointReturnedRestoredPairDecay) :
    Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay := by
  match hfinite with
  | ⟨R, C, hR_pos, hC_pos, hbounds⟩ =>
      exact
        ⟨R, C, hR_pos, hC_pos,
          fun w hw_re_pos hRle =>
            match hbounds w hw_re_pos hRle with
            | ⟨N, hpair_bound⟩ =>
                hpair_bound.mono
                  (fun T hpair_T =>
                    let P : ℂ :=
                      (((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
                        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
                        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) -
                        (Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T +
                          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w))
                    have hnorm :
                        ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ =
                          ‖P‖ :=
                      Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_eq_endpointReturnedRestoredPair_norm_owner
                        N w T
                    Eq.subst
                      (motive := fun x : ℝ =>
                        x ≤
                          (C / ‖w‖) *
                            Complex.binetSecondFormulaDecayingTailIntegral w)
                      hnorm.symm
                      hpair_T)⟩

/-- Full lower-vertical difference decay from the endpoint-returned restored
paired finite-height estimate.

This is the predicate-level closure of
`binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_endpointReturnedRestoredPair_decay`:
the paired finite-height estimate bounds the cancelled lower vertical side
eventually, and the lower-vertical closure theorem transports that bound to
the full improper lower-vertical difference. -/
theorem Complex.binetSecondFormula_lowerVerticalDifference_decay_of_endpointReturnedRestoredPair_decay
    (hfinite : Complex.BinetSecondFormulaEndpointReturnedRestoredPairDecay) :
    Complex.BinetSecondFormulaLowerVerticalDifferenceDecay := by
  have hfinite_lower :
      Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay :=
    Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_endpointReturnedRestoredPair_decay
      hfinite
  exact
    Complex.binetSecondFormula_lowerVerticalDifference_decay_of_eventually_lowerVerticalUpTo_decay
      hfinite_lower

/-- Endpoint-returned restored pair decay is equivalent to the finite-height
cancelled lower-vertical estimate.

This pins down the remaining branch-wall analytic target as a single
finite-height lower-vertical bound.  The endpoint-returned formulation is the
canonical Abel-Plana bookkeeping form; the lower-vertical formulation is the
canonical analytic estimate form. -/
theorem Complex.binetSecondFormula_endpointReturnedRestoredPair_decay_iff_finiteHeightLowerVerticalDifference_decay :
    Complex.BinetSecondFormulaEndpointReturnedRestoredPairDecay ↔
      Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay := by
  exact
    ⟨fun hpair =>
      Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_endpointReturnedRestoredPair_decay
        hpair,
      fun hlower =>
        Complex.binetSecondFormula_endpointReturnedRestoredPair_decay_of_finiteHeightLowerVerticalDifference_decay
          hlower⟩

/-- Branch-wall tail absorption from the finite-height cancelled lower-vertical
estimate.

This is the direct owner-level consumption surface for the branch-wall analytic
input: finite-height lower-vertical cancellation is first closed to the full
improper lower vertical side, then the lower-vertical split gives tail
absorption. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_finiteHeightLowerVerticalDifference_decay
    (hfinite :
      Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  have hlower :
      Complex.BinetSecondFormulaLowerVerticalDifferenceDecay :=
    Complex.binetSecondFormula_lowerVerticalDifference_decay_of_eventually_lowerVerticalUpTo_decay
      hfinite
  exact
    Complex.binetSecondFormula_branchTail_wallCancellation_of_lowerVerticalDifference_decay
      hlower

/-- Full Binet branch package from the finite-height cancelled lower-vertical
estimate.

This is the exact non-circular analytic input needed by downstream Gamma/Binet
value owners: the finite-height wall-cancellation estimate supplies tail
absorption, and branch coherence is already owned by the Binet logarithm
coherence theorem. -/
theorem Complex.binetSecondFormula_branchUniformTailAbsorption_of_finiteHeightLowerVerticalDifference_decay
    (hfinite :
      Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay) :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption := by
  have htail :
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption :=
    Complex.binetSecondFormula_branchTail_wallCancellation_of_finiteHeightLowerVerticalDifference_decay
      hfinite
  exact
    Complex.BinetSecondFormulaBranchUniformTailAbsorption.of_tail_ownerCoherence
      htail

/-- Compatibility branch-wall tail absorption constructor from separate
endpoint-restored finite-height static-boundary and endpoint-restored
contour-error estimates.

The canonical endpoint-restored owner route is the paired endpoint-return
estimate below.  This theorem remains as a transport lemma for a proof
that genuinely supplies both separate estimates without discarding the endpoint
defect. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_boundarySolvedStatic_and_endpointRestoredContourError_decay
    (hfinite :
      ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
        0 < R ∧
        0 < Cstatic ∧
        0 < Cerror ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∃ N : ℕ,
              (∀ᶠ T : ℝ in atTop,
                ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
                  Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                  Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                  (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    (Cstatic / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w) ∧
              (∀ᶠ T : ℝ in atTop,
                ‖Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T‖ ≤
                    (Cerror / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w)) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  have hlower :
      ∃ R : ℝ, ∃ C : ℝ,
        0 < R ∧
        0 < C ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∀ᶠ T : ℝ in atTop,
              ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                  Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                (C / ‖w‖) *
                  Complex.binetSecondFormulaDecayingTailIntegral w :=
    Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_boundarySolvedStatic_and_endpointRestoredContourError_decay
      hfinite
  exact
    Complex.binetSecondFormula_branchTail_wallCancellation_of_eventually_lowerVerticalUpTo_decay
      hlower

/-- Branch-wall tail absorption from the endpoint-returned restored paired
finite-height estimate.

This is the non-circular endpoint-restored replacement for the historical
static/error split: the finite-height analytic input is the paired expression
whose two half-endpoint terms cancel algebraically. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_endpointReturnedRestoredPair_decay
    (hfinite : Complex.BinetSecondFormulaEndpointReturnedRestoredPairDecay) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  have hlower :
      Complex.BinetSecondFormulaLowerVerticalDifferenceDecay :=
    Complex.binetSecondFormula_lowerVerticalDifference_decay_of_endpointReturnedRestoredPair_decay
      hfinite
  exact
    Complex.binetSecondFormula_branchTail_wallCancellation_of_lowerVerticalDifference_decay
      hlower

/-- Full Binet branch package from the endpoint-returned restored paired
finite-height decay target.

The paired decay target supplies the tail-absorption half of
`BinetSecondFormulaBranchUniformTailAbsorption`; the branch-coherence half is
the already-owned Binet logarithm coherence theorem. -/
theorem Complex.binetSecondFormula_branchUniformTailAbsorption_of_endpointReturnedRestoredPair_decay
    (hfinite : Complex.BinetSecondFormulaEndpointReturnedRestoredPairDecay) :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption := by
  have htail :
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption :=
    Complex.binetSecondFormula_branchTail_wallCancellation_of_endpointReturnedRestoredPair_decay
      hfinite
  exact
    Complex.BinetSecondFormulaBranchUniformTailAbsorption.of_tail_ownerCoherence
      htail

/-- Finite-height lower-vertical decay from the solved static boundary decay.

The contour-error estimate is discharged by the finite-height boundary target
and the paired contour-error cancellation theorem, so the only remaining
analytic input is the solved static boundary expression. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_boundarySolvedStatic_decay
    (hfinite :
      ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
        0 < R ∧
        2 ≤ R ∧
        0 < Cstatic ∧
        0 < Cerror ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∃ N : ℕ,
              (∀ᶠ T : ℝ in atTop,
                (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                      (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                        Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                    (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
                  ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                      (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                        Complex.I *
                          Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                    (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
                  Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T) ∧
              (∀ᶠ T : ℝ in atTop,
                ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                  Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                  Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                  Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                  (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    (Cstatic / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w)) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∀ᶠ T : ℝ in atTop,
            ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
              (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
              (C / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w := by
  match hfinite with
  | ⟨R, Cstatic, Cerror, hR_pos, hR_two, hCstatic_pos, hCerror_pos, hbounds⟩ =>
      have hwith_error :
          ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
            0 < R ∧
            0 < Cstatic ∧
            0 < Cerror ∧
            ∀ w : ℂ,
              0 < w.re →
              R ≤ ‖w‖ →
                ∃ N : ℕ,
                  (∀ᶠ T : ℝ in atTop,
                    ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                      Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                        (Cstatic / ‖w‖) *
                          Complex.binetSecondFormulaDecayingTailIntegral w) ∧
                  (∀ᶠ T : ℝ in atTop,
                    ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
                        (Cerror / ‖w‖) *
                          Complex.binetSecondFormulaDecayingTailIntegral w) := by
        exact
          ⟨R, Cstatic, Cerror, hR_pos, hCstatic_pos, hCerror_pos,
            fun w hw_re_pos hRle =>
              match hbounds w hw_re_pos hRle with
              | ⟨N, hboundary, hstatic⟩ =>
                  have hw_norm_two : 2 ≤ ‖w‖ :=
                    le_trans hR_two hRle
                  have herror :
                      ∀ᶠ T : ℝ in atTop,
                        ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
                          (Cerror / ‖w‖) *
                            Complex.binetSecondFormulaDecayingTailIntegral w :=
                    Complex.binetSecondFormula_finiteHeightContourError_eventually_scaled_decayingTail_of_boundaryTarget_owner
                      hw_re_pos hw_norm_two N hboundary hCerror_pos
                  ⟨N, hstatic, herror⟩⟩
      exact
        Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_boundarySolvedStatic_and_contourError_decay
          hwith_error

/-- Assemble the solved-static package from the structural boundary target
and the quantitative solved-static estimate.

The boundary target supplies the finite-height Abel-Plana normalized boundary
identity; the quantitative predicate supplies only the static norm estimate.
This keeps the analytic scale estimate separate from the contour assembly. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_decay_of_boundaryTarget_and_staticEstimate
    (hboundary :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTarget)
    (hstatic :
      Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate)
    (Cerror : ℝ)
    (hCerror_pos : 0 < Cerror) :
    ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
      0 < R ∧
      2 ≤ R ∧
      0 < Cstatic ∧
      0 < Cerror ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∃ N : ℕ,
            (∀ᶠ T : ℝ in atTop,
              (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                    (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                      Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                  (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
                ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                    (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                      Complex.I *
                        Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                  (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
                Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T) ∧
            (∀ᶠ T : ℝ in atTop,
              ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                  Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                  Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                  (Cstatic / ‖w‖) *
                    Complex.binetSecondFormulaDecayingTailIntegral w) := by
  match hboundary with
  | ⟨Rboundary, hRboundary_pos, hRboundary_two, hboundary_bound⟩ =>
      match hstatic with
      | ⟨Rstatic, Cstatic, hRstatic_pos, hRstatic_two, hCstatic_pos, hstatic_bound⟩ =>
          let R : ℝ := max Rboundary Rstatic
          have hR_pos : 0 < R :=
            lt_of_lt_of_le hRboundary_pos (le_max_left Rboundary Rstatic)
          have hR_two : 2 ≤ R :=
            le_trans hRboundary_two (le_max_left Rboundary Rstatic)
          exact
            ⟨R, Cstatic, Cerror, hR_pos, hR_two, hCstatic_pos, hCerror_pos,
              fun w hw_re_pos hRle =>
                have hRboundary_le : Rboundary ≤ ‖w‖ :=
                  le_trans (le_max_left Rboundary Rstatic) hRle
                have hRstatic_le : Rstatic ≤ ‖w‖ :=
                  le_trans (le_max_right Rboundary Rstatic) hRle
                match hstatic_bound w hw_re_pos hRstatic_le with
                | ⟨N, hstatic_T⟩ =>
                    have hboundary_T :
                        ∀ᶠ T : ℝ in atTop,
                          (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                                (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                                  Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                              (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
                            ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                                (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                                  Complex.I *
                                    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                              (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
                            Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T :=
                      hboundary_bound w hw_re_pos hRboundary_le N
                    ⟨N, hboundary_T, hstatic_T⟩⟩

/-- The lower-vertical difference decay predicate is exactly the public
wall-cancellation theorem after transporting across the proved Binet tail
split. -/
theorem Complex.binetSecondFormula_lowerVerticalDifference_decay_iff_wallCancellation :
    Complex.BinetSecondFormulaLowerVerticalDifferenceDecay ↔
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  exact
    Iff.intro
      (fun hdifference =>
      Complex.binetSecondFormula_branchTail_wallCancellation_of_lowerVerticalDifference_decay
        hdifference)
      (fun htail =>
        match htail with
        | ⟨R, C, hR_pos, hC_pos, htail_bound⟩ =>
            ⟨R, C, hR_pos, hC_pos,
              fun w hw_re_pos hRle =>
                have hnorm :
                    ‖Complex.binetSecondFormulaTailRemainder w‖ =
                      ‖Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
                        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ :=
                  Complex.binetSecondFormula_tailRemainder_norm_eq_lowerVerticalFullIntegral_sub_initialWindow_norm_owner
                    hw_re_pos
                Eq.subst
                  (motive := fun x : ℝ =>
                    x ≤
                      (C / ‖w‖) *
                        Complex.binetSecondFormulaDecayingTailIntegral w)
                  hnorm
                  (htail_bound w hw_re_pos hRle)⟩)

/-- Finite-height lower-vertical decay from public wall-cancellation tail
absorption.

This is a pure transport theorem.  Wall cancellation is first moved to the
full lower-vertical difference by the Binet tail split, and then convergence
transports that full lower-vertical bound back to finite height with a doubled
constant. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_wallCancellation
    (htail :
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption) :
    Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay := by
  have hdifference :
      Complex.BinetSecondFormulaLowerVerticalDifferenceDecay :=
    Complex.binetSecondFormula_lowerVerticalDifference_decay_iff_wallCancellation.mpr
      htail
  exact
    Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_lowerVerticalDifference_decay
      hdifference

/-- Constructor from a genuinely contour-deformed kernel comparison and a
uniform full-sector kernel majorant to branch-wall tail absorption.

This is the non-circular contour route: the comparison to `K` is an
integral-level contour statement, and the majorant for `K` is the ordinary
decaying scalar Binet tail.  No raw principal-branch wall estimate is used. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_contourKernel_uniformMajorant
    {K : Complex.BinetSecondFormulaContourDeformedTailKernel}
    {R C : ℝ}
    (hR_pos : 0 < R)
    (hC_pos : 0 < C)
    (hcomparison : Complex.BinetSecondFormulaContourTailIntegralComparison K R)
    (hK_integrable :
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          MeasureTheory.IntegrableOn
            (fun t : ℝ => K w t)
            (Set.Ioi (‖w‖ / 2)))
    (hmajorant : Complex.BinetSecondFormulaContourTailUniformMajorant K R C) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  let Ctail : ℝ := 2 * C
  have hCtail_pos : 0 < Ctail :=
    mul_pos two_pos hC_pos
  have hdecay :
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), ‖K w t‖ ≤
            (Ctail / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
    exact fun w hw_re_pos hRle =>
      have hraw :
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), ‖K w t‖ ≤
            ((2 * C) / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
        Complex.binetSecondFormula_contourTailKernel_integral_decay_of_uniform_majorant
          hK_integrable
          hmajorant
          w hw_re_pos hRle
      have hCtail_eq : Ctail = 2 * C := by
        rfl
      Eq.subst
          (motive := fun x : ℝ =>
            2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), ‖K w t‖ ≤
              (x / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                  t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
          hCtail_eq.symm
          hraw
  exact
    ⟨R, Ctail, hR_pos, hCtail_pos,
      Complex.binetSecondFormula_tailRemainder_norm_le_of_contourTailKernel_integral_decay
        hcomparison
        hdecay⟩

/-- Specialized branch-wall transport through the canonical decaying contour
kernel.

This is a pure assembly lemma: an integral-level contour comparison to
`binetSecondFormulaDecayingTailKernel` immediately gives the public wall
cancellation bound because that kernel is already integrable and has the
uniform full-sector decaying majorant. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_decayingContourKernelComparison
    (hcomparison :
      Complex.BinetSecondFormulaContourTailIntegralComparison
        Complex.binetSecondFormulaDecayingTailKernel 2) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  exact
    Complex.binetSecondFormula_branchTail_wallCancellation_of_contourKernel_uniformMajorant
      (K := Complex.binetSecondFormulaDecayingTailKernel)
      (R := 2)
      (C := 1)
      two_pos
      zero_lt_one
      hcomparison
      (fun w _hw_re_pos _hRle =>
        Complex.binetSecondFormula_decayingTailKernel_integrableOn_tail w)
      Complex.binetSecondFormula_decayingTailKernel_uniform_majorant

/-- Finite-height lower-vertical decay from the canonical decaying contour
kernel comparison.

This is the finite-height form of
`binetSecondFormula_branchTail_wallCancellation_of_decayingContourKernelComparison`:
the contour comparison gives wall cancellation, and wall cancellation is then
transported back to finite height by convergence of the lower vertical side. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_decayingContourKernelComparison
    (hcomparison :
      Complex.BinetSecondFormulaContourTailIntegralComparison
        Complex.binetSecondFormulaDecayingTailKernel 2) :
    Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay := by
  have htail :
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption :=
    Complex.binetSecondFormula_branchTail_wallCancellation_of_decayingContourKernelComparison
      hcomparison
  exact
    Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_wallCancellation
      htail

/-- Branch-wall transport from a contour-deformed kernel with a decaying
majorant.

This is a pure assembly lemma: an integral-level contour comparison to a
kernel `K`, split-tail integrability of `K`, and the uniform full-sector
`C / ‖w‖` majorant for `K` imply the public wall cancellation bound. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_contourKernelPackage
    (hpackage :
      ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel,
        ∃ R : ℝ, ∃ C : ℝ,
          0 < R ∧
          0 < C ∧
          Complex.BinetSecondFormulaContourTailIntegralComparison K R ∧
          (∀ w : ℂ,
            0 < w.re →
            R ≤ ‖w‖ →
              MeasureTheory.IntegrableOn
                (fun t : ℝ => K w t)
                (Set.Ioi (‖w‖ / 2))) ∧
          Complex.BinetSecondFormulaContourTailUniformMajorant K R C) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  match hpackage with
  | ⟨K, R, C, hR_pos, hC_pos, hcomparison, hK_integrable, hmajorant⟩ =>
      exact
        Complex.binetSecondFormula_branchTail_wallCancellation_of_contourKernel_uniformMajorant
          (K := K)
          (R := R)
          (C := C)
          hR_pos
          hC_pos
          hcomparison
          hK_integrable
          hmajorant

/-- Finite-height lower-vertical decay from a contour-kernel package.

This is a pure finite-height assembly lemma for future analytic leaves: once
a branch-safe contour-deformed kernel is supplied together with its integral
comparison, split-tail integrability, and uniform decaying majorant, the
finite-height lower-vertical cancellation predicate follows. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_contourKernelPackage
    (hpackage :
      ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel,
        ∃ R : ℝ, ∃ C : ℝ,
          0 < R ∧
          0 < C ∧
          Complex.BinetSecondFormulaContourTailIntegralComparison K R ∧
          (∀ w : ℂ,
            0 < w.re →
            R ≤ ‖w‖ →
              MeasureTheory.IntegrableOn
                (fun t : ℝ => K w t)
                (Set.Ioi (‖w‖ / 2))) ∧
          Complex.BinetSecondFormulaContourTailUniformMajorant K R C) :
    Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay := by
  have htail :
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption :=
    Complex.binetSecondFormula_branchTail_wallCancellation_of_contourKernelPackage
      hpackage
  exact
    Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_wallCancellation
      htail

/-- Assemble the historical solved-static input pair from the structural
boundary target and an independent decaying contour-kernel comparison.

This is the non-circular contour route to the old static input pair.  The
remaining analytic comparison is integral-level: the actual Binet tail
remainder must be compared with the already majorized decaying contour kernel.
Once that comparison is supplied, branch-wall tail absorption and solved-static
decay are both pure owner-level transports. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_inputs_of_boundaryTarget_and_decayingContourKernelComparison
    (hboundary :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTarget)
    (hcomparison :
      Complex.BinetSecondFormulaContourTailIntegralComparison
        Complex.binetSecondFormulaDecayingTailKernel 2) :
    Complex.BinetSecondFormulaFiniteHeightBoundaryTarget ∧
      Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate := by
  have htail :
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption :=
    Complex.binetSecondFormula_branchTail_wallCancellation_of_decayingContourKernelComparison
      hcomparison
  exact
    Complex.binetSecondFormula_boundarySolvedStatic_inputs_of_boundaryTarget_and_tailAbsorption
      hboundary htail

/-- Assemble the historical solved-static input pair from the structural
boundary target and a contour-tail majorant integral decay estimate.

This is the non-circular route through the already compared contour majorant
kernel: the majorant integral estimate gives tail absorption, and the static
decay is then only a full-height cancellation transport. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_inputs_owner :
    ¬ (Complex.BinetSecondFormulaFiniteHeightBoundaryTarget ∧
        Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate) := by
  exact Complex.not_binetSecondFormula_boundarySolvedStatic_inputs_owner_target

/-- Owner obstruction for the historical solved-static Abel-Plana boundary
decay route.

The old route bundled the endpoint-free boundary target into the finite-height
static decay package.  Since that boundary target is false, the route is not a
valid owner theorem. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_decay_owner :
    ¬ (Complex.BinetSecondFormulaFiniteHeightBoundaryTarget ∧
        Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate) := by
  exact Complex.binetSecondFormula_boundarySolvedStatic_inputs_owner

/-- Endpoint-restored finite-height contour input at the lower-vertical
bookkeeping layer. -/
theorem Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_lowerVertical_owner :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs := by
  exact
    Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_owner

/-- Endpoint-restored finite-height contour input available at the historical
lower-vertical owner location. -/
theorem Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_lowerVertical_compat :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs := by
  exact
    Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_owner

/-- Endpoint-restored finite-height contour input available at the historical
branch-wall owner location. -/
theorem Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_branchWall_compat :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs := by
  exact
    Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_owner

/-- Owner analytic package currently available after endpoint restoration:
sector window plus corrected finite-height contour inputs. -/
theorem Complex.binetSecondFormula_branchTail_sectorWindow_and_endpointRestoredFiniteHeightContourInputs_owner :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorLogWindowComparison ∧
      Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs := by
  exact
    ⟨Complex.binetSecondFormula_branchTail_sectorWindow_owner,
      Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_branchWall_compat⟩

/-- Projection of sector-local absorption of the branch-wall local-indentation
envelope into the standard Binet decaying tail integral. -/
theorem Complex.binetSecondFormula_branchLocalIndentation_sectorLogWindowComparison_owner :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorLogWindowComparison := by
  exact
    Complex.binetSecondFormula_branchTail_sectorWindow_owner

/-- Owner sector-local tail-remainder estimate after absorbing the
local-indentation envelope. -/
theorem Complex.binetSecondFormula_tailRemainder_sectorBound_owner :
    Complex.BinetSecondFormulaTailRemainderSectorLocalAbsorption := by
  exact
    Complex.binetSecondFormula_tailRemainder_sectorBound_of_localIndentation_absorption
      Complex.binetSecondFormula_tailRemainder_localIndentation_add_far_scaled_decay_ownerGap
      Complex.binetSecondFormula_branchLocalIndentation_sectorAbsorption_owner

/-- Principal-tail sector estimate after absorbing the local-indentation envelope.

The input `hlocal` is the contour estimate with the branch-wall window still
visible; `habsorb` is the scale-correct sector-local absorption theorem for
that window.  The conclusion keeps the local scalar contribution as `Clocal`;
the pure `C / ‖w‖` full-sector decay is owned below by paired branch-wall
contour cancellation. -/
theorem Complex.binetSecondFormula_branchWall_tailAbsorption_of_principalTailCancellation
    (hprincipal :
      Complex.BinetSecondFormulaBranchWallPrincipalTailCancellation) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  match hprincipal with
  | ⟨C, hC_pos, hprincipal_bound⟩ =>
      let Rtail : ℝ := 2
      let Ctail : ℝ := C + 2
      have hRtail_pos : 0 < Rtail :=
        two_pos
      have hCtail_pos : 0 < Ctail :=
        add_pos hC_pos two_pos
      have hcontour_decay :
          ∀ w : ℂ,
            0 < w.re →
            Rtail ≤ ‖w‖ →
              2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                  ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ ≤
                (Ctail / ‖w‖) *
                  Complex.binetSecondFormulaDecayingTailIntegral w :=
        Complex.binetSecondFormula_contourTailMajorantKernel_integral_accounting
          hprincipal_bound
          Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_le_ownerGap
      have htail_decay :
          ∀ w : ℂ,
            0 < w.re →
            Rtail ≤ ‖w‖ →
              ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
                (Ctail / ‖w‖) *
                  Complex.binetSecondFormulaDecayingTailIntegral w :=
        Complex.binetSecondFormula_tailRemainder_norm_le_of_contourTailMajorantKernel_integral_decay
          hcontour_decay
      exact
        ⟨Rtail, Ctail, hRtail_pos, hCtail_pos, htail_decay⟩

/-- Wall tail absorption from the sharp bounded-window branch-wall estimate.

This is the correctly localized owner reduction: after the far tail has been
handled by the existing scaled estimate, the remaining theorem is exactly the
bounded-window moving-spike cancellation estimate. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_boundedWindow_decay
    (hbounded :
      ∃ Cbounded : ℝ,
        0 < Cbounded ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
              (Cbounded / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  exact
    Complex.binetSecondFormula_branchWall_tailAbsorption_of_principalTailCancellation
      (Complex.binetSecondFormula_branchWallPrincipalTailCancellation_of_boundedWindow_decay
        hbounded)

/-- Wall tail absorption from a scaled estimate for the weighted moving
branch-wall logarithmic envelope on the bounded window. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_weightedFullLogEnvelope_decay
    (hweighted :
      ∃ Cweighted : ℝ,
        0 < Cweighted ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 *
                  (max |Real.log (w.re / (3 * ‖w‖))|
                    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
                    Real.pi)) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cweighted / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  exact
    Complex.binetSecondFormula_branchTail_wallCancellation_of_boundedWindow_decay
      (Complex.binetSecondFormula_boundedWindow_decay_of_weightedFullLogEnvelope_decay
        hweighted)

/-- Branch-wall tail absorption from the legacy principal-tail norm estimate.

This is now a thin wrapper through the contour-level tail-remainder decay
target, keeping the final tail package independent of the raw principal-kernel
norm formulation. -/
theorem Complex.binetSecondFormula_branchUniform_tail_absorption_of_principalTailCancellation
    (hprincipal :
      Complex.BinetSecondFormulaBranchWallPrincipalTailCancellation) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  exact
    Complex.binetSecondFormula_branchWall_tailAbsorption_of_principalTailCancellation
      hprincipal

/-- Endpoint-restored finite-height contour input available at the historical
branch-uniform tail owner location. -/
theorem Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_branchUniformTail_compat :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs := by
  exact
    Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_owner

/-- Endpoint-restored finite-height contour input available at the historical
branch-uniform package owner location. -/
theorem Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_branchUniform_compat :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs :=
  Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_branchUniformTail_compat

/-- Branch-uniform full-sector integral tail majorant for the Binet arctangent
kernel, after contour deformation. -/
theorem Complex.binetSecondFormula_arctan_tail_branchUniform_fullSector_integral_majorant_from_contour
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (2 * C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  match Complex.BinetSecondFormulaBranchUniformTailAbsorption.tail hbranch with
  | ⟨R, C, hR, hC, htail⟩ =>
      let htail' :
          ∀ w : ℂ,
            0 < w.re →
            R ≤ ‖w‖ →
              ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
                (2 * (C / 2) / ‖w‖) *
                  (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
        fun w hw_re_pos hRle =>
          have hscale :
              2 * (C / 2) / ‖w‖ = C / ‖w‖ :=
            congrArg (fun x : ℝ => x / ‖w‖) (mul_div_cancel₀ C two_ne_zero)
          Eq.subst
            (motive := fun x : ℝ =>
              ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
                x *
                  (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
            hscale.symm
            (htail w hw_re_pos hRle)
      exact
        ⟨R, C / 2, hR, half_pos hC,
          htail'⟩

/-- Integrated form of the branch-uniform full-sector tail majorant.

This theorem contains no branch analysis: it repackages the contour-deformed
integral majorant with the constant in the usual `C / ‖w‖` form. -/
theorem Complex.binetSecondFormula_arctan_tail_branchUniform_fullSector_integral_majorant :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := fun hbranch =>
  let ⟨Rtail, Ctail, hRtail, hCtail, htail⟩ :=
    Complex.binetSecondFormula_arctan_tail_branchUniform_fullSector_integral_majorant_from_contour
      hbranch
  ⟨Rtail, 2 * Ctail, hRtail, mul_pos two_pos hCtail,
    fun w hw_re_pos hRtail_le => htail w hw_re_pos hRtail_le⟩

/-- Full-sector tail absorption for the Binet remainder split at `‖w‖ / 2`.

The only analytic root used here is the branch-uniform integrated tail
majorant above.  The remaining argument is real-variable tail absorption: the
Binet majorant tail decays exponentially from `‖w‖ / 2`, hence is bounded by a
constant for large `‖w‖`, leaving the explicit `1 / ‖w‖` factor. -/
theorem Complex.binetSecondFormula_tail_remainder_fullSector_norm_le_div_norm :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤ K / ‖w‖ := fun hbranch =>
  let ⟨Rtail, Ctail, hRtail, hCtail, htail_majorant⟩ :=
    Complex.binetSecondFormula_arctan_tail_branchUniform_fullSector_integral_majorant
      hbranch
  ⟨max Rtail 2, 2 * Ctail,
    lt_of_lt_of_le hRtail (le_max_left Rtail 2),
    mul_pos two_pos hCtail,
    fun w hw_re_pos hw_norm_large =>
      let hRtail_le : Rtail ≤ ‖w‖ :=
        le_trans (le_max_left Rtail 2) hw_norm_large
      let htwo_le_norm : (2 : ℝ) ≤ ‖w‖ :=
        le_trans (le_max_right Rtail 2) hw_norm_large
      let hhalf_ge_one : (1 : ℝ) ≤ ‖w‖ / 2 :=
        (le_div_iff₀ two_pos).mpr
          (Eq.subst
            (motive := fun x : ℝ => x ≤ ‖w‖)
            (one_mul (2 : ℝ)).symm
            htwo_le_norm)
      let htail :
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (Ctail / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
        htail_majorant w hw_re_pos hRtail_le
      let hreal_tail :
          ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
            2 * Real.exp (-Real.pi * (‖w‖ / 2)) :=
        Real.binetSecondFormula_kernel_majorant_tail_integral_le_exp
          (a := ‖w‖ / 2) hhalf_ge_one
      let hcoeff_nonneg : 0 ≤ Ctail / ‖w‖ :=
        div_nonneg (le_of_lt hCtail) (norm_nonneg w)
      let htail_exp :
          (Ctail / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) ≤
            (Ctail / ‖w‖) *
              (2 * Real.exp (-Real.pi * (‖w‖ / 2))) :=
        mul_le_mul_of_nonneg_left hreal_tail hcoeff_nonneg
      let hexponent_nonpos : -Real.pi * (‖w‖ / 2) ≤ 0 :=
        let hproduct_nonneg : 0 ≤ Real.pi * (‖w‖ / 2) :=
          mul_nonneg (le_of_lt Real.pi_pos)
            (div_nonneg (norm_nonneg w) zero_le_two)
        calc
          -Real.pi * (‖w‖ / 2) = -(Real.pi * (‖w‖ / 2)) :=
            neg_mul Real.pi (‖w‖ / 2)
          _ ≤ 0 := neg_nonpos.mpr hproduct_nonneg
      let hexp_le_one : Real.exp (-Real.pi * (‖w‖ / 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr hexponent_nonpos
      let htwo_exp_le_two : 2 * Real.exp (-Real.pi * (‖w‖ / 2)) ≤ (2 : ℝ) :=
        calc
          2 * Real.exp (-Real.pi * (‖w‖ / 2)) ≤ 2 * 1 :=
            mul_le_mul_of_nonneg_left hexp_le_one zero_le_two
          _ = 2 := mul_one 2
      let htail_const :
          (Ctail / ‖w‖) *
              (2 * Real.exp (-Real.pi * (‖w‖ / 2))) ≤
            (Ctail / ‖w‖) * 2 :=
        mul_le_mul_of_nonneg_left htwo_exp_le_two hcoeff_nonneg
      let htarget : (Ctail / ‖w‖) * 2 = (2 * Ctail) / ‖w‖ :=
        calc
          (Ctail / ‖w‖) * 2 = (Ctail * ‖w‖⁻¹) * 2 := rfl
          _ = 2 * (Ctail * ‖w‖⁻¹) :=
            mul_comm (Ctail * ‖w‖⁻¹) 2
          _ = (2 * Ctail) * ‖w‖⁻¹ :=
            (mul_assoc 2 Ctail ‖w‖⁻¹).symm
          _ = (2 * Ctail) / ‖w‖ := rfl
      le_trans htail
        (le_trans htail_exp
          (le_trans htail_const
            (le_of_eq htarget)))⟩

/-- Convert the honest split Binet remainder bound to a pure
open-right-half-plane `O(1 / ‖w‖)` estimate from branch-tail absorption.

The small split piece already carries the explicit `1 / ‖w‖` factor. -/
theorem Complex.binetSecondFormula_remainder_bound_closedRightHalfPlane_requires_tail_absorption :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaRemainder w‖ ≤ K / ‖w‖ := fun hbranch =>
  let J : ℝ :=
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let ⟨Rtail, Ktail, hRtail, hKtail, htailBound⟩ :=
    Complex.binetSecondFormula_tail_remainder_fullSector_norm_le_div_norm
      hbranch
  let K : ℝ := 4 * J + Ktail
  let hJ_pos : 0 < J :=
    Real.binetSecondFormula_kernel_majorant_integral_pos
  let hK : 0 < K :=
    add_pos (mul_pos four_pos hJ_pos) hKtail
  ⟨Rtail, K, hRtail, hK, fun w hw_re_pos hRtail_le =>
    let hsplit :
        Complex.binetSecondFormulaRemainder w =
          Complex.binetSecondFormulaSmallRemainder w +
            Complex.binetSecondFormulaTailRemainder w :=
      Complex.binetSecondFormulaRemainder_eq_small_add_tail (w := w) hw_re_pos
    let hsmall :
        ‖Complex.binetSecondFormulaSmallRemainder w‖ ≤ 4 * J / ‖w‖ :=
      Complex.binetSecondFormula_small_remainder_norm_le_integral_majorant
        (w := w) hw_re_pos
    let htail :
        ‖Complex.binetSecondFormulaTailRemainder w‖ ≤ Ktail / ‖w‖ :=
      htailBound w hw_re_pos hRtail_le
    let hsum :
        ‖Complex.binetSecondFormulaSmallRemainder w +
            Complex.binetSecondFormulaTailRemainder w‖ ≤
          4 * J / ‖w‖ + Ktail / ‖w‖ :=
      calc
        ‖Complex.binetSecondFormulaSmallRemainder w +
            Complex.binetSecondFormulaTailRemainder w‖
            ≤ ‖Complex.binetSecondFormulaSmallRemainder w‖ +
                ‖Complex.binetSecondFormulaTailRemainder w‖ :=
          norm_add_le _ _
        _ ≤ 4 * J / ‖w‖ + Ktail / ‖w‖ :=
          add_le_add hsmall htail
    let hcombine :
        4 * J / ‖w‖ + Ktail / ‖w‖ = K / ‖w‖ :=
      calc
        4 * J / ‖w‖ + Ktail / ‖w‖ =
            (4 * J + Ktail) / ‖w‖ :=
          (add_div (4 * J) Ktail ‖w‖).symm
        _ = K / ‖w‖ := rfl
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ K / ‖w‖)
      hsplit.symm
      (hsum.trans_eq hcombine)⟩

/-- Pure-decay Binet/log-Gamma comparison from branch-tail absorption.

Use `Complex.binetSecondFormula_logGamma_with_split_remainder_bound_closedRightHalfPlane`
for the split statement.  This theorem converts the split Binet estimate into
pure `O(1 / ‖w‖)` decay using the same branch-tail absorption input. -/
theorem Complex.binetSecondFormula_logGamma_with_remainder_bound_closedRightHalfPlane_requires_tail_absorption :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        Complex.binetLogGammaBranch w =
            Complex.binetLogGammaMainTerm w +
              Complex.binetSecondFormulaRemainder w ∧
          ‖Complex.binetSecondFormulaRemainder w‖ ≤ K / ‖w‖ := fun hbranch =>
  let ⟨Rlog, hRlog, hlog⟩ :=
    Complex.binetSecondFormula_logGamma_closedRightHalfPlane_largeRadius
  let ⟨Rtail, K, _hRtail, hK, htail⟩ :=
    Complex.binetSecondFormula_remainder_bound_closedRightHalfPlane_requires_tail_absorption
      hbranch
  ⟨max Rlog Rtail, K,
    lt_of_lt_of_le hRlog (le_max_left Rlog Rtail),
    hK,
    fun w hw_re_pos hnorm =>
      let hRlog_le : Rlog ≤ ‖w‖ :=
        le_trans (le_max_left Rlog Rtail) hnorm
      let hRtail_le : Rtail ≤ ‖w‖ :=
        le_trans (le_max_right Rlog Rtail) hnorm
      ⟨hlog w hw_re_pos hRlog_le,
        htail w hw_re_pos hRtail_le⟩⟩

end
end LFunctions
end Boundary
