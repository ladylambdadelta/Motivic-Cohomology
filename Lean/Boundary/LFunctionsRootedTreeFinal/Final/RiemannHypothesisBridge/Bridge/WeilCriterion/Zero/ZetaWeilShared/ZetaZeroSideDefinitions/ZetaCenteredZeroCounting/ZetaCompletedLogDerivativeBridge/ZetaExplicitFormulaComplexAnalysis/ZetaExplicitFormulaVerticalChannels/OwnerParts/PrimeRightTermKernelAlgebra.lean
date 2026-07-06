import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineLineMeasurability

/-!
# Right von Mangoldt single-term kernel algebra

This file owns the definitional algebra for a single right-line von Mangoldt
Dirichlet term.  It deliberately contains no sum-integral exchange and no
Fourier inversion.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped LSeries.notation

namespace ZetaAdmissibleFunction

/-- The single Dirichlet term kernel on the right affine line. -/
noncomputable def zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (↗Λ) (zetaCompletedExplicitFormulaRightAffineLine F t) n *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)

/-- The single-term kernel is the product of the `n`th Dirichlet term and the
fixed test-transform factor on the right centered affine line. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F n t =
      LSeries.term (↗Λ) (zetaCompletedExplicitFormulaRightAffineLine F t) n *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) :=
  rfl

/-- At a positive natural index, the single-term kernel unfolds to the
ordinary Dirichlet monomial. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_eq_of_ne_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F n t =
      ((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
  unfold zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
  exact congrArg
    (fun z : ℂ =>
      z *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))
    (LSeries.term_of_ne_zero hn (↗Λ)
      (zetaCompletedExplicitFormulaRightAffineLine F t))

/-- The zeroth right von Mangoldt term kernel vanishes because the zeroth
Dirichlet-series term is defined to be zero. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F 0 t =
      0 := by
  unfold zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
  calc
    LSeries.term (↗Λ) (zetaCompletedExplicitFormulaRightAffineLine F t) 0 *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) =
        0 *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
      exact congrArg
        (fun z : ℂ =>
          z *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))
        (LSeries.term_zero (↗Λ)
          (zetaCompletedExplicitFormulaRightAffineLine F t))
    _ = 0 := by
      exact zero_mul
        (zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))

/-- The zeroth right von Mangoldt term has zero whole-line integral. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_integral_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
        f F 0 t) =
      0 := by
  have hfun :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel
          f F 0 t) =
        fun _t : ℝ => (0 : ℂ) := by
    funext t
    exact zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_zero
      f F t
  exact
    Eq.trans
      (congrArg
        (fun φ : ℝ → ℂ => ∫ t : ℝ, φ t)
        hfun)
      (integral_zero (α := ℝ) (G := ℂ))

/-- The norm of a right von Mangoldt term kernel factors into the norm of the
Dirichlet term and the norm of the test-transform factor. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_norm_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) (t : ℝ) :
    ‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F n t‖ =
      ‖LSeries.term (↗Λ)
          (zetaCompletedExplicitFormulaRightAffineLine F t) n‖ *
        ‖zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ := by
  exact
    norm_mul
      (LSeries.term (↗Λ)
        (zetaCompletedExplicitFormulaRightAffineLine F t) n)
      (zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
