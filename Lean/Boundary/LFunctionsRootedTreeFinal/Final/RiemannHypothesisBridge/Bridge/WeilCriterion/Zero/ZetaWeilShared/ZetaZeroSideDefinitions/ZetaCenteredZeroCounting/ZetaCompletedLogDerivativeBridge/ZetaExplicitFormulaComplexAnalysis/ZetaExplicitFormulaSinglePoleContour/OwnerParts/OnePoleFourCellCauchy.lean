import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.PositiveHeightRawCauchy

/-!
# Four-cell Cauchy specialization for the isolated `s = 1` correction pole

This file specializes the general four-cell Cauchy-Goursat theorem from the
single-pole contour owner to the isolated correction kernel

`z ↦ zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z`

and the one-point exceptional set `{1}`.  The remaining hypotheses are the real
analytic facts that the kernel is continuous on each closed cell and
differentiable on each open cell away from the pole.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The one-point exceptional set for the isolated `s = 1` correction kernel is
countable. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_singleton_countable :
    ({(1 : ℂ)} : Set ℂ).Countable :=
  Set.countable_singleton (1 : ℂ)

/-- Four-cell Cauchy cancellation for the isolated `s = 1` correction kernel,
with the exceptional set fixed to the pole `{1}` on every cell. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_fourCellBoundary_eq_zero_of_cellRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (HcBottom :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        ([[ ((1 - F.c) + (-T) * Complex.I).re,
             (F.c + (-R) * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + (-T) * Complex.I).im,
             (F.c + (-R) * Complex.I).im ]]))
    (HdBottom :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + (-T) * Complex.I).re
                  (F.c + (-R) * Complex.I).re)
                (max ((1 - F.c) + (-T) * Complex.I).re
                  (F.c + (-R) * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + (-T) * Complex.I).im
                  (F.c + (-R) * Complex.I).im)
                (max ((1 - F.c) + (-T) * Complex.I).im
                  (F.c + (-R) * Complex.I).im) \ ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcTop :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        ([[ ((1 - F.c) + R * Complex.I).re,
             (F.c + T * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + R * Complex.I).im,
             (F.c + T * Complex.I).im ]]))
    (HdTop :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + R * Complex.I).re
                  (F.c + T * Complex.I).re)
                (max ((1 - F.c) + R * Complex.I).re
                  (F.c + T * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + R * Complex.I).im
                  (F.c + T * Complex.I).im)
                (max ((1 - F.c) + R * Complex.I).im
                  (F.c + T * Complex.I).im) \ ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcLeft :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        ([[ ((1 - F.c) + (-R) * Complex.I).re,
             ((1 - R) + R * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + (-R) * Complex.I).im,
             ((1 - R) + R * Complex.I).im ]]))
    (HdLeft :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + (-R) * Complex.I).re
                  ((1 - R) + R * Complex.I).re)
                (max ((1 - F.c) + (-R) * Complex.I).re
                  ((1 - R) + R * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + (-R) * Complex.I).im
                  ((1 - R) + R * Complex.I).im)
                (max ((1 - F.c) + (-R) * Complex.I).im
                  ((1 - R) + R * Complex.I).im) \ ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcRight :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        ([[ ((1 + R) + (-R) * Complex.I).re,
             (F.c + R * Complex.I).re ]] ×ℂ
          [[ ((1 + R) + (-R) * Complex.I).im,
             (F.c + R * Complex.I).im ]]))
    (HdRight :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 + R) + (-R) * Complex.I).re
                  (F.c + R * Complex.I).re)
                (max ((1 + R) + (-R) * Complex.I).re
                  (F.c + R * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 + R) + (-R) * Complex.I).im
                  (F.c + R * Complex.I).im)
                (max ((1 + R) + (-R) * Complex.I).im
                  (F.c + R * Complex.I).im) \ ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x) :
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      F T R = 0 := by
  exact
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_zero_of_cauchy
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      F T R
      ({(1 : ℂ)} : Set ℂ)
      ({(1 : ℂ)} : Set ℂ)
      ({(1 : ℂ)} : Set ℂ)
      ({(1 : ℂ)} : Set ℂ)
      zetaCompletedExplicitFormulaCorrectionOnePole_singleton_countable
      zetaCompletedExplicitFormulaCorrectionOnePole_singleton_countable
      zetaCompletedExplicitFormulaCorrectionOnePole_singleton_countable
      zetaCompletedExplicitFormulaCorrectionOnePole_singleton_countable
      HcBottom HdBottom HcTop HdTop HcLeft HdLeft HcRight HdRight

/-- Canonical-puncture-radius four-cell Cauchy cancellation for the isolated
`s = 1` correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_fourCellBoundary_eq_zero_of_cellRegularity_canonicalRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (HcBottom :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        ([[ ((1 - F.c) + (-T) * Complex.I).re,
             (F.c + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + (-T) * Complex.I).im,
             (F.c + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im ]]))
    (HdBottom :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + (-T) * Complex.I).re
                  (F.c + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re)
                (max ((1 - F.c) + (-T) * Complex.I).re
                  (F.c + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + (-T) * Complex.I).im
                  (F.c + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im)
                (max ((1 - F.c) + (-T) * Complex.I).im
                  (F.c + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcTop :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        ([[ ((1 - F.c) + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re,
             (F.c + T * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im,
             (F.c + T * Complex.I).im ]]))
    (HdTop :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re
                  (F.c + T * Complex.I).re)
                (max ((1 - F.c) + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re
                  (F.c + T * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im
                  (F.c + T * Complex.I).im)
                (max ((1 - F.c) + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im
                  (F.c + T * Complex.I).im) \ ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcLeft :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        ([[ ((1 - F.c) + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re,
             ((1 - zetaExplicitFormulaOnePolePunctureRadius F T) +
                (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im,
             ((1 - zetaExplicitFormulaOnePolePunctureRadius F T) +
                (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im ]]))
    (HdLeft :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re
                  ((1 - zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re)
                (max ((1 - F.c) + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re
                  ((1 - zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im
                  ((1 - zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im)
                (max ((1 - F.c) + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im
                  ((1 - zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcRight :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        ([[ ((1 + zetaExplicitFormulaOnePolePunctureRadius F T) +
                (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re,
             (F.c + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re ]] ×ℂ
          [[ ((1 + zetaExplicitFormulaOnePolePunctureRadius F T) +
                (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im,
             (F.c + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im ]]))
    (HdRight :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 + zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re
                  (F.c + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re)
                (max ((1 + zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re
                  (F.c + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 + zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im
                  (F.c + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im)
                (max ((1 + zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im
                  (F.c + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x) :
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      F T (zetaExplicitFormulaOnePolePunctureRadius F T) = 0 := by
  exact
    zetaCompletedExplicitFormulaCorrectionOnePole_fourCellBoundary_eq_zero_of_cellRegularity
      f F T (zetaExplicitFormulaOnePolePunctureRadius F T)
      HcBottom HdBottom HcTop HdTop HcLeft HdLeft HcRight HdRight

/-- Positive-height raw standard Cauchy value from the canonical four-cell
Cauchy regularity hypotheses, the square-punctured boundary decomposition, and
the inner-square residue calculation. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_cellRegularity_boundary_inner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T : ℝ}
    (hT : 0 < T)
    (hboundary :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) =
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T))
    (HcBottom :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        ([[ ((1 - F.c) + (-T) * Complex.I).re,
             (F.c + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + (-T) * Complex.I).im,
             (F.c + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im ]]))
    (HdBottom :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + (-T) * Complex.I).re
                  (F.c + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re)
                (max ((1 - F.c) + (-T) * Complex.I).re
                  (F.c + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + (-T) * Complex.I).im
                  (F.c + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im)
                (max ((1 - F.c) + (-T) * Complex.I).im
                  (F.c + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcTop :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        ([[ ((1 - F.c) + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re,
             (F.c + T * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im,
             (F.c + T * Complex.I).im ]]))
    (HdTop :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re
                  (F.c + T * Complex.I).re)
                (max ((1 - F.c) + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re
                  (F.c + T * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im
                  (F.c + T * Complex.I).im)
                (max ((1 - F.c) + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im
                  (F.c + T * Complex.I).im) \ ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcLeft :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        ([[ ((1 - F.c) + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re,
             ((1 - zetaExplicitFormulaOnePolePunctureRadius F T) +
                (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re ]] ×ℂ
          [[ ((1 - F.c) + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im,
             ((1 - zetaExplicitFormulaOnePolePunctureRadius F T) +
                (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im ]]))
    (HdLeft :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 - F.c) + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re
                  ((1 - zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re)
                (max ((1 - F.c) + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re
                  ((1 - zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 - F.c) + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im
                  ((1 - zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im)
                (max ((1 - F.c) + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im
                  ((1 - zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (HcRight :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        ([[ ((1 + zetaExplicitFormulaOnePolePunctureRadius F T) +
                (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re,
             (F.c + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re ]] ×ℂ
          [[ ((1 + zetaExplicitFormulaOnePolePunctureRadius F T) +
                (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im,
             (F.c + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im ]]))
    (HdRight :
      ∀ x : ℂ,
        x ∈
            Set.Ioo
                (min ((1 + zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re
                  (F.c + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re)
                (max ((1 + zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).re
                  (F.c + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).re) ×ℂ
              Set.Ioo
                (min ((1 + zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im
                  (F.c + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im)
                (max ((1 + zetaExplicitFormulaOnePolePunctureRadius F T) +
                    (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I).im
                  (F.c + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I).im) \
                  ({(1 : ℂ)} : Set ℂ) →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
            x)
    (hinner :
      zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (zetaExplicitFormulaOnePolePunctureRadius F T) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) :
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
      f F T =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2)) := by
  have hfour :
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) = 0 :=
    zetaCompletedExplicitFormulaCorrectionOnePole_fourCellBoundary_eq_zero_of_cellRegularity_canonicalRadius
      f F HcBottom HdBottom HcTop HdTop HcLeft HdLeft HcRight HdRight
  exact
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height_geometric_inputs
      f F hT hboundary hfour hinner

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
