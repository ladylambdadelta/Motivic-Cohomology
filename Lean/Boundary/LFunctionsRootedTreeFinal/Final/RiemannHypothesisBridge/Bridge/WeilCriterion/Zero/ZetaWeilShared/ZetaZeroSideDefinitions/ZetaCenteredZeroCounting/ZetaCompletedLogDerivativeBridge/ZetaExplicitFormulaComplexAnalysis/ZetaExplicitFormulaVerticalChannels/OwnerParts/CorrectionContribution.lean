import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleSides

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

/-- The standard-contour correction boundary value obtained from the separated
`s = 0` and `s = 1` pole-face transports.  This is intentionally distinct from
the older centered contribution normalization until the contour-side basepoint
transport theorem identifies them. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionStandardContourContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  -(((2 * (Real.pi : ℂ) * Complex.I) *
    (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I) -
    (((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)

/-- The standard-contour correction boundary value unfolds to the separated
right-minus-left pole-face residue expression. -/
theorem zetaCompletedExplicitFormulaCorrectionStandardContourContribution_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionStandardContourContribution f =
      -(((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I) -
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) :=
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
