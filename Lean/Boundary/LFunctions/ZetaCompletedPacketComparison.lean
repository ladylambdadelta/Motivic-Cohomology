import Boundary.LFunctions.ZetaGuinandWeilExplicitFormula
import Boundary.LFunctions.ZetaExplicitFormulaBoundaryTransport
import Boundary.LFunctions.ZetaPacketComparison

/-!
# Boundary completed packet comparison

This file composes the owned arrows:

`Weil form → zero Krein → explicit boundary sum → boundary-defect Gram → packet norm square`

The only analytic dependency is the imported Guinand–Weil explicit-formula
input typeclass.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The zero-side Krein gram equals the boundary-defect Gram. -/
theorem zetaCompletedZeroKreinGram_eq_boundaryDefectGram
    [ZetaGuinandWeilExplicitFormulaInput]
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      zetaCompletedBoundaryDefectGram f := by
  calc
    zetaCompletedZeroKreinGram f
        = ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f :=
          zeta_completed_explicit_formula_autocorrelation f
    _   = zetaCompletedBoundaryDefectGram f := by
          simpa using
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectKreinGram
              (f := f))

/-- The completed Weil form on an autocorrelation equals the packet norm square. -/
theorem zetaWeilFormCompleted_eq_packetNormSq
    [ZetaGuinandWeilExplicitFormulaInput]
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) =
      zetaCompletedPacketNormSq f := by
  calc
    zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f)
        = zetaCompletedZeroKreinGram f :=
          zetaWeilFormCompleted_eq_zeroKreinGram (ZetaAdmissibleFunction.autocorrelation f)
    _   = zetaCompletedBoundaryDefectGram f :=
          zetaCompletedZeroKreinGram_eq_boundaryDefectGram
            (f := f)
    _   = zetaCompletedPacketNormSq f :=
          zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq f

/-- The completed Weil form on an autocorrelation is nonnegative. -/
theorem zetaWeilFormCompleted_autocorrelation_nonnegative
    [ZetaGuinandWeilExplicitFormulaInput]
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaWeilFormCompleted_eq_packetNormSq (f := f)]
  exact zetaCompletedPacketNormSq_nonnegative f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
