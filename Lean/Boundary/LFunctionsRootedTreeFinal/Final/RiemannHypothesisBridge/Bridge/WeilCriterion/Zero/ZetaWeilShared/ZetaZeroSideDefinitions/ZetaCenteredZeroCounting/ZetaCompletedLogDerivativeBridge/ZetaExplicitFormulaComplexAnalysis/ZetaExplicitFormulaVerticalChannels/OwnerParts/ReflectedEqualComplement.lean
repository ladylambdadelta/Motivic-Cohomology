import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeNaturalTimeArithmetic

/-!
# Reflected sample equals complement

Records the thin owner-level wrapper from the two-face prime decomposition to
the reflected/complement equality.
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

/-- The reflected boundary sample equals the complement from a two-face decomposition. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample_of_split
    (f : ZetaAdmissibleFunction) (n : ℕ)
    (hsplit :
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n) :
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n =
      zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n :=
  zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample_of_timeSummand_eq_oneSided_add_reflected
    f n hsplit

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
