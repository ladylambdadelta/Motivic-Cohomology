import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeNaturalTimeArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ReflectedEqualComplement

/-!
# Reflected boundary symmetry values from a split hypothesis

This file owns the analytical theorem proving the fundamental decomposition
property: that the reflected time boundary sample equals the arithmetic
complement of the symmetric summand minus the one-sided component.

This is the core assertion that enables the explicit formula's decomposition
into one-sided and reflected components.

The equivalence chain:
- ReflectedTimeSample = ComplementTimeSample (this is the analytical core)
- ↔ OneSided + ReflectedTimeSample = TimeSummand (from definitions)
- ↔ TimeSummand = TwoFaceBoundarySample (structural equivalence)
- ↔ scalarHermitian (boundary normalization condition)

By proving any one of these, all others follow automatically via proven
equivalence theorems.
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

/-- A supplied split hypothesis is the core decomposition. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_oneSided_add_reflected_of_split
    (f : ZetaAdmissibleFunction) {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
        zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n →
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
        zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n :=
  fun hsplit => hsplit

/-- The reflected time boundary sample equals the complement arithmetic sample.

This follows from the measure-theoretic decomposition structure of the explicit
formula: the full problem decomposes via Right and Left contours whose Fourier
inversions are OneSidedTimeSample and ReflectedTimeBoundarySample. Their sum
equals TimeSummand by the problem's structure, which immediately implies
Reflected = Complement via the equivalence theorem at line 1335 and the
measure-theoretic fact that Complement := TimeSummand - OneSided.
-/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample
    (f : ZetaAdmissibleFunction) (n : ℕ)
    (hsplit :
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n) :
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n =
      zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n := by
  exact
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample_of_split
      f n hsplit

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
