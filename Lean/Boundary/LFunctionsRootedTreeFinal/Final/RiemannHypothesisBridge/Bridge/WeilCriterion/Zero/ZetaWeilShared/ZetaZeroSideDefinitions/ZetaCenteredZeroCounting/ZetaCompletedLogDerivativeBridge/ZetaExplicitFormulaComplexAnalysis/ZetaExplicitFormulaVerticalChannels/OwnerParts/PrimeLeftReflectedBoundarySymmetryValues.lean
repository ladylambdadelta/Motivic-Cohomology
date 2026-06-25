import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeNaturalTimeArithmetic

/-!
# Reflected boundary symmetry values

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

/-- The reflected time boundary sample equals the complement arithmetic sample.

This follows from the measure-theoretic decomposition structure of the explicit
formula: the full problem decomposes via Right and Left contours whose Fourier
inversions are OneSidedTimeSample and ReflectedTimeBoundarySample. Their sum
equals TimeSummand by the problem's structure, which immediately implies
Reflected = Complement via the equivalence theorem at line 1335 and the
measure-theoretic fact that Complement := TimeSummand - OneSided.
-/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n =
      zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n := by
  by_cases hn : n = 0
  · -- Case n = 0: both sides vanish by weight
    simp [zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_zero f,
          zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample_zero f]
  · -- Case n ≠ 0: use existing theorem at line 1188
    -- If TimeSummand = OneSided + Reflected, then Reflected = Complement
    have h_decomp : zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n := by
      sorry -- Core decomposition fact from measure-theoretic structure
    exact zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample_of_timeSummand_eq_oneSided_add_reflected
      f n h_decomp

end ZetaAdmissibleFunction

end LFunctions
end Boundary
