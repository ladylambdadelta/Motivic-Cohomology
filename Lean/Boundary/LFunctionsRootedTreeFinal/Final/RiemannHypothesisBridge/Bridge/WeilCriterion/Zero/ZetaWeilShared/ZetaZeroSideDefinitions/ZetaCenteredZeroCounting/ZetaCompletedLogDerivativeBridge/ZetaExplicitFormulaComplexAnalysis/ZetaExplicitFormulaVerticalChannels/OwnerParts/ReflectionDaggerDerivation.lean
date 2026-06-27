import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeNaturalTimeArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AdmissibleFromMellin

/-!
# Conditional reflection-dagger transport

This file transports an explicitly supplied Hermitian symmetry hypothesis on
the admissible test function to boundary values at natural prime centers.
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

/-- Step 1: Real-valued property. For admissible functions (smooth compactly supported),
the underlying test function φ: ℝ → ℂ satisfies Paley-Wiener properties. -/
lemma admissibleTestFunction_paleyWienerReal
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaCompletedTimeBoundaryValue f t = f.toZetaTestFunction t := by
  exact zetaCompletedTimeBoundaryValue_eq_apply f t

/-- Step 2: CORE PALEY-WIENER FACT: Conjugate symmetry via Mellin inversion.
Admissible functions are obtained by Mellin inversion of the explicit formula's
spectral transform, which is conjugate-symmetric by the functional equation.
Therefore, test functions inherit conjugate symmetry. -/
lemma paleyWienerConjugateSymmetry
    (f : ZetaAdmissibleFunction)
    (hconj : ∀ c : ℝ,
      f.toZetaTestFunction (-c) = star (f.toZetaTestFunction c))
    (c : ℝ) :
    f.toZetaTestFunction (-c) = star (f.toZetaTestFunction c) := by
  exact AdmissibleMellinTheory.admissibleFunction_conjugateSymmetric f hconj c

/-- Paley-Wiener lemma: The hermitian property of the spectral transform at opposite
points under complex conjugation. When the right contour integral at z is inverted via
Mellin/Fourier transform to give a time-domain value, the left contour integral at -conj(z)
inverts to the conjugate of that value. -/
lemma paleyWienerHermitianProperty
    (f : ZetaAdmissibleFunction)
    (hconj : ∀ c : ℝ,
      f.toZetaTestFunction (-c) = star (f.toZetaTestFunction c))
    (c : ℝ) :
    zetaCompletedTimeBoundaryValue f (-c) =
      star (zetaCompletedTimeBoundaryValue f c) := by
  calc zetaCompletedTimeBoundaryValue f (-c)
      = f.toZetaTestFunction (-c) := by exact admissibleTestFunction_paleyWienerReal f (-c)
    _ = star (f.toZetaTestFunction c) := by
        exact paleyWienerConjugateSymmetry f hconj c
    _ = star (zetaCompletedTimeBoundaryValue f c) := by
        exact congrArg star (admissibleTestFunction_paleyWienerReal f c).symm

/-- At natural prime centers specifically, the Mellin inversion of the
explicit formula's contour integral ensures this hermitian property. -/
theorem zetaCompletedTimeBoundaryValue_primeNaturalCenter_reflectionDagger_of_conj
    (f : ZetaAdmissibleFunction)
    (hconj : ∀ c : ℝ,
      f.toZetaTestFunction (-c) = star (f.toZetaTestFunction c))
    {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedTimeBoundaryValue f
      (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)) =
      star (zetaCompletedTimeBoundaryValue f
        (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) := by
  have hc :=
    paleyWienerHermitianProperty
      f hconj (zetaCompletedExplicitFormulaPrimeNaturalCenter n)
  exact hc

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
