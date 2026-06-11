import Boundary.LFunctions.WeilCriterion
import Boundary.LFunctions.ZetaPacketEnergy

/-!
# Boundary zeta criterion surface

This file is the owner-level checkpoint for the final explicit-formula route.
 The packet-side norm-square theorem is already proved in the packet energy
 layer; this file re-exports that honest theorem surface and keeps the final
 bridge location explicit.

The remaining missing mathematical ingredient is the admissible-test-function
to packet-transform bridge needed to connect the packet theorem to the Weil
criterion.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The packet norm-square identity in the owner namespace. -/
theorem zetaPacketNormSquare (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.normSq x =
      ZetaPacketEnsemble.primePacketGram x +
      ZetaPacketEnsemble.archimedeanPacketGram x +
      ZetaPacketEnsemble.correctionPacketGram x := by
  exact ZetaPacketEnsemble.zetaPacketNormSquare x

/-- The packet energy identity in the owner namespace. -/
theorem zetaPacketEnergy_eq_sum (x : ZetaPacketEnsemble) :
    ZetaPacketEnsemble.packetEnergy x =
      ZetaPacketEnsemble.packetEnergyPrime x +
      ZetaPacketEnsemble.packetEnergyArchimedean x +
      ZetaPacketEnsemble.packetEnergyCorrection x := by
  exact ZetaPacketEnsemble.packetEnergy_eq_sum x

/-- The packet energy is nonnegative in the owner namespace. -/
theorem zetaPacketEnergy_nonneg (x : ZetaPacketEnsemble) :
    0 ≤ ZetaPacketEnsemble.packetEnergy x := by
  exact ZetaPacketEnsemble.packetEnergy_nonneg x

/-- The criterion's autocorrelation probes satisfy the named Weil-positivity predicate. -/
theorem zetaCriterion_autocorrelation_weilPositivity_predicate :
    ZetaAutocorrelationWeilPositivity := by
  intro φ hφ
  rcases hφ with ⟨f, rfl⟩
  exact Boundary.LFunctions.ZetaAdmissibleFunction
    .zetaWeilFormCompleted_autocorrelation_nonnegative_classFree (f := f)

/-- The criterion's probe positivity predicate is the raw Weil-positivity predicate. -/
theorem zetaCriterion_weilPositivity_predicate :
    ZetaWeilPositivity := by
  intro φ
  exact Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_nonnegative_of_probe
    (f := φ)

/-- The criterion's raw Weil-positivity predicate is pointwise nonnegativity. -/
theorem zetaCriterion_weilPositivity_iff :
    ZetaWeilPositivity ↔
      ∀ φ : ZetaProbe, 0 ≤ zetaWeilFormCompleted φ := by
  rfl

/-- Pointwise nonnegativity is the criterion's raw Weil-positivity predicate. -/
theorem zetaCriterion_weilPositivity_iff' :
    (∀ φ : ZetaProbe, 0 ≤ zetaWeilFormCompleted φ) ↔ ZetaWeilPositivity := by
  rfl

/-- Autocorrelation-generated probes have nonnegative completed zero-side real sum. -/
theorem zetaCriterion_autocorrelation_zeroSide_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.autocorrelation f) := by
  exact
    (Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_eq_zeroSide
      (f := f)).symm ▸
      Boundary.LFunctions.ZetaAdmissibleFunction
        .zetaWeilFormCompleted_autocorrelation_nonnegative_classFree (f := f)

/-- Autocorrelation-generated probes satisfy the criterion's Weil positivity. -/
theorem zetaCriterion_autocorrelation_weilPositivity
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) := by
  exact Boundary.LFunctions.ZetaAdmissibleFunction
    .zetaWeilFormCompleted_autocorrelation_nonnegative_classFree (f := f)

/-- The criterion's autocorrelation Weil positivity is the zero-side nonnegativity statement. -/
theorem zetaCriterion_autocorrelation_weilPositivity_iff
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) ↔
      0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.autocorrelation f) := by
  exact
    (Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_eq_zeroSide
      (f := f)).symm ▸ Iff.rfl

/-- The zero-side nonnegativity statement is the criterion's autocorrelation Weil positivity. -/
theorem zetaCriterion_autocorrelation_weilPositivity_iff'
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.autocorrelation f) ↔
      0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) := by
  exact
    (Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_eq_zeroSide
      (f := f)) ▸ Iff.rfl

/-- Zero-side nonnegativity implies criterion Weil positivity for autocorrelation probes. -/
theorem zetaCriterion_autocorrelation_weilPositivity_of_zeroSide
    (f : ZetaAdmissibleFunction)
    (h : 0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.autocorrelation f)) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) := by
  exact
    (Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_eq_zeroSide
      (f := f)).symm ▸ h

end

end LFunctions
end Boundary
