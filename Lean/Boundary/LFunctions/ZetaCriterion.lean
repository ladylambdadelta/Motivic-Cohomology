import Boundary.LFunctions.WeilCriterion
import Boundary.LFunctions.ZetaPacketEnergy
import Boundary.LFunctions.ZetaExplicitFormulaBoundaryTransport
import Boundary.LFunctions.ZetaExplicitFormulaContourBridge

/-!
# Boundary zeta criterion surface

This file is the owner-level checkpoint for the final explicit-formula route.
 The packet-side norm-square theorem is already proved in the packet energy
 layer; this file re-exports that honest theorem surface and keeps the final
 bridge location explicit.

The convolution-autocorrelation lane is proved by transporting the zero-side
Krein form to the Hermitian packet norm square. The raw all-probe Weil
positivity statement is intentionally kept as a separate stronger theorem.
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

/-- The analytic explicit-formula equality needed for convolution-autocorrelation positivity. -/
theorem zetaCriterion_convolutionAutocorrelation_zeroKreinGram_eq_boundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  exact ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation f

/-- Historical name for the convolution-autocorrelation zero-side/boundary bridge. -/
theorem zetaCriterion_autocorrelation_zeroKreinGram_eq_boundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  exact zetaCriterion_convolutionAutocorrelation_zeroKreinGram_eq_boundarySum f

/-- The criterion's convolution-autocorrelation probes satisfy the named Weil-positivity
predicate. -/
theorem zetaCriterion_autocorrelation_weilPositivity_predicate :
    ZetaAutocorrelationWeilPositivity := by
  intro φ hφ
  rcases hφ with ⟨f, hφ⟩
  let g : ZetaAdmissibleFunction := ZetaAdmissibleFunction.convolutionAutocorrelation f
  have hφg :
      zetaWeilFormCompleted φ = zetaWeilFormCompleted g :=
    zetaWeilFormCompleted_congr_toZetaTestFunction hφ
  have hzero_boundary :
      zetaCompletedZeroKreinGram g =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
    exact zetaCriterion_convolutionAutocorrelation_zeroKreinGram_eq_boundarySum f
  have hboundary :
      0 ≤ ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_nonnegative f
  have hzero : 0 ≤ zetaCompletedZeroKreinGram g :=
    Eq.subst (motive := fun x : ℝ => 0 ≤ x) hzero_boundary.symm hboundary
  have hweil_zero :
      zetaWeilFormCompleted g = zetaCompletedZeroKreinGram g :=
    zetaWeilFormCompleted_eq_zeroKreinGram g
  have hweil_g : 0 ≤ zetaWeilFormCompleted g :=
    Eq.subst (motive := fun x : ℝ => 0 ≤ x) hweil_zero.symm hzero
  exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hφg.symm hweil_g

/-- The criterion's probe positivity predicate is the raw Weil-positivity predicate. -/
theorem zetaCriterion_weilPositivity_predicate :
    ZetaWeilPositivity := by
  sorry

/-- The criterion's convolution-autocorrelation Weil-positivity predicate is pointwise
nonnegativity on convolution-autocorrelation probes. -/
theorem zetaCriterion_autocorrelation_weilPositivity_iff_predicate :
    ZetaAutocorrelationWeilPositivity ↔
      ∀ φ : ZetaProbe, IsZetaAutocorrelationProbe φ →
        0 ≤ zetaWeilFormCompleted φ := by
  rfl

/-- The criterion's raw Weil-positivity predicate is pointwise nonnegativity. -/
theorem zetaCriterion_weilPositivity_iff :
    ZetaWeilPositivity ↔
      ∀ φ : ZetaProbe, 0 ≤ zetaWeilFormCompleted φ := by
  rfl

/-- Pointwise nonnegativity is the criterion's raw Weil-positivity predicate. -/
theorem zetaCriterion_weilPositivity_iff' :
    (∀ φ : ZetaProbe, 0 ≤ zetaWeilFormCompleted φ) ↔ ZetaWeilPositivity := by
  rfl

/-- Convolution-autocorrelation-generated probes have nonnegative completed zero-side real sum. -/
theorem zetaCriterion_convolutionAutocorrelation_zeroSide_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  let g : ZetaAdmissibleFunction := ZetaAdmissibleFunction.convolutionAutocorrelation f
  have hzero_boundary :
      zetaCompletedZeroKreinGram g =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
    exact zetaCriterion_convolutionAutocorrelation_zeroKreinGram_eq_boundarySum f
  have hboundary :
      0 ≤ ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_nonnegative f
  have hzero : 0 ≤ zetaCompletedZeroKreinGram g :=
    Eq.subst (motive := fun x : ℝ => 0 ≤ x) hzero_boundary.symm hboundary
  exact hzero

/-- Historical name for convolution-autocorrelation zero-side nonnegativity. -/
theorem zetaCriterion_autocorrelation_zeroSide_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact zetaCriterion_convolutionAutocorrelation_zeroSide_nonnegative f

/-- Convolution-autocorrelation-generated probes satisfy the criterion's Weil positivity. -/
theorem zetaCriterion_autocorrelation_weilPositivity
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact
    (Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_eq_zeroSide
      (f := f)).symm ▸
      zetaCriterion_convolutionAutocorrelation_zeroSide_nonnegative f

/-- The criterion's convolution-autocorrelation Weil positivity is the zero-side
nonnegativity statement. -/
theorem zetaCriterion_autocorrelation_weilPositivity_iff
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) ↔
      0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact
    (Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_eq_zeroSide
      (f := f)).symm ▸ Iff.rfl

/-- The zero-side nonnegativity statement is the criterion's convolution-autocorrelation Weil
positivity. -/
theorem zetaCriterion_autocorrelation_weilPositivity_iff'
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) ↔
      0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact
    (Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_eq_zeroSide
      (f := f)) ▸ Iff.rfl

/-- Zero-side nonnegativity implies criterion Weil positivity for convolution-autocorrelation
probes. -/
theorem zetaCriterion_autocorrelation_weilPositivity_of_zeroSide
    (f : ZetaAdmissibleFunction)
    (h : 0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact
    (Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_eq_zeroSide
      (f := f)).symm ▸ h

end

end LFunctions
end Boundary
