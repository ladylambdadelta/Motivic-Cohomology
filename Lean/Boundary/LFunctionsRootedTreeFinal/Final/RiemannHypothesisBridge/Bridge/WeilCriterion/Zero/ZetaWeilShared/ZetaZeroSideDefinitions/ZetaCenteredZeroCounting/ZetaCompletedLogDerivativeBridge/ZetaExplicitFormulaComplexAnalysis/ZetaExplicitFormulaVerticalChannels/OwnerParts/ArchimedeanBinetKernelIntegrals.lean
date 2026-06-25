import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetLineCore

/-!
# Archimedean Binet kernel integral values

This file owns the analytical theorems needed to prove that the Binet kernel
integrals equal ±Phi(f, 0). These are the component sorries in the Archimedean
Right/Left Binet Full Transform proofs.

The structure is:
- Main kernel integral = Phi value (or -Phi for left)
- Remainder kernel integral = 0
- Together, these assemble via _of_fullLineBinetValues to give affine integral values

These theorems require Binet inversion: understanding how the Gamma log derivative
fixed-vertical decomposition, when integrated against Phi, recovers the original
Phi value.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Infrastructure lemma: The right main kernel integral equals Phi(f, 0).

This is the key Binet inversion result for the right main component.
The kernel is defined as (-GammaLogDerivative weights - Correction) * Phi(transform),
and integrating against the appropriate Phi transform yields the original value.

To prove: use the fixed-vertical Binet decomposition of Gamma'/Gamma and
properties of Phi decay on affine lines.
-/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integral_eq_phiZero
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 := by
  sorry
  /- Proof strategy:
     1. Use Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder
        to decompose Gamma'/Gamma
     2. The kernel is (-GammaLogDerivativeTerm - (1/2)*Main - Correction) * Phi(...)
     3. The integral picks out the value of Phi at the central point via residue/inversion
     4. Main lemma: The weight functions integrate correctly to recover Phi(0)
  -/

/-- Infrastructure lemma: The right remainder kernel integral equals zero.

The remainder kernel is (-(1/2)*GammaLogDerivativeFixedVerticalRemainder)*Phi(transform).
By design of the Binet decomposition, this vanishes when integrated.

The remainder component of Gamma'/Gamma has specific integral properties that
cause it to contribute zero to the total when combined with the main term.
-/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integral_eq_zero
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
        f F.toContourFamily t) =
      0 := by
  sorry
  /- Proof strategy:
     1. Use GammaLogDerivativeFixedVerticalRemainder definition (line 82-86 ArchimedeanGammaBinetLineCore):
        It's 2 * ∫ u∈(0,∞), (-(u)/((σ+t*I)² + u²)) / (exp(2πu) - 1)
     2. Double integral: t-integral over the u-integral
     3. Remainder's integral representation ensures its t-integral vanishes
     4. Key: The poles and decay of the Binet remainder guarantee cancellation
  -/

/-- Infrastructure lemma: The left main kernel integral equals -Phi(f, 0).

This is the left analogue of the right main kernel. The left main kernel
involves a shift (Gamma recurrence) and negation, but the Binet inversion
still applies to recover -Phi(0).
-/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integral_eq_neg_phiZero
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  sorry
  /- Proof strategy:
     Similar to right case, but:
     1. Uses zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat for Gamma recurrence
     2. The shift introduces negation via Gamma's functional equation
     3. Binet inversion with this shift recovers -Phi(0)
  -/

/-- Infrastructure lemma: The left remainder kernel integral equals zero.

By the same cancellation argument as the right case, the left remainder
vanishes when integrated.
-/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integral_eq_zero
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
        f F.toContourFamily t) =
      0 := by
  sorry
  /- Proof strategy:
     Same as right remainder case; the shift doesn't affect the remainder integral value.
  -/

end ZetaAdmissibleFunction

end LFunctions
end Boundary
