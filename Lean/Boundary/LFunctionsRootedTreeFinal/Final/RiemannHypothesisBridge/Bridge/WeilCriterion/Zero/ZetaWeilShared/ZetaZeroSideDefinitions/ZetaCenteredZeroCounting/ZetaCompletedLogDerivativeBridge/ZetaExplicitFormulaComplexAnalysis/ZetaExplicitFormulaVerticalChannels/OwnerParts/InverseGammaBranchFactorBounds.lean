import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetBranchCoherence
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaFactorBounds

/-!
# Branch inverse-Gamma factor bounds

This file owns branch-coherence wrappers for inverse-Gamma fixed-line bounds.
The estimates themselves are already unconditional fixed-line Gamma/Binet
bounds; the branch package is consumed only to keep the active archimedean lane
in the branch-correct normalization.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open LSeries ArithmeticFunction
open scoped ArithmeticFunction

namespace ZetaAdmissibleFunction

/-- Branch-coherence right-line inverse-Gamma logarithmic-derivative bound. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_branchBinet_owner
    (F : ExplicitFormulaContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
            B * (1 + ‖t‖) :=
  Eq.subst
    (motive := fun branchData : Complex.binetBranchLogGammaCoherence =>
      ∃ B : ℝ,
        0 ≤ B ∧
          ∀ t : ℝ,
            ‖inverseGammaCompletionLogDeriv
                (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
              B * (1 + ‖t‖))
    (Eq.refl hbranch)
    (zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_gammaBinet_owner
      F)

/-- Branch-coherence shifted left-line inverse-Gamma logarithmic-derivative
bound. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_branchBinet_shift_owner
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (N : ℕ)
    (hshift_pos : 0 < ((1 - F.c) / 2 : ℝ) + (N : ℝ)) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
            B * (1 + ‖t‖) :=
  Eq.subst
    (motive := fun branchData : Complex.binetBranchLogGammaCoherence =>
      ∃ B : ℝ,
        0 ≤ B ∧
          ∀ t : ℝ,
            ‖inverseGammaCompletionLogDeriv
                (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
              B * (1 + ‖t‖))
    (Eq.refl hbranch)
    (zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinet_shift_owner
      F hregular N hshift_pos)

/-- Branch-coherence left-line inverse-Gamma logarithmic-derivative bound. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_branchBinet_owner
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
            B * (1 + ‖t‖) :=
  Eq.subst
    (motive := fun branchData : Complex.binetBranchLogGammaCoherence =>
      ∃ B : ℝ,
        0 ≤ B ∧
          ∀ t : ℝ,
            ‖inverseGammaCompletionLogDeriv
                (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
              B * (1 + ‖t‖))
    (Eq.refl hbranch)
    (zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinet_owner
      F hregular)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
