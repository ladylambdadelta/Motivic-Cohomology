import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaWeilShared
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.WeilCriterion

/-!
# Boundary zeta zero Krein form

This file owns the zero-side Krein form used as the first analytic target in
the completed explicit-formula chain. It lives on the probe carrier and is
definitionally the completed zero-side real form.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The completed zero-side Krein form attached to a probe. -/
noncomputable def zetaCompletedZeroKreinGram (φ : ZetaProbe) : ℝ :=
  zetaCompletedZeroSideRe φ

/-- The completed Weil form is the zero-side Krein form. -/
theorem zetaWeilFormCompleted_eq_zeroKreinGram (φ : ZetaProbe) :
    zetaWeilFormCompleted φ = zetaCompletedZeroKreinGram φ := by
  rfl

/-- The zero-side Krein form is definitionally the completed zero-side form. -/
theorem zetaCompletedZeroKreinGram_eq_zeroSide
    (φ : ZetaProbe) :
    zetaCompletedZeroKreinGram φ = zetaCompletedZeroSideRe φ := by
  rfl

/-- The zero-side Krein form depends only on the underlying test function. -/
theorem zetaCompletedZeroKreinGram_congr_toZetaTestFunction
    {φ ψ : ZetaProbe}
    (h : φ.toZetaTestFunction' = ψ.toZetaTestFunction') :
    zetaCompletedZeroKreinGram φ = zetaCompletedZeroKreinGram ψ := by
  have hzero :
      zetaCompletedZeroSideRe φ = zetaCompletedZeroSideRe ψ :=
    zetaCompletedZeroSideRe_congr_toZetaTestFunction h
  exact
    (zetaCompletedZeroKreinGram_eq_zeroSide φ).trans
      (hzero.trans (zetaCompletedZeroKreinGram_eq_zeroSide ψ).symm)

end
end LFunctions
end Boundary
