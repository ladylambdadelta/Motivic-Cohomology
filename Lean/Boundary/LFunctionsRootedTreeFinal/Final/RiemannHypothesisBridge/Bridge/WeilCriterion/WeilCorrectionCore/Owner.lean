import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CenteredZeros.Owner

/-!
# Boundary Weil correction core

This file owns the centered pole-correction term used by the Weil criterion and
completed boundary packet comparison layers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The pole correction term in the centered Weil normalization. -/
def zetaWeilCorrection (s : ℂ) : ℂ :=
  1 / (1 / 2 + s) + 1 / (1 - (1 / 2 + s))

theorem zetaWeilCorrection_neg (s : ℂ) :
    zetaWeilCorrection (-s) = zetaWeilCorrection s := by
  unfold zetaWeilCorrection
  exact centeredCompletedRiemannZeta_correction_symm s

/-- The centered pole correction symmetry rewritten for downstream packet files. -/
theorem zetaWeilCorrection_centered_reflection (s : ℂ) :
    zetaWeilCorrection (-s) = zetaWeilCorrection s := by
  exact zetaWeilCorrection_neg s

end
end LFunctions
end Boundary
