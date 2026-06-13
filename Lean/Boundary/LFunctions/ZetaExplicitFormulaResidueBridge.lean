import Boundary.LFunctions.ZetaExplicitFormulaBoundaryTransport
import Boundary.LFunctions.ZetaExplicitFormulaComplexAnalysis

/-!
# Boundary explicit-formula residue scalar

This file owns the residue-shaped scalar name used by the contour-shift
assembly. The comparison with the analytic boundary scalar is proved in the
final contour-shift target by uniqueness of the residue-side and vertical-side
limits.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The completed residue boundary sum attached to an admissible probe. -/
noncomputable def zetaCompletedResidueBoundarySum (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedZeroKreinGram f

/-- The zero-side Krein form is the completed residue boundary sum. -/
theorem zetaCompletedZeroKreinGram_eq_residueBoundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      zetaCompletedResidueBoundarySum f := by
  rfl

/-- Owner residue theorem for the completed explicit-formula contour family.

This is the residue-side limit theorem: the finite rectangle residue calculus, with zeros
counted by analytic multiplicity, converges to the completed residue boundary scalar. -/
theorem explicitFormulaFamilyContourIntegral_tendsto_residueBoundarySum_ownerResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyContourIntegral f F T)
      atTop
      (𝓝 (zetaCompletedResidueBoundarySum f : ℂ)) := by
  sorry

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
