import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroLocalFiniteness.Owner

/-!
# Boundary zero-side definitions

This aggregate owner exports the primitive zero-side surface and owns the
finite-height consequence that depends on the centered-zero counting children.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Topology

/-- Completed zeros are locally finite in centered height balls. -/
theorem finite_completedZerosInCenteredHeightBall
    (T : ℝ) :
    (completedZerosInCenteredHeightBall T).Finite := by
  let S : Set ℂ := centeredZetaZerosInCenteredHeightBall T
  have himage_subset :
      Subtype.val '' completedZerosInCenteredHeightBall T ⊆ S := by
    intro z hz
    rcases hz with ⟨ρ, hρ, hzρ⟩
    unfold S
    unfold centeredZetaZerosInCenteredHeightBall
    constructor
    · have hzero_raw : centeredCompletedRiemannZeta (ρ : ℂ) = 0 :=
        (centeredCompletedRiemannZetaFunction_eq (ρ : ℂ)).symm.trans
          (zetaCompletedZero_zero ρ)
      exact Eq.subst
        (motive := fun w : ℂ => centeredCompletedRiemannZeta w = 0)
        hzρ
        hzero_raw
    · have hheight :
          1 + ‖((ρ : ℂ) - (1 / 2 : ℂ)).im‖ ≤ T := by
        exact Eq.subst
          (motive := fun x : ℝ => x ≤ T)
          (by
            unfold zetaCompletedZeroCenteredHeight
            unfold zetaCenteredZero
            rfl)
          hρ
      exact Eq.subst
        (motive := fun w : ℂ =>
          1 + ‖(w - (1 / 2 : ℂ)).im‖ ≤ T)
        hzρ
        hheight
  have hfinite_image :
      (Subtype.val '' completedZerosInCenteredHeightBall T).Finite :=
    Set.Finite.subset
      (finite_centeredZetaZerosInCenteredHeightBall T)
      himage_subset
  exact Set.Finite.of_finite_image
    hfinite_image
    (fun ρ hρ η hη hval => Subtype.ext hval)

end
end LFunctions
end Boundary
