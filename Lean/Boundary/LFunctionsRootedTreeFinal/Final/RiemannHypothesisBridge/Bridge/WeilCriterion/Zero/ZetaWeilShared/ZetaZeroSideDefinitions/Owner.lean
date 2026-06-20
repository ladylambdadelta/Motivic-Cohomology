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
    exact
      match hz with
      | ⟨ρ, hρ, hzρ⟩ =>
          let hzero_raw : centeredCompletedRiemannZeta (ρ : ℂ) = 0 :=
            (centeredCompletedRiemannZetaFunction_eq (ρ : ℂ)).symm.trans
              (zetaCompletedZero_zero ρ)
          let hzero_z : centeredCompletedRiemannZeta z = 0 :=
            Eq.subst
              (motive := fun w : ℂ => centeredCompletedRiemannZeta w = 0)
              hzρ
              hzero_raw
          let hheight_raw :
              1 + ‖((ρ : ℂ) - (1 / 2 : ℂ)).im‖ ≤ T :=
            hρ
          let hheight_z :
              1 + ‖(z - (1 / 2 : ℂ)).im‖ ≤ T :=
            Eq.subst
              (motive := fun w : ℂ =>
                1 + ‖(w - (1 / 2 : ℂ)).im‖ ≤ T)
              hzρ
              hheight_raw
          ⟨hzero_z, hheight_z⟩
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
