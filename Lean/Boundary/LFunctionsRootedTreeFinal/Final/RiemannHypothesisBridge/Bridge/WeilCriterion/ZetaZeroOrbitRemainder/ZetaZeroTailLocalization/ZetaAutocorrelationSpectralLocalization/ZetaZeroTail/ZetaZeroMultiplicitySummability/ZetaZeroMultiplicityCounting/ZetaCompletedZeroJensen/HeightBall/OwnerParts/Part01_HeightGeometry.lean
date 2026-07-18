import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.JensenBound.Owner

/-!
# Height-ball zero counting

This owner layer transports closed-disk Jensen bounds to centered-height zero counting.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- Completed zeros in a centered height ball lie in a controlled ordinary closed disk.

The geometric input is the centered critical-strip bound for completed zeros: the real part
is bounded, while the centered height controls the imaginary part. -/
theorem completedZero_mem_centeredClosedDisk_of_mem_centeredHeightBall
    (T : ℝ) (hT : 1 ≤ T)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : zetaCompletedZeroCenteredHeight ρ ≤ T) :
    ‖(ρ : ℂ)‖ ≤ T + 2 := by
  have hstrip :
      -(1 / 2 : ℝ) ≤ (ρ : ℂ).re ∧
        (ρ : ℂ).re ≤ (1 / 2 : ℝ) :=
    zetaCompletedZero_re_mem_centeredCriticalStrip ρ
  have hheight :
      1 + ‖((ρ : ℂ) - (1 / 2 : ℂ)).im‖ ≤ T := by
    exact hρ
  have hbox : (ρ : ℂ) ∈ centeredCriticalHeightBox T :=
    ⟨hstrip.1, hstrip.2, hheight⟩
  have hnorm_radius :
      ‖(ρ : ℂ)‖ ≤ 2 + |T| :=
    centeredCriticalHeightBox_norm_le_radius hbox
  have hT_nonneg : 0 ≤ T :=
    le_trans zero_le_one hT
  have habs : |T| = T :=
    abs_of_nonneg hT_nonneg
  have hradius : 2 + |T| = T + 2 := by
    have habsRadius : 2 + |T| = 2 + T :=
      congrArg (fun x : ℝ => 2 + x) habs
    exact Eq.trans habsRadius (add_comm 2 T)
  exact Eq.subst
    (motive := fun x : ℝ => ‖(ρ : ℂ)‖ ≤ x)
    hradius
    hnorm_radius
end

end LFunctions
end Boundary
