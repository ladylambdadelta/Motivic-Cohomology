import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.HeightBall.OwnerParts.Part01_HeightGeometry

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- Inside the height ball, both summands equal the same multiplicity. -/
theorem completedZeroMultiplicityHeightBallSummand_le_closedDiskSummand_of_height
    (T : ℝ) (hT : 1 ≤ T)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hheight : zetaCompletedZeroCenteredHeight ρ ≤ T) :
    completedZeroMultiplicityHeightBallSummand T ρ ≤
      completedZeroMultiplicityClosedDiskSummand (T + 2) ρ := by
  have hdisk : ‖(ρ : ℂ)‖ ≤ T + 2 :=
    completedZero_mem_centeredClosedDisk_of_mem_centeredHeightBall T hT ρ hheight
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ if ‖(ρ : ℂ)‖ ≤ T + 2 then
        (zetaZeroMultiplicity (ρ : ℂ) : ℝ) else 0)
    (if_pos hheight).symm
    (Eq.subst
      (motive := fun x : ℝ =>
        (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤ x)
      (if_pos hdisk).symm
      (le_refl (zetaZeroMultiplicity (ρ : ℂ) : ℝ)))

/-- Outside the height ball but inside the disk, nonnegativity gives the comparison. -/
theorem completedZeroMultiplicityHeightBallSummand_le_closedDiskSummand_of_not_height_of_disk
    (T : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hheight : ¬ zetaCompletedZeroCenteredHeight ρ ≤ T)
    (hdisk : ‖(ρ : ℂ)‖ ≤ T + 2) :
    completedZeroMultiplicityHeightBallSummand T ρ ≤
      completedZeroMultiplicityClosedDiskSummand (T + 2) ρ := by
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ completedZeroMultiplicityClosedDiskSummand (T + 2) ρ)
    (if_neg hheight).symm
    (Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (if_pos hdisk).symm
      (Nat.cast_nonneg (zetaZeroMultiplicity (ρ : ℂ))))

/-- Outside both regions, both summands vanish. -/
theorem completedZeroMultiplicityHeightBallSummand_le_closedDiskSummand_of_not_height_of_not_disk
    (T : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hheight : ¬ zetaCompletedZeroCenteredHeight ρ ≤ T)
    (hdisk : ¬ ‖(ρ : ℂ)‖ ≤ T + 2) :
    completedZeroMultiplicityHeightBallSummand T ρ ≤
      completedZeroMultiplicityClosedDiskSummand (T + 2) ρ := by
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ completedZeroMultiplicityClosedDiskSummand (T + 2) ρ)
    (if_neg hheight).symm
    (Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (if_neg hdisk).symm
      (le_refl (0 : ℝ)))

/-- The height-ball multiplicity summand is bounded by the controlled disk summand. -/
theorem completedZeroMultiplicityHeightBallSummand_le_closedDiskSummand
    (T : ℝ) (hT : 1 ≤ T)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    [Decidable (zetaCompletedZeroCenteredHeight ρ ≤ T)]
    [Decidable (‖(ρ : ℂ)‖ ≤ T + 2)] :
    completedZeroMultiplicityHeightBallSummand T ρ ≤
      completedZeroMultiplicityClosedDiskSummand (T + 2) ρ := by
  exact
    match (inferInstance : Decidable (zetaCompletedZeroCenteredHeight ρ ≤ T)) with
    | Decidable.isTrue hheight =>
        completedZeroMultiplicityHeightBallSummand_le_closedDiskSummand_of_height
          T hT ρ hheight
    | Decidable.isFalse hheight =>
        match (inferInstance : Decidable (‖(ρ : ℂ)‖ ≤ T + 2)) with
        | Decidable.isTrue hdisk =>
            completedZeroMultiplicityHeightBallSummand_le_closedDiskSummand_of_not_height_of_disk
              T ρ hheight hdisk
        | Decidable.isFalse hdisk =>
            completedZeroMultiplicityHeightBallSummand_le_closedDiskSummand_of_not_height_of_not_disk
              T ρ hheight hdisk
end

end LFunctions
end Boundary
