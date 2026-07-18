import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ClosedDisk.OwnerParts.Part01_Definitions

namespace Boundary
namespace LFunctions

noncomputable section

/-- The closed-disk summand is nonnegative in the inside branch. -/
theorem completedZeroMultiplicityClosedDiskSummand_nonnegative_of_mem
    (R : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ‖(ρ : ℂ)‖ ≤ R) :
    0 ≤ completedZeroMultiplicityClosedDiskSummand R ρ := by
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    (if_pos hρ).symm
    (Nat.cast_nonneg (zetaZeroMultiplicity (ρ : ℂ)))

/-- The closed-disk summand is nonnegative in the outside branch. -/
theorem completedZeroMultiplicityClosedDiskSummand_nonnegative_of_not_mem
    (R : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ¬ ‖(ρ : ℂ)‖ ≤ R) :
    0 ≤ completedZeroMultiplicityClosedDiskSummand R ρ := by
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    (if_neg hρ).symm
    (le_refl (0 : ℝ))

/-- Closed-disk multiplicity summands are nonnegative. -/
theorem completedZeroMultiplicityClosedDiskSummand_nonnegative
    (R : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    [Decidable (‖(ρ : ℂ)‖ ≤ R)] :
    0 ≤ completedZeroMultiplicityClosedDiskSummand R ρ := by
  exact
    match (inferInstance : Decidable (‖(ρ : ℂ)‖ ≤ R)) with
    | Decidable.isTrue hρ =>
        completedZeroMultiplicityClosedDiskSummand_nonnegative_of_mem R ρ hρ
    | Decidable.isFalse hρ =>
        completedZeroMultiplicityClosedDiskSummand_nonnegative_of_not_mem R ρ hρ

/-- Closed-disk multiplicity summands vanish outside the closed disk. -/
theorem completedZeroMultiplicityClosedDiskSummand_eq_zero_of_not_mem
    (R : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∉ completedZerosInCenteredClosedDisk R) :
    completedZeroMultiplicityClosedDiskSummand R ρ = 0 := by
  exact if_neg hρ

/-- The real half-shift has zero imaginary coordinate. -/
theorem complex_half_im_eq_zero :
    (1 / 2 : ℂ).im = 0 := by
  have hdivision :
      ((1 : ℂ) / (2 : ℝ)).im = (1 : ℂ).im / (2 : ℝ) :=
    Complex.div_ofReal_im (1 : ℂ) 2
  have hone :
      (1 : ℂ).im / (2 : ℝ) = (0 : ℝ) / (2 : ℝ) :=
    congrArg (fun x : ℝ => x / (2 : ℝ)) Complex.one_im
  have hzero :
      (0 : ℝ) / (2 : ℝ) = 0 :=
    zero_div 2
  exact Eq.trans hdivision (Eq.trans hone hzero)

/-- Centering by the real half-shift preserves the imaginary coordinate. -/
theorem zetaCenteredZero_im_eq
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (zetaCenteredZero (ρ : ℂ)).im = (ρ : ℂ).im := by
  have hsub :
      ((ρ : ℂ) - (1 / 2 : ℂ)).im =
        (ρ : ℂ).im - (1 / 2 : ℂ).im :=
    Complex.sub_im (ρ : ℂ) (1 / 2 : ℂ)
  have hhalf :
      (ρ : ℂ).im - (1 / 2 : ℂ).im = (ρ : ℂ).im - 0 :=
    congrArg (fun x : ℝ => (ρ : ℂ).im - x) complex_half_im_eq_zero
  have hzero :
      (ρ : ℂ).im - 0 = (ρ : ℂ).im :=
    sub_zero (ρ : ℂ).im
  exact Eq.trans hsub (Eq.trans hhalf hzero)

/-- A completed zero in a closed disk satisfies the centered-height estimate. -/
theorem completedZero_centeredHeight_le_norm
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ‖(zetaCenteredZero (ρ : ℂ)).im‖ ≤ ‖(ρ : ℂ)‖ := by
  have him :
      ‖(zetaCenteredZero (ρ : ℂ)).im‖ = ‖(ρ : ℂ).im‖ :=
    congrArg (fun x : ℝ => ‖x‖) (zetaCenteredZero_im_eq ρ)
  have himNorm :
      ‖(ρ : ℂ).im‖ ≤ ‖(ρ : ℂ)‖ :=
    Complex.abs_im_le_abs (ρ : ℂ)
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ ‖(ρ : ℂ)‖)
    him.symm
    himNorm

/-- A completed zero in an ordinary closed disk lies in the enlarged centered-height ball. -/
theorem completedZero_mem_centeredHeightBall_of_mem_centeredClosedDisk
    (R : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∈ completedZerosInCenteredClosedDisk R) :
    ρ ∈ completedZerosInCenteredHeightBall (R + 1) := by
  have hheight :
      1 + ‖(zetaCenteredZero (ρ : ℂ)).im‖ ≤ 1 + ‖(ρ : ℂ)‖ :=
    add_le_add_left (completedZero_centeredHeight_le_norm ρ) 1
  have hradius :
      1 + ‖(ρ : ℂ)‖ ≤ 1 + R :=
    add_le_add_left hρ 1
  have hcommute :
      1 + R = R + 1 :=
    add_comm 1 R
  have hradiusFinal :
      1 + ‖(ρ : ℂ)‖ ≤ R + 1 :=
    Eq.subst
      (motive := fun x : ℝ => 1 + ‖(ρ : ℂ)‖ ≤ x)
      hcommute
      hradius
  exact le_trans hheight hradiusFinal

/-- Centered ordinary closed disks contain only finitely many completed zeros. -/
theorem finite_completedZerosInCenteredClosedDisk
    (R : ℝ) :
    (completedZerosInCenteredClosedDisk R).Finite := by
  have hsubset :
      completedZerosInCenteredClosedDisk R ⊆
        completedZerosInCenteredHeightBall (R + 1) :=
    fun ρ hρ =>
      completedZero_mem_centeredHeightBall_of_mem_centeredClosedDisk R ρ hρ
  exact Set.Finite.subset
    (finite_completedZerosInCenteredHeightBall (R + 1))
    hsubset

end

end LFunctions
end Boundary

