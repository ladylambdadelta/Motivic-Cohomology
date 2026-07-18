import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.OwnerParts.Part04_BaseExponentComparison

namespace Boundary
namespace LFunctions

noncomputable section

theorem completedZeroCenteredHeightShellCountingEnvelope_eq_expanded
    (C : ℝ) (d k m : ℕ) :
    completedZeroCenteredHeightShellCountingEnvelope C d k m =
      C * (((m + 1 : ℕ) : ℝ) ^ d) *
        (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)) :=
  Eq.refl (completedZeroCenteredHeightShellCountingEnvelope C d k m)

theorem completedZeroCenteredHeightShellTailProduct_eq_expanded
    (C : ℝ) (d k m : ℕ) :
    completedZeroCenteredHeightShellTailConstant C d k *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) =
      C * (2 : ℝ) ^ (d + k + 3) *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) :=
  Eq.refl
    (C * (2 : ℝ) ^ (d + k + 3) *
      (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)))

theorem shellTail_exponent_margin
    (d k : ℕ) : d + (k + 2) ≤ d + k + 3 := by
  have hassoc : d + (k + 2) = d + k + 2 :=
    (Nat.add_assoc d k 2).symm
  exact Eq.subst
    (motive := fun value : ℕ => value ≤ d + k + 3)
    hassoc.symm
    (Nat.le_succ (d + k + 2))

theorem completedZeroCenteredHeightShellEnvelope_left_normalization
    (C : ℝ) (d k m : ℕ) :
    C * (((m + 1 : ℕ) : ℝ) ^ d) *
        (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)) =
      C * ((1 + ‖((m : ℕ) : ℝ)‖) ^ d *
        (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ))) := by
  have hendpoint :
      (((m + 1 : ℕ) : ℝ)) = 1 + ‖((m : ℕ) : ℝ)‖ :=
    natSucc_cast_eq_one_add_natNorm m
  have hpower :
      (((m + 1 : ℕ) : ℝ) ^ d) =
        (1 + ‖((m : ℕ) : ℝ)‖) ^ d :=
    congrArg (fun value : ℝ => value ^ d) hendpoint
  have hreplace :
      C * (((m + 1 : ℕ) : ℝ) ^ d) *
          (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)) =
        C * ((1 + ‖((m : ℕ) : ℝ)‖) ^ d) *
          (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)) := congrArg
    (fun value : ℝ => C * value *
      (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)))
    hpower
  have hassoc :
      C * ((1 + ‖((m : ℕ) : ℝ)‖) ^ d) *
          (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)) =
        C * ((1 + ‖((m : ℕ) : ℝ)‖) ^ d *
          (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ))) :=
    mul_assoc C ((1 + ‖((m : ℕ) : ℝ)‖) ^ d)
      ((max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)))
  exact Eq.trans hreplace hassoc

theorem completedZeroCenteredHeightShellEnvelope_expanded_le_tail_expanded
    (C : ℝ) (d k m : ℕ) (hCpos : 0 < C) :
    C * (((m + 1 : ℕ) : ℝ) ^ d) *
        (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)) ≤
      C * (2 : ℝ) ^ (d + k + 3) *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) := by
  have hleft :
      C * (((m + 1 : ℕ) : ℝ) ^ d) *
          (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)) =
        C * ((1 + ‖((m : ℕ) : ℝ)‖) ^ d *
          (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ))) :=
    completedZeroCenteredHeightShellEnvelope_left_normalization C d k m
  have hcore :
      C * ((1 + ‖((m : ℕ) : ℝ)‖) ^ d *
          (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ))) ≤
        C * ((2 : ℝ) ^ (d + k + 3) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ))) :=
    real_const_mul_growth_decay_product_le_tail_of_baseComparison
      d (d + k + 3) (k + 2) hCpos
      (le_max_left 1 ‖((m : ℕ) : ℝ)‖)
      (le_add_of_nonneg_right (norm_nonneg ((m : ℕ) : ℝ)))
      (one_add_natNorm_le_two_mul_max_one_natNorm m)
      (shellTail_exponent_margin d k)
  have hright :
      C * (2 : ℝ) ^ (d + k + 3) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) =
        C * ((2 : ℝ) ^ (d + k + 3) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ))) :=
    mul_assoc C ((2 : ℝ) ^ (d + k + 3))
      ((1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)))
  exact Eq.subst
    (motive := fun leftValue : ℝ =>
      leftValue ≤ C * (2 : ℝ) ^ (d + k + 3) *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)))
    hleft.symm
    (Eq.subst
      (motive := fun rightValue : ℝ =>
        C * ((1 + ‖((m : ℕ) : ℝ)‖) ^ d *
          (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ))) ≤ rightValue)
      hright.symm
      hcore)

theorem completedZeroCenteredHeightShellCountingEnvelope_le_tail_of_expanded
    (C : ℝ) (d k m : ℕ)
    (hbound :
      C * (((m + 1 : ℕ) : ℝ) ^ d) *
          (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ)) ≤
        C * (2 : ℝ) ^ (d + k + 3) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ))) :
    completedZeroCenteredHeightShellCountingEnvelope C d k m ≤
      completedZeroCenteredHeightShellTailConstant C d k *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) :=
  Eq.subst
    (motive := fun rightValue : ℝ =>
      completedZeroCenteredHeightShellCountingEnvelope C d k m ≤ rightValue)
    (completedZeroCenteredHeightShellTailProduct_eq_expanded C d k m).symm
    (Eq.subst
      (motive := fun leftValue : ℝ =>
        leftValue ≤ C * (2 : ℝ) ^ (d + k + 3) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)))
      (completedZeroCenteredHeightShellCountingEnvelope_eq_expanded C d k m).symm
      hbound)

theorem completedZeroCenteredHeightShellCountingEnvelope_le_tailConstant_of_heightBase
    (C : ℝ) (d k m : ℕ)
    (hCpos : 0 < C) :
    completedZeroCenteredHeightShellCountingEnvelope C d k m ≤
      completedZeroCenteredHeightShellTailConstant C d k *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) := by
  exact completedZeroCenteredHeightShellCountingEnvelope_le_tail_of_expanded
    C d k m
    (completedZeroCenteredHeightShellEnvelope_expanded_le_tail_expanded
      C d k m hCpos)

/-- The shell counting envelope is bounded by the explicit polynomial tail
constant. -/
theorem completedZeroCenteredHeightShellCountingEnvelope_le_tailConstant
    (C : ℝ) (d k m : ℕ)
    (hCpos : 0 < C) :
    completedZeroCenteredHeightShellCountingEnvelope C d k m ≤
      completedZeroCenteredHeightShellTailConstant C d k *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) := by
  exact completedZeroCenteredHeightShellCountingEnvelope_le_tailConstant_of_heightBase
    C d k m hCpos

/-- The cumulative shell envelope is bounded by a one-dimensional polynomial
tail after increasing the constant. -/
theorem exists_completedZeroCenteredHeightShellCountingEnvelope_le_polynomialTail
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ m : ℕ,
        completedZeroCenteredHeightShellCountingEnvelope C d k m ≤
          A * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) := by
  exact ⟨completedZeroCenteredHeightShellTailConstant C d k,
    completedZeroCenteredHeightShellTailConstant_pos C d k hCpos,
    fun m =>
      completedZeroCenteredHeightShellCountingEnvelope_le_tailConstant
        C d k m hCpos⟩

end

end LFunctions
end Boundary
