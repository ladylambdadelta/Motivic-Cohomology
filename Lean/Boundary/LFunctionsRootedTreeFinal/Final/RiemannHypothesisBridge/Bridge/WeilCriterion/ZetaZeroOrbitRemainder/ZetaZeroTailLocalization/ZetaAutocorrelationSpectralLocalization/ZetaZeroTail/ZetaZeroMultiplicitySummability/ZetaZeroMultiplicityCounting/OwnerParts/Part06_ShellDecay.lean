import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.OwnerParts.Part05_ShellSigma

namespace Boundary
namespace LFunctions

noncomputable section

/-- The total decay mass in one centered-height shell. -/
noncomputable def completedZeroCenteredHeightShellDecayMass
    (d k m : ℕ) : ℝ :=
  ∑' x : completedZeroCenteredHeightShellFiber m,
    zetaCompletedZeroCenteredHeight (x.1 : {ρ : ℂ // ZetaCompletedZero ρ}) ^
      (-(d + k + 3 : ℤ))

/-- The polynomial decay restricted to a shell fiber. -/
noncomputable def completedZeroCenteredHeightShellFiberDecay
    (d k : ℕ)
    (x : CompletedZeroCenteredHeightShellSigma) : ℝ :=
  zetaCompletedZeroCenteredHeight
      (completedZeroCenteredHeightShellSigma_forget x) ^
    (-(d + k + 3 : ℤ))

/-- Shell-fiber decay is nonnegative. -/
theorem completedZeroCenteredHeightShellFiberDecay_nonnegative
    (d k : ℕ)
    (x : CompletedZeroCenteredHeightShellSigma) :
    0 ≤ completedZeroCenteredHeightShellFiberDecay d k x := by
  exact zpow_nonneg
    (le_trans zero_le_one
      (zetaCompletedZeroCenteredHeight_ge_one
        (completedZeroCenteredHeightShellSigma_forget x)))
    (-(d + k + 3 : ℤ))

/-- The shell-fiber `tsum` at height `m` is the shell decay mass. -/
theorem completedZeroCenteredHeightShellFiberDecay_tsum_eq_shellDecayMass
    (d k m : ℕ) :
    (∑' x : completedZeroCenteredHeightShellFiber m,
      zetaCompletedZeroCenteredHeight (x.1 : {ρ : ℂ // ZetaCompletedZero ρ}) ^
        (-(d + k + 3 : ℤ))) =
      completedZeroCenteredHeightShellDecayMass d k m :=
  Eq.refl (completedZeroCenteredHeightShellDecayMass d k m)

theorem completedZeroCenteredHeightShellFiberDecay_family_eq_shellMass
    (d k : ℕ) :
    (fun m : ℕ =>
      ∑' x : completedZeroCenteredHeightShellFiber m,
        completedZeroCenteredHeightShellFiberDecay d k ⟨m, x⟩) =
      fun m : ℕ => completedZeroCenteredHeightShellDecayMass d k m :=
  funext (fun m =>
    completedZeroCenteredHeightShellFiberDecay_tsum_eq_shellDecayMass d k m)

/-- Each completed-zero centered-height shell fiber is finite. -/
theorem finite_completedZeroCenteredHeightShellFiber
    (m : ℕ) :
    (Set.univ : Set (completedZeroCenteredHeightShellFiber m)).Finite := by
  exact finite_univ_subtype_of_finite_set
    (finite_completedZeroCenteredHeightShell m)

/-- Decay over a fixed completed-zero centered-height shell fiber is summable. -/
theorem summable_completedZeroCenteredHeightShellFiberDecay_fixed
    (d k m : ℕ) :
    Summable
      (fun x : completedZeroCenteredHeightShellFiber m =>
        completedZeroCenteredHeightShellFiberDecay d k ⟨m, x⟩) := by
  exact summable_of_finite_support_real
    (fun x : completedZeroCenteredHeightShellFiber m =>
      completedZeroCenteredHeightShellFiberDecay d k ⟨m, x⟩)
    Set.univ
    (finite_completedZeroCenteredHeightShellFiber m)
    (fun x hx => False.elim (hx trivial))

/-- Summability over shell masses is equivalent to summability over the sigma
shell decomposition. -/
theorem summable_completedZeroCenteredHeightShellFiberDecay_of_shellMass
    (d k : ℕ)
    (hshell :
      Summable
        (fun m : ℕ =>
          completedZeroCenteredHeightShellDecayMass d k m)) :
    Summable
      (fun x : CompletedZeroCenteredHeightShellSigma =>
        completedZeroCenteredHeightShellFiberDecay d k x) := by
  exact
    (summable_sigma_of_nonneg
      (fun x : CompletedZeroCenteredHeightShellSigma =>
        completedZeroCenteredHeightShellFiberDecay_nonnegative d k x)).mpr
      (And.intro
        (fun m => summable_completedZeroCenteredHeightShellFiberDecay_fixed d k m)
        (by
          have hfiberSums :=
            completedZeroCenteredHeightShellFiberDecay_family_eq_shellMass d k
          exact Eq.subst
            (motive := fun u : ℕ → ℝ => Summable u)
            hfiberSums.symm
            hshell))


end

end LFunctions
end Boundary
