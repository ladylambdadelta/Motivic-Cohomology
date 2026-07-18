import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.OwnerParts.Part06_ShellDecay

namespace Boundary
namespace LFunctions

noncomputable section

/-- Summability transports across a bijective map of index types. -/
theorem summable_of_bijective_index_transport_real
    {α β : Type*} (e : α → β) (u : β → ℝ)
    (hinj : Function.Injective e)
    (hsurj : Function.Surjective e)
    (hsum : Summable (fun a : α => u (e a))) :
    Summable u := by
  let E : α ≃ β := Equiv.ofBijective e ⟨hinj, hsurj⟩
  have hE :
      (fun a : α => u (E a)) = fun a : α => u (e a) :=
    Eq.refl (fun a : α => u (e a))
  exact E.summable_iff.mp
    (Eq.subst
      (motive := fun v : α → ℝ => Summable v)
      hE.symm
      hsum)

/-- Shell-fiber decay is the base negative-height decay after forgetting the
shell coordinate. -/
theorem completedZeroCenteredHeightShellFiberDecay_eq_baseDecay
    (d k : ℕ)
    (x : CompletedZeroCenteredHeightShellSigma) :
    completedZeroCenteredHeightShellFiberDecay d k x =
      zetaCompletedZeroCenteredHeight
          (completedZeroCenteredHeightShellSigma_forget x) ^
        (-(d + k + 3 : ℤ)) :=
  Eq.refl
    (zetaCompletedZeroCenteredHeight
      (completedZeroCenteredHeightShellSigma_forget x) ^
        (-(d + k + 3 : ℤ)))

theorem completedZeroCenteredHeightShellFiberDecay_family_eq_baseDecay
    (d k : ℕ) :
    (fun x : CompletedZeroCenteredHeightShellSigma =>
      completedZeroCenteredHeightShellFiberDecay d k x) =
      fun x : CompletedZeroCenteredHeightShellSigma =>
        zetaCompletedZeroCenteredHeight
            (completedZeroCenteredHeightShellSigma_forget x) ^
          (-(d + k + 3 : ℤ)) :=
  funext (completedZeroCenteredHeightShellFiberDecay_eq_baseDecay d k)

/-- Summability over the sigma shell decomposition transports to summability
over completed zeros. -/
theorem summable_completedZero_centeredHeight_negativePower_of_shellSigma
    (d k : ℕ)
    (hsigma :
      Summable
        (fun x : CompletedZeroCenteredHeightShellSigma =>
          completedZeroCenteredHeightShellFiberDecay d k x)) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) := by
  exact summable_of_bijective_index_transport_real
    completedZeroCenteredHeightShellSigma_forget
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ)))
    completedZeroCenteredHeightShellSigma_forget_injective
    completedZeroCenteredHeightShellSigma_forget_surjective
    (Eq.subst
      (motive := fun u : CompletedZeroCenteredHeightShellSigma → ℝ =>
        Summable u)
      (completedZeroCenteredHeightShellFiberDecay_family_eq_baseDecay d k)
      hsigma)

/-- Summable centered-height shell masses transport to summability over all
completed zeros. -/
theorem summable_completedZero_centeredHeight_negativePower_of_shellMass
    (d k : ℕ)
    (hshell :
      Summable
        (fun m : ℕ =>
          completedZeroCenteredHeightShellDecayMass d k m)) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) := by
  exact summable_completedZero_centeredHeight_negativePower_of_shellSigma
    d
    k
    (summable_completedZeroCenteredHeightShellFiberDecay_of_shellMass
      d k hshell)


end

end LFunctions
end Boundary
