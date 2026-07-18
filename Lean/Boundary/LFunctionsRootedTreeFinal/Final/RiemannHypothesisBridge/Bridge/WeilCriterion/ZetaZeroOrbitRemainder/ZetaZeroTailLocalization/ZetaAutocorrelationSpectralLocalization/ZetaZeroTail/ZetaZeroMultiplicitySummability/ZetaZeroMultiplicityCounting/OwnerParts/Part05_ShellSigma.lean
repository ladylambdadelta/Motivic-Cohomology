import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.OwnerParts.Part04_HeightShells

namespace Boundary
namespace LFunctions

noncomputable section

/-- A finite set has a finite subtype of its elements. -/
theorem finite_univ_subtype_of_finite_set
    {α : Type*} {s : Set α}
    (hs : s.Finite) :
    (Set.univ : Set s).Finite := by
  match hs.nonempty_fintype with
  | ⟨inst⟩ =>
      letI : Fintype s := inst
      exact Set.finite_univ

/-- The completed-zero shell fiber at integer height `m`. -/
def completedZeroCenteredHeightShellFiber
    (m : ℕ) : Type :=
  {ρ : {ρ : ℂ // ZetaCompletedZero ρ} //
    ρ ∈ completedZeroCenteredHeightShell m}

/-- The sigma type of all completed-zero shell fibers. -/
abbrev CompletedZeroCenteredHeightShellSigma : Type :=
  Sigma completedZeroCenteredHeightShellFiber

/-- Forget a shell-fiber point to its completed zero. -/
def completedZeroCenteredHeightShellSigma_forget
    (x : CompletedZeroCenteredHeightShellSigma) :
    {ρ : ℂ // ZetaCompletedZero ρ} :=
  x.2.1

theorem completedZeroCenteredHeightShellSigma_forget_constructor
    (m : ℕ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hm : ρ ∈ completedZeroCenteredHeightShell m) :
    completedZeroCenteredHeightShellSigma_forget ⟨m, ⟨ρ, hm⟩⟩ = ρ :=
  Eq.refl ρ

/-- The shell-fiber forgetful map is surjective onto completed zeros. -/
theorem completedZeroCenteredHeightShellSigma_forget_surjective :
    Function.Surjective completedZeroCenteredHeightShellSigma_forget := by
  intro ρ
  exact
    Exists.elim
      (exists_completedZeroCenteredHeightShell_index ρ)
      (fun m hm =>
        Exists.intro ⟨m, ⟨ρ, hm⟩⟩
          (completedZeroCenteredHeightShellSigma_forget_constructor m ρ hm))

theorem completedZeroCenteredHeightShellFiber_heq_of_base_eq
    {m n : ℕ}
    {ρ η : {ρ : ℂ // ZetaCompletedZero ρ}}
    (hρm : ρ ∈ completedZeroCenteredHeightShell m)
    (hηn : η ∈ completedZeroCenteredHeightShell n)
    (hbase : ρ = η) :
    HEq
      (⟨ρ, hρm⟩ : completedZeroCenteredHeightShellFiber m)
      (⟨η, hηn⟩ : completedZeroCenteredHeightShellFiber n) := by
  have hηnOnρ : ρ ∈ completedZeroCenteredHeightShell n :=
    Eq.subst
      (motive := fun q : {ρ : ℂ // ZetaCompletedZero ρ} =>
        q ∈ completedZeroCenteredHeightShell n)
      hbase.symm
      hηn
  have hmn : m = n :=
    completedZeroCenteredHeightShell_index_unique hρm hηnOnρ
  exact Eq.ndrec
    (motive := fun nIndex : ℕ =>
      ∀ hηIndex : η ∈ completedZeroCenteredHeightShell nIndex,
        HEq
          (⟨ρ, hρm⟩ : completedZeroCenteredHeightShellFiber m)
          (⟨η, hηIndex⟩ : completedZeroCenteredHeightShellFiber nIndex))
    (fun hηm =>
      have hfiber :
          (⟨ρ, hρm⟩ : completedZeroCenteredHeightShellFiber m) =
            ⟨η, hηm⟩ :=
        Subtype.ext hbase
      heq_of_eq hfiber)
    hmn
    hηn

theorem completedZeroCenteredHeightShellSigma_eq_of_components
    {m n : ℕ}
    {ρ η : {ρ : ℂ // ZetaCompletedZero ρ}}
    (hρm : ρ ∈ completedZeroCenteredHeightShell m)
    (hηn : η ∈ completedZeroCenteredHeightShell n)
    (hbase : ρ = η) :
    (⟨m, ⟨ρ, hρm⟩⟩ : CompletedZeroCenteredHeightShellSigma) =
      ⟨n, ⟨η, hηn⟩⟩ := by
  have hηnOnρ : ρ ∈ completedZeroCenteredHeightShell n :=
    Eq.subst
      (motive := fun q : {ρ : ℂ // ZetaCompletedZero ρ} =>
        q ∈ completedZeroCenteredHeightShell n)
      hbase.symm
      hηn
  have hmn : m = n :=
    completedZeroCenteredHeightShell_index_unique hρm hηnOnρ
  have hfiber :=
    completedZeroCenteredHeightShellFiber_heq_of_base_eq hρm hηn hbase
  exact Sigma.ext hmn hfiber

/-- The shell-fiber forgetful map is injective; integer height shells are disjoint. -/
theorem completedZeroCenteredHeightShellSigma_forget_injective :
    Function.Injective completedZeroCenteredHeightShellSigma_forget := by
  intro x y hxy
  exact
    match x with
    | ⟨m, ρm⟩ =>
        match y with
        | ⟨n, ρn⟩ =>
            match ρm with
            | ⟨ρ, hρm⟩ =>
                match ρn with
                | ⟨η, hηn⟩ =>
                    completedZeroCenteredHeightShellSigma_eq_of_components
                      hρm hηn hxy


end

end LFunctions
end Boundary
