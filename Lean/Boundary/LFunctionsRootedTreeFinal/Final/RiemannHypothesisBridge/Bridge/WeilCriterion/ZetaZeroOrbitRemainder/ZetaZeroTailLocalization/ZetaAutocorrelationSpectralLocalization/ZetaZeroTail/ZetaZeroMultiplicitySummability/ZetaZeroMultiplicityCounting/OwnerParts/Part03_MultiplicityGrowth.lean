import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.OwnerParts.Part02_HeightBallCounting

namespace Boundary
namespace LFunctions

noncomputable section

theorem zetaZeroMultiplicity_norm_le_counting_bound
    (C : ℝ) (d : ℕ)
    (hcount : ∀ T : ℝ, 1 ≤ T →
      completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ ≤
      C * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) := by
  have hmultCount :
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤
        completedZeroMultiplicityCountingInCenteredHeightBall
          (zetaCompletedZeroCenteredHeight ρ) :=
    zetaZeroMultiplicity_le_countingFunction_at_height ρ
  have hcountHeight :
      completedZeroMultiplicityCountingInCenteredHeightBall
          (zetaCompletedZeroCenteredHeight ρ) ≤
        C * zetaCompletedZeroCenteredHeight ρ ^ d :=
    hcount
      (zetaCompletedZeroCenteredHeight ρ)
      (zetaCompletedZeroCenteredHeight_ge_one ρ)
  have hnaturalBound :
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤
        C * zetaCompletedZeroCenteredHeight ρ ^ d :=
    le_trans hmultCount hcountHeight
  have hpower :
      zetaCompletedZeroCenteredHeight ρ ^ d =
        zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) :=
    (zpow_natCast (zetaCompletedZeroCenteredHeight ρ) d).symm
  have hintegerBound :
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤
        C * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) :=
    Eq.subst
      (motive := fun power : ℝ =>
        (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤ C * power)
      hpower
      hnaturalBound
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤ C * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ))
    (norm_complex_ofNat_zetaZeroMultiplicity ρ).symm
    hintegerBound

theorem zetaZeroMultiplicityGrowthEnvelope_of_counting_bound
    (C : ℝ) (d : ℕ) (hCpos : 0 < C)
    (hcount : ∀ T : ℝ, 1 ≤ T →
      completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    ∃ M : ℝ, ∃ degree : ℕ,
      0 < M ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ ≤
          M * zetaCompletedZeroCenteredHeight ρ ^ (degree : ℤ) :=
  Exists.intro C
    (Exists.intro d
      (And.intro hCpos
        (zetaZeroMultiplicity_norm_le_counting_bound C d hcount)))

/-- Completed-zero multiplicities have polynomial growth in centered height, as a local
consequence of multiplicity-aware zero counting. -/
theorem exists_zetaZeroMultiplicityGrowthEnvelope_bound_from_counting
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ M : ℝ, ∃ d : ℕ,
      0 < M ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ ≤
          M * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) := by
  exact
    Exists.elim
      (exists_completedZeroMultiplicityCounting_height_bound
        hbranch
        hpartialOneTwo hcompactOneTwo
        hfinite
        hpartialLeft hcompactBoundary)
      (fun C hC =>
        Exists.elim hC
          (fun d hd =>
            And.elim
              (fun hCpos hcount =>
                zetaZeroMultiplicityGrowthEnvelope_of_counting_bound
                  C d hCpos hcount)
              hd))


end

end LFunctions
end Boundary
