import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.QuantitativeSeparation.AffineSeedDaggerTransfer

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace QuantitativeSeparation

theorem exists_fixedFiberProbe_with_seedDaggerProductL1Norm_lt
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hSeparated :
      ∀ rho : ℂ,
        ZetaCompletedZero rho →
          rho ∉ S →
            rho ∉ daggerClosedSpectralSampleFinset P)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
        completedZeroSeedDaggerProductL1Norm S f < epsilon := by
  let delta : ℝ := min epsilon 1 / 2
  have hminimumPositive : 0 < min epsilon 1 :=
    lt_min hepsilon zero_lt_one
  have hdeltaPositive : 0 < delta :=
    div_pos hminimumPositive zero_lt_two
  have hdeltaSubunit : delta < 1 := by
    have hminimumLeOne : min epsilon 1 ≤ 1 := min_le_right epsilon 1
    have hhalfLe : delta ≤ 1 / 2 :=
      div_le_div_of_nonneg_right hminimumLeOne zero_le_two
    exact lt_of_le_of_lt hhalfLe one_half_lt_one
  have hdeltaEpsilon : delta < epsilon := by
    have hhalfMinimum : delta < min epsilon 1 :=
      half_lt_self hminimumPositive
    exact lt_of_lt_of_le hhalfMinimum (min_le_left epsilon 1)
  obtain ⟨h, hkernel, happroximation⟩ :=
    exists_zetaCompletedZeroSideCoordinateL1_kernel_approximation
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      (daggerClosedSpectralSampleFinset P)
      (-(zetaCompletedZeroSideCoordinateL1LinearMap
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
        f₀))
      delta hdeltaPositive
  have htransfer :=
    fixedFiber_seedDaggerProduct_lt_of_kernelApproximation
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀ h hSeparated epsilon delta hdeltaPositive hdeltaSubunit
      hdeltaEpsilon hkernel happroximation
  exact ⟨f₀ + h, htransfer.1, htransfer.2⟩

end QuantitativeSeparation
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
