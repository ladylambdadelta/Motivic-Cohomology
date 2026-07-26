import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalDebtAnnihilatorCore

/-!
# Diagonal residual bounded coefficient source

This file owns the bounded completed-zero coefficient presentation of the
completed diagonal-debt coordinate residual.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed diagonal-debt coordinate residual is represented by a
bounded completed-zero coordinate coefficient family, with the
positive/off-diagonal gap vanishing explicitly supplied. -/
theorem exists_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_boundedCoordinateCoefficient_of_positiveOffDiagonalGap_eq_zero_source_primitive
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    ∃ b : ZetaCompletedZeroCoordinateLInfinity,
      ZetaCompletedZeroSideAnnihilatorVanishes
        b hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary ∧
      ((Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
        ℂ) =
        zetaCompletedZeroSideAnnihilator
          b hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary f :=
  exists_diagonalDebtCoordinateResidual_boundedAnnihilator_core_of_positiveOffDiagonalGap_eq_zero_source
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
    hcompactBoundary f D hmajorant hgapZero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
