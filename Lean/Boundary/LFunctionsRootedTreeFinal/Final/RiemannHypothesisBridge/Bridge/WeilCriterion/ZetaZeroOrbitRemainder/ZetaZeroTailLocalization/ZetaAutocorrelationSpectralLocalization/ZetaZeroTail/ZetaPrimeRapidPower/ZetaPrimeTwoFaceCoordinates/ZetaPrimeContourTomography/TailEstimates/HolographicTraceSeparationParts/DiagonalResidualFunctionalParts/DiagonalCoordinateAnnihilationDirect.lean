import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalCoordinateAnnihilation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalDebtAnnihilatorGapAssembly

/-!
# Direct diagonal coordinate annihilation wrappers

This file owns the direct wrappers obtained after the positive/off-diagonal
gap-zero theorem has been assembled.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed diagonal-debt coordinate residual is represented by a
bounded completed-zero coordinate coefficient family that annihilates
admissible probe coordinates. -/
theorem exists_diagonalCoordinateResidual_boundedAnnihilator_source
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
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
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
  exists_diagonalCoordinateResidual_boundedAnnihilator_of_positiveOffDiagonalGap_eq_zero_source
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
    hcompactBoundary f D hmajorant
    (completedPrimePositiveOffDiagonalGap_eq_zero_source
      f D hmajorant hcoordinateZero)

/-- The completed diagonal-debt coordinate residual is represented by a
bounded completed-zero coordinate coefficient family that annihilates
admissible probe coordinates, with the positive/off-diagonal gap vanishing
explicitly supplied. -/
theorem exists_diagonalCoordinateResidual_boundedAnnihilator_of_positiveOffDiagonalGap_eq_zero_direct_source
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
  exists_diagonalCoordinateResidual_boundedAnnihilator_of_positiveOffDiagonalGap_eq_zero_source
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
    hcompactBoundary f D hmajorant hgapZero

/-- The completed diagonal-debt coordinate residual is represented by a
continuous completed-zero coordinate functional which vanishes on admissible
probe coordinates. -/
theorem exists_diagonalCoordinateResidual_vanishingCoordinateFunctional_source
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
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    ∃ L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ,
      (∀ g : ZetaAdmissibleFunction,
        L
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite
            hpartialLeft hcompactBoundary g) = 0) ∧
      ((Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
        ℂ) =
        L
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite
            hpartialLeft hcompactBoundary f) :=
  exists_diagonalCoordinateResidual_vanishingCoordinateFunctional_of_positiveOffDiagonalGap_eq_zero_source
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
    hcompactBoundary f D hmajorant
    (completedPrimePositiveOffDiagonalGap_eq_zero_source
      f D hmajorant hcoordinateZero)

/-- The completed diagonal-debt coordinate residual is represented by a
continuous completed-zero coordinate functional which vanishes on admissible
probe coordinates, with the positive/off-diagonal gap vanishing explicitly
supplied. -/
theorem exists_diagonalCoordinateResidual_vanishingCoordinateFunctional_of_positiveOffDiagonalGap_eq_zero_direct_source
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
    ∃ L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ,
      (∀ g : ZetaAdmissibleFunction,
        L
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite
            hpartialLeft hcompactBoundary g) = 0) ∧
      ((Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
        ℂ) =
        L
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite
            hpartialLeft hcompactBoundary f) :=
  exists_diagonalCoordinateResidual_vanishingCoordinateFunctional_of_positiveOffDiagonalGap_eq_zero_source
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
    hcompactBoundary f D hmajorant hgapZero

/-- Density of completed-zero probe coordinates kills the completed
diagonal-debt coordinate residual. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_real_eq_zero_of_coordinateDensity_source
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
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0)
    (hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary = Set.univ) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_real_eq_zero_of_coordinateDensity_and_positiveOffDiagonalGap_eq_zero_source
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
    hcompactBoundary f D hmajorant hdense
    (completedPrimePositiveOffDiagonalGap_eq_zero_source
      f D hmajorant hcoordinateZero)

/-- Density of completed-zero probe coordinates kills the completed
diagonal-debt coordinate residual, with the positive/off-diagonal gap
vanishing explicitly supplied. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_real_eq_zero_of_coordinateDensity_and_positiveOffDiagonalGap_eq_zero_direct_source
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
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0)
    (hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary = Set.univ) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_real_eq_zero_of_coordinateDensity_and_positiveOffDiagonalGap_eq_zero_source
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
    hcompactBoundary f D hmajorant hdense hgapZero

/-- The completed diagonal-debt coordinate residual has zero real scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_real_eq_zero_source_primitive
    (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  hcoordinateZero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
