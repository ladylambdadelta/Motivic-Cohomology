import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.BoundedCoefficient
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.ResidualCoordinate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransportParts.PositiveRealWindowLimit

/-!
# Diagonal coordinate annihilation

This file owns the density/annihilator vanishing theorem for the completed
diagonal-debt coordinate residual.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed diagonal coordinate residual real scalar expands as the sum
of the positive coordinate trace and the completed two-face real scalar. -/
theorem diagonalCoordinateResidualReal_eq_positiveCoordinate_add_twoFace_source
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  diagonalDebtCoordinateResidual_re_eq_positiveCoordinate_add_twoFace_source
    f hmajorant

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs expand the
completed diagonal coordinate residual real scalar as the sum of the positive
coordinate trace and the completed two-face real scalar. -/
theorem diagonalCoordinateResidualReal_eq_positiveCoordinate_add_twoFace_of_diagonalDebtCoordinate_re_hasSum_source
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  diagonalDebtCoordinateResidual_re_eq_positiveCoordinate_add_twoFace_of_diagonalDebtCoordinate_re_hasSum_source
    f C Creflect hhasSum hhasSumReflect

/-- The completed diagonal-debt coordinate residual is represented by a
bounded completed-zero coordinate coefficient family, with the
positive/off-diagonal gap vanishing explicitly supplied. -/
theorem exists_diagonalCoordinateResidual_boundedAnnihilator_of_positiveOffDiagonalGap_eq_zero_source
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
  exists_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_boundedCoordinateCoefficient_of_positiveOffDiagonalGap_eq_zero_source_primitive
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
    hcompactBoundary f D hmajorant hgapZero

/-- The completed diagonal-debt coordinate residual is represented by a
continuous completed-zero coordinate functional, with the positive/off-diagonal
gap vanishing explicitly supplied. -/
theorem exists_diagonalCoordinateResidual_vanishingCoordinateFunctional_of_positiveOffDiagonalGap_eq_zero_source
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
  match
    exists_diagonalCoordinateResidual_boundedAnnihilator_of_positiveOffDiagonalGap_eq_zero_source
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
      hcompactBoundary f D hmajorant hgapZero
  with
  | ⟨b, hvanishes, hrepresents⟩ =>
      let L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ :=
        zetaCompletedZeroSideL1DualContinuousLinearMap b
      let hLvanishes :
          ∀ g : ZetaAdmissibleFunction,
            L
              (zetaCompletedZeroSideCoordinateL1LinearMap
                hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary g) = 0 :=
        fun g : ZetaAdmissibleFunction =>
          let happly :
              L
                  (zetaCompletedZeroSideCoordinateL1LinearMap
                    hbranch hpartialOneTwo hcompactOneTwo hfinite
                    hpartialLeft hcompactBoundary g) =
                zetaCompletedZeroSideL1DualPairing b
                  (zetaCompletedZeroSideCoordinateL1LinearMap
                    hbranch hpartialOneTwo hcompactOneTwo hfinite
                    hpartialLeft hcompactBoundary g) :=
            zetaCompletedZeroSideL1DualContinuousLinearMap_apply
              b
              (zetaCompletedZeroSideCoordinateL1LinearMap
                hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary g)
          let hpairing :
              zetaCompletedZeroSideL1DualPairing b
                  (zetaCompletedZeroSideCoordinateL1LinearMap
                    hbranch hpartialOneTwo hcompactOneTwo hfinite
                    hpartialLeft hcompactBoundary g) =
                zetaCompletedZeroSideAnnihilator
                  b hbranch hpartialOneTwo hcompactOneTwo hfinite
                  hpartialLeft hcompactBoundary g :=
            Eq.refl
              (zetaCompletedZeroSideAnnihilator
                b hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary g)
          happly.trans (hpairing.trans (hvanishes g))
      let hLevaluation :
          ((Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
            ℂ) =
            L
              (zetaCompletedZeroSideCoordinateL1LinearMap
                hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary f) :=
        let hpairing :
            zetaCompletedZeroSideAnnihilator
                b hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary f =
              zetaCompletedZeroSideL1DualPairing b
                (zetaCompletedZeroSideCoordinateL1LinearMap
                  hbranch hpartialOneTwo hcompactOneTwo hfinite
                  hpartialLeft hcompactBoundary f) :=
          Eq.refl
            (zetaCompletedZeroSideAnnihilator
              b hbranch hpartialOneTwo hcompactOneTwo hfinite
              hpartialLeft hcompactBoundary f)
        let happly :
            zetaCompletedZeroSideL1DualPairing b
                (zetaCompletedZeroSideCoordinateL1LinearMap
                  hbranch hpartialOneTwo hcompactOneTwo hfinite
                  hpartialLeft hcompactBoundary f) =
              L
                (zetaCompletedZeroSideCoordinateL1LinearMap
                  hbranch hpartialOneTwo hcompactOneTwo hfinite
                  hpartialLeft hcompactBoundary f) :=
          (zetaCompletedZeroSideL1DualContinuousLinearMap_apply
            b
            (zetaCompletedZeroSideCoordinateL1LinearMap
              hbranch hpartialOneTwo hcompactOneTwo hfinite
              hpartialLeft hcompactBoundary f)).symm
        hrepresents.trans (hpairing.trans happly)
      ⟨L, hLvanishes, hLevaluation⟩

/-- Density of completed-zero probe coordinates kills the completed
diagonal-debt coordinate residual, with the positive/off-diagonal gap
vanishing explicitly supplied. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_real_eq_zero_of_coordinateDensity_and_positiveOffDiagonalGap_eq_zero_source
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
    (hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary = Set.univ)
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  match
    exists_diagonalCoordinateResidual_vanishingCoordinateFunctional_of_positiveOffDiagonalGap_eq_zero_source
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
      hcompactBoundary f D hmajorant hgapZero
  with
  | ⟨L, hvanishes, hrepresents⟩ =>
      let hLzero :
          L = 0 :=
        completedZeroCoordinateContinuousLinearMap_eq_zero_of_coordinateDensity
          hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary L hvanishes hdense
      let happlyZero :
          L
              (zetaCompletedZeroSideCoordinateL1LinearMap
                hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary f) =
            (0 : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ)
              (zetaCompletedZeroSideCoordinateL1LinearMap
                hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary f) :=
        congrArg
          (fun M : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ =>
            M
              (zetaCompletedZeroSideCoordinateL1LinearMap
                hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary f))
          hLzero
      let hzeroApply :
          (0 : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ)
              (zetaCompletedZeroSideCoordinateL1LinearMap
                hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary f) =
            0 :=
        Eq.refl (0 : ℂ)
      let hcomplexZero :
          ((Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
            ℂ) = 0 :=
        hrepresents.trans (happlyZero.trans hzeroApply)
      Complex.ofReal_eq_zero.mp hcomplexZero

/-- The completed diagonal-debt coordinate residual has zero real scalar, with
the positive/off-diagonal gap vanishing explicitly supplied. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_real_eq_zero_of_positiveOffDiagonalGap_eq_zero_source_primitive
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  let hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption :=
    Complex.binetSecondFormulaBranchUniformTailAbsorption_owner
  let hreflected : PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope :=
    poleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope_owner
  let hpartialOneTwo : BoundaryLineOneAbelPartialMajorant :=
    boundaryLineOneAbelPartialMajorant_from_realParam
  let hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound :=
    poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
  let hfinite : PoleClearedRightCriticalStripAdmissibleGrowth :=
    poleClearedRightCriticalStripAdmissibleGrowth_owner hbranch hreflected
  let hpartialLeft : ReflectedBoundaryAbelPartialMajorant :=
    reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
      hpartialOneTwo
  let hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound :=
    poleClearedRightCriticalStripCompactBoundaryBound_from_compact
  let hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary = Set.univ :=
    zetaCompletedZeroSideCoordinateL1Closure_eq_univ
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_real_eq_zero_of_coordinateDensity_and_positiveOffDiagonalGap_eq_zero_source
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
    hcompactBoundary f D hmajorant hdense hgapZero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
