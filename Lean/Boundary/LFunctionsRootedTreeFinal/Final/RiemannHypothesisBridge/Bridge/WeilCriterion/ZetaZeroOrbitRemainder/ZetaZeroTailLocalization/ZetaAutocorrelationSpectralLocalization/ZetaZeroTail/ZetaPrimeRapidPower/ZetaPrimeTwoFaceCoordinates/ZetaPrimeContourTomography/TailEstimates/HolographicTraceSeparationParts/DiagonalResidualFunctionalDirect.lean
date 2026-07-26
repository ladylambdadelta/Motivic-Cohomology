import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.BoundedCoefficientDirect

/-!
# Direct diagonal residual coordinate functional wrappers

This file owns the direct holographic trace-separation wrappers after the
positive/off-diagonal gap has been assembled.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed diagonal-debt coordinate residual is represented by a
bounded completed-zero coordinate coefficient family that annihilates
admissible probe coordinates. -/
theorem exists_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_boundedCoordinateCoefficient_ownerHolographicTraceSeparation
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
  exists_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_boundedCoordinateCoefficient_source_primitive
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
    hcompactBoundary f D hmajorant hcoordinateZero

/-- The completed diagonal-debt coordinate residual is represented by a
bounded completed-zero coordinate coefficient family that annihilates
admissible probe coordinates, with the positive/off-diagonal gap vanishing
explicitly supplied. -/
theorem exists_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_boundedCoordinateCoefficient_of_positiveOffDiagonalGap_eq_zero_direct_ownerHolographicTraceSeparation
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
  exists_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_boundedCoordinateCoefficient_of_positiveOffDiagonalGap_eq_zero_direct_source_primitive
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
    hcompactBoundary f D hmajorant hgapZero

/-- The completed diagonal-debt coordinate residual is represented by a
continuous completed-zero coordinate functional which vanishes on admissible
probe coordinates. -/
theorem exists_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_coordinateFunctional_ownerHolographicTraceSeparation
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
  match
    exists_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_boundedCoordinateCoefficient_ownerHolographicTraceSeparation
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
      hcompactBoundary f D hmajorant hcoordinateZero
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

/-- The completed diagonal-debt coordinate residual is represented by a
continuous completed-zero coordinate functional which vanishes on admissible
probe coordinates, with the positive/off-diagonal gap vanishing explicitly
supplied. -/
theorem exists_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_coordinateFunctional_of_positiveOffDiagonalGap_eq_zero_direct_ownerHolographicTraceSeparation
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
    exists_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_boundedCoordinateCoefficient_of_positiveOffDiagonalGap_eq_zero_direct_ownerHolographicTraceSeparation
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

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
