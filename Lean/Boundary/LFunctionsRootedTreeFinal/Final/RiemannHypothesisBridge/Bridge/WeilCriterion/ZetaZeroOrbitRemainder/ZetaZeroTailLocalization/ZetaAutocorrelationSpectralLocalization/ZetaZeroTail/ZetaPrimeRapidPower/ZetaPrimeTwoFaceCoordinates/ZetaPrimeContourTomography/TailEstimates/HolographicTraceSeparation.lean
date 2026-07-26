import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalDirect
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.VisibleRemainderConvergence
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.OwnerParts.Part07
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDefectEnergy

/-!
# Holographic completed prime trace separation

This file owns the global trace-reconstruction step behind completed prime
contour/time transport.
-/

namespace Boundary
namespace LFunctions
noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed prime trace residual distribution is represented by a single
bounded completed-zero coefficient family which annihilates the admissible
probe coordinates. -/
theorem exists_completedPrimeTraceResidualDistribution_coordinateCoefficient
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
      ((completedPrimeTraceTimeScalar f -
            completedPrimeTraceSpectralScalar f : ℝ) : ℂ) =
          zetaCompletedZeroSideAnnihilator
            b hbranch hpartialOneTwo hcompactOneTwo hfinite
            hpartialLeft hcompactBoundary f :=
  match
    exists_completedPrimeTraceResidualDistribution_boundedCoordinateCoefficient_at
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary f D hmajorant hcoordinateZero
  with
  | ⟨b, hvanishes, hrepresents⟩ =>
      let hrepresentsUnfolded :
          ((completedPrimeTraceTimeScalar f -
              completedPrimeTraceSpectralScalar f : ℝ) : ℂ) =
            zetaCompletedZeroSideAnnihilator
              b hbranch hpartialOneTwo hcompactOneTwo hfinite
              hpartialLeft hcompactBoundary f :=
        Eq.trans
          (completedPrimeTraceResidualComplexScalar_eq f).symm
          hrepresents
      ⟨b, hvanishes, hrepresentsUnfolded⟩

/-- The completed prime trace scalar difference is represented by the global
completed-zero residual coefficient. -/
theorem exists_completedPrimeTraceScalarDifference_coordinateCoefficient
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
      ((completedPrimeTraceTimeScalar f -
            completedPrimeTraceSpectralScalar f : ℝ) : ℂ) =
          zetaCompletedZeroSideAnnihilator
            b hbranch hpartialOneTwo hcompactOneTwo hfinite
            hpartialLeft hcompactBoundary f :=
  match
    exists_completedPrimeTraceResidualDistribution_coordinateCoefficient
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary f D hmajorant hcoordinateZero
  with
  | ⟨b, hvanishes, hrepresents⟩ =>
      ⟨b, hvanishes, hrepresents⟩

/-- The completed prime trace scalar difference is represented by a continuous
completed-zero coordinate functional which vanishes on probe coordinates. -/
theorem exists_completedPrimeTraceScalarDifference_coordinateFunctional
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
      ((completedPrimeTraceTimeScalar f -
          completedPrimeTraceSpectralScalar f : ℝ) : ℂ) =
        L
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite
            hpartialLeft hcompactBoundary f) :=
  match
    exists_completedPrimeTraceScalarDifference_coordinateCoefficient
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary f D hmajorant hcoordinateZero
  with
  | ⟨b, hvanishes, hrepresentation⟩ =>
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
          ((completedPrimeTraceTimeScalar f -
              completedPrimeTraceSpectralScalar f : ℝ) : ℂ) =
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
        hrepresentation.trans (hpairing.trans happly)
      ⟨L, hLvanishes, hLevaluation⟩

/-- A coordinate-functional representation of the trace scalar difference and
density force the trace scalar difference to vanish. -/
theorem completedPrimeTraceScalarDifference_eq_zero_of_coordinateFunctional
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
    completedPrimeTraceTimeScalar f -
        completedPrimeTraceSpectralScalar f = 0 :=
  match
    exists_completedPrimeTraceScalarDifference_coordinateFunctional
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary f D hmajorant hcoordinateZero
  with
  | ⟨L, hvanishes, hrep⟩ =>
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
          ((completedPrimeTraceTimeScalar f -
              completedPrimeTraceSpectralScalar f : ℝ) : ℂ) = 0 :=
        hrep.trans (happlyZero.trans hzeroApply)
      Complex.ofReal_eq_zero.mp hcomplexZero

/-- Coordinate-density scalar reconstruction: the dense completed-zero probe
coordinates determine the two completed prime trace scalar presentations. -/
theorem completedPrimeTraceTimeScalar_eq_spectralScalar_of_coordinateDensity
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
    completedPrimeTraceTimeScalar f =
      completedPrimeTraceSpectralScalar f :=
  sub_eq_zero.mp
    (completedPrimeTraceScalarDifference_eq_zero_of_coordinateFunctional
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary f D hmajorant hcoordinateZero hdense)

/-- Coordinate-density trace reconstruction: if completed-zero probe
coordinates are dense in the `l1` trace space, then the time/log prime trace
and contour-realized spectral prime trace are the same scalar on
autocorrelation probes. -/
theorem zetaCompletedExplicitFormulaPrimePowerContribution_re_eq_spectralSampleContribution_re_of_coordinateDensity
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
    Complex.re
        (zetaCompletedExplicitFormulaPrimePowerContribution
          (convolutionAutocorrelation f)) =
      Complex.re
        (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
          (convolutionAutocorrelation f)) :=
  let hscalar :
      completedPrimeTraceTimeScalar f =
        completedPrimeTraceSpectralScalar f :=
    completedPrimeTraceTimeScalar_eq_spectralScalar_of_coordinateDensity
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary f D hmajorant hcoordinateZero hdense
  let htime :
      Complex.re
        (zetaCompletedExplicitFormulaPrimePowerContribution
          (convolutionAutocorrelation f)) =
        completedPrimeTraceTimeScalar f :=
    (completedPrimeTraceTimeScalar_eq f).symm
  let hspectral :
      completedPrimeTraceSpectralScalar f =
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
            (convolutionAutocorrelation f)) :=
    completedPrimeTraceSpectralScalar_eq f
  htime.trans (hscalar.trans hspectral)

/-- Holographic trace reconstruction from bounded completed-zero annihilator
uniqueness.

The proof is the trace-theoretic reconstruction step through a bounded
zero-side annihilator and kernel density. -/
theorem zetaCompletedExplicitFormulaPrimePowerContribution_re_eq_spectralSampleContribution_re_of_annihilatorDensity
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
    Complex.re
        (zetaCompletedExplicitFormulaPrimePowerContribution
          (convolutionAutocorrelation f)) =
      Complex.re
        (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
          (convolutionAutocorrelation f)) :=
  let hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary = Set.univ :=
    zetaCompletedZeroSideCoordinateL1Closure_eq_univ
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary
  zetaCompletedExplicitFormulaPrimePowerContribution_re_eq_spectralSampleContribution_re_of_coordinateDensity
    hbranch hpartialOneTwo hcompactOneTwo hfinite
    hpartialLeft hcompactBoundary f D hmajorant hcoordinateZero hdense

theorem zetaCompletedExplicitFormulaPrimePowerContribution_re_eq_spectralSampleContribution_re_ownerHolographicTraceSeparation
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Complex.re
        (zetaCompletedExplicitFormulaPrimePowerContribution
          (convolutionAutocorrelation f)) =
      Complex.re
        (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
          (convolutionAutocorrelation f)) :=
  zetaCompletedExplicitFormulaPrimePowerContribution_re_eq_spectralSampleContribution_re_ownerTraceReconstruction
    f D

theorem completedPrimeTraceFunctionalGap_eq_zero_ownerHolographicTraceSeparation
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeTraceFunctionalGap f = 0 :=
  completedPrimeTraceFunctionalGap_eq_zero_traceTransport_source_core f D

theorem zetaCompletedExplicitFormulaPrimePowerContribution_re_eq_spectralSampleContribution_re_of_traceGap_zero
    (f : ZetaAdmissibleFunction)
    (hgap : completedPrimeTraceFunctionalGap f = 0) :
    Complex.re
        (zetaCompletedExplicitFormulaPrimePowerContribution
          (convolutionAutocorrelation f)) =
      Complex.re
        (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
          (convolutionAutocorrelation f)) :=
  let hgapUnfolded :
      Complex.re
          (zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f)) -
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
            (convolutionAutocorrelation f)) = 0 :=
    Eq.trans (completedPrimeTraceFunctionalGap_eq f).symm hgap
  sub_eq_zero.mp hgapUnfolded

theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_traceGap_zero_and_positiveOffDiagonalGap_zero_ownerHolographicTraceSeparation
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (htraceZero : completedPrimeTraceFunctionalGap f = 0)
    (hpositiveGapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  diagonalDebtCoordinateResidual_re_eq_zero_of_traceGap_zero_and_positiveOffDiagonalGap_zero_source
    f
    hmajorant
    htraceZero
    hpositiveGapZero

theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_positiveCoordinate_zero_ownerHolographicTraceSeparation
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hpositiveZero :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  (diagonalDebtCoordinateTsum_re_eq_zero_iff_positiveCoordinate_zero_source
    f hmajorant).mpr
    hpositiveZero

/-- Genuine completed prime defect-energy annihilation gives the missing
diagonal-coordinate zero. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_defectEnergy_zero_ownerHolographicTraceSeparation
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (henergyZero : zetaCompletedPrimeDefectEnergy f = 0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  let hpositiveZero :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_of_spectralMajorant_and_defectEnergy_zero
      f
      hmajorant
      henergyZero
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_positiveCoordinate_zero_ownerHolographicTraceSeparation
    f hmajorant hpositiveZero

/-- After source two-face cancellation, diagonal-coordinate annihilation is
equivalent to genuine completed prime defect-energy annihilation. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_iff_defectEnergy_zero_ownerHolographicTraceSeparation
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0 ↔
      zetaCompletedPrimeDefectEnergy f = 0 :=
  let hdiagonalPositive :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
          0 ↔
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
    diagonalDebtCoordinateTsum_re_eq_zero_iff_positiveCoordinate_zero_source f hmajorant
  let henergyPositive :
      zetaCompletedPrimeDefectEnergy f = 0 ↔
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
    zetaCompletedPrimeDefectEnergy_eq_zero_iff_positiveCoordinateTsumRe_eq_zero_of_spectralMajorant
      f hmajorant
  Iff.intro
    (fun hdiagonal =>
      henergyPositive.mpr (hdiagonalPositive.mp hdiagonal))
    (fun henergy =>
      hdiagonalPositive.mpr (henergyPositive.mp henergy))

/-- Density-level holographic trace separation annihilates the real scalar of
the completed diagonal-debt coordinate presentation.

This is the trace-faithfulness theorem behind positive-coordinate
reconstruction with every analytic control and the completed-zero coordinate
density hypothesis visible. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_coordinateDensity_ownerHolographicTraceSeparation
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0)
    (hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary = Set.univ) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  hcoordinateZero

/-- Density-level holographic trace separation with gap vanishing supplied. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_coordinateDensity_and_positiveOffDiagonalGap_eq_zero_ownerHolographicTraceSeparation
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary = Set.univ)
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  let htransport :
      CompletedSummedPrimeContourTimeTransport f :=
    completedPrimeContourTransportSummedTransport_owner
      f D
  let hgapResidual :
      completedPrimePositiveOffDiagonalGap f =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
    completedPrimePositiveOffDiagonalGap_eq_diagonalDebtCoordinateTsum_re_summedTransport
      f htransport hmajorant
  let hdiagonalZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0 :=
    hgapResidual.symm.trans hgapZero
  let hdenseTransport :
      (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
          0) =
        (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
          0) :=
    congrArg
      (fun value :
        zetaCompletedZeroSideCoordinateL1Closure
            hbranch hpartialOneTwo hcompactOneTwo hfinite
            hpartialLeft hcompactBoundary = Set.univ =>
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
          0)
      (Eq.refl hdense)
  Eq.mp hdenseTransport hdiagonalZero

/-- Owner wrapper for density-level diagonal-debt coordinate annihilation. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_ownerHolographicTraceSeparation
    (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
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
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_coordinateDensity_ownerHolographicTraceSeparation
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
    hcompactBoundary f hcoordinateZero hdense

/-- Holographic trace separation annihilates the real scalar of the completed
diagonal-debt coordinate presentation, with the positive/off-diagonal gap
vanishing explicitly supplied. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_positiveOffDiagonalGap_eq_zero_ownerHolographicTraceSeparation
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
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
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_coordinateDensity_and_positiveOffDiagonalGap_eq_zero_ownerHolographicTraceSeparation
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
    hcompactBoundary f D hmajorant hdense hgapZero

/-- The off-diagonal channel is the raw positive coordinate once diagonal debt vanishes. -/
theorem completedPrimeOffDiagonalChannel_eq_zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_of_diagonalDebtCoordinateTsum_re_eq_zero_ownerHolographicTraceSeparation
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    completedPrimeOffDiagonalChannel f =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
  let htransport :
      CompletedSummedPrimeContourTimeTransport f :=
    completedPrimeContourTransportSummedTransport_owner
      f D
  completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_diagonalDebtCoordinateTsum_re_eq_zero
    f htransport hmajorant hdiagonal

/-- Diagonal-density cancellation and positivity force the two-face real scalar to vanish. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_positiveTraceFaithfulness_ownerHolographicTraceSeparation
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0)
    (hfaithful :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
  zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_diagonalCoordinate_zero_and_positiveChannel
    f
    hmajorant
    hdiagonal
    hfaithful

/-- Holographic trace separation identifies the completed off-diagonal trace
scalar with the raw completed positive coordinate presentation.

This is the coordinate-reconstruction half of the positive trace theorem: the
off-diagonal trace sees the positive defect-square coordinate total directly,
without first reconstructing diagonal debt. -/
theorem completedPrimeOffDiagonalChannel_eq_zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_ownerHolographicTraceSeparation
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    completedPrimeOffDiagonalChannel f =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
  completedPrimeOffDiagonalChannel_eq_zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_of_diagonalDebtCoordinateTsum_re_eq_zero_ownerHolographicTraceSeparation
    f D hmajorant
    hcoordinateZero

/-- Holographic trace separation identifies the completed off-diagonal trace
scalar with the owner completed positive channel.

This is the owner-channel half of the positive trace theorem: the same
off-diagonal trace scalar represents the completed positive channel after
lower-weight trace reconstruction. -/
theorem completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_ownerHolographicTraceSeparation
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f :=
  completedPrimeOffDiagonalChannel_eq_ownerPositiveChannel_twoFaceZero_source
    f D

/-- Holographic trace separation identifies the raw completed positive
coordinate presentation with the owner completed positive channel.

This is the trace-faithfulness form needed by the finite-window diagonal lane:
the positive coordinate total is reconstructed from the same completed prime
trace character as the owner positive channel, without using diagonal-coordinate
transport. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_ownerHolographicTraceSeparation
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  (completedPrimeOffDiagonalChannel_eq_zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_ownerHolographicTraceSeparation
    f D hmajorant hcoordinateZero).symm.trans
    (completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_ownerHolographicTraceSeparation
      f D)

/-- Holographic trace separation and lower-weight normalization annihilate the
raw completed positive coordinate trace. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_ownerHolographicTraceSeparation
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
  (diagonalDebtCoordinateTsum_re_eq_zero_iff_positiveCoordinate_zero_source
    f hmajorant).mp
    hcoordinateZero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
