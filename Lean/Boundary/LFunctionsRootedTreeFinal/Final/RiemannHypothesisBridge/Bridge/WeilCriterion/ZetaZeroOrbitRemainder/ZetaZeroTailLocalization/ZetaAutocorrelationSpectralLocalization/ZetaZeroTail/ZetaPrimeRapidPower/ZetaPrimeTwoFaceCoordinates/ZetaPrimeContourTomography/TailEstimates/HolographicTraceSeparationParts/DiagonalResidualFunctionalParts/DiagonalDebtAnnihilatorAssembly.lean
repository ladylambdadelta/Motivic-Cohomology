import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalDebtAnnihilatorGapAssembly

/-!
# Diagonal-debt annihilator assembly

This file owns the functional-package and bounded-annihilator assembly for the
diagonal-debt coordinate residual, after the scalar source identities have been
peeled into `DiagonalDebtAnnihilatorSource`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- If the named positive/off-diagonal mismatch vanishes, then the completed
diagonal-debt coordinate residual is the completed prime trace residual. -/
theorem diagonalDebtCoordinateResidual_eq_completedPrimeTraceResidual_of_positiveOffDiagonalGap_eq_zero_source
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    ((Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
      ℂ) =
      completedPrimeTraceResidualComplexScalar f :=
  let hfunctionalGap :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      completedPrimeTraceFunctionalGap f :=
    diagonalDebtCoordinateResidual_re_eq_completedPrimeTraceFunctionalGap_of_positiveOffDiagonalGap_eq_zero_source
      f
      hmajorant
      hgapZero
  let htraceGap :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        completedPrimeTraceTimeScalar f -
        completedPrimeTraceSpectralScalar f :=
    hfunctionalGap.trans (completedPrimeTraceFunctionalGap_eq f)
  let hcoerce :
      ((Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
        ℂ) =
        ((completedPrimeTraceTimeScalar f -
          completedPrimeTraceSpectralScalar f : ℝ) : ℂ) :=
    congrArg (fun value : ℝ => (value : ℂ)) htraceGap
  hcoerce.trans (completedPrimeTraceResidualComplexScalar_eq f).symm

/-- Source construction of a diagonal-debt residual coordinate functional,
with the positive/off-diagonal mismatch vanishing explicitly supplied. -/
theorem exists_diagonalDebtCoordinateResidual_functionalPackage_of_positiveOffDiagonalGap_eq_zero_source
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
      DiagonalDebtCoordinateFunctionalVanishes
        hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary L ∧
      DiagonalDebtCoordinateFunctionalRepresents
        hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary f L :=
  let L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ :=
    0
  let hvanishes :
      DiagonalDebtCoordinateFunctionalVanishes
        hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary L :=
    fun g : ZetaAdmissibleFunction =>
      Eq.refl (0 : ℂ)
  let htwoFace :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source f
  let hoffOwner :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeOffDiagonalChannel_eq_ownerPositiveChannel_of_twoFace_re_eq_zero_source
      f D htwoFace
  let hownerZero :
      completedPrimeDefectKernelPositiveChannel f = 0 :=
    completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
      f
  let hoffZero :
      completedPrimeOffDiagonalChannel f = 0 :=
    hoffOwner.trans hownerZero
  let hgapRaw :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f -
          completedPrimeOffDiagonalChannel f =
        0 :=
    (completedPrimePositiveOffDiagonalGap_eq f).symm.trans hgapZero
  let hsubTransport :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f -
          completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f - 0 :=
    congrArg
      (fun value : ℝ =>
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f - value)
      hoffZero
  let hpositiveSubZero :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f - 0 = 0 :=
    hsubTransport.symm.trans hgapRaw
  let hpositiveZero :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
    (sub_zero
      (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)).symm.trans
      hpositiveSubZero
  let hsum :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    diagonalDebtCoordinateResidual_re_eq_positiveCoordinate_add_twoFace_source
      f
      hmajorant
  let hpositiveTransport :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        0 + Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    congrArg
      (fun value : ℝ =>
        value + Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))
      hpositiveZero
  let htwoFaceTransport :
      0 + Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        0 + 0 :=
    congrArg (fun value : ℝ => 0 + value) htwoFace
  let haddZero : (0 : ℝ) + 0 = 0 :=
    add_zero 0
  let hdiagonalRealZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0 :=
    hsum.trans
      (hpositiveTransport.trans
        (htwoFaceTransport.trans haddZero))
  let hdiagonalComplexTransport :
      ((Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
        ℂ) =
        ((0 : ℝ) : ℂ) :=
    congrArg (fun value : ℝ => (value : ℂ)) hdiagonalRealZero
  let hdiagonalComplexZero :
      ((Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
        ℂ) = 0 :=
    hdiagonalComplexTransport.trans (Eq.refl (0 : ℂ))
  let hrepresents :
      DiagonalDebtCoordinateFunctionalRepresents
        hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary f L :=
    let hLzero :
        L
          (zetaCompletedZeroSideCoordinateL1LinearMap
            hbranch hpartialOneTwo hcompactOneTwo hfinite
            hpartialLeft hcompactBoundary f) = 0 :=
      Eq.refl (0 : ℂ)
    hdiagonalComplexZero.trans hLzero.symm
  ⟨L, hvanishes, hrepresents⟩

/-- Source construction of a diagonal-debt residual coordinate functional with
the off-diagonal/positive-coordinate comparison explicit. -/
theorem exists_diagonalDebtCoordinateResidual_functionalPackage_of_offDiagonal_eq_positiveCoordinate_source
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
    (hoffPositive :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f) :
    ∃ L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ,
      DiagonalDebtCoordinateFunctionalVanishes
        hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary L ∧
      DiagonalDebtCoordinateFunctionalRepresents
        hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary f L :=
    exists_diagonalDebtCoordinateResidual_functionalPackage_of_positiveOffDiagonalGap_eq_zero_source
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
    hcompactBoundary f D
    hmajorant
    (completedPrimePositiveOffDiagonalGap_eq_zero_of_offDiagonal_eq_positiveCoordinate_source
      f hoffPositive)

/-- The source functional package supplies probe-coordinate vanishing. -/
theorem diagonalDebtCoordinateResidual_functionalPackage_vanishes_direct_source
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction)
    (L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ)
    (hpackage :
      DiagonalDebtCoordinateFunctionalVanishes
        hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary L ∧
      DiagonalDebtCoordinateFunctionalRepresents
        hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary f L) :
    ∀ g : ZetaAdmissibleFunction,
      L
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary g) = 0 :=
  hpackage.1

/-- The source functional package supplies the selected diagonal-debt residual
representation. -/
theorem diagonalDebtCoordinateResidual_functionalPackage_represents_direct_source
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction)
    (L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ)
    (hpackage :
      DiagonalDebtCoordinateFunctionalVanishes
        hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary L ∧
      DiagonalDebtCoordinateFunctionalRepresents
        hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary f L) :
    ((Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
      ℂ) =
      L
        (zetaCompletedZeroSideCoordinateL1LinearMap
          hbranch hpartialOneTwo hcompactOneTwo hfinite
          hpartialLeft hcompactBoundary f) :=
  hpackage.2

/-- Direct diagonal-debt trace reconstruction as a vanishing continuous
completed-zero coordinate functional, with the positive/off-diagonal gap
vanishing explicitly supplied. -/
theorem exists_diagonalDebtCoordinateResidual_vanishingCoordinateFunctional_of_positiveOffDiagonalGap_eq_zero_source
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
    exists_diagonalDebtCoordinateResidual_functionalPackage_of_positiveOffDiagonalGap_eq_zero_source
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
      hcompactBoundary f D hmajorant hgapZero
  with
  | ⟨L, hpackage⟩ =>
      let hvanishes :
          ∀ g : ZetaAdmissibleFunction,
            L
              (zetaCompletedZeroSideCoordinateL1LinearMap
                hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary g) = 0 :=
        diagonalDebtCoordinateResidual_functionalPackage_vanishes_direct_source
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
          hcompactBoundary f L hpackage
      let hrepresents :
          ((Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
            ℂ) =
            L
              (zetaCompletedZeroSideCoordinateL1LinearMap
                hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary f) :=
        diagonalDebtCoordinateResidual_functionalPackage_represents_direct_source
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
          hcompactBoundary f L hpackage
      ⟨L, hvanishes, hrepresents⟩

/-- Direct diagonal-debt trace reconstruction as a vanishing continuous
completed-zero coordinate functional, with the off-diagonal/positive-coordinate
comparison explicit. -/
theorem exists_diagonalDebtCoordinateResidual_vanishingCoordinateFunctional_of_offDiagonal_eq_positiveCoordinate_source
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
    (hoffPositive :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f) :
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
    exists_diagonalDebtCoordinateResidual_functionalPackage_of_offDiagonal_eq_positiveCoordinate_source
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
      hcompactBoundary f D hmajorant hoffPositive
  with
  | ⟨L, hpackage⟩ =>
      let hvanishes :
          ∀ g : ZetaAdmissibleFunction,
            L
              (zetaCompletedZeroSideCoordinateL1LinearMap
                hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary g) = 0 :=
        diagonalDebtCoordinateResidual_functionalPackage_vanishes_direct_source
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
          hcompactBoundary f L hpackage
      let hrepresents :
          ((Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
            ℂ) =
            L
              (zetaCompletedZeroSideCoordinateL1LinearMap
                hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary f) :=
        diagonalDebtCoordinateResidual_functionalPackage_represents_direct_source
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
          hcompactBoundary f L hpackage
      ⟨L, hvanishes, hrepresents⟩

/-- Direct diagonal-debt trace reconstruction as a bounded completed-zero
annihilator, with the positive/off-diagonal gap vanishing explicitly supplied. -/
theorem exists_diagonalDebtCoordinateResidual_boundedAnnihilator_of_positiveOffDiagonalGap_eq_zero_source
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
  match
    exists_diagonalDebtCoordinateResidual_vanishingCoordinateFunctional_of_positiveOffDiagonalGap_eq_zero_source
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
      hcompactBoundary f D hmajorant hgapZero
  with
  | ⟨L, hLvanishes, hrepresents⟩ =>
      match exists_zetaCompletedZeroSideL1DualRepresentation L with
      | ⟨b, hb⟩ =>
          let hvanishes :
              ZetaCompletedZeroSideAnnihilatorVanishes
                b hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary :=
            fun g : ZetaAdmissibleFunction =>
              let hpairing :
                  zetaCompletedZeroSideAnnihilator
                      b hbranch hpartialOneTwo hcompactOneTwo hfinite
                      hpartialLeft hcompactBoundary g =
                    zetaCompletedZeroSideL1DualPairing b
                      (zetaCompletedZeroSideCoordinateL1LinearMap
                        hbranch hpartialOneTwo hcompactOneTwo hfinite
                        hpartialLeft hcompactBoundary g) :=
                Eq.refl
                  (zetaCompletedZeroSideAnnihilator
                    b hbranch hpartialOneTwo hcompactOneTwo hfinite
                    hpartialLeft hcompactBoundary g)
              let hdual :
                  zetaCompletedZeroSideL1DualPairing b
                      (zetaCompletedZeroSideCoordinateL1LinearMap
                        hbranch hpartialOneTwo hcompactOneTwo hfinite
                        hpartialLeft hcompactBoundary g) =
                    L
                      (zetaCompletedZeroSideCoordinateL1LinearMap
                        hbranch hpartialOneTwo hcompactOneTwo hfinite
                        hpartialLeft hcompactBoundary g) :=
                (hb
                  (zetaCompletedZeroSideCoordinateL1LinearMap
                    hbranch hpartialOneTwo hcompactOneTwo hfinite
                    hpartialLeft hcompactBoundary g)).symm
              hpairing.trans (hdual.trans (hLvanishes g))
          let hrepresentation :
              ((Complex.re
                  (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
                ℂ) =
                zetaCompletedZeroSideAnnihilator
                  b hbranch hpartialOneTwo hcompactOneTwo hfinite
                  hpartialLeft hcompactBoundary f :=
            let hdual :
                L
                    (zetaCompletedZeroSideCoordinateL1LinearMap
                      hbranch hpartialOneTwo hcompactOneTwo hfinite
                      hpartialLeft hcompactBoundary f) =
                  zetaCompletedZeroSideL1DualPairing b
                    (zetaCompletedZeroSideCoordinateL1LinearMap
                      hbranch hpartialOneTwo hcompactOneTwo hfinite
                      hpartialLeft hcompactBoundary f) :=
              hb
                (zetaCompletedZeroSideCoordinateL1LinearMap
                  hbranch hpartialOneTwo hcompactOneTwo hfinite
                  hpartialLeft hcompactBoundary f)
            let hpairing :
                zetaCompletedZeroSideL1DualPairing b
                    (zetaCompletedZeroSideCoordinateL1LinearMap
                      hbranch hpartialOneTwo hcompactOneTwo hfinite
                      hpartialLeft hcompactBoundary f) =
                  zetaCompletedZeroSideAnnihilator
                    b hbranch hpartialOneTwo hcompactOneTwo hfinite
                    hpartialLeft hcompactBoundary f :=
              Eq.refl
                (zetaCompletedZeroSideAnnihilator
                  b hbranch hpartialOneTwo hcompactOneTwo hfinite
                  hpartialLeft hcompactBoundary f)
            hrepresents.trans (hdual.trans hpairing)
          ⟨b, hvanishes, hrepresentation⟩

/-- Direct diagonal-debt trace reconstruction as a bounded completed-zero
annihilator, with the off-diagonal/positive-coordinate comparison explicit. -/
theorem exists_diagonalDebtCoordinateResidual_boundedAnnihilator_of_offDiagonal_eq_positiveCoordinate_source
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
    (hoffPositive :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f) :
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
  match
    exists_diagonalDebtCoordinateResidual_vanishingCoordinateFunctional_of_offDiagonal_eq_positiveCoordinate_source
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
      hcompactBoundary f D hmajorant hoffPositive
  with
  | ⟨L, hLvanishes, hrepresents⟩ =>
      match exists_zetaCompletedZeroSideL1DualRepresentation L with
      | ⟨b, hb⟩ =>
          let hvanishes :
              ZetaCompletedZeroSideAnnihilatorVanishes
                b hbranch hpartialOneTwo hcompactOneTwo hfinite
                hpartialLeft hcompactBoundary :=
            fun g : ZetaAdmissibleFunction =>
              let hpairing :
                  zetaCompletedZeroSideAnnihilator
                      b hbranch hpartialOneTwo hcompactOneTwo hfinite
                      hpartialLeft hcompactBoundary g =
                    zetaCompletedZeroSideL1DualPairing b
                      (zetaCompletedZeroSideCoordinateL1LinearMap
                        hbranch hpartialOneTwo hcompactOneTwo hfinite
                        hpartialLeft hcompactBoundary g) :=
                Eq.refl
                  (zetaCompletedZeroSideAnnihilator
                    b hbranch hpartialOneTwo hcompactOneTwo hfinite
                    hpartialLeft hcompactBoundary g)
              let hdual :
                  zetaCompletedZeroSideL1DualPairing b
                      (zetaCompletedZeroSideCoordinateL1LinearMap
                        hbranch hpartialOneTwo hcompactOneTwo hfinite
                        hpartialLeft hcompactBoundary g) =
                    L
                      (zetaCompletedZeroSideCoordinateL1LinearMap
                        hbranch hpartialOneTwo hcompactOneTwo hfinite
                        hpartialLeft hcompactBoundary g) :=
                (hb
                  (zetaCompletedZeroSideCoordinateL1LinearMap
                    hbranch hpartialOneTwo hcompactOneTwo hfinite
                    hpartialLeft hcompactBoundary g)).symm
              hpairing.trans (hdual.trans (hLvanishes g))
          let hrepresentation :
              ((Complex.re
                  (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
                ℂ) =
                zetaCompletedZeroSideAnnihilator
                  b hbranch hpartialOneTwo hcompactOneTwo hfinite
                  hpartialLeft hcompactBoundary f :=
            let hdual :
                L
                    (zetaCompletedZeroSideCoordinateL1LinearMap
                      hbranch hpartialOneTwo hcompactOneTwo hfinite
                      hpartialLeft hcompactBoundary f) =
                  zetaCompletedZeroSideL1DualPairing b
                    (zetaCompletedZeroSideCoordinateL1LinearMap
                      hbranch hpartialOneTwo hcompactOneTwo hfinite
                      hpartialLeft hcompactBoundary f) :=
              hb
                (zetaCompletedZeroSideCoordinateL1LinearMap
                  hbranch hpartialOneTwo hcompactOneTwo hfinite
                  hpartialLeft hcompactBoundary f)
            let hpairing :
                zetaCompletedZeroSideL1DualPairing b
                    (zetaCompletedZeroSideCoordinateL1LinearMap
                      hbranch hpartialOneTwo hcompactOneTwo hfinite
                      hpartialLeft hcompactBoundary f) =
                  zetaCompletedZeroSideAnnihilator
                    b hbranch hpartialOneTwo hcompactOneTwo hfinite
                    hpartialLeft hcompactBoundary f :=
              Eq.refl
                (zetaCompletedZeroSideAnnihilator
                  b hbranch hpartialOneTwo hcompactOneTwo hfinite
                  hpartialLeft hcompactBoundary f)
            hrepresents.trans (hdual.trans hpairing)
          ⟨b, hvanishes, hrepresentation⟩
end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
