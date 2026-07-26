import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointFiniteBesselParts.PositiveTraceMatrix
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointFiniteBesselParts.PrimeOffDiagonalWindow

/-!
# Endpoint finite renormalized trace exhaustion

This file owns the finite trace/GNS reconstruction theorem for the endpoint
fiber in the renormalized positive boundary windows.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- A finite physical trace-kernel split for the endpoint fiber. -/
def CompletedEndpointFinitePhysicalTraceKernelSplit
    (N : ℕ) (f : ZetaAdmissibleFunction) : Prop :=
  ∃ kernelRemainder : ℝ,
    finitePositiveRenormalizedBoundaryWindow N f =
      (completedWeilEndpointTraceFiber f).gram + kernelRemainder ∧
    0 ≤ kernelRemainder ∧
    completedEndpointPhysicalHiddenKernelWindow N f = kernelRemainder

/-- A finite physical trace-kernel split gives nonnegativity of the finite
physical hidden-kernel window. -/
theorem completedEndpointPhysicalHiddenKernelWindow_nonnegative_of_finiteTraceKernelSplit
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hsplit : CompletedEndpointFinitePhysicalTraceKernelSplit N f) :
    0 ≤ completedEndpointPhysicalHiddenKernelWindow N f :=
  match hsplit with
  | ⟨kernelRemainder, hrest⟩ =>
      let hnonnegative : 0 ≤ kernelRemainder :=
        hrest.right.left
      let hkernel :
          completedEndpointPhysicalHiddenKernelWindow N f =
            kernelRemainder :=
        hrest.right.right
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        hkernel.symm
        hnonnegative

/-- A nonnegative finite physical hidden-kernel window gives the finite
physical trace-kernel split. -/
theorem completedEndpointFinitePhysicalTraceKernelSplit_of_hiddenKernelWindow_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hkernel : 0 ≤ completedEndpointPhysicalHiddenKernelWindow N f) :
    CompletedEndpointFinitePhysicalTraceKernelSplit N f :=
  let kernelRemainder : ℝ := completedEndpointPhysicalHiddenKernelWindow N f
  let hboundary :
      finitePositiveRenormalizedBoundaryWindow N f =
        (completedWeilEndpointTraceFiber f).gram + kernelRemainder :=
    endpointTraceDebt_add_sub_cancel
      (finitePositiveRenormalizedBoundaryWindow N f)
      ((completedWeilEndpointTraceFiber f).gram)
  let hnonnegative : 0 ≤ kernelRemainder := hkernel
  let hkernelEq :
      completedEndpointPhysicalHiddenKernelWindow N f = kernelRemainder :=
    Eq.refl kernelRemainder
  Exists.intro kernelRemainder
    (And.intro hboundary
      (And.intro hnonnegative hkernelEq))

/-- The finite residual left after removing the visible endpoint Gram from a
renormalized positive boundary window. -/
noncomputable def completedEndpointFiniteRenormalizedTraceResidualWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePositiveRenormalizedBoundaryWindow N f -
    (completedWeilEndpointTraceFiber f).gram

/-- The finite renormalized endpoint residual unfolds to boundary window minus
endpoint Gram. -/
theorem completedEndpointFiniteRenormalizedTraceResidualWindow_eq
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedEndpointFiniteRenormalizedTraceResidualWindow N f =
      finitePositiveRenormalizedBoundaryWindow N f -
        (completedWeilEndpointTraceFiber f).gram :=
  Eq.refl (completedEndpointFiniteRenormalizedTraceResidualWindow N f)

/-- The finite renormalized endpoint residual is the finite physical hidden
endpoint-kernel window. -/
theorem completedEndpointFiniteRenormalizedTraceResidualWindow_eq_physicalHiddenKernelWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedEndpointFiniteRenormalizedTraceResidualWindow N f =
      completedEndpointPhysicalHiddenKernelWindow N f :=
  Eq.refl (completedEndpointFiniteRenormalizedTraceResidualWindow N f)

/-- Nonnegativity of the finite renormalized endpoint residual gives endpoint
Gram domination by the finite renormalized boundary window. -/
theorem endpointGram_le_finitePositiveRenormalizedBoundaryWindow_of_residual_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hresidual :
      0 ≤ completedEndpointFiniteRenormalizedTraceResidualWindow N f) :
    (completedWeilEndpointTraceFiber f).gram ≤
      finitePositiveRenormalizedBoundaryWindow N f :=
  let hsub :
      0 ≤
        finitePositiveRenormalizedBoundaryWindow N f -
          (completedWeilEndpointTraceFiber f).gram :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedEndpointFiniteRenormalizedTraceResidualWindow_eq N f)
      hresidual
  sub_nonneg.mp hsub

/-- Endpoint Gram domination by the finite renormalized boundary window gives
nonnegativity of the finite renormalized endpoint residual. -/
theorem completedEndpointFiniteRenormalizedTraceResidualWindow_nonnegative_of_endpointGram_le
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hbound :
      (completedWeilEndpointTraceFiber f).gram ≤
        finitePositiveRenormalizedBoundaryWindow N f) :
    0 ≤ completedEndpointFiniteRenormalizedTraceResidualWindow N f :=
  let hsub :
      0 ≤
        finitePositiveRenormalizedBoundaryWindow N f -
          (completedWeilEndpointTraceFiber f).gram :=
    sub_nonneg.mpr hbound
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
      (completedEndpointFiniteRenormalizedTraceResidualWindow_eq N f).symm
    hsub

/-- The finite renormalized boundary window is the finite prime off-diagonal
channel plus the non-prime archimedean/correction channel. -/
theorem finitePositiveRenormalizedBoundaryWindow_eq_primeOffDiagonal_add_archCorrection
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePositiveRenormalizedBoundaryWindow N f =
      zetaPrimeOffDiagonalChannel N f +
        zetaArchimedeanCorrectionAutocorrelationChannel f :=
  let hfinite :
      finitePositiveRenormalizedBoundaryWindow N f =
        finitePartBoundaryWindow N f :=
    finitePositiveRenormalizedBoundaryWindow_eq_finitePartBoundaryWindow
      N f
  let P : ℝ := zetaPrimeOffDiagonalChannel N f
  let D : ℝ := zetaPrimeDiagonalDebt N f
  let A : ℝ := zetaArchimedeanCorrectionAutocorrelationChannel f
  let hfiniteNormal :
      finitePartBoundaryWindow N f = P + D + -D + A :=
    Eq.refl (finitePartBoundaryWindow N f)
  let hcancel : D + -D = 0 :=
    add_neg_cancel D
  let hassoc :
        P + D + -D + A = P + (D + -D) + A :=
      congrArg (fun value : ℝ => value + A)
        (add_assoc P D (-D))
  let hzero :
        P + (D + -D) + A = P + 0 + A :=
      congrArg (fun value : ℝ => P + value + A) hcancel
  let haddZero :
        P + 0 + A = P + A :=
      congrArg (fun value : ℝ => value + A) (add_zero P)
  let hnormal :
      P + D + -D + A = P + A :=
    hassoc.trans (hzero.trans haddZero)
  hfinite.trans (hfiniteNormal.trans hnormal)

/-- The non-prime endpoint residual left after removing the endpoint trace Gram
from the archimedean/correction channel. -/
noncomputable def completedEndpointNonPrimeTraceResidual
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaArchimedeanCorrectionAutocorrelationChannel f -
    (completedWeilEndpointTraceFiber f).gram

/-- The non-prime endpoint residual unfolds to archimedean/correction minus the
endpoint trace Gram. -/
theorem completedEndpointNonPrimeTraceResidual_eq_archCorrection_sub_endpointGram
    (f : ZetaAdmissibleFunction) :
    completedEndpointNonPrimeTraceResidual f =
      zetaArchimedeanCorrectionAutocorrelationChannel f -
        (completedWeilEndpointTraceFiber f).gram :=
  Eq.refl (completedEndpointNonPrimeTraceResidual f)

/-- The archimedean autocorrelation square is the centered archimedean
Hermitian packet Gram. -/
theorem zetaArchimedeanAutocorrelationSquareEnergy_eq_archimedeanPacketGram
    (f : ZetaAdmissibleFunction) :
    zetaArchimedeanAutocorrelationSquareEnergy f =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) :=
  let phi : ℂ := zetaCompletedExplicitFormulaPhi f 0
  let amp : ℂ := zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f
  let hpaired :
      amp * star amp = (2 : ℂ) * (phi * star phi) :=
    zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution_eq_weightedPaired_owner
      f
  let hreal :
      Complex.re (amp * star amp) =
        Complex.re ((2 : ℂ) * (phi * star phi)) :=
    congrArg Complex.re hpaired
  let hcoordinate :
      ZetaHermitianPacketEnsemble.coordinateGram amp =
        Complex.re (amp * star amp) :=
    (complex_re_mul_star_self_eq_normSq_hermitianPacket amp).symm
  let hsquare :
      Complex.re ((2 : ℂ) * (phi * star phi)) =
        zetaArchimedeanAutocorrelationSquareEnergy f :=
    complex_two_mul_conjSquare_re phi
  let hcentered :
      ZetaHermitianPacketEnsemble.coordinateGram amp =
        zetaArchimedeanAutocorrelationSquareEnergy f :=
    hcoordinate.trans (hreal.trans hsquare)
  let hpacket :
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) =
        ZetaHermitianPacketEnsemble.coordinateGram amp :=
    zetaCompletedHermitianBoundaryDefect_archimedeanPacketGram_eq_centeredAmplitudeGram
      f
  hcentered.symm.trans hpacket.symm

/-- The non-prime autocorrelation channel is the sum of the two non-prime
Hermitian packet Grams. -/
theorem zetaArchimedeanCorrectionAutocorrelationChannel_eq_arch_add_correctionPacketGram
    (f : ZetaAdmissibleFunction) :
    zetaArchimedeanCorrectionAutocorrelationChannel f =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
  let hchannel :
      zetaArchimedeanCorrectionAutocorrelationChannel f =
        zetaArchimedeanCorrectionAutocorrelationSquareEnergy f :=
    zetaArchimedeanCorrectionAutocorrelationChannel_eq_squareEnergy f
  let harch :
      zetaArchimedeanAutocorrelationSquareEnergy f =
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
    zetaArchimedeanAutocorrelationSquareEnergy_eq_archimedeanPacketGram f
  let hcorrection :
      zetaCorrectionAutocorrelationSquareEnergy f =
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
    Eq.refl (zetaCorrectionAutocorrelationSquareEnergy f)
  let hsum :
      zetaArchimedeanCorrectionAutocorrelationSquareEnergy f =
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    Eq.trans
      (Eq.refl (zetaArchimedeanCorrectionAutocorrelationSquareEnergy f))
      (congrArg₂ HAdd.hAdd harch hcorrection)
  hchannel.trans hsum

/-- The non-prime autocorrelation residual is the canonical packet
archimedean/correction endpoint remainder. -/
theorem completedEndpointNonPrimeTraceResidual_eq_archCorrectionRemainder
    (f : ZetaAdmissibleFunction) :
    completedEndpointNonPrimeTraceResidual f =
      completedEndpointFiberArchCorrectionRemainder f :=
  let A : ℝ := zetaArchimedeanCorrectionAutocorrelationChannel f
  let P : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) +
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f)
  let E : ℝ := (completedWeilEndpointTraceFiber f).gram
  let hleft :
      completedEndpointNonPrimeTraceResidual f = A - E :=
    completedEndpointNonPrimeTraceResidual_eq_archCorrection_sub_endpointGram f
  let hchannel : A = P :=
    zetaArchimedeanCorrectionAutocorrelationChannel_eq_arch_add_correctionPacketGram
      f
  let hmiddle : A - E = P - E :=
    congrArg (fun value : ℝ => value - E) hchannel
  let hright :
      completedEndpointFiberArchCorrectionRemainder f = P - E :=
    completedEndpointFiberArchCorrectionRemainder_eq_arch_add_correction_sub_endpointFiberGram
      f
  hleft.trans (hmiddle.trans hright.symm)

/-- The non-prime carrier-separation target for endpoint trace exhaustion:
after the endpoint carrier is removed from the non-prime autocorrelation
channel, the residual is nonnegative. -/
def CompletedEndpointNonPrimeTraceResidualNonnegative
    (f : ZetaAdmissibleFunction) : Prop :=
  0 ≤ completedEndpointNonPrimeTraceResidual f

/-- The non-prime carrier-separation target unfolds to scalar
nonnegativity. -/
theorem completedEndpointNonPrimeTraceResidualNonnegative_iff
    (f : ZetaAdmissibleFunction) :
    CompletedEndpointNonPrimeTraceResidualNonnegative f ↔
      0 ≤ completedEndpointNonPrimeTraceResidual f :=
  Iff.intro
    (fun h => h)
    (fun h => h)

/-- Nonnegativity of the archimedean/correction endpoint remainder transports
to nonnegativity of the non-prime endpoint residual. -/
theorem completedEndpointNonPrimeTraceResidual_nonnegative_of_archCorrectionRemainder_nonnegative
    (f : ZetaAdmissibleFunction)
    (harchCorrection :
      0 ≤ completedEndpointFiberArchCorrectionRemainder f) :
    0 ≤ completedEndpointNonPrimeTraceResidual f :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedEndpointNonPrimeTraceResidual_eq_archCorrectionRemainder f).symm
    harchCorrection

/-- Named predicate form of non-prime residual nonnegativity transported from
the archimedean/correction endpoint remainder. -/
theorem completedEndpointNonPrimeTraceResidualNonnegative_of_archCorrectionRemainder_nonnegative
    (f : ZetaAdmissibleFunction)
    (harchCorrection :
      0 ≤ completedEndpointFiberArchCorrectionRemainder f) :
    CompletedEndpointNonPrimeTraceResidualNonnegative f :=
  (completedEndpointNonPrimeTraceResidualNonnegative_iff f).mpr
    (completedEndpointNonPrimeTraceResidual_nonnegative_of_archCorrectionRemainder_nonnegative
      f harchCorrection)

/-- The finite renormalized endpoint residual is the finite prime
off-diagonal channel plus the non-prime endpoint residual. -/
theorem completedEndpointFiniteRenormalizedTraceResidualWindow_eq_primeOffDiagonal_add_nonPrimeResidual
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedEndpointFiniteRenormalizedTraceResidualWindow N f =
      zetaPrimeOffDiagonalChannel N f +
        completedEndpointNonPrimeTraceResidual f :=
  let P : ℝ := zetaPrimeOffDiagonalChannel N f
  let A : ℝ := zetaArchimedeanCorrectionAutocorrelationChannel f
  let E : ℝ := (completedWeilEndpointTraceFiber f).gram
  let hwindow :
      finitePositiveRenormalizedBoundaryWindow N f = P + A :=
    finitePositiveRenormalizedBoundaryWindow_eq_primeOffDiagonal_add_archCorrection
      N f
  let hresidual :
      completedEndpointNonPrimeTraceResidual f = A - E :=
    completedEndpointNonPrimeTraceResidual_eq_archCorrection_sub_endpointGram f
  let hraw :
      completedEndpointFiniteRenormalizedTraceResidualWindow N f =
        finitePositiveRenormalizedBoundaryWindow N f - E :=
    completedEndpointFiniteRenormalizedTraceResidualWindow_eq N f
  let hfiniteResidual :
      completedEndpointFiniteRenormalizedTraceResidualWindow N f =
        (P + A) - E :=
    Eq.trans
      hraw
      (congrArg (fun value : ℝ => value - E) hwindow)
  let hsub :
        (P + A) - E = (P + A) + -E :=
      sub_eq_add_neg (P + A) E
  let hassoc :
        (P + A) + -E = P + (A + -E) :=
      add_assoc P A (-E)
  let hsubInner :
        P + (A + -E) = P + (A - E) :=
      congrArg (fun value : ℝ => P + value)
        (sub_eq_add_neg A E).symm
  let hregroup :
      (P + A) - E = P + (A - E) :=
    hsub.trans (hassoc.trans hsubInner)
  hfiniteResidual.trans
    (hregroup.trans
      (congrArg (fun value : ℝ => P + value) hresidual.symm))

/-- A vanished finite prime off-diagonal window and nonnegative non-prime
residual give nonnegativity of the finite renormalized endpoint residual. -/
theorem completedEndpointFiniteRenormalizedTraceResidualWindow_nonnegative_of_primeOffDiagonal_zero
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hoffDiagonal : zetaPrimeOffDiagonalChannel N f = 0)
    (hnonPrime : 0 ≤ completedEndpointNonPrimeTraceResidual f) :
    0 ≤ completedEndpointFiniteRenormalizedTraceResidualWindow N f :=
  let hsplit :
      completedEndpointFiniteRenormalizedTraceResidualWindow N f =
        zetaPrimeOffDiagonalChannel N f +
          completedEndpointNonPrimeTraceResidual f :=
    completedEndpointFiniteRenormalizedTraceResidualWindow_eq_primeOffDiagonal_add_nonPrimeResidual
      N f
  let hzeroSplit :
      zetaPrimeOffDiagonalChannel N f +
          completedEndpointNonPrimeTraceResidual f =
        0 + completedEndpointNonPrimeTraceResidual f :=
    congrArg
      (fun value : ℝ => value + completedEndpointNonPrimeTraceResidual f)
      hoffDiagonal
  let hcollapse :
      0 + completedEndpointNonPrimeTraceResidual f =
        completedEndpointNonPrimeTraceResidual f :=
    zero_add (completedEndpointNonPrimeTraceResidual f)
  let hresidual :
      completedEndpointFiniteRenormalizedTraceResidualWindow N f =
        completedEndpointNonPrimeTraceResidual f :=
    hsplit.trans (hzeroSplit.trans hcollapse)
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    hresidual.symm
    hnonPrime

/-- Finite renormalized endpoint trace compression: eventually the finite
renormalized positive boundary window dominates the visible endpoint Gram. -/
def CompletedEndpointFiniteRenormalizedTraceExhaustion
    (f : ZetaAdmissibleFunction) : Prop :=
  ∀ᶠ N in atTop,
    (completedWeilEndpointTraceFiber f).gram ≤
      finitePositiveRenormalizedBoundaryWindow N f

/-- The finite renormalized trace-exhaustion predicate unfolds to the endpoint
Gram domination statement. -/
theorem completedEndpointFiniteRenormalizedTraceExhaustion_iff_endpointGram_eventually_le
    (f : ZetaAdmissibleFunction) :
    CompletedEndpointFiniteRenormalizedTraceExhaustion f ↔
      ∀ᶠ N in atTop,
        (completedWeilEndpointTraceFiber f).gram ≤
          finitePositiveRenormalizedBoundaryWindow N f :=
  Iff.intro
    (fun h => h)
    (fun h => h)

/-- Source finite renormalized endpoint residual nonnegativity. -/
theorem completedEndpointFiniteRenormalizedTraceResidualWindow_eventually_nonnegative_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    ∀ᶠ N in atTop,
      0 ≤ completedEndpointFiniteRenormalizedTraceResidualWindow N f :=
  let hnonPrimeScalar :
      0 ≤ completedEndpointNonPrimeTraceResidual f :=
    (completedEndpointNonPrimeTraceResidualNonnegative_iff f).mp hnonPrime
  (zetaPrimeOffDiagonalChannel_eventually_eq_zero_source f D).mono
    (fun N hN =>
      completedEndpointFiniteRenormalizedTraceResidualWindow_nonnegative_of_primeOffDiagonal_zero
        N f hN hnonPrimeScalar)

/-- Source finite physical hidden-kernel window nonnegativity.

This is the finite trace/GNS reconstruction theorem: after the cutoff has
captured the endpoint reconstruction vector, the renormalized finite boundary
trace has nonnegative hidden kernel after the visible endpoint Gram is removed. -/
theorem completedEndpointPhysicalHiddenKernelWindow_eventually_nonnegative_traceExhaustion_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    ∀ᶠ N in atTop,
      0 ≤ completedEndpointPhysicalHiddenKernelWindow N f :=
  (completedEndpointFiniteRenormalizedTraceResidualWindow_eventually_nonnegative_source
    f D hnonPrime).mono
    (fun N hN =>
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        (completedEndpointFiniteRenormalizedTraceResidualWindow_eq_physicalHiddenKernelWindow
          N f)
        hN)

/-- Source finite physical trace-kernel split. -/
theorem completedEndpointFinitePhysicalTraceKernelSplit_eventually_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    ∀ᶠ N in atTop,
      CompletedEndpointFinitePhysicalTraceKernelSplit N f :=
  (completedEndpointPhysicalHiddenKernelWindow_eventually_nonnegative_traceExhaustion_source
    f D hnonPrime).mono
    (fun N hN =>
      completedEndpointFinitePhysicalTraceKernelSplit_of_hiddenKernelWindow_nonnegative
        N f hN)

/-- Source finite renormalized endpoint trace compression. -/
theorem completedEndpointFiniteRenormalizedTraceExhaustion_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    CompletedEndpointFiniteRenormalizedTraceExhaustion f :=
  (completedEndpointFiniteRenormalizedTraceResidualWindow_eventually_nonnegative_source
    f D hnonPrime).mono
    (fun N hN =>
      endpointGram_le_finitePositiveRenormalizedBoundaryWindow_of_residual_nonnegative
        N f hN)

/-- Source finite renormalized endpoint trace compression in unfolded form. -/
theorem completedEndpointFiniteRenormalizedBoundaryWindow_endpointGram_eventually_le_traceExhaustion_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    ∀ᶠ N in atTop,
      (completedWeilEndpointTraceFiber f).gram ≤
        finitePositiveRenormalizedBoundaryWindow N f :=
  (completedEndpointFiniteRenormalizedTraceExhaustion_iff_endpointGram_eventually_le
    f).mp
    (completedEndpointFiniteRenormalizedTraceExhaustion_source f D hnonPrime)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
