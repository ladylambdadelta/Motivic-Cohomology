import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.OwnerParts.Part07
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.EndpointTraceReconstruction

/-!
# Endpoint trace compression

This file connects the concrete endpoint fiber to the positive completed GNS
presentation and records the scalar remainders used by the endpoint trace
domination owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The endpoint trace fiber of an arbitrary completed Hilbert source. -/
noncomputable def completedBoundaryHilbertSourceEndpointTraceFiber
    (X : CompletedBoundaryHilbertSource) :
    CompletedWeilEndpointTraceFiber :=
  { negativeFiber :=
      zetaCompletedExplicitFormulaPhi X.seed (-(1 / 2 : ℂ))
    positiveFiber :=
      zetaCompletedExplicitFormulaPhi X.seed (1 / 2 : ℂ) }

/-- The Hilbert-source endpoint trace fiber of a canonical source is the
seed endpoint trace fiber. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_source_eq
    (f : ZetaAdmissibleFunction) :
    completedBoundaryHilbertSourceEndpointTraceFiber
        (completedBoundaryHilbertSource f) =
      completedWeilEndpointTraceFiber f :=
  Eq.refl
    (completedBoundaryHilbertSourceEndpointTraceFiber
      (completedBoundaryHilbertSource f))

/-- The Hilbert-source endpoint trace Gram of a canonical source is the seed
endpoint trace Gram. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_source_gram_eq
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryHilbertSourceEndpointTraceFiber
        (completedBoundaryHilbertSource f)).gram =
      (completedWeilEndpointTraceFiber f).gram :=
  congrArg CompletedWeilEndpointTraceFiber.gram
    (completedBoundaryHilbertSourceEndpointTraceFiber_source_eq f)

/-- The endpoint trace fiber of a Hilbert source has nonnegative Gram. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_gram_nonnegative
    (X : CompletedBoundaryHilbertSource) :
    0 ≤ (completedBoundaryHilbertSourceEndpointTraceFiber X).gram :=
  (completedBoundaryHilbertSourceEndpointTraceFiber X).gram_nonnegative

/-- The ordered-heart endpoint trace-compression remainder of a completed
Hilbert source. -/
noncomputable def completedBoundaryHilbertSourceEndpointCompressionRemainder
    (X : CompletedBoundaryHilbertSource) : ℝ :=
  completedOrderedHeartScalar X -
    (completedBoundaryHilbertSourceEndpointTraceFiber X).gram

/-- The ordered-heart endpoint compression remainder unfolds to the positive
ordered-heart scalar minus the endpoint trace Gram. -/
theorem completedBoundaryHilbertSourceEndpointCompressionRemainder_eq_orderedHeart_sub_endpointGram
    (X : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertSourceEndpointCompressionRemainder X =
      completedOrderedHeartScalar X -
        (completedBoundaryHilbertSourceEndpointTraceFiber X).gram :=
  Eq.refl (completedBoundaryHilbertSourceEndpointCompressionRemainder X)

/-- Nonnegativity of the Hilbert-source endpoint compression remainder is
exactly domination of the endpoint trace Gram by the ordered-heart scalar. -/
theorem completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_iff_endpointGram_le_orderedHeart
    (X : CompletedBoundaryHilbertSource) :
    0 ≤ completedBoundaryHilbertSourceEndpointCompressionRemainder X ↔
      (completedBoundaryHilbertSourceEndpointTraceFiber X).gram ≤
        completedOrderedHeartScalar X :=
  Iff.intro
    (fun hcompression =>
      let hsub :
        0 ≤
          completedOrderedHeartScalar X -
            (completedBoundaryHilbertSourceEndpointTraceFiber X).gram :=
        Eq.subst
          (motive := fun value : ℝ => 0 ≤ value)
          (completedBoundaryHilbertSourceEndpointCompressionRemainder_eq_orderedHeart_sub_endpointGram
            X)
          hcompression
      sub_nonneg.mp hsub)
    (fun hdomination =>
      let hsub :
        0 ≤
          completedOrderedHeartScalar X -
            (completedBoundaryHilbertSourceEndpointTraceFiber X).gram :=
        sub_nonneg.mpr hdomination
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        (completedBoundaryHilbertSourceEndpointCompressionRemainder_eq_orderedHeart_sub_endpointGram
          X).symm
        hsub)

/-- Endpoint trace Gram domination by the ordered-heart scalar gives
nonnegativity of the Hilbert-source endpoint compression remainder. -/
theorem completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_of_endpointGram_le_orderedHeart
    (X : CompletedBoundaryHilbertSource)
    (hdomination :
      (completedBoundaryHilbertSourceEndpointTraceFiber X).gram ≤
        completedOrderedHeartScalar X) :
    0 ≤ completedBoundaryHilbertSourceEndpointCompressionRemainder X :=
  (completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_iff_endpointGram_le_orderedHeart
    X).mpr hdomination

/-- Nonnegativity of the Hilbert-source endpoint compression remainder gives
endpoint trace Gram domination by the ordered-heart scalar. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_orderedHeart_of_compressionRemainder_nonnegative
    (X : CompletedBoundaryHilbertSource)
    (hcompression :
      0 ≤ completedBoundaryHilbertSourceEndpointCompressionRemainder X) :
    (completedBoundaryHilbertSourceEndpointTraceFiber X).gram ≤
      completedOrderedHeartScalar X :=
  (completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_iff_endpointGram_le_orderedHeart
    X).mp hcompression

/-- The endpoint-kernel split statement for a completed Hilbert source:
the ordered-heart scalar is the finite endpoint trace Gram plus a nonnegative
kernel remainder. -/
def completedBoundaryHilbertSourceEndpointKernelSplit
    (X : CompletedBoundaryHilbertSource) : Prop :=
  ∃ kernelRemainder : ℝ,
    completedOrderedHeartScalar X =
      (completedBoundaryHilbertSourceEndpointTraceFiber X).gram +
        kernelRemainder ∧
    0 ≤ kernelRemainder

/-- If the ordered-heart scalar splits as endpoint trace Gram plus a
nonnegative kernel remainder, then the endpoint trace Gram is dominated by
the ordered-heart scalar. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_orderedHeart_of_endpointKernelSplit
    (X : CompletedBoundaryHilbertSource)
    (kernelRemainder : ℝ)
    (hordered :
      completedOrderedHeartScalar X =
        (completedBoundaryHilbertSourceEndpointTraceFiber X).gram +
          kernelRemainder)
    (hkernel : 0 ≤ kernelRemainder) :
    (completedBoundaryHilbertSourceEndpointTraceFiber X).gram ≤
      completedOrderedHeartScalar X :=
  let hsum :
      (completedBoundaryHilbertSourceEndpointTraceFiber X).gram ≤
        (completedBoundaryHilbertSourceEndpointTraceFiber X).gram +
          kernelRemainder :=
    le_add_of_nonneg_right hkernel
  Eq.subst
    (motive := fun value : ℝ =>
      (completedBoundaryHilbertSourceEndpointTraceFiber X).gram ≤ value)
    hordered.symm
    hsum

/-- An endpoint-kernel split gives nonnegativity of the Hilbert-source
endpoint compression remainder. -/
theorem completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_of_endpointKernelSplit
    (X : CompletedBoundaryHilbertSource)
    (kernelRemainder : ℝ)
    (hordered :
      completedOrderedHeartScalar X =
        (completedBoundaryHilbertSourceEndpointTraceFiber X).gram +
          kernelRemainder)
    (hkernel : 0 ≤ kernelRemainder) :
    0 ≤ completedBoundaryHilbertSourceEndpointCompressionRemainder X :=
  completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_of_endpointGram_le_orderedHeart
    X
    (completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_orderedHeart_of_endpointKernelSplit
      X kernelRemainder hordered hkernel)

/-- A named endpoint-kernel split gives domination of the endpoint trace Gram
by the ordered-heart scalar. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_orderedHeart_of_endpointKernelSplitProp
    (X : CompletedBoundaryHilbertSource)
    (hsplit : completedBoundaryHilbertSourceEndpointKernelSplit X) :
    (completedBoundaryHilbertSourceEndpointTraceFiber X).gram ≤
      completedOrderedHeartScalar X :=
  Exists.elim hsplit
    (fun kernelRemainder splitSpec =>
      completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_orderedHeart_of_endpointKernelSplit
        X kernelRemainder splitSpec.1 splitSpec.2)

/-- A named endpoint-kernel split gives nonnegativity of the Hilbert-source
endpoint compression remainder. -/
theorem completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_of_endpointKernelSplitProp
    (X : CompletedBoundaryHilbertSource)
    (hsplit : completedBoundaryHilbertSourceEndpointKernelSplit X) :
    0 ≤ completedBoundaryHilbertSourceEndpointCompressionRemainder X :=
  completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_of_endpointGram_le_orderedHeart
    X
    (completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_orderedHeart_of_endpointKernelSplitProp
      X hsplit)

/-- The positive-presentation remainder after removing the finite endpoint
fiber.  This is the Hilbert/GNS compression scalar used by endpoint trace
domination. -/
noncomputable def completedEndpointFiberPositivePresentationRemainder
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedGNSPositiveBoundaryPresentationScalar f -
    (completedWeilEndpointTraceFiber f).gram

/-- The archimedean/correction residual after removing the endpoint fiber
from the non-prime positive packet coordinates. -/
noncomputable def completedEndpointFiberArchCorrectionRemainder
    (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) +
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) -
    (completedWeilEndpointTraceFiber f).gram

/-- The positive-presentation compression remainder unfolds to the positive
GNS presentation minus the endpoint fiber Gram. -/
theorem completedEndpointFiberPositivePresentationRemainder_eq_positive_sub_endpointFiberGram
    (f : ZetaAdmissibleFunction) :
    completedEndpointFiberPositivePresentationRemainder f =
      zetaCompletedGNSPositiveBoundaryPresentationScalar f -
        (completedWeilEndpointTraceFiber f).gram :=
  Eq.refl (completedEndpointFiberPositivePresentationRemainder f)

/-- The seed-level positive presentation compression remainder is the
Hilbert-source endpoint compression remainder of the canonical source. -/
theorem completedEndpointFiberPositivePresentationRemainder_eq_sourceEndpointCompressionRemainder
    (f : ZetaAdmissibleFunction) :
    completedEndpointFiberPositivePresentationRemainder f =
      completedBoundaryHilbertSourceEndpointCompressionRemainder
        (completedBoundaryHilbertSource f) :=
  let ordered : ℝ :=
    completedOrderedHeartScalar (completedBoundaryHilbertSource f)
  let positive : ℝ :=
    zetaCompletedGNSPositiveBoundaryPresentationScalar f
  let sourceGram : ℝ :=
    (completedBoundaryHilbertSourceEndpointTraceFiber
      (completedBoundaryHilbertSource f)).gram
  let seedGram : ℝ := (completedWeilEndpointTraceFiber f).gram
  let hpositive : positive = ordered :=
    (completedBoundaryHermitianGNSScalar_source_eq_positivePresentationScalar
      f).symm
  let hgram : sourceGram = seedGram :=
    completedBoundaryHilbertSourceEndpointTraceFiber_source_gram_eq f
  let hfirst :
      completedEndpointFiberPositivePresentationRemainder f =
        positive - seedGram :=
    completedEndpointFiberPositivePresentationRemainder_eq_positive_sub_endpointFiberGram
      f
  let hsecond :
      positive - seedGram = ordered - seedGram :=
    congrArg (fun value : ℝ => value - seedGram) hpositive
  let hthird :
      ordered - seedGram = ordered - sourceGram :=
    congrArg (fun value : ℝ => ordered - value) hgram.symm
  let hfourth :
      ordered - sourceGram =
        completedBoundaryHilbertSourceEndpointCompressionRemainder
          (completedBoundaryHilbertSource f) :=
    (completedBoundaryHilbertSourceEndpointCompressionRemainder_eq_orderedHeart_sub_endpointGram
      (completedBoundaryHilbertSource f)).symm
  hfirst.trans (hsecond.trans (hthird.trans hfourth))

/-- Nonnegativity of the canonical Hilbert-source endpoint compression
remainder is exactly nonnegativity of the seed positive-presentation
compression remainder. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_iff_sourceEndpointCompressionRemainder
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedEndpointFiberPositivePresentationRemainder f ↔
      0 ≤
        completedBoundaryHilbertSourceEndpointCompressionRemainder
          (completedBoundaryHilbertSource f) :=
  Iff.intro
    (fun hseed =>
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        (completedEndpointFiberPositivePresentationRemainder_eq_sourceEndpointCompressionRemainder
          f)
        hseed)
    (fun hsource =>
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        (completedEndpointFiberPositivePresentationRemainder_eq_sourceEndpointCompressionRemainder
          f).symm
        hsource)

/-- Canonical Hilbert-source endpoint compression nonnegativity gives
seed-level positive-presentation compression nonnegativity. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_of_sourceEndpointCompressionRemainder
    (f : ZetaAdmissibleFunction)
    (hsource :
      0 ≤
        completedBoundaryHilbertSourceEndpointCompressionRemainder
          (completedBoundaryHilbertSource f)) :
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  (completedEndpointFiberPositivePresentationRemainder_nonnegative_iff_sourceEndpointCompressionRemainder
    f).mpr hsource

/-- A canonical-source endpoint-kernel split gives seed-level positive
presentation compression nonnegativity. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_of_sourceEndpointKernelSplit
    (f : ZetaAdmissibleFunction)
    (kernelRemainder : ℝ)
    (hordered :
      completedOrderedHeartScalar (completedBoundaryHilbertSource f) =
        (completedBoundaryHilbertSourceEndpointTraceFiber
          (completedBoundaryHilbertSource f)).gram + kernelRemainder)
    (hkernel : 0 ≤ kernelRemainder) :
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  completedEndpointFiberPositivePresentationRemainder_nonnegative_of_sourceEndpointCompressionRemainder
    f
    (completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_of_endpointKernelSplit
      (completedBoundaryHilbertSource f) kernelRemainder hordered hkernel)

/-- The named canonical-source endpoint-kernel split gives seed-level
positive presentation compression nonnegativity. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_of_sourceEndpointKernelSplitProp
    (f : ZetaAdmissibleFunction)
    (hsplit :
      completedBoundaryHilbertSourceEndpointKernelSplit
        (completedBoundaryHilbertSource f)) :
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  completedEndpointFiberPositivePresentationRemainder_nonnegative_of_sourceEndpointCompressionRemainder
    f
    (completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_of_endpointKernelSplitProp
      (completedBoundaryHilbertSource f) hsplit)

/-- The archimedean/correction residual unfolds to its two packet Gram
coordinates minus the endpoint fiber Gram. -/
theorem completedEndpointFiberArchCorrectionRemainder_eq_arch_add_correction_sub_endpointFiberGram
    (f : ZetaAdmissibleFunction) :
    completedEndpointFiberArchCorrectionRemainder f =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) -
        (completedWeilEndpointTraceFiber f).gram :=
  Eq.refl (completedEndpointFiberArchCorrectionRemainder f)

/-- Nonnegativity of the archimedean/correction residual is exactly domination
of the endpoint fiber Gram by the two non-prime packet Gram coordinates. -/
theorem completedEndpointFiberArchCorrectionRemainder_nonnegative_iff_endpointFiberGram_le_arch_add_correction
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedEndpointFiberArchCorrectionRemainder f ↔
      (completedWeilEndpointTraceFiber f).gram ≤
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
  let A : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let C : ℝ :=
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let E : ℝ := (completedWeilEndpointTraceFiber f).gram
  Iff.intro
    (fun residualNonnegative =>
      let hsub : 0 ≤ A + C - E :=
        Eq.subst
          (motive := fun value : ℝ => 0 ≤ value)
          (completedEndpointFiberArchCorrectionRemainder_eq_arch_add_correction_sub_endpointFiberGram
            f)
          residualNonnegative
      sub_nonneg.mp hsub)
    (fun endpointFiberDomination =>
      let hsub : 0 ≤ A + C - E :=
        sub_nonneg.mpr endpointFiberDomination
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        (completedEndpointFiberArchCorrectionRemainder_eq_arch_add_correction_sub_endpointFiberGram
          f).symm
        hsub)

/-- Domination of the endpoint fiber Gram by the non-prime packet Grams proves
nonnegativity of the archimedean/correction residual. -/
theorem completedEndpointFiberArchCorrectionRemainder_nonnegative_of_endpointFiberGram_le_arch_add_correction
    (f : ZetaAdmissibleFunction)
    (endpointFiberDomination :
      (completedWeilEndpointTraceFiber f).gram ≤
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f)) :
    0 ≤ completedEndpointFiberArchCorrectionRemainder f :=
  (completedEndpointFiberArchCorrectionRemainder_nonnegative_iff_endpointFiberGram_le_arch_add_correction
    f).mpr endpointFiberDomination

/-- The archimedean packet Gram is the Gram of its centered spectral
amplitude. -/
theorem zetaCompletedHermitianBoundaryDefect_archimedeanPacketGram_eq_centeredAmplitudeGram
    (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) =
      ZetaHermitianPacketEnsemble.coordinateGram
        (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) :=
  let A : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let a : ℂ := zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f
  let complexGram :
      (A : ℂ) = a * star a :=
    (zetaCompletedArchimedeanBoundaryRealizedGram_eq_hermitianArchimedeanPacketGram
      f).symm
  let realGram :
      Complex.re (A : ℂ) = Complex.re (a * star a) :=
    congrArg Complex.re complexGram
  let hofReal :
      A = Complex.re (A : ℂ) :=
    (Complex.ofReal_re A).symm
  let hcoordinate :
      Complex.re (a * star a) =
        ZetaHermitianPacketEnsemble.coordinateGram a :=
    complex_re_mul_star_self_eq_normSq_hermitianPacket a
  hofReal.trans (realGram.trans hcoordinate)

/-- The archimedean/correction residual in fully visible spectral-coordinate
form: centered packet Grams minus the two endpoint evaluation squares. -/
theorem completedEndpointFiberArchCorrectionRemainder_eq_centeredPacketGrams_sub_endpointPhiNorms
    (f : ZetaAdmissibleFunction) :
    completedEndpointFiberArchCorrectionRemainder f =
      ZetaHermitianPacketEnsemble.coordinateGram
          (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
        ZetaHermitianPacketEnsemble.coordinateGram
          ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
            zetaCompletedExplicitFormulaPhi f 0) -
        (Complex.normSq
            (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
          Complex.normSq
            (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ))) :=
  let A : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let C : ℝ :=
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let E : ℝ := (completedWeilEndpointTraceFiber f).gram
  let centeredA : ℝ :=
    ZetaHermitianPacketEnsemble.coordinateGram
      (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f)
  let centeredC : ℝ :=
    ZetaHermitianPacketEnsemble.coordinateGram
      ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
        zetaCompletedExplicitFormulaPhi f 0)
  let endpointNorms : ℝ :=
    Complex.normSq
        (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
      Complex.normSq
        (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ))
  let hresidual :
      completedEndpointFiberArchCorrectionRemainder f = A + C - E :=
    completedEndpointFiberArchCorrectionRemainder_eq_arch_add_correction_sub_endpointFiberGram
      f
  let hA : A = centeredA :=
    zetaCompletedHermitianBoundaryDefect_archimedeanPacketGram_eq_centeredAmplitudeGram
      f
  let hC : C = centeredC :=
    zetaCompletedHermitianBoundaryDefect_correctionPacketGram_eq_centeredPolePhiNormSq
      f
  let hE : E = endpointNorms :=
    completedWeilEndpointTraceFiber_gram_eq_endpointPhi_normSq_add f
  hresidual.trans
    (congrArg₂ HSub.hSub
      (congrArg₂ HAdd.hAdd hA hC)
      hE)

/-- The fully visible centered-packet endpoint inequality proves nonnegativity
of the archimedean/correction residual. -/
theorem completedEndpointFiberArchCorrectionRemainder_nonnegative_of_endpointPhiNorms_le_centeredPacketGrams
    (f : ZetaAdmissibleFunction)
    (endpointPhiDomination :
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) ≤
        ZetaHermitianPacketEnsemble.coordinateGram
            (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
          ZetaHermitianPacketEnsemble.coordinateGram
            ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
              zetaCompletedExplicitFormulaPhi f 0)) :
    0 ≤ completedEndpointFiberArchCorrectionRemainder f :=
  let centeredA : ℝ :=
    ZetaHermitianPacketEnsemble.coordinateGram
      (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f)
  let centeredC : ℝ :=
    ZetaHermitianPacketEnsemble.coordinateGram
      ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
        zetaCompletedExplicitFormulaPhi f 0)
  let endpointNorms : ℝ :=
    Complex.normSq
        (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
      Complex.normSq
        (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ))
  let hsub : 0 ≤ centeredA + centeredC - endpointNorms :=
    sub_nonneg.mpr endpointPhiDomination
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedEndpointFiberArchCorrectionRemainder_eq_centeredPacketGrams_sub_endpointPhiNorms
      f).symm
    hsub

/-- The positive-presentation endpoint compression remainder splits into
prime positive energy plus the archimedean/correction endpoint residual. -/
theorem completedEndpointFiberPositivePresentationRemainder_eq_primePositive_add_archCorrectionRemainder
    (f : ZetaAdmissibleFunction) :
    completedEndpointFiberPositivePresentationRemainder f =
      completedPrimeDefectKernelPositiveChannel f +
        completedEndpointFiberArchCorrectionRemainder f :=
  let P : ℝ := completedPrimeDefectKernelPositiveChannel f
  let A : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let C : ℝ :=
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let E : ℝ := (completedWeilEndpointTraceFiber f).gram
  let positiveNormal :
      zetaCompletedGNSPositiveBoundaryPresentationScalar f =
        P + A + C :=
    zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_primeDefect_add_archimedean_add_correction
      f
  let remainderNormal :
      completedEndpointFiberPositivePresentationRemainder f =
        (P + A + C) - E :=
    Eq.trans
      (completedEndpointFiberPositivePresentationRemainder_eq_positive_sub_endpointFiberGram
        f)
      (congrArg (fun value : ℝ => value - E) positiveNormal)
  let regroupStepOne :
      (P + A + C) - E = (P + A + C) + -E :=
    sub_eq_add_neg (P + A + C) E
  let regroupStepTwo :
      (P + A + C) + -E = P + (A + C) + -E :=
    congrArg
      (fun value : ℝ => value + -E)
      (add_assoc P A C)
  let regroupStepThree :
      P + (A + C) + -E = P + ((A + C) + -E) :=
    add_assoc P (A + C) (-E)
  let regroupStepFour :
      P + ((A + C) + -E) = P + (A + C - E) :=
    congrArg
      (fun value : ℝ => P + value)
      (sub_eq_add_neg (A + C) E).symm
  let regroup :
      (P + A + C) - E = P + (A + C - E) :=
    regroupStepOne.trans
      (regroupStepTwo.trans (regroupStepThree.trans regroupStepFour))
  remainderNormal.trans
    (regroup.trans
      (congrArg
        (fun value : ℝ => P + value)
        (completedEndpointFiberArchCorrectionRemainder_eq_arch_add_correction_sub_endpointFiberGram
          f).symm))

/-- Prime positivity plus nonnegativity of the archimedean/correction endpoint
residual proves nonnegativity of the positive-presentation compression
remainder. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_of_archCorrectionRemainder
    (f : ZetaAdmissibleFunction)
    (archCorrectionRemainderNonnegative :
      0 ≤ completedEndpointFiberArchCorrectionRemainder f) :
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  let primeNonnegative :
      0 ≤ completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeDefectKernelPositiveChannel_nonnegative f
  let sumNonnegative :
      0 ≤
        completedPrimeDefectKernelPositiveChannel f +
          completedEndpointFiberArchCorrectionRemainder f :=
    add_nonneg primeNonnegative archCorrectionRemainderNonnegative
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedEndpointFiberPositivePresentationRemainder_eq_primePositive_add_archCorrectionRemainder
      f).symm
    sumNonnegative

/-- Adding the positive-presentation compression remainder back to the
endpoint fiber recovers the positive GNS presentation scalar. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_endpointFiberGram_add_positivePresentationRemainder
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationScalar f =
      (completedWeilEndpointTraceFiber f).gram +
        completedEndpointFiberPositivePresentationRemainder f :=
  let positive : ℝ := zetaCompletedGNSPositiveBoundaryPresentationScalar f
  let fiberGram : ℝ := (completedWeilEndpointTraceFiber f).gram
  let split :
      positive = fiberGram + (positive - fiberGram) :=
    endpointTraceDebt_add_sub_cancel positive fiberGram
  split

/-- Nonnegativity of the positive-presentation compression remainder is
equivalent to domination of the endpoint fiber by the positive presentation. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_iff_endpointFiberGram_le_positivePresentation
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedEndpointFiberPositivePresentationRemainder f ↔
      (completedWeilEndpointTraceFiber f).gram ≤
        zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  Iff.intro
    (fun remainderNonnegative =>
      let hsub :
        0 ≤
          zetaCompletedGNSPositiveBoundaryPresentationScalar f -
            (completedWeilEndpointTraceFiber f).gram :=
        Eq.subst
          (motive := fun value : ℝ => 0 ≤ value)
          (completedEndpointFiberPositivePresentationRemainder_eq_positive_sub_endpointFiberGram
            f)
          remainderNonnegative
      sub_nonneg.mp hsub)
    (fun endpointFiberDomination =>
      let hsub :
        0 ≤
          zetaCompletedGNSPositiveBoundaryPresentationScalar f -
            (completedWeilEndpointTraceFiber f).gram :=
        sub_nonneg.mpr endpointFiberDomination
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        (completedEndpointFiberPositivePresentationRemainder_eq_positive_sub_endpointFiberGram
          f).symm
        hsub)

/-- A nonnegative positive-presentation compression remainder gives endpoint
fiber domination of the positive GNS presentation. -/
theorem endpointFiberGram_le_positivePresentation_of_positivePresentationRemainder_nonnegative
    (f : ZetaAdmissibleFunction)
    (positivePresentationRemainderNonnegative :
      0 ≤ completedEndpointFiberPositivePresentationRemainder f) :
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  (completedEndpointFiberPositivePresentationRemainder_nonnegative_iff_endpointFiberGram_le_positivePresentation
    f).mp positivePresentationRemainderNonnegative

/-- If the endpoint fiber Gram is dominated by the positive GNS presentation
and the physical boundary has been identified with that presentation, then the
endpoint trace-compression remainder is nonnegative. -/
theorem completedWeilEndpointTraceRemainder_nonnegative_of_endpointFiberGram_le_positivePresentation
    (f : ZetaAdmissibleFunction)
    (boundaryToPositive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f)
    (endpointFiberDomination :
      (completedWeilEndpointTraceFiber f).gram ≤
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    0 ≤ completedWeilEndpointTraceRemainder f :=
  let endpointFiberBound :
      (completedWeilEndpointTraceFiber f).gram ≤
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    Eq.subst
      (motive := fun value : ℝ =>
        (completedWeilEndpointTraceFiber f).gram ≤ value)
      boundaryToPositive.symm
      endpointFiberDomination
  (completedWeilEndpointTraceRemainder_nonnegative_iff_endpointFiberGram_le_boundary
    f).mpr endpointFiberBound

/-- Boundary domination of the endpoint fiber is exactly nonnegativity of the
endpoint trace remainder. -/
theorem completedWeilEndpointTraceRemainder_nonnegative_of_endpointFiberGram_le_boundary
    (f : ZetaAdmissibleFunction)
    (endpointFiberDomination :
      (completedWeilEndpointTraceFiber f).gram ≤
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))) :
    0 ≤ completedWeilEndpointTraceRemainder f :=
  (completedWeilEndpointTraceRemainder_nonnegative_iff_endpointFiberGram_le_boundary
    f).mpr endpointFiberDomination

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
