import Boundary.LFunctions.ZetaCompletedWeightStream
import Boundary.LFunctions.ZetaPacketComparison
import Boundary.LFunctions.ZetaHermitianPacket
import Boundary.LFunctions.ZetaZeroTail

/-!
# Completed boundary Hilbert sources

This file owns the completed Hilbert-source object, its packet/GNS kernel,
ordered-heart quotient, and the basic completed Hilbert pairing API.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The Hilbert-source object for the completed boundary realization.

The completed explicit-formula boundary channel is not a linear form on raw admissible
functions: the pole/correction contribution contains a fixed square coordinate.  The Hilbert
source therefore consists of the analytic seed together with that correction coordinate. -/
structure CompletedBoundaryHilbertSource where
  seed : ZetaAdmissibleFunction
  correctionCoordinate : ℝ

namespace CompletedBoundaryHilbertSource

instance : Zero CompletedBoundaryHilbertSource :=
  ⟨{ seed := 0
     correctionCoordinate := 0 }⟩

instance : Add CompletedBoundaryHilbertSource :=
  ⟨fun X Y =>
    { seed := X.seed + Y.seed
      correctionCoordinate := X.correctionCoordinate + Y.correctionCoordinate }⟩

instance : Neg CompletedBoundaryHilbertSource :=
  ⟨fun X =>
    { seed := -X.seed
      correctionCoordinate := -X.correctionCoordinate }⟩

instance : Sub CompletedBoundaryHilbertSource :=
  ⟨fun X Y => X + -Y⟩

instance : SMul ℝ CompletedBoundaryHilbertSource :=
  ⟨fun a X =>
    { seed := a • X.seed
      correctionCoordinate := a * X.correctionCoordinate }⟩

@[ext]
theorem ext
    {X Y : CompletedBoundaryHilbertSource}
    (hseed : X.seed = Y.seed)
    (hcorr : X.correctionCoordinate = Y.correctionCoordinate) :
    X = Y := by
  cases X with
  | mk Xseed Xcorr =>
    cases Y with
    | mk Yseed Ycorr =>
      change Xseed = Yseed at hseed
      change Xcorr = Ycorr at hcorr
      cases hseed
      cases hcorr
      rfl

instance : AddCommGroup CompletedBoundaryHilbertSource where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  sub := Sub.sub
  zsmul := fun n X =>
    { seed := n • X.seed
      correctionCoordinate := n * X.correctionCoordinate }
  add_assoc := by
    intro X Y Z
    ext
    · exact add_assoc X.seed Y.seed Z.seed
    · exact add_assoc X.correctionCoordinate Y.correctionCoordinate Z.correctionCoordinate
  zero_add := by
    intro X
    ext
    · exact zero_add X.seed
    · exact zero_add X.correctionCoordinate
  add_zero := by
    intro X
    ext
    · exact add_zero X.seed
    · exact add_zero X.correctionCoordinate
  add_comm := by
    intro X Y
    ext
    · exact add_comm X.seed Y.seed
    · exact add_comm X.correctionCoordinate Y.correctionCoordinate
  add_left_neg := by
    intro X
    ext
    · exact neg_add_cancel X.seed
    · exact neg_add_cancel X.correctionCoordinate
  sub_eq_add_neg := by
    intro X Y
    rfl
  nsmul := fun n X =>
    { seed := n • X.seed
      correctionCoordinate := n * X.correctionCoordinate }
  nsmul_zero := by
    intro X
    ext
    · exact nsmul_zero X.seed
    · change ((0 : ℕ) : ℝ) * X.correctionCoordinate = 0
      exact zero_mul X.correctionCoordinate
  nsmul_succ := by
    intro n X
    ext
    · exact nsmul_succ n X.seed
    · change ((n + 1 : ℕ) : ℝ) * X.correctionCoordinate =
        n * X.correctionCoordinate + X.correctionCoordinate
      calc
        ((n + 1 : ℕ) : ℝ) * X.correctionCoordinate =
            (((n : ℕ) : ℝ) + 1) * X.correctionCoordinate := by
          exact congrArg (fun a : ℝ => a * X.correctionCoordinate)
            (Nat.cast_add n 1)
        _ =
            ((n : ℕ) : ℝ) * X.correctionCoordinate +
              1 * X.correctionCoordinate := by
          exact add_mul ((n : ℕ) : ℝ) 1 X.correctionCoordinate
        _ =
            ((n : ℕ) : ℝ) * X.correctionCoordinate +
              X.correctionCoordinate := by
          exact congrArg
            (fun a : ℝ => ((n : ℕ) : ℝ) * X.correctionCoordinate + a)
            (one_mul X.correctionCoordinate)
  zsmul_zero' := by
    intro X
    ext
    · exact zsmul_zero' X.seed
    · change ((0 : ℤ) : ℝ) * X.correctionCoordinate = 0
      exact zero_mul X.correctionCoordinate
  zsmul_succ' := by
    intro n X
    ext
    · exact zsmul_succ' n X.seed
    · change (((Int.ofNat n + 1 : ℤ) : ℝ) * X.correctionCoordinate) =
        (n : ℤ) * X.correctionCoordinate + X.correctionCoordinate
      have hcast :
          ((Int.ofNat n + 1 : ℤ) : ℝ) = ((n : ℤ) : ℝ) + 1 := by
        exact Int.cast_add (Int.ofNat n) 1
      calc
        ((Int.ofNat n + 1 : ℤ) : ℝ) * X.correctionCoordinate =
            (((n : ℤ) : ℝ) + 1) * X.correctionCoordinate := by
          exact congrArg (fun a : ℝ => a * X.correctionCoordinate) hcast
        _ =
            ((n : ℤ) : ℝ) * X.correctionCoordinate +
              1 * X.correctionCoordinate := by
          exact add_mul ((n : ℤ) : ℝ) 1 X.correctionCoordinate
        _ =
            ((n : ℤ) : ℝ) * X.correctionCoordinate +
              X.correctionCoordinate := by
          exact congrArg
            (fun a : ℝ => ((n : ℤ) : ℝ) * X.correctionCoordinate + a)
            (one_mul X.correctionCoordinate)
  zsmul_neg' := by
    intro n X
    ext
    · exact zsmul_neg' n X.seed
    · change (((-Int.ofNat n : ℤ) : ℝ) * X.correctionCoordinate) =
        -(((n : ℤ) : ℝ) * X.correctionCoordinate)
      calc
        ((-Int.ofNat n : ℤ) : ℝ) * X.correctionCoordinate =
            (-((n : ℤ) : ℝ)) * X.correctionCoordinate := by
          exact congrArg (fun a : ℝ => a * X.correctionCoordinate)
            (Int.cast_neg (Int.ofNat n))
        _ = -(((n : ℤ) : ℝ) * X.correctionCoordinate) := by
          exact neg_mul ((n : ℤ) : ℝ) X.correctionCoordinate

instance : Module ℝ CompletedBoundaryHilbertSource where
  one_smul := by
    intro X
    ext
    · exact one_smul ℝ X.seed
    · exact one_mul X.correctionCoordinate
  mul_smul := by
    intro a b X
    ext
    · exact mul_smul a b X.seed
    · exact mul_assoc a b X.correctionCoordinate
  smul_zero := by
    intro a
    ext
    · exact smul_zero a
    · exact mul_zero a
  smul_add := by
    intro a X Y
    ext
    · exact smul_add a X.seed Y.seed
    · exact mul_add a X.correctionCoordinate Y.correctionCoordinate
  add_smul := by
    intro a b X
    ext
    · exact add_smul a b X.seed
    · exact add_mul a b X.correctionCoordinate
  zero_smul := by
    intro X
    ext
    · exact zero_smul ℝ X.seed
    · exact zero_mul X.correctionCoordinate

end CompletedBoundaryHilbertSource

/-- The completed Hilbert source attached to an admissible seed.  The correction coordinate is
the explicit square-root correction packet coordinate. -/
def completedBoundaryHilbertSource
    (f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertSource :=
  { seed := f
    correctionCoordinate := zetaCompletionCorrectionPacketCoordinate }

/-- The packet realization of a completed Hilbert source.

The correction coordinate is the source coordinate, not the fixed completed-zeta coordinate.
This keeps the packet realization compatible with lower-weight source changes and makes the
GNS scalar a genuine packet-kernel scalar. -/
noncomputable def completedBoundaryHilbertSourcePacket
    (X : CompletedBoundaryHilbertSource) : ZetaPacketEnsemble :=
  zetaCompletedBoundaryDefectPrime X.seed +
    zetaCompletedBoundaryDefectArchimedean X.seed +
    ZetaPacketEnsemble.single ZetaPacketLabel.correction X.correctionCoordinate

/-- The completed real-shadow packet kernel on Hilbert sources, realized as the packet dot
product.  This kernel remains available for packet-comparison statements; the ordered-heart
scalar below is owned by the Hermitian defect-kernel realization. -/
noncomputable def completedBoundaryGNSKernel
    (X Y : CompletedBoundaryHilbertSource) : ℝ :=
  ZetaPacketEnsemble.dotProduct
    (completedBoundaryHilbertSourcePacket X)
    (completedBoundaryHilbertSourcePacket Y)

/-- The completed positive GNS kernel is symmetric. -/
theorem completedBoundaryGNSKernel_symmetric
    (X Y : CompletedBoundaryHilbertSource) :
    completedBoundaryGNSKernel X Y =
      completedBoundaryGNSKernel Y X := by
  unfold completedBoundaryGNSKernel
  exact ZetaPacketEnsemble.dotProduct_comm
    (completedBoundaryHilbertSourcePacket X)
    (completedBoundaryHilbertSourcePacket Y)

/-- The completed positive GNS radical is the zero-norm radical of the packet kernel. -/
def completedBoundaryGNSRadical
    (X : CompletedBoundaryHilbertSource) : Prop :=
  completedBoundaryGNSKernel X X = 0

/-- Zero GNS norm kills left cross-terms in the completed positive packet kernel. -/
theorem completedBoundaryGNSKernel_left_zero_of_self_zero
    {X Y : CompletedBoundaryHilbertSource}
    (hX : completedBoundaryGNSRadical X) :
    completedBoundaryGNSKernel X Y = 0 := by
  unfold completedBoundaryGNSRadical at hX
  unfold completedBoundaryGNSKernel at hX
  unfold completedBoundaryGNSKernel
  exact ZetaPacketEnsemble.dotProduct_left_eq_zero_of_normSq_eq_zero hX

/-- Zero GNS norm kills right cross-terms in the completed positive packet kernel. -/
theorem completedBoundaryGNSKernel_right_zero_of_self_zero
    {X Y : CompletedBoundaryHilbertSource}
    (hY : completedBoundaryGNSRadical Y) :
    completedBoundaryGNSKernel X Y = 0 := by
  unfold completedBoundaryGNSRadical at hY
  unfold completedBoundaryGNSKernel at hY
  unfold completedBoundaryGNSKernel
  exact ZetaPacketEnsemble.dotProduct_right_eq_zero_of_normSq_eq_zero hY

/-- The completed positive GNS kernel is nonnegative on the diagonal. -/
theorem completedBoundaryGNSKernel_self_nonnegative
    (X : CompletedBoundaryHilbertSource) :
    0 ≤ completedBoundaryGNSKernel X X := by
  unfold completedBoundaryGNSKernel
  exact ZetaPacketEnsemble.normSq_nonneg
    (completedBoundaryHilbertSourcePacket X)

/-- The real-shadow packet norm-square of the canonical Hilbert source.  This is a packet
comparison scalar, not the owner scalar of the completed ordered heart. -/
def completedBoundaryRealShadowGNSNormSq
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedBoundaryGNSKernel
    (completedBoundaryHilbertSource f)
    (completedBoundaryHilbertSource f)

/-- The real-shadow packet norm-square is nonnegative. -/
theorem completedBoundaryRealShadowGNSNormSq_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryRealShadowGNSNormSq f := by
  unfold completedBoundaryRealShadowGNSNormSq
  exact completedBoundaryGNSKernel_self_nonnegative
    (completedBoundaryHilbertSource f)

/-- The Hermitian/GNS scalar attached to a completed Hilbert source.

This scalar is induced by the completed positive GNS kernel.  Analytic defect-kernel and
finite-window formulas compare to this scalar by separate transport theorems; they do not
define positivity. -/
noncomputable def completedBoundaryHermitianGNSScalar
    (X : CompletedBoundaryHilbertSource) : ℝ :=
  completedPrimeDefectKernelPositiveChannel X.seed +
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect X.seed) +
    X.correctionCoordinate * X.correctionCoordinate

/-- The Hermitian/GNS scalar is nonnegative on every completed Hilbert source. -/
theorem completedBoundaryHermitianGNSScalar_nonnegative
    (X : CompletedBoundaryHilbertSource) :
    0 ≤ completedBoundaryHermitianGNSScalar X := by
  unfold completedBoundaryHermitianGNSScalar
  exact add_nonneg
    (add_nonneg
      (completedPrimeDefectKernelPositiveChannel_nonnegative X.seed)
      (ZetaHermitianPacketEnsemble.archimedeanPacketGram_nonnegative
        (zetaCompletedHermitianBoundaryDefect X.seed)))
    (mul_self_nonneg X.correctionCoordinate)

/-- On canonical sources, the Hermitian/GNS scalar is the completed positive GNS
presentation scalar. -/
theorem completedBoundaryHermitianGNSScalar_source_eq_positivePresentationScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryHermitianGNSScalar (completedBoundaryHilbertSource f) =
      zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
  have hpresentation :
      zetaCompletedGNSPositiveBoundaryPresentationScalar f =
        completedPrimeDefectKernelPositiveChannel f +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_primeDefect_add_archimedean_add_correction
      f
  have hcorrection :
      ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) =
        zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate :=
    zetaCompletedHermitianBoundaryDefect_correctionPacketGram_eq_coordinate_sq f
  unfold completedBoundaryHermitianGNSScalar
  unfold completedBoundaryHilbertSource
  calc
    completedPrimeDefectKernelPositiveChannel f +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
        zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate =
        completedPrimeDefectKernelPositiveChannel f +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) := by
      exact congrArg
        (fun x : ℝ =>
          completedPrimeDefectKernelPositiveChannel f +
            ZetaHermitianPacketEnsemble.archimedeanPacketGram
              (zetaCompletedHermitianBoundaryDefect f) +
            x)
        hcorrection.symm
    _ = zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
      exact hpresentation.symm

/-- The lower-weight exact Hilbert source is the zero source: it has no analytic seed and no
correction square coordinate. -/
def completedBoundaryLowerWeightExactHilbertSource :
    CompletedBoundaryHilbertSource :=
  0

/-- The reduced completed boundary channel: prime, archimedean, and residual completion
channels, with the affine pole/correction square coordinate removed from the raw boundary
functional. -/
def completedBoundaryReducedChannel
    (g : ZetaAdmissibleFunction) : ℂ :=
  primeBoundaryChannel g +
    archimedeanBoundaryChannel g +
    completionBoundaryChannel g

/-- The completed Hilbert pairing.  The reduced analytic channel is paired through
`convolutionPair`; the correction contribution is paired by the explicit real correction
coordinate. -/
def completedBoundaryHilbertPairing
    (X Y : CompletedBoundaryHilbertSource) : ℝ :=
  Complex.re
      (completedBoundaryReducedChannel (convolutionPair X.seed Y.seed)) +
    X.correctionCoordinate * Y.correctionCoordinate

/-- A Hilbert source is lower-weight radical when it pairs trivially with every completed
Hilbert source on both sides. -/
def CompletedBoundaryHilbertSource.LowerWeightRadical
    (D : CompletedBoundaryHilbertSource) : Prop :=
  ∀ T : CompletedBoundaryHilbertSource,
    completedBoundaryHilbertPairing D T = 0 ∧
      completedBoundaryHilbertPairing T D = 0

/-- The scalar induced by the completed positive GNS kernel on a Hilbert-source representative
of the ordered heart. -/
def completedOrderedHeartScalar
    (X : CompletedBoundaryHilbertSource) : ℝ :=
  completedBoundaryHermitianGNSScalar X

/-- Two completed Hilbert sources are GNS-tomographically equivalent when they have the same
Hermitian defect-kernel scalar in the completed ordered heart. -/
def CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent
    (X Y : CompletedBoundaryHilbertSource) : Prop :=
  completedBoundaryHermitianGNSScalar X =
    completedBoundaryHermitianGNSScalar Y

/-- GNS-tomographic equivalence is reflexive. -/
theorem CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.refl
    (X : CompletedBoundaryHilbertSource) :
    CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X X := by
  rfl

/-- GNS-tomographic equivalence is symmetric. -/
theorem CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.symm
    {X Y : CompletedBoundaryHilbertSource}
    (h :
      CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Y) :
    CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent Y X := by
  exact h.symm

/-- GNS-tomographic equivalence is transitive. -/
theorem CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.trans
    {X Y Z : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Y)
    (hYZ :
      CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent Y Z) :
    CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Z := by
  exact hXY.trans hYZ

/-- GNS tomography determines the ordered-heart scalar.  This is the positive-kernel
analogue of projective tomography: equality against all probes identifies the diagonal
quadratic scalar in the completed ordered heart. -/
theorem completedOrderedHeartScalar_eq_of_GNSTomography
    {X Y : CompletedBoundaryHilbertSource}
    (h :
      CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Y) :
    completedOrderedHeartScalar X = completedOrderedHeartScalar Y := by
  unfold completedOrderedHeartScalar
  exact h

/-- Equal Hilbert-source representatives are GNS-tomographically equivalent. -/
theorem completedBoundaryHilbertSource_GNSTomography_of_eq
    {X Y : CompletedBoundaryHilbertSource}
    (hXY : X = Y) :
    CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Y := by
  exact Eq.subst
    (motive := fun Z : CompletedBoundaryHilbertSource =>
      CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Z)
    hXY.symm
    (CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.refl X)

/-- Equal Hilbert-source representatives have the same ordered-heart scalar. -/
theorem completedOrderedHeartScalar_eq_of_eq
    {X Y : CompletedBoundaryHilbertSource}
    (hXY : X = Y) :
    completedOrderedHeartScalar X = completedOrderedHeartScalar Y :=
  completedOrderedHeartScalar_eq_of_GNSTomography
    (completedBoundaryHilbertSource_GNSTomography_of_eq hXY)

/-- The completed ordered-heart quotient relation on Hilbert-source representatives. -/
def completedBoundaryHilbertSourceGNSTomographySetoid :
    Setoid CompletedBoundaryHilbertSource where
  r := CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent
  iseqv := by
    constructor
    · intro X
      exact CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.refl X
    · intro X Y hXY
      exact CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.symm hXY
    · intro X Y Z hXY hYZ
      exact CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.trans hXY hYZ

/-- The completed ordered heart: Hilbert sources modulo lower-weight/GNS tomography. -/
abbrev CompletedBoundaryOrderedHeartClass :=
  Quotient completedBoundaryHilbertSourceGNSTomographySetoid

/-- The quotient class of a completed Hilbert-source representative. -/
def completedBoundaryOrderedHeartClass
    (X : CompletedBoundaryHilbertSource) :
    CompletedBoundaryOrderedHeartClass :=
  Quotient.mk completedBoundaryHilbertSourceGNSTomographySetoid X

/-- The ordered-heart scalar descends through GNS-tomographic equivalence. -/
def completedBoundaryOrderedHeartClassScalar :
    CompletedBoundaryOrderedHeartClass → ℝ :=
  Quotient.lift completedOrderedHeartScalar
    (fun X Y hXY => completedOrderedHeartScalar_eq_of_GNSTomography hXY)

/-- The scalar of a represented ordered-heart class is the representative's ordered-heart
scalar. -/
theorem completedBoundaryOrderedHeartClassScalar_mk
    (X : CompletedBoundaryHilbertSource) :
    completedBoundaryOrderedHeartClassScalar
        (completedBoundaryOrderedHeartClass X) =
      completedOrderedHeartScalar X := by
  rfl

/-- GNS-tomographically equivalent representatives define the same completed ordered-heart
class. -/
theorem completedBoundaryOrderedHeartClass_eq_of_GNSTomography
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Y) :
    completedBoundaryOrderedHeartClass X =
      completedBoundaryOrderedHeartClass Y := by
  exact Quotient.sound hXY

/-- Equal Hilbert-source representatives define the same completed ordered-heart class. -/
theorem completedBoundaryOrderedHeartClass_eq_of_eq
    {X Y : CompletedBoundaryHilbertSource}
    (hXY : X = Y) :
    completedBoundaryOrderedHeartClass X =
      completedBoundaryOrderedHeartClass Y := by
  exact completedBoundaryOrderedHeartClass_eq_of_GNSTomography
    (completedBoundaryHilbertSource_GNSTomography_of_eq hXY)

/-- Zero-tail tomography equivalence for completed Hilbert sources.

This is the quotient relation appropriate for zero-tail descent: two sources are equivalent
when every finite completed-zero tail cut has the same real absolute tail value on their
analytic seeds. It is intentionally separate from scalar-only GNS tomography. -/
def CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent
    (X Y : CompletedBoundaryHilbertSource) : Prop :=
  ∀ S : Finset ℂ,
    |Complex.re (zetaZeroTail S X.seed)| =
      |Complex.re (zetaZeroTail S Y.seed)|

/-- Spectral tomography equivalence for completed Hilbert sources.

This is the raw probe/spectral version of tomography: the analytic seeds have the same
spectral transform at every complex spectral parameter. -/
def CompletedBoundaryHilbertSource.SpectrallyTomographicallyEquivalent
    (X Y : CompletedBoundaryHilbertSource) : Prop :=
  ∀ z : ℂ, zetaSpectralEval X.seed z = zetaSpectralEval Y.seed z

/-- Spectral tomography identifies every completed-zero side contribution. -/
theorem zetaZeroSideContribution_eq_of_spectralTomography
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.SpectrallyTomographicallyEquivalent X Y)
    (ρ : ℂ) :
    zetaZeroSideContribution ρ X.seed =
      zetaZeroSideContribution ρ Y.seed := by
  unfold zetaZeroSideContribution
  exact congrArg
    (fun w : ℂ => - (zetaZeroMultiplicity ρ : ℂ) * w)
    (hXY (zetaCenteredZero ρ))

/-- Spectral tomography identifies every completed zero-tail functional. -/
theorem zetaZeroTail_eq_of_spectralTomography
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.SpectrallyTomographicallyEquivalent X Y)
    (S : Finset ℂ) :
    zetaZeroTail S X.seed = zetaZeroTail S Y.seed := by
  unfold zetaZeroTail
  exact tsum_congr
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
      zetaZeroSideContribution_eq_of_spectralTomography hXY (ρ : ℂ))

/-- Spectral tomography descends to zero-tail tomography. -/
theorem CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.of_spectralTomography
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.SpectrallyTomographicallyEquivalent X Y) :
    CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent X Y := by
  intro S
  exact congrArg (fun w : ℂ => |Complex.re w|)
    (zetaZeroTail_eq_of_spectralTomography hXY S)

/-- Zero-tail tomography equivalence is reflexive. -/
theorem CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.refl
    (X : CompletedBoundaryHilbertSource) :
    CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent X X := by
  intro S
  rfl

/-- Zero-tail tomography equivalence is symmetric. -/
theorem CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.symm
    {X Y : CompletedBoundaryHilbertSource}
    (h :
      CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent X Y) :
    CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent Y X := by
  intro S
  exact (h S).symm

/-- Zero-tail tomography equivalence is transitive. -/
theorem CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.trans
    {X Y Z : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent X Y)
    (hYZ :
      CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent Y Z) :
    CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent X Z := by
  intro S
  exact (hXY S).trans (hYZ S)

/-- The completed zero-tail quotient relation on Hilbert-source representatives. -/
def completedBoundaryHilbertSourceZeroTailTomographySetoid :
    Setoid CompletedBoundaryHilbertSource where
  r := CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent
  iseqv := by
    constructor
    · intro X
      exact CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.refl X
    · intro X Y hXY
      exact CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.symm hXY
    · intro X Y Z hXY hYZ
      exact CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.trans hXY hYZ

/-- The completed zero-tail ordered-heart quotient: Hilbert sources modulo zero-tail
tomography. -/
abbrev CompletedBoundaryZeroTailOrderedHeartClass :=
  Quotient completedBoundaryHilbertSourceZeroTailTomographySetoid

/-- The quotient class of a completed Hilbert-source representative in the zero-tail
ordered-heart quotient. -/
def completedBoundaryZeroTailOrderedHeartClass
    (X : CompletedBoundaryHilbertSource) :
    CompletedBoundaryZeroTailOrderedHeartClass :=
  Quotient.mk completedBoundaryHilbertSourceZeroTailTomographySetoid X

/-- Zero-tail-tomographically equivalent representatives define the same zero-tail
ordered-heart class. -/
theorem completedBoundaryZeroTailOrderedHeartClass_eq_of_zeroTailTomography
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent X Y) :
    completedBoundaryZeroTailOrderedHeartClass X =
      completedBoundaryZeroTailOrderedHeartClass Y := by
  exact Quotient.sound hXY

/-- Spectral tomography identifies the zero-tail ordered-heart quotient class. -/
theorem completedBoundaryZeroTailOrderedHeartClass_eq_of_spectralTomography
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.SpectrallyTomographicallyEquivalent X Y) :
    completedBoundaryZeroTailOrderedHeartClass X =
      completedBoundaryZeroTailOrderedHeartClass Y := by
  exact completedBoundaryZeroTailOrderedHeartClass_eq_of_zeroTailTomography
    (CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent.of_spectralTomography
      hXY)

/-- Contour/channel tomography identifies the zero-tail ordered-heart quotient class.

This is the quotient-level forgetting theorem for scheduled contour realizations: once the
chosen realization supplies the same spectral/channel evaluations for two Hilbert sources,
the zero-tail ordered-heart class no longer depends on the chosen contour representative. -/
theorem completedBoundaryZeroTailOrderedHeartClass_eq_of_contourChannelTomography
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      ∀ z : ℂ, zetaSpectralEval X.seed z = zetaSpectralEval Y.seed z) :
    completedBoundaryZeroTailOrderedHeartClass X =
      completedBoundaryZeroTailOrderedHeartClass Y := by
  exact completedBoundaryZeroTailOrderedHeartClass_eq_of_spectralTomography hXY

/-- The completed GNS norm-square induced by the completed Hilbert quotient pairing.

This is the canonical ordered-heart scalar of the realized Hilbert source, owned by the
positive packet kernel.  The reduced time-side boundary pairing is related to this scalar by
separate transport/comparison theorems. -/
def completedBoundaryGNSNormSq
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedOrderedHeartScalar (completedBoundaryHilbertSource f)

/-- The completed GNS norm-square is the ordered-heart scalar of the realized Hilbert source. -/
theorem completedBoundaryGNSNormSq_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryGNSNormSq f =
      completedOrderedHeartScalar (completedBoundaryHilbertSource f) := by
  rfl

/-- The completed GNS norm-square is induced by the Hermitian defect-kernel ordered-heart
scalar. -/
theorem completedBoundaryGNSNormSq_eq_hermitianGNSScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryGNSNormSq f =
      completedBoundaryHermitianGNSScalar
        (completedBoundaryHilbertSource f) := by
  rfl

/-- The completed ordered-heart GNS norm-square is nonnegative. -/
theorem completedBoundaryGNSNormSq_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryGNSNormSq f := by
  unfold completedBoundaryGNSNormSq
  unfold completedOrderedHeartScalar
  exact completedBoundaryHermitianGNSScalar_nonnegative
    (completedBoundaryHilbertSource f)

/-- Compatibility name for the completed positive GNS norm-square.  The owner scalar is
`completedBoundaryGNSNormSq`; this abbreviation keeps older packet-comparison wrappers useful
without creating a second scalar. -/
abbrev completedBoundaryGNSPositiveNormSq
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedBoundaryGNSNormSq f

/-- The completed positive GNS norm-square is nonnegative. -/
theorem completedBoundaryGNSPositiveNormSq_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryGNSPositiveNormSq f := by
  exact completedBoundaryGNSNormSq_nonnegative f

/-- The Hilbert pairing unfolds to the reduced analytic source pairing plus the explicit
correction-coordinate product. -/
theorem completedBoundaryHilbertPairing_eq_reduced_add_correction
    (X Y : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertPairing X Y =
      Complex.re
          (completedBoundaryReducedChannel (convolutionPair X.seed Y.seed)) +
        X.correctionCoordinate * Y.correctionCoordinate := by
  rfl

/-- The scalar induced by the reduced time-side Hilbert pairing.  This is retained as a
comparison scalar; the completed ordered-heart scalar is owned by the positive GNS kernel. -/
def completedBoundaryTimePairingScalar
    (X : CompletedBoundaryHilbertSource) : ℝ :=
  completedBoundaryHilbertPairing X X

/-- The prime boundary channel vanishes on the zero admissible probe. -/
theorem primeBoundaryChannel_zero :
    primeBoundaryChannel (0 : ZetaAdmissibleFunction) = 0 := by
  unfold primeBoundaryChannel
  unfold zetaCompletedExplicitFormulaPrimeContribution
  unfold zetaCompletedExplicitFormulaPrimePowerContribution
  let term : ZetaPrimePowerIndex → ℝ :=
    fun ι : ZetaPrimePowerIndex =>
      -(ZetaPrimePowerIndex.weight ι *
        Complex.re
          (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
              (ZetaPrimePowerIndex.center ι) +
            star
              (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                (ZetaPrimePowerIndex.center ι))))
  have hterm : term = fun _ι : ZetaPrimePowerIndex => 0 := by
    funext ι
    unfold term
    have hpos :
        zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
            (ZetaPrimePowerIndex.center ι) =
          0 :=
      zetaCompletedTimeBoundaryValue_zero (ZetaPrimePowerIndex.center ι)
    have hstar :
        star
            (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
              (ZetaPrimePowerIndex.center ι)) =
          0 := by
      exact (congrArg star hpos).trans (star_zero ℂ)
    have hsum :
        zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
            (ZetaPrimePowerIndex.center ι) +
          star
            (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
              (ZetaPrimePowerIndex.center ι)) =
        0 := by
      calc
        zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
            (ZetaPrimePowerIndex.center ι) +
          star
            (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
              (ZetaPrimePowerIndex.center ι)) =
            0 + 0 := by
          exact congrArg₂ HAdd.hAdd hpos hstar
        _ = 0 := by
          exact zero_add 0
    have hre :
        Complex.re
          (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
              (ZetaPrimePowerIndex.center ι) +
            star
              (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                (ZetaPrimePowerIndex.center ι))) =
          0 := by
      exact (congrArg Complex.re hsum).trans Complex.zero_re
    calc
      -(ZetaPrimePowerIndex.weight ι *
          Complex.re
            (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                (ZetaPrimePowerIndex.center ι) +
              star
                (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                  (ZetaPrimePowerIndex.center ι)))) =
          -(ZetaPrimePowerIndex.weight ι * 0) := by
        exact congrArg
          (fun x : ℝ => -(ZetaPrimePowerIndex.weight ι * x))
          hre
      _ = -0 := by
        exact congrArg Neg.neg (mul_zero (ZetaPrimePowerIndex.weight ι))
      _ = 0 := by
        exact neg_zero
  change ((∑' ι : ZetaPrimePowerIndex, term ι) : ℂ) = 0
  calc
    ((∑' ι : ZetaPrimePowerIndex, term ι) : ℂ) =
        ((∑' _ι : ZetaPrimePowerIndex, (0 : ℝ)) : ℂ) := by
      exact congrArg
        (fun u : ZetaPrimePowerIndex → ℝ =>
          ((∑' ι : ZetaPrimePowerIndex, u ι) : ℂ))
        hterm
    _ = ((0 : ℝ) : ℂ) := by
      exact congrArg (fun x : ℝ => (x : ℂ)) (tsum_zero)
    _ = 0 := by
      exact Complex.ofReal_zero

/-- The archimedean boundary channel vanishes on the zero admissible probe. -/
theorem archimedeanBoundaryChannel_zero :
    archimedeanBoundaryChannel (0 : ZetaAdmissibleFunction) = 0 := by
  unfold archimedeanBoundaryChannel
  unfold zetaCompletedExplicitFormulaArchimedeanContribution
  have hphi :
      zetaCompletedExplicitFormulaPhi (0 : ZetaAdmissibleFunction) 0 = 0 :=
    zetaCompletedExplicitFormulaPhi_zero 0
  calc
    (2 : ℂ) * zetaCompletedExplicitFormulaPhi (0 : ZetaAdmissibleFunction) 0 =
        (2 : ℂ) * 0 := by
      exact congrArg (fun z : ℂ => (2 : ℂ) * z) hphi
    _ = 0 := by
      exact mul_zero (2 : ℂ)

/-- The residual completion boundary channel vanishes on the zero admissible probe. -/
theorem completionBoundaryChannel_zero :
    completionBoundaryChannel (0 : ZetaAdmissibleFunction) = 0 := by
  rfl

/-- The reduced completed boundary channel vanishes on the zero admissible probe. -/
theorem completedBoundaryReducedChannel_zero :
    completedBoundaryReducedChannel (0 : ZetaAdmissibleFunction) = 0 := by
  unfold completedBoundaryReducedChannel
  calc
    primeBoundaryChannel (0 : ZetaAdmissibleFunction) +
        archimedeanBoundaryChannel (0 : ZetaAdmissibleFunction) +
        completionBoundaryChannel (0 : ZetaAdmissibleFunction) =
      0 + 0 + 0 := by
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd primeBoundaryChannel_zero archimedeanBoundaryChannel_zero)
        completionBoundaryChannel_zero
    _ = 0 + 0 := by
      exact add_zero (0 + 0)
    _ = 0 := by
      exact zero_add 0

/-- The reduced completed boundary channel of the zero convolution pair is zero. -/
theorem completedBoundaryReducedChannel_convolutionPair_zero_zero :
    completedBoundaryReducedChannel
        (convolutionPair (0 : ZetaAdmissibleFunction) 0) =
      0 := by
  exact (congrArg completedBoundaryReducedChannel convolutionPair_zero_zero).trans
    completedBoundaryReducedChannel_zero

/-- The reduced completed boundary channel of a convolution pair with zero left input is
zero. -/
theorem completedBoundaryReducedChannel_convolutionPair_zero_left
    (h : ZetaAdmissibleFunction) :
    completedBoundaryReducedChannel
        (convolutionPair (0 : ZetaAdmissibleFunction) h) =
      0 := by
  exact (congrArg completedBoundaryReducedChannel (convolutionPair_zero_left h)).trans
    completedBoundaryReducedChannel_zero

/-- The reduced completed boundary channel of a convolution pair with zero right input is
zero. -/
theorem completedBoundaryReducedChannel_convolutionPair_zero_right
    (f : ZetaAdmissibleFunction) :
    completedBoundaryReducedChannel
        (convolutionPair f (0 : ZetaAdmissibleFunction)) =
      0 := by
  exact (congrArg completedBoundaryReducedChannel (convolutionPair_zero_right f)).trans
    completedBoundaryReducedChannel_zero

/-- The zero Hilbert source has zero self-pairing. -/
theorem completedBoundaryHilbertPairing_zero_zero :
    completedBoundaryHilbertPairing
        (0 : CompletedBoundaryHilbertSource)
        (0 : CompletedBoundaryHilbertSource) =
      0 := by
  unfold completedBoundaryHilbertPairing
  change
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair (0 : ZetaAdmissibleFunction) 0)) +
      0 * 0 =
    0
  calc
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair (0 : ZetaAdmissibleFunction) 0)) +
      0 * 0 =
        Complex.re 0 + 0 * 0 := by
      exact congrArg
        (fun z : ℂ => Complex.re z + 0 * 0)
        completedBoundaryReducedChannel_convolutionPair_zero_zero
    _ = 0 + 0 * 0 := by
      exact congrArg (fun x : ℝ => x + 0 * 0) Complex.zero_re
    _ = 0 + 0 := by
      exact congrArg (fun x : ℝ => 0 + x) (zero_mul 0)
    _ = 0 := by
      exact zero_add 0

/-- The zero Hilbert source pairs trivially on the left. -/
theorem completedBoundaryHilbertPairing_zero_left
    (Y : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertPairing
        (0 : CompletedBoundaryHilbertSource)
        Y =
      0 := by
  unfold completedBoundaryHilbertPairing
  change
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair (0 : ZetaAdmissibleFunction) Y.seed)) +
      0 * Y.correctionCoordinate =
    0
  calc
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair (0 : ZetaAdmissibleFunction) Y.seed)) +
      0 * Y.correctionCoordinate =
        Complex.re 0 + 0 * Y.correctionCoordinate := by
      exact congrArg
        (fun z : ℂ => Complex.re z + 0 * Y.correctionCoordinate)
        (completedBoundaryReducedChannel_convolutionPair_zero_left Y.seed)
    _ = 0 + 0 * Y.correctionCoordinate := by
      exact congrArg (fun x : ℝ => x + 0 * Y.correctionCoordinate) Complex.zero_re
    _ = 0 + 0 := by
      exact congrArg (fun x : ℝ => 0 + x) (zero_mul Y.correctionCoordinate)
    _ = 0 := by
      exact zero_add 0

/-- The zero Hilbert source pairs trivially on the right. -/
theorem completedBoundaryHilbertPairing_zero_right
    (X : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertPairing
        X
        (0 : CompletedBoundaryHilbertSource) =
      0 := by
  unfold completedBoundaryHilbertPairing
  change
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair X.seed (0 : ZetaAdmissibleFunction))) +
      X.correctionCoordinate * 0 =
    0
  calc
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair X.seed (0 : ZetaAdmissibleFunction))) +
      X.correctionCoordinate * 0 =
        Complex.re 0 + X.correctionCoordinate * 0 := by
      exact congrArg
        (fun z : ℂ => Complex.re z + X.correctionCoordinate * 0)
        (completedBoundaryReducedChannel_convolutionPair_zero_right X.seed)
    _ = 0 + X.correctionCoordinate * 0 := by
      exact congrArg (fun x : ℝ => x + X.correctionCoordinate * 0) Complex.zero_re
    _ = 0 + 0 := by
      exact congrArg (fun x : ℝ => 0 + x) (mul_zero X.correctionCoordinate)
    _ = 0 := by
      exact zero_add 0

/-- The zero Hilbert source is lower-weight radical. -/
theorem completedBoundaryHilbertSource_zero_lowerWeightRadical :
    CompletedBoundaryHilbertSource.LowerWeightRadical
      (0 : CompletedBoundaryHilbertSource) := by
  intro T
  exact
    ⟨completedBoundaryHilbertPairing_zero_left T,
      completedBoundaryHilbertPairing_zero_right T⟩

/-- Adding a lower-weight radical Hilbert source does not change the reduced time-pairing
scalar, provided the completed Hilbert pairing is additive in both variables. -/
theorem completedBoundaryTimePairingScalar_eq_of_add_lowerWeightRadical
    (B_add_left :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing (x + y) z =
          completedBoundaryHilbertPairing x z +
            completedBoundaryHilbertPairing y z)
    (B_add_right :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x (y + z) =
          completedBoundaryHilbertPairing x y +
            completedBoundaryHilbertPairing x z)
    (Y D : CompletedBoundaryHilbertSource)
    (hD : CompletedBoundaryHilbertSource.LowerWeightRadical D) :
    completedBoundaryTimePairingScalar (Y + D) =
      completedBoundaryTimePairingScalar Y := by
  have hDYD :
      completedBoundaryHilbertPairing D (Y + D) = 0 :=
    (hD (Y + D)).1
  have hYD :
      completedBoundaryHilbertPairing Y D = 0 :=
    (hD Y).2
  unfold completedBoundaryTimePairingScalar
  calc
    completedBoundaryHilbertPairing (Y + D) (Y + D) =
        completedBoundaryHilbertPairing Y (Y + D) +
          completedBoundaryHilbertPairing D (Y + D) := by
      exact B_add_left Y D (Y + D)
    _ =
        completedBoundaryHilbertPairing Y (Y + D) + 0 := by
      exact congrArg
        (fun x : ℝ => completedBoundaryHilbertPairing Y (Y + D) + x)
        hDYD
    _ =
        completedBoundaryHilbertPairing Y (Y + D) := by
      exact add_zero (completedBoundaryHilbertPairing Y (Y + D))
    _ =
        completedBoundaryHilbertPairing Y Y +
          completedBoundaryHilbertPairing Y D := by
      exact B_add_right Y Y D
    _ =
        completedBoundaryHilbertPairing Y Y + 0 := by
      exact congrArg
        (fun x : ℝ => completedBoundaryHilbertPairing Y Y + x)
        hYD
    _ =
        completedBoundaryHilbertPairing Y Y := by
      exact add_zero (completedBoundaryHilbertPairing Y Y)

/-- The additive decomposition `X = Y + (X - Y)` for Hilbert sources. -/
theorem completedBoundaryHilbertSource_eq_add_sub
    (X Y : CompletedBoundaryHilbertSource) :
    X = Y + (X - Y) := by
  have h :
      Y + (X - Y) = X := by
    calc
      Y + (X - Y) =
          Y + (X + -Y) := by
        rfl
      _ =
          (Y + X) + -Y := by
        exact (add_assoc Y X (-Y)).symm
      _ =
          (X + Y) + -Y := by
        exact congrArg (fun Z : CompletedBoundaryHilbertSource => Z + -Y)
          (add_comm Y X)
      _ =
          X + (Y + -Y) := by
        exact add_assoc X Y (-Y)
      _ =
          X + 0 := by
        exact congrArg (fun Z : CompletedBoundaryHilbertSource => X + Z)
          (add_right_neg Y)
      _ =
          X := by
        exact add_zero X
  exact h.symm

/-- Two Hilbert-source representatives have the same reduced time-pairing scalar when their
difference is lower-weight radical, provided the completed Hilbert pairing is additive in both
variables. -/
theorem completedBoundaryTimePairingScalar_eq_of_lowerWeightRadical_sub
    (B_add_left :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing (x + y) z =
          completedBoundaryHilbertPairing x z +
            completedBoundaryHilbertPairing y z)
    (B_add_right :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x (y + z) =
          completedBoundaryHilbertPairing x y +
            completedBoundaryHilbertPairing x z)
    (X Y : CompletedBoundaryHilbertSource)
    (hD : CompletedBoundaryHilbertSource.LowerWeightRadical (X - Y)) :
    completedBoundaryTimePairingScalar X =
      completedBoundaryTimePairingScalar Y := by
  have hdecomp : X = Y + (X - Y) :=
    completedBoundaryHilbertSource_eq_add_sub X Y
  calc
    completedBoundaryTimePairingScalar X =
        completedBoundaryTimePairingScalar (Y + (X - Y)) := by
      exact congrArg completedBoundaryTimePairingScalar hdecomp
    _ =
        completedBoundaryTimePairingScalar Y := by
      exact completedBoundaryTimePairingScalar_eq_of_add_lowerWeightRadical
        B_add_left
        B_add_right
        Y
        (X - Y)
        hD

/-- Rearranging the real parts of the reduced channel plus pole channel. -/
theorem completedBoundaryReduced_re_add_pole_re_middle_swap
    (p a q r : ℝ) :
    (p + a + r) + q = p + a + q + r := by
  calc
    (p + a + r) + q = ((p + a) + r) + q := by
      rfl
    _ = (p + a) + (r + q) := by
      exact add_assoc (p + a) r q
    _ = (p + a) + (q + r) := by
      exact congrArg (fun x : ℝ => (p + a) + x) (add_comm r q)
    _ = ((p + a) + q) + r := by
      exact (add_assoc (p + a) q r).symm
    _ = p + a + q + r := by
      rfl

/-- Rearranging the real parts of the reduced channel plus pole channel. -/
theorem completedBoundaryReduced_re_add_pole_re
    (p a q r : ℂ) :
    Complex.re (p + a + r) + Complex.re q =
      Complex.re (p + a + q + r) := by
  calc
    Complex.re (p + a + r) + Complex.re q =
        (Complex.re (p + a) + Complex.re r) + Complex.re q := by
      exact congrArg (fun x : ℝ => x + Complex.re q)
        (Complex.add_re (p + a) r)
    _ =
        (Complex.re p + Complex.re a + Complex.re r) + Complex.re q := by
      exact congrArg (fun x : ℝ => (x + Complex.re r) + Complex.re q)
        (Complex.add_re p a)
    _ =
        Complex.re p + Complex.re a + Complex.re q + Complex.re r := by
      exact completedBoundaryReduced_re_add_pole_re_middle_swap
        (Complex.re p) (Complex.re a) (Complex.re q) (Complex.re r)
    _ =
        Complex.re (p + a + q) + Complex.re r := by
      exact congrArg (fun x : ℝ => x + Complex.re r)
        ((congrArg (fun x : ℝ => x + Complex.re q)
          (Complex.add_re p a)).symm)
    _ =
        Complex.re (p + a + q + r) := by
      exact (Complex.add_re (p + a + q) r).symm

/-- The Hilbert pairing of a realized seed with itself is the real completed boundary
channel on its autocorrelation probe.  The affine pole/correction contribution is represented
by the explicit correction coordinate in `CompletedBoundaryHilbertSource`. -/
theorem completedBoundaryHilbertPairing_source_self_eq_boundaryChannel_re
    (f : ZetaAdmissibleFunction) :
    completedBoundaryHilbertPairing
        (completedBoundaryHilbertSource f)
        (completedBoundaryHilbertSource f) =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  let g : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let p : ℂ := primeBoundaryChannel g
  let a : ℂ := archimedeanBoundaryChannel g
  let q : ℂ := poleBoundaryChannel g
  let r : ℂ := completionBoundaryChannel g
  have hconv : convolutionPair f f = g := by
    unfold g
    exact convolutionPair_self f
  have hcorr :
      zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate =
        Complex.re q := by
    unfold q
    unfold g
    exact (zetaCorrectionAutocorrelationChannel_eq_squareEnergy f).symm
  have hchannel :
      completedBoundaryChannel g = p + a + q + r := by
    unfold p
    unfold a
    unfold q
    unfold r
    exact completedBoundaryChannel_eq_prime_add_archimedean_add_pole_add_completion g
  have hreduced :
      primeBoundaryChannel (convolutionPair f f) +
          archimedeanBoundaryChannel (convolutionPair f f) +
          completionBoundaryChannel (convolutionPair f f) =
        p + a + r := by
    calc
      primeBoundaryChannel (convolutionPair f f) +
          archimedeanBoundaryChannel (convolutionPair f f) +
          completionBoundaryChannel (convolutionPair f f) =
        primeBoundaryChannel g +
            archimedeanBoundaryChannel g +
            completionBoundaryChannel g := by
        exact congrArg
          (fun u : ZetaAdmissibleFunction =>
            primeBoundaryChannel u + archimedeanBoundaryChannel u +
              completionBoundaryChannel u)
          hconv
      _ = p + a + r := by
        rfl
  unfold completedBoundaryHilbertPairing
  unfold completedBoundaryHilbertSource
  unfold completedBoundaryReducedChannel
  calc
    Complex.re
          (primeBoundaryChannel (convolutionPair f f) +
            archimedeanBoundaryChannel (convolutionPair f f) +
            completionBoundaryChannel (convolutionPair f f)) +
        zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate =
        Complex.re (p + a + r) +
          zetaCompletionCorrectionPacketCoordinate *
            zetaCompletionCorrectionPacketCoordinate := by
      exact congrArg₂ HAdd.hAdd
        (congrArg Complex.re hreduced)
        rfl
    _ = Complex.re (p + a + r) + Complex.re q := by
      exact congrArg
        (fun x : ℝ => Complex.re (p + a + r) + x)
        hcorr
    _ = Complex.re (p + a + q + r) := by
      exact completedBoundaryReduced_re_add_pole_re p a q r
    _ = Complex.re (completedBoundaryChannel g) := by
      exact congrArg Complex.re hchannel.symm

/-- The canonical completed Hilbert-source packet is the completed boundary defect packet. -/
theorem completedBoundaryHilbertSourcePacket_source_eq_boundaryDefect
    (f : ZetaAdmissibleFunction) :
    completedBoundaryHilbertSourcePacket (completedBoundaryHilbertSource f) =
      zetaCompletedBoundaryDefect f := by
  unfold completedBoundaryHilbertSourcePacket
  unfold completedBoundaryHilbertSource
  unfold zetaCompletedBoundaryDefect
  unfold zetaCompletedBoundaryDefectCorrection
  rfl

/-- The diagonal GNS kernel of a canonical source is the completed boundary-defect Gram. -/
theorem completedBoundaryGNSKernel_source_self_eq_boundaryDefectGram
    (f : ZetaAdmissibleFunction) :
    completedBoundaryGNSKernel
        (completedBoundaryHilbertSource f)
        (completedBoundaryHilbertSource f) =
      zetaCompletedBoundaryDefectGram f := by
  have hpacket :
      completedBoundaryHilbertSourcePacket (completedBoundaryHilbertSource f) =
        zetaCompletedBoundaryDefect f :=
    completedBoundaryHilbertSourcePacket_source_eq_boundaryDefect f
  unfold completedBoundaryGNSKernel
  unfold zetaCompletedBoundaryDefectGram
  exact congrArg₂ ZetaPacketEnsemble.dotProduct hpacket hpacket

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
