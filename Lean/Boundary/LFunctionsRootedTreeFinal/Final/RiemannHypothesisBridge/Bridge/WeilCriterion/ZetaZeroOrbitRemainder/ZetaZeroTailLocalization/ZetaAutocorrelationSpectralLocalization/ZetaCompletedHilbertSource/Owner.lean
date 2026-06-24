import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletedBoundaryDefect.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.HermitianBoundaryDefect
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ConvolutionChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.HorizontalContour.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeNaturalTimeArithmetic

/-!
# Completed boundary Hilbert sources

This file owns the completed Hilbert-source object, its packet/GNS kernel,
ordered-heart quotient, and the basic completed Hilbert pairing API.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open LSeries ArithmeticFunction
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The Hilbert-source object for the completed boundary realization.

The completed explicit-formula boundary channel is not a linear form on raw admissible
functions: the pole/correction contribution is represented by the centered-pole Hermitian
packet attached to the seed transform.  The Hilbert source therefore carries the analytic seed
together with the real coordinate used by the comparison pairing. -/
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
    exact CompletedBoundaryHilbertSource.ext
      (add_assoc X.seed Y.seed Z.seed)
      (add_assoc X.correctionCoordinate Y.correctionCoordinate Z.correctionCoordinate)
  zero_add := by
    intro X
    exact CompletedBoundaryHilbertSource.ext
      (zero_add X.seed)
      (zero_add X.correctionCoordinate)
  add_zero := by
    intro X
    exact CompletedBoundaryHilbertSource.ext
      (add_zero X.seed)
      (add_zero X.correctionCoordinate)
  add_comm := by
    intro X Y
    exact CompletedBoundaryHilbertSource.ext
      (add_comm X.seed Y.seed)
      (add_comm X.correctionCoordinate Y.correctionCoordinate)
  neg_add_cancel := by
    intro X
    exact CompletedBoundaryHilbertSource.ext
      (neg_add_cancel X.seed)
      (neg_add_cancel X.correctionCoordinate)
  sub_eq_add_neg := by
    intro X Y
    rfl
  nsmul := fun n X =>
    { seed := n • X.seed
      correctionCoordinate := n * X.correctionCoordinate }
  nsmul_zero := by
    intro X
    exact CompletedBoundaryHilbertSource.ext
      (zero_nsmul X.seed)
      (by
        calc
          ((0 : ℕ) : ℝ) * X.correctionCoordinate =
              (0 : ℝ) * X.correctionCoordinate := by
            exact congrArg (fun a : ℝ => a * X.correctionCoordinate)
              (Nat.cast_zero)
          _ = 0 := by
            exact zero_mul X.correctionCoordinate)
  nsmul_succ := by
    intro n X
    exact CompletedBoundaryHilbertSource.ext
      (succ_nsmul X.seed n)
      (by
        change ((n + 1 : ℕ) : ℝ) * X.correctionCoordinate =
        n * X.correctionCoordinate + X.correctionCoordinate
        have hcast :
            ((n + 1 : ℕ) : ℝ) = ((n : ℕ) : ℝ) + 1 := by
          exact (Nat.cast_add n 1).trans
            (congrArg (fun a : ℝ => ((n : ℕ) : ℝ) + a) Nat.cast_one)
        calc
          ((n + 1 : ℕ) : ℝ) * X.correctionCoordinate =
              (((n : ℕ) : ℝ) + 1) * X.correctionCoordinate := by
            exact congrArg (fun a : ℝ => a * X.correctionCoordinate) hcast
          _ =
              ((n : ℕ) : ℝ) * X.correctionCoordinate +
                1 * X.correctionCoordinate := by
            exact add_mul ((n : ℕ) : ℝ) 1 X.correctionCoordinate
          _ =
              ((n : ℕ) : ℝ) * X.correctionCoordinate +
                X.correctionCoordinate := by
            exact congrArg
              (fun a : ℝ => ((n : ℕ) : ℝ) * X.correctionCoordinate + a)
              (one_mul X.correctionCoordinate))
  zsmul_zero' := by
    intro X
    exact CompletedBoundaryHilbertSource.ext
      (SubNegMonoid.zsmul_zero' X.seed)
      (by
        calc
          ((0 : ℤ) : ℝ) * X.correctionCoordinate =
              (0 : ℝ) * X.correctionCoordinate := by
            exact congrArg (fun a : ℝ => a * X.correctionCoordinate)
              (Int.cast_zero)
          _ = 0 := by
            exact zero_mul X.correctionCoordinate)
  zsmul_succ' := by
    intro n X
    exact CompletedBoundaryHilbertSource.ext
      (SubNegMonoid.zsmul_succ' n X.seed)
      (by
        change ((((n.succ : ℕ) : ℤ) : ℝ) * X.correctionCoordinate) =
          (((n : ℕ) : ℤ) : ℝ) * X.correctionCoordinate + X.correctionCoordinate
        have hsucc :
            (((n.succ : ℕ) : ℤ) : ℝ) =
              (((n : ℕ) : ℤ) : ℝ) + 1 := by
          calc
            (((n.succ : ℕ) : ℤ) : ℝ) =
                ((n.succ : ℕ) : ℝ) := by
              exact Int.cast_natCast n.succ
            _ = ((n : ℕ) : ℝ) + 1 := by
              exact Nat.cast_succ n
            _ = (((n : ℕ) : ℤ) : ℝ) + 1 := by
              exact congrArg (fun a : ℝ => a + 1)
                (Int.cast_natCast n).symm
        calc
          (((n.succ : ℕ) : ℤ) : ℝ) * X.correctionCoordinate =
              ((((n : ℕ) : ℤ) : ℝ) + 1) * X.correctionCoordinate := by
            exact congrArg (fun a : ℝ => a * X.correctionCoordinate) hsucc
          _ =
              (((n : ℕ) : ℤ) : ℝ) * X.correctionCoordinate +
                1 * X.correctionCoordinate := by
            exact add_mul (((n : ℕ) : ℤ) : ℝ) 1 X.correctionCoordinate
          _ =
              (((n : ℕ) : ℤ) : ℝ) * X.correctionCoordinate +
                X.correctionCoordinate := by
            exact congrArg
              (fun a : ℝ =>
                (((n : ℕ) : ℤ) : ℝ) * X.correctionCoordinate + a)
              (one_mul X.correctionCoordinate))
  zsmul_neg' := by
    intro n X
    exact CompletedBoundaryHilbertSource.ext
      (SubNegMonoid.zsmul_neg' n X.seed)
      (by
        change (((Int.negSucc n : ℤ) : ℝ) * X.correctionCoordinate) =
          -(((((n.succ : ℕ) : ℤ) : ℝ) * X.correctionCoordinate))
        have hneg :
            ((Int.negSucc n : ℤ) : ℝ) =
              -((((n.succ : ℕ) : ℤ) : ℝ)) := by
          calc
            ((Int.negSucc n : ℤ) : ℝ) =
                -(((n + 1 : ℕ) : ℝ)) := by
              exact Int.cast_negSucc n
            _ = -((((n.succ : ℕ) : ℤ) : ℝ)) := by
              exact congrArg Neg.neg (Int.cast_natCast n.succ).symm
        calc
          ((Int.negSucc n : ℤ) : ℝ) * X.correctionCoordinate =
              -((((n.succ : ℕ) : ℤ) : ℝ)) * X.correctionCoordinate := by
            exact congrArg (fun a : ℝ => a * X.correctionCoordinate) hneg
          _ =
              -(((((n.succ : ℕ) : ℤ) : ℝ) * X.correctionCoordinate)) := by
            exact neg_mul ((((n.succ : ℕ) : ℤ) : ℝ))
              X.correctionCoordinate)

instance : Module ℝ CompletedBoundaryHilbertSource where
  one_smul := by
    intro X
    exact CompletedBoundaryHilbertSource.ext
      (one_smul ℝ X.seed)
      (one_mul X.correctionCoordinate)
  mul_smul := by
    intro a b X
    exact CompletedBoundaryHilbertSource.ext
      (mul_smul a b X.seed)
      (mul_assoc a b X.correctionCoordinate)
  smul_zero := by
    intro a
    exact CompletedBoundaryHilbertSource.ext
      (smul_zero a)
      (mul_zero a)
  smul_add := by
    intro a X Y
    exact CompletedBoundaryHilbertSource.ext
      (smul_add a X.seed Y.seed)
      (mul_add a X.correctionCoordinate Y.correctionCoordinate)
  add_smul := by
    intro a b X
    exact CompletedBoundaryHilbertSource.ext
      (add_smul a b X.seed)
      (add_mul a b X.correctionCoordinate)
  zero_smul := by
    intro X
    exact CompletedBoundaryHilbertSource.ext
      (zero_smul ℝ X.seed)
      (zero_mul X.correctionCoordinate)

end CompletedBoundaryHilbertSource

/-- The completed Hilbert source attached to an admissible seed.  The correction coordinate is
the nonnegative square root of the centered-pole Hermitian correction packet gram. -/
def completedBoundaryHilbertSource
    (f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertSource :=
  { seed := f
    correctionCoordinate :=
      Real.sqrt
        (ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f)) }

/-- The canonical correction coordinate squares to the centered-pole Hermitian correction
packet gram. -/
theorem completedBoundaryHilbertSource_correctionCoordinate_sq
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryHilbertSource f).correctionCoordinate *
        (completedBoundaryHilbertSource f).correctionCoordinate =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  let C : ℝ :=
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  have hC_nonnegative : 0 ≤ C :=
    ZetaHermitianPacketEnsemble.correctionPacketGram_nonnegative
      (zetaCompletedHermitianBoundaryDefect f)
  unfold completedBoundaryHilbertSource
  change Real.sqrt C * Real.sqrt C = C
  calc
    Real.sqrt C * Real.sqrt C = (Real.sqrt C) ^ 2 := by
      exact (pow_two (Real.sqrt C)).symm
    _ = C := by
      exact Real.sq_sqrt hC_nonnegative

/-- The packet realization of a completed Hilbert source.

The correction coordinate is the source coordinate.  This keeps the packet realization
compatible with lower-weight source changes; the ordered-heart scalar below is normalized
through the Hermitian centered-pole packet. -/
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
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect X.seed)

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
    (ZetaHermitianPacketEnsemble.correctionPacketGram_nonnegative
      (zetaCompletedHermitianBoundaryDefect X.seed))

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
  unfold completedBoundaryHermitianGNSScalar
  unfold completedBoundaryHilbertSource
  calc
    completedPrimeDefectKernelPositiveChannel f +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) =
        completedPrimeDefectKernelPositiveChannel f +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) := by
      rfl
    _ = zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
      exact hpresentation.symm

/-- The lower-weight exact Hilbert source is the zero source: it has no analytic seed and no
centered-pole correction coordinate. -/
def completedBoundaryLowerWeightExactHilbertSource :
    CompletedBoundaryHilbertSource :=
  0

/-- The reduced completed boundary channel: prime, archimedean, and residual completion
channels, with the affine centered-pole correction term removed from the raw boundary
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
  exact Eq.symm h

/-- GNS-tomographic equivalence is transitive. -/
theorem CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.trans
    {X Y Z : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Y)
    (hYZ :
      CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent Y Z) :
    CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Z := by
  exact Eq.trans hXY hYZ

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
  cases hXY
  exact CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.refl X

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
  let term : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      -(((ZetaPrimePowerIndex.weight ι : ℝ) : ℂ) *
        ((Complex.re
            (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                (ZetaPrimePowerIndex.center ι) +
              star
                (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                  (ZetaPrimePowerIndex.center ι))) : ℝ) : ℂ))
  have hterm : term = fun _ι : ZetaPrimePowerIndex => 0 := by
    ext ι
    show term ι = 0
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
      -(((ZetaPrimePowerIndex.weight ι : ℝ) : ℂ) *
          ((Complex.re
              (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                  (ZetaPrimePowerIndex.center ι) +
                star
                  (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                    (ZetaPrimePowerIndex.center ι))) : ℝ) : ℂ)) =
          -(((ZetaPrimePowerIndex.weight ι : ℝ) : ℂ) * ((0 : ℝ) : ℂ)) := by
        exact congrArg
          (fun x : ℝ =>
            -(((ZetaPrimePowerIndex.weight ι : ℝ) : ℂ) * ((x : ℝ) : ℂ)))
          hre
      _ = -0 := by
        exact congrArg Neg.neg
          (mul_zero (((ZetaPrimePowerIndex.weight ι : ℝ) : ℂ)))
      _ = 0 := by
        exact neg_zero
  change (∑' ι : ZetaPrimePowerIndex, term ι) = 0
  calc
    (∑' ι : ZetaPrimePowerIndex, term ι) =
        (∑' _ι : ZetaPrimePowerIndex, (0 : ℂ)) := by
      exact congrArg
        (fun u : ZetaPrimePowerIndex → ℂ =>
          (∑' ι : ZetaPrimePowerIndex, u ι))
        hterm
    _ = 0 := by
      exact tsum_zero
    _ = 0 := by
      rfl

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
  apply CompletedBoundaryHilbertSource.ext
  · change X.seed = Y.seed + (X.seed + -Y.seed)
    exact
      (calc
        Y.seed + (X.seed + -Y.seed) =
            (Y.seed + X.seed) + -Y.seed := by
          exact (add_assoc Y.seed X.seed (-Y.seed)).symm
        _ = (X.seed + Y.seed) + -Y.seed := by
          exact congrArg (fun Z : ZetaAdmissibleFunction => Z + -Y.seed)
            (add_comm Y.seed X.seed)
        _ = X.seed + (Y.seed + -Y.seed) := by
          exact add_assoc X.seed Y.seed (-Y.seed)
        _ = X.seed + 0 := by
          exact congrArg (fun Z : ZetaAdmissibleFunction => X.seed + Z)
            (add_right_neg Y.seed)
        _ = X.seed := by
          exact add_zero X.seed).symm
  · change X.correctionCoordinate =
      Y.correctionCoordinate + (X.correctionCoordinate + -Y.correctionCoordinate)
    exact
      (calc
        Y.correctionCoordinate +
            (X.correctionCoordinate + -Y.correctionCoordinate) =
            (Y.correctionCoordinate + X.correctionCoordinate) +
              -Y.correctionCoordinate := by
          exact
            (add_assoc Y.correctionCoordinate X.correctionCoordinate
              (-Y.correctionCoordinate)).symm
        _ = (X.correctionCoordinate + Y.correctionCoordinate) +
              -Y.correctionCoordinate := by
          exact congrArg (fun Z : ℝ => Z + -Y.correctionCoordinate)
            (add_comm Y.correctionCoordinate X.correctionCoordinate)
        _ = X.correctionCoordinate +
              (Y.correctionCoordinate + -Y.correctionCoordinate) := by
          exact
            add_assoc X.correctionCoordinate Y.correctionCoordinate
              (-Y.correctionCoordinate)
        _ = X.correctionCoordinate + 0 := by
          exact congrArg (fun Z : ℝ => X.correctionCoordinate + Z)
            (add_right_neg Y.correctionCoordinate)
        _ = X.correctionCoordinate := by
          exact add_zero X.correctionCoordinate).symm

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
      (completedBoundaryHilbertSource f).correctionCoordinate *
          (completedBoundaryHilbertSource f).correctionCoordinate =
        Complex.re q := by
    have hcoord :
        (completedBoundaryHilbertSource f).correctionCoordinate *
            (completedBoundaryHilbertSource f).correctionCoordinate =
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
      completedBoundaryHilbertSource_correctionCoordinate_sq f
    have hq :
        Complex.re q =
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) := by
      unfold q
      unfold g
      change
        Complex.re
            (zetaCompletedExplicitFormulaCorrectionContribution
              (convolutionAutocorrelation f)) =
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f)
      have howner :
          zetaCompletedExplicitFormulaCorrectionContribution
              (convolutionAutocorrelation f) =
            zetaCompletedExplicitFormulaCorrectionConvolutionContribution f :=
        zetaCompletedExplicitFormulaCorrectionContribution_convolutionAutocorrelation_eq_owner
          f
      calc
        Complex.re
            (zetaCompletedExplicitFormulaCorrectionContribution
              (convolutionAutocorrelation f)) =
            Complex.re
              (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) := by
          exact congrArg Complex.re howner
        _ =
            ZetaHermitianPacketEnsemble.correctionPacketGram
              (zetaCompletedHermitianBoundaryDefect f) := by
          exact
            zetaCompletedExplicitFormulaCorrectionConvolutionChannel_holographic
              f
    exact hcoord.trans hq.symm
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
        (completedBoundaryHilbertSource f).correctionCoordinate *
          (completedBoundaryHilbertSource f).correctionCoordinate =
        Complex.re (p + a + r) +
          (completedBoundaryHilbertSource f).correctionCoordinate *
            (completedBoundaryHilbertSource f).correctionCoordinate := by
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

/-- The raw Hilbert pairing identifies with the positive Hermitian/GNS scalar once the
remaining prime channel is identified with the positive defect-kernel channel. -/
theorem completedBoundaryHilbertPairing_source_self_eq_positivePresentationScalar_of_prime
    (f : ZetaAdmissibleFunction) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      completedPrimeDefectKernelPositiveChannel f →
    completedBoundaryHilbertPairing
        (completedBoundaryHilbertSource f)
        (completedBoundaryHilbertSource f) =
      zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
  intro hprime
  let X : CompletedBoundaryHilbertSource := completedBoundaryHilbertSource f
  have hpresentation :
      completedBoundaryHermitianGNSScalar X =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
    unfold X
    exact completedBoundaryHermitianGNSScalar_source_eq_positivePresentationScalar f
  have hpairing :
      completedBoundaryHilbertPairing X X =
        completedBoundaryHermitianGNSScalar X := by
    have hconv : convolutionPair f f = convolutionAutocorrelation f :=
      convolutionPair_self f
    have hreduced :
        Complex.re
            (completedBoundaryReducedChannel (convolutionPair f f)) =
          completedPrimeDefectKernelPositiveChannel f +
            ZetaHermitianPacketEnsemble.archimedeanPacketGram
              (zetaCompletedHermitianBoundaryDefect f) := by
      unfold completedBoundaryReducedChannel
      calc
        Complex.re
            (primeBoundaryChannel (convolutionPair f f) +
              archimedeanBoundaryChannel (convolutionPair f f) +
              completionBoundaryChannel (convolutionPair f f)) =
            Complex.re
              (primeBoundaryChannel (convolutionAutocorrelation f) +
                archimedeanBoundaryChannel (convolutionAutocorrelation f) +
                completionBoundaryChannel (convolutionAutocorrelation f)) := by
          exact congrArg
            (fun g : ZetaAdmissibleFunction =>
              Complex.re
                (primeBoundaryChannel g +
                  archimedeanBoundaryChannel g +
                  completionBoundaryChannel g))
            hconv
        _ =
            Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) +
              Complex.re (archimedeanBoundaryChannel (convolutionAutocorrelation f)) := by
          have hcompletion :
              completionBoundaryChannel (convolutionAutocorrelation f) = 0 :=
            completionBoundaryChannel_unfold (convolutionAutocorrelation f)
          calc
            Complex.re
              (primeBoundaryChannel (convolutionAutocorrelation f) +
                archimedeanBoundaryChannel (convolutionAutocorrelation f) +
                completionBoundaryChannel (convolutionAutocorrelation f)) =
                Complex.re
                  (primeBoundaryChannel (convolutionAutocorrelation f) +
                    archimedeanBoundaryChannel (convolutionAutocorrelation f) +
                    0) := by
              exact congrArg Complex.re
                (congrArg
                  (fun z : ℂ =>
                    primeBoundaryChannel (convolutionAutocorrelation f) +
                      archimedeanBoundaryChannel (convolutionAutocorrelation f) + z)
                  hcompletion)
            _ =
                Complex.re
                  (primeBoundaryChannel (convolutionAutocorrelation f) +
                    archimedeanBoundaryChannel (convolutionAutocorrelation f)) := by
              exact congrArg Complex.re
                (add_zero
                  (primeBoundaryChannel (convolutionAutocorrelation f) +
                    archimedeanBoundaryChannel (convolutionAutocorrelation f)))
            _ =
                Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) +
                  Complex.re (archimedeanBoundaryChannel (convolutionAutocorrelation f)) := by
              exact Complex.add_re
                (primeBoundaryChannel (convolutionAutocorrelation f))
                (archimedeanBoundaryChannel (convolutionAutocorrelation f))
        _ =
            completedPrimeDefectKernelPositiveChannel f +
              Complex.re (archimedeanBoundaryChannel (convolutionAutocorrelation f)) := by
          exact congrArg
            (fun x : ℝ =>
              x +
                Complex.re (archimedeanBoundaryChannel (convolutionAutocorrelation f)))
            hprime
        _ =
            completedPrimeDefectKernelPositiveChannel f +
              ZetaHermitianPacketEnsemble.archimedeanPacketGram
                (zetaCompletedHermitianBoundaryDefect f) := by
          have harchContribution :
              archimedeanBoundaryChannel (convolutionAutocorrelation f) =
                zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f := by
            change
              zetaCompletedExplicitFormulaArchimedeanContribution
                  (convolutionAutocorrelation f) =
                zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f
            exact
              zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_paired_owner
                f
          have harchRe :
              Complex.re
                  (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
                ZetaHermitianPacketEnsemble.archimedeanPacketGram
                  (zetaCompletedHermitianBoundaryDefect f) :=
            zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_re_eq_archimedeanPacketGram
              f
          exact congrArg
            (fun x : ℝ => completedPrimeDefectKernelPositiveChannel f + x)
            ((congrArg Complex.re harchContribution).trans harchRe)
    unfold completedBoundaryHilbertPairing
    unfold completedBoundaryHermitianGNSScalar
    unfold X
    have hcoord :
        (completedBoundaryHilbertSource f).correctionCoordinate *
            (completedBoundaryHilbertSource f).correctionCoordinate =
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
      completedBoundaryHilbertSource_correctionCoordinate_sq f
    calc
      Complex.re
            (completedBoundaryReducedChannel
              (convolutionPair
                (completedBoundaryHilbertSource f).seed
                (completedBoundaryHilbertSource f).seed)) +
          (completedBoundaryHilbertSource f).correctionCoordinate *
            (completedBoundaryHilbertSource f).correctionCoordinate =
          (completedPrimeDefectKernelPositiveChannel f +
              ZetaHermitianPacketEnsemble.archimedeanPacketGram
                (zetaCompletedHermitianBoundaryDefect f)) +
            (completedBoundaryHilbertSource f).correctionCoordinate *
              (completedBoundaryHilbertSource f).correctionCoordinate := by
        exact congrArg
          (fun x : ℝ =>
            x +
              (completedBoundaryHilbertSource f).correctionCoordinate *
                (completedBoundaryHilbertSource f).correctionCoordinate)
          hreduced
      _ =
          (completedPrimeDefectKernelPositiveChannel f +
              ZetaHermitianPacketEnsemble.archimedeanPacketGram
                (zetaCompletedHermitianBoundaryDefect f)) +
            ZetaHermitianPacketEnsemble.correctionPacketGram
              (zetaCompletedHermitianBoundaryDefect f) := by
        exact congrArg
          (fun x : ℝ =>
            (completedPrimeDefectKernelPositiveChannel f +
              ZetaHermitianPacketEnsemble.archimedeanPacketGram
                (zetaCompletedHermitianBoundaryDefect f)) + x)
          hcoord
  calc
    completedBoundaryHilbertPairing X X =
        completedBoundaryHermitianGNSScalar X := by
      exact hpairing
    _ = zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
      exact hpresentation

/-- The raw completed boundary channel identifies with the positive Hermitian/GNS presentation
scalar after the remaining prime-channel comparison is supplied. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_eq_positivePresentationScalar_of_prime
    (f : ZetaAdmissibleFunction) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      completedPrimeDefectKernelPositiveChannel f →
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
      zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
  intro hprime
  let X : CompletedBoundaryHilbertSource := completedBoundaryHilbertSource f
  have hraw :
      completedBoundaryHilbertPairing X X =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
    unfold X
    exact completedBoundaryHilbertPairing_source_self_eq_boundaryChannel_re f
  have hpositive :
      completedBoundaryHilbertPairing X X =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
    unfold X
    exact
      completedBoundaryHilbertPairing_source_self_eq_positivePresentationScalar_of_prime
        f hprime
  exact hraw.symm.trans hpositive

/-- The reconstructed prime convolution channel and the positive prime-defect channel add to
the finite prime diagonal debt. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_add_positiveChannel_eq_diagonalDebt_re
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) +
        completedPrimeDefectKernelPositiveChannel f =
      Complex.re (zetaPrimeDefectKernelDiagonalDebt f) := by
  let P : ℂ := zetaPrimeDefectKernelPositiveForm f
  let B : ℂ := zetaCompletedExplicitFormulaPrimeConvolutionContribution f
  let D : ℂ := zetaPrimeDefectKernelDiagonalDebt f
  have hpositive :
      completedPrimeDefectKernelPositiveChannel f = Complex.re P := by
    exact completedPrimeDefectKernelPositiveChannel_eq_finitePositiveForm_re f
  have hbalance :
      P + B = D := by
    exact zetaCompletedExplicitFormulaPrimeConvolutionContribution_add_primeDefectKernelPositiveForm_eq_diagonalDebt
      f
  calc
    Complex.re B + completedPrimeDefectKernelPositiveChannel f =
        Complex.re B + Complex.re P := by
      exact congrArg (fun x : ℝ => Complex.re B + x) hpositive
    _ = Complex.re P + Complex.re B := by
      exact add_comm (Complex.re B) (Complex.re P)
    _ = Complex.re (P + B) := by
      exact (Complex.add_re P B).symm
    _ = Complex.re D := by
      exact congrArg Complex.re hbalance

/-- The finite time-distribution window of an autocorrelation is the physical
off-diagonal prime window. -/
theorem finitePrimeTimeDistributionWindow_convolutionAutocorrelation_eq_physical
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) =
      finitePhysicalPrimeOffDiagonalWindow N f := by
  unfold finitePrimeTimeDistributionWindow
  unfold finitePhysicalPrimeOffDiagonalWindow
  unfold finitePartPrimeOffDiagonalWindow
  unfold zetaPrimeOffDiagonalChannel
  exact Finset.sum_congr rfl
    (fun ι _hι =>
      completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical
        ι f)

/-- The finite time-distribution windows exhaust the completed time distribution pairing. -/
theorem finitePrimeTimeDistributionWindow_convolutionAutocorrelation_tendsto_timePairing
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeTimeDistributionPairing
        (convolutionAutocorrelation f))) := by
  have hfun :
      (fun N : ℕ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)) =
        fun N : ℕ => finitePhysicalPrimeOffDiagonalWindow N f := by
    funext N
    exact finitePrimeTimeDistributionWindow_convolutionAutocorrelation_eq_physical
      N f
  have hphysical :
      Tendsto
        (fun N : ℕ => finitePhysicalPrimeOffDiagonalWindow N f)
        atTop
        (𝓝 (completedPhysicalPrimeOffDiagonalChannel f)) :=
    finitePhysicalPrimeOffDiagonalWindow_tendsto_completedPhysicalPrimeOffDiagonalChannel
      f
  have hlimit :
      completedPhysicalPrimeOffDiagonalChannel f =
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) :=
    completedPhysicalPrimeOffDiagonalChannel_eq_timeDistributionPairing f
  have hphysical_time :
      Tendsto
        (fun N : ℕ => finitePhysicalPrimeOffDiagonalWindow N f)
        atTop
        (𝓝 (completedPrimeTimeDistributionPairing
          (convolutionAutocorrelation f))) :=
    Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ => finitePhysicalPrimeOffDiagonalWindow N f)
          atTop
          (𝓝 x))
      hlimit
      hphysical
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop
        (𝓝 (completedPrimeTimeDistributionPairing
          (convolutionAutocorrelation f))))
    hfun.symm
    hphysical_time

/-- Explicit owner gap: the finite contour-transport remainder vanishes at the level of
the chosen finite reconstruction stream.

This is the finite, not asymptotic, residue/contour bookkeeping statement needed to use the
time-side finite window itself as the common finite reconstruction stream. -/
theorem completedPrimeContourRealizedTimeDistributionCoordinate_eq_timeDistributionCoordinate_of_complexCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hcoordinate :
      finitePrimeContourRealizedComplexCoordinate ι (convolutionAutocorrelation f) =
        finitePrimeTimeDistributionComplexCoordinate ι (convolutionAutocorrelation f)) :
    completedPrimeContourRealizedTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) =
      completedPrimeTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) := by
  calc
    completedPrimeContourRealizedTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) =
        Complex.re
          (finitePrimeContourRealizedComplexCoordinate
            ι (convolutionAutocorrelation f)) := by
      exact
        (finitePrimeContourRealizedComplexCoordinate_re_eq_contourRealizedCoordinate
          ι (convolutionAutocorrelation f)).symm
    _ =
        Complex.re
          (finitePrimeTimeDistributionComplexCoordinate
            ι (convolutionAutocorrelation f)) := by
      exact congrArg Complex.re hcoordinate
    _ =
        completedPrimeTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) := by
      exact finitePrimeTimeDistributionComplexCoordinate_re_eq_timeCoordinate
        ι (convolutionAutocorrelation f)

/-- A pointwise equality between the spectral contour sample and the time-boundary sample
identifies the corresponding symmetrized complex prime coordinates. -/
theorem completedPrimeContourRealizedComplexCoordinate_eq_timeComplexCoordinate_of_sample
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hsample :
      zetaCompletedSpectralLaplaceTransform
          (convolutionAutocorrelation f) ι.center =
        zetaCompletedTimeBoundaryValue
          (convolutionAutocorrelation f) ι.center) :
    finitePrimeContourRealizedComplexCoordinate
        ι (convolutionAutocorrelation f) =
      finitePrimeTimeDistributionComplexCoordinate
        ι (convolutionAutocorrelation f) := by
  calc
    finitePrimeContourRealizedComplexCoordinate
        ι (convolutionAutocorrelation f) =
        -((ι.weight : ℂ) *
          (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedSpectralLaplaceTransform
                (convolutionAutocorrelation f) ι.center))) := by
      exact finitePrimeContourRealizedComplexCoordinate_eq
        ι (convolutionAutocorrelation f)
    _ =
        -((ι.weight : ℂ) *
          (zetaCompletedTimeBoundaryValue
              (convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedTimeBoundaryValue
                (convolutionAutocorrelation f) ι.center))) := by
      exact congrArg
        (fun z : ℂ => -((ι.weight : ℂ) * (z + star z)))
        hsample
    _ =
        finitePrimeTimeDistributionComplexCoordinate
          ι (convolutionAutocorrelation f) := by
      exact
        (finitePrimeTimeDistributionComplexCoordinate_eq
          ι (convolutionAutocorrelation f)).symm

/-- A coordinatewise contour/time transport identity cancels the corresponding
contour-transport remainder coordinate. -/
theorem completedPrimeContourTransportCoordinateRemainderFamily_eq_zero_of_coordinate_transport
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hcoordinate :
      completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) =
        completedPrimeTimeDistributionCoordinate
          ι (convolutionAutocorrelation f)) :
    completedPrimeContourTransportCoordinateRemainderFamily f ι = 0 := by
  calc
    completedPrimeContourTransportCoordinateRemainderFamily f ι =
        completedPrimeContourTransportCoordinateRemainder ι f := by
      exact completedPrimeContourTransportCoordinateRemainderFamily_apply ι f
    _ =
        completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) -
          completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) := by
      exact completedPrimeContourTransportCoordinateRemainder_eq_contour_sub_time
        ι f
    _ =
        completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) -
          completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) := by
      exact congrArg
        (fun x : ℝ =>
          x -
            completedPrimeTimeDistributionCoordinate
              ι (convolutionAutocorrelation f))
        hcoordinate
    _ = 0 := by
      exact sub_self
        (completedPrimeTimeDistributionCoordinate
          ι (convolutionAutocorrelation f))

/-- A coordinatewise cancellation on the selected finite prime-power window cancels the
finite contour-transport coordinate-remainder window. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_zero_of_coordinatewise
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hcoordinate :
      ∀ ι : ZetaPrimePowerIndex,
        ι ∈ ZetaPrimePowerIndex.window N →
          completedPrimeContourTransportCoordinateRemainderFamily f ι = 0) :
    finitePrimeContourTransportCoordinateRemainderWindow N f = 0 := by
  calc
    finitePrimeContourTransportCoordinateRemainderWindow N f =
        ∑ ι in ZetaPrimePowerIndex.window N,
          completedPrimeContourTransportCoordinateRemainderFamily f ι := by
      exact finitePrimeContourTransportCoordinateRemainderWindow_eq_windowSum N f
    _ = 0 := by
      exact Finset.sum_eq_zero hcoordinate

/-- A finite time/log window equality cancels the finite contour-transport remainder
window by the owner remainder accounting identity. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_zero_of_window_eq
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hwindow :
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) =
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f)) :
    finitePrimeContourTransportCoordinateRemainderWindow N f = 0 := by
  let T : ℝ := finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)
  let C : ℝ :=
    finitePrimeContourRealizedTimeDistributionWindow N
      (convolutionAutocorrelation f)
  let R : ℝ := finitePrimeContourTransportCoordinateRemainderWindow N f
  have hsum : T + R = C := by
    unfold T
    unfold C
    unfold R
    exact finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow N f
  have hC_eq_T : C = T := by
    unfold T
    unfold C
    exact hwindow.symm
  have hsum_eq_T : T + R = T := hsum.trans hC_eq_T
  have hleft :
    -T + (T + R) = R := by
    calc
      -T + (T + R) = (-T + T) + R := by
        exact (add_assoc (-T) T R).symm
      _ = 0 + R := by
        exact congrArg (fun x : ℝ => x + R) (neg_add_cancel T)
      _ = R := by
        exact zero_add R
  have hright :
      -T + T = 0 := by
    exact neg_add_cancel T
  have htransport :
      -T + (T + R) = -T + T := by
    exact congrArg (fun x : ℝ => -T + x) hsum_eq_T
  calc
    R = -T + (T + R) := by
      exact hleft.symm
    _ = -T + T := by
      exact htransport
    _ = 0 := by
      exact hright

/-- The finite contour-realized prime window of an autocorrelation is the finite spectral
prime off-diagonal window. -/
theorem finitePrimeContourRealizedTimeDistributionWindow_convolutionAutocorrelation_eq_spectral
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) =
      finiteSpectralPrimeOffDiagonalWindow N f := by
  unfold finitePrimeContourRealizedTimeDistributionWindow
  unfold finiteSpectralPrimeOffDiagonalWindow
  exact congrArg Complex.re
    (Finset.sum_congr rfl
      (fun ι _hι =>
        congrArg
          (fun z : ℂ => -((ι.weight : ℂ) * (z + star z)))
            ((congrFun
              (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform
                (convolutionAutocorrelation f))
              ι.center).symm)))

/-- The spectral off-diagonal coordinate is the contour-realized coordinate after the
completed spectral transform is identified with the explicit-formula transform. -/
theorem zetaSpectralPrimeOffDiagonalCoordinate_eq_contourRealizedCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaSpectralPrimeOffDiagonalCoordinate ι f =
      completedPrimeContourRealizedTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) := by
  have hΦ :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) ι.center =
        zetaCompletedSpectralLaplaceTransform
          (convolutionAutocorrelation f) ι.center := by
    exact
      congrFun
        (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform
          (convolutionAutocorrelation f))
        ι.center
  calc
    zetaSpectralPrimeOffDiagonalCoordinate ι f =
        Complex.re
          (-((ι.weight : ℂ) *
            (zetaCompletedExplicitFormulaPhi
                (convolutionAutocorrelation f) ι.center +
              star
                (zetaCompletedExplicitFormulaPhi
                  (convolutionAutocorrelation f) ι.center)))) := by
      rfl
    _ =
        Complex.re
          (-((ι.weight : ℂ) *
            (zetaCompletedSpectralLaplaceTransform
                (convolutionAutocorrelation f) ι.center +
              star
                (zetaCompletedSpectralLaplaceTransform
                  (convolutionAutocorrelation f) ι.center)))) := by
      exact congrArg
        (fun z : ℂ =>
          Complex.re (-((ι.weight : ℂ) * (z + star z))))
        hΦ
    _ =
        completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) := by
      rfl

/-- The autocorrelation time-side prime coordinate unfolds to the signed real
symmetrized logarithmic-boundary coefficient. -/
theorem completedPrimeAutocorrelationTimeCoordinate_eq_weightedTimeBoundarySample
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) =
      -(ι.weight *
        Complex.re
          (zetaCompletedTimeBoundaryValue
              (convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedTimeBoundaryValue
                (convolutionAutocorrelation f) ι.center))) := by
  rfl

/-- The contour-realized prime coordinate unfolds to the real part of the signed spectral
sample coefficient. -/
theorem completedPrimeContourRealizedCoordinate_eq_weightedSpectralSample
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionCoordinate
        ι (convolutionAutocorrelation f) =
      Complex.re
        (-((ι.weight : ℂ) *
          (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedSpectralLaplaceTransform
                (convolutionAutocorrelation f) ι.center)))) := by
  rfl

/-- The real part of the owner Hermitian symmetrization is twice the real part of the
sample. -/
theorem complex_re_add_star_eq_two_re
    (z : ℂ) :
    Complex.re (z + star z) = 2 * Complex.re z := by
  have hadd :
      Complex.re (z + star z) = Complex.re z + Complex.re (star z) := by
    exact Complex.add_re z (star z)
  have hstar :
      Complex.re (star z) = Complex.re z := by
    rfl
  calc
    Complex.re (z + star z) =
        Complex.re z + Complex.re (star z) := hadd
    _ = Complex.re z + Complex.re z := by
      exact congrArg (fun x : ℝ => Complex.re z + x) hstar
    _ = 2 * Complex.re z := by
      exact (two_mul (Complex.re z)).symm

/-- The time-side symmetrized autocorrelation sample is twice the real translated
autocorrelation inner product. -/
theorem completedPrimeAutocorrelationSymmetrizedTimeSample_re_eq_two_translateInner
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedTimeBoundaryValue
            (convolutionAutocorrelation f) ι.center +
          star
            (zetaCompletedTimeBoundaryValue
              (convolutionAutocorrelation f) ι.center)) =
      2 * Complex.re (zetaSeedInner (zetaTranslate ι.center f) f) := by
  have htime :
      zetaCompletedTimeBoundaryValue
          (convolutionAutocorrelation f) ι.center =
        convolutionAutocorrelationKernel f ι.center :=
    zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_eq_kernel f ι.center
  have hsum :
      zetaCompletedTimeBoundaryValue
          (convolutionAutocorrelation f) ι.center +
        star
          (zetaCompletedTimeBoundaryValue
            (convolutionAutocorrelation f) ι.center) =
        convolutionAutocorrelationKernel f ι.center +
          star (convolutionAutocorrelationKernel f ι.center) := by
    exact congrArg₂ HAdd.hAdd htime (congrArg star htime)
  have hneg :
      convolutionAutocorrelationKernel f (-ι.center) =
        star (convolutionAutocorrelationKernel f ι.center) :=
    convolutionAutocorrelationKernel_neg_eq_conj f ι.center
  calc
    Complex.re
        (zetaCompletedTimeBoundaryValue
            (convolutionAutocorrelation f) ι.center +
          star
            (zetaCompletedTimeBoundaryValue
              (convolutionAutocorrelation f) ι.center)) =
        Complex.re
          (convolutionAutocorrelationKernel f ι.center +
            star (convolutionAutocorrelationKernel f ι.center)) := by
      exact congrArg Complex.re hsum
    _ =
        Complex.re
          (convolutionAutocorrelationKernel f ι.center +
            convolutionAutocorrelationKernel f (-ι.center)) := by
      exact congrArg
        (fun z : ℂ =>
          Complex.re (convolutionAutocorrelationKernel f ι.center + z))
        hneg.symm
    _ = 2 * Complex.re (zetaSeedInner (zetaTranslate ι.center f) f) := by
      exact convolutionAutocorrelationKernel_add_neg_eq_two_re_translateInner
        f ι.center

/-- The natural two-face boundary sample of a convolution-autocorrelation probe
reduces to the Hermitian time-boundary sum at the positive natural center.

This is the acyclic bridge from the Hilbert/autocorrelation symmetry theorem
to the vertical-channel natural-prime arithmetic owner.  It still does not
identify this two-face presentation with the vertical-channel `TimeSummand`;
that remaining comparison owns the explicit-formula constants. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_convolutionAutocorrelation_of_ne_zero
    (seed : ZetaAdmissibleFunction) {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample
        (convolutionAutocorrelation seed) n =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          (zetaCompletedTimeBoundaryValue
              (convolutionAutocorrelation seed)
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
            star
              (zetaCompletedTimeBoundaryValue
                (convolutionAutocorrelation seed)
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) := by
  let a : ℝ := zetaCompletedExplicitFormulaPrimeNaturalCenter n
  have hpos :
      zetaCompletedTimeBoundaryValue (convolutionAutocorrelation seed) a =
        convolutionAutocorrelationKernel seed a :=
    zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_eq_kernel seed a
  have hneg_time :
      zetaCompletedTimeBoundaryValue (convolutionAutocorrelation seed) (-a) =
        convolutionAutocorrelationKernel seed (-a) :=
    zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_eq_kernel seed (-a)
  have hneg_kernel :
      convolutionAutocorrelationKernel seed (-a) =
        star (convolutionAutocorrelationKernel seed a) :=
    convolutionAutocorrelationKernel_neg_eq_conj seed a
  have hreflect :
      zetaCompletedTimeBoundaryValue
          (convolutionAutocorrelation seed)
          (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)) =
        star
          (zetaCompletedTimeBoundaryValue
            (convolutionAutocorrelation seed)
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) := by
    calc
      zetaCompletedTimeBoundaryValue
          (convolutionAutocorrelation seed)
          (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)) =
          zetaCompletedTimeBoundaryValue
            (convolutionAutocorrelation seed) (-a) := by
        rfl
      _ = convolutionAutocorrelationKernel seed (-a) := hneg_time
      _ = star (convolutionAutocorrelationKernel seed a) := hneg_kernel
      _ =
          star
            (zetaCompletedTimeBoundaryValue
              (convolutionAutocorrelation seed)
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) := by
        exact congrArg star hpos.symm
  exact
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_of_ne_zero_of_reflectionDagger
      (convolutionAutocorrelation seed) hn hreflect

/-- The spectral symmetrized autocorrelation sample is twice the real part of the paired
seed spectral sample. -/
theorem completedPrimeAutocorrelationSymmetrizedSpectralSample_re_eq_two_pairedSample
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedSpectralLaplaceTransform
            (convolutionAutocorrelation f) ι.center +
          star
            (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f) ι.center)) =
      2 *
        Complex.re
          (zetaCompletedSpectralLaplaceTransform f ι.center *
            star
              (zetaCompletedSpectralLaplaceTransform f (-(ι.center : ℂ)))) := by
  let P : ℂ :=
    zetaCompletedSpectralLaplaceTransform f ι.center *
      star (zetaCompletedSpectralLaplaceTransform f (-(ι.center : ℂ)))
  have hfactor :
      zetaCompletedSpectralLaplaceTransform
          (convolutionAutocorrelation f) ι.center = P := by
    unfold P
    calc
      zetaCompletedSpectralLaplaceTransform
          (convolutionAutocorrelation f) ι.center =
          zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) ι.center := by
        exact
          (congrFun
            (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform
              (convolutionAutocorrelation f))
            ι.center).symm
      _ =
          zetaCompletedExplicitFormulaPhi f ι.center *
            star
              (zetaCompletedExplicitFormulaPhi f (-(ι.center : ℂ))) := by
        exact zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair
          f ι.center
      _ =
          zetaCompletedSpectralLaplaceTransform f ι.center *
            star
              (zetaCompletedExplicitFormulaPhi f (-(ι.center : ℂ))) := by
        exact congrArg
          (fun z : ℂ =>
            z *
              star
                (zetaCompletedExplicitFormulaPhi f (-(ι.center : ℂ))))
          (congrFun
            (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform f)
            ι.center)
      _ =
          zetaCompletedSpectralLaplaceTransform f ι.center *
            star
              (zetaCompletedSpectralLaplaceTransform f (-(ι.center : ℂ))) := by
        exact congrArg
          (fun z : ℂ =>
            zetaCompletedSpectralLaplaceTransform f ι.center * star z)
          (congrFun
            (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform f)
            (-(ι.center : ℂ)))
  calc
    Complex.re
        (zetaCompletedSpectralLaplaceTransform
            (convolutionAutocorrelation f) ι.center +
          star
            (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f) ι.center)) =
        Complex.re (P + star P) := by
      exact congrArg Complex.re
        (congrArg₂ HAdd.hAdd hfactor (congrArg star hfactor))
    _ = 2 * Complex.re P := by
      exact complex_re_add_star_eq_two_re P
    _ =
        2 *
          Complex.re
            (zetaCompletedSpectralLaplaceTransform f ι.center *
            star
              (zetaCompletedSpectralLaplaceTransform f (-(ι.center : ℂ)))) := by
      rfl

/-- The translated seed inner product is the uncentered autocorrelation kernel. -/
theorem completedPrimeAutocorrelationTranslateInner_re_eq_kernel_re
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    Complex.re (zetaSeedInner (zetaTranslate a f) f) =
      Complex.re (convolutionAutocorrelationKernel f a) := by
  have hkernel :
      convolutionAutocorrelationKernel f a =
        zetaSeedInner (zetaTranslate a f) f :=
    convolutionAutocorrelationKernel_eq_translateInner f a
  exact congrArg Complex.re hkernel.symm

/-- The paired `Φ` sample is the `Φ` sample of the autocorrelation probe. -/
theorem completedPrimePairedPhiSample_re_eq_autocorrelationPhi_re
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaPhi f (a : ℂ) *
          star
            (zetaCompletedExplicitFormulaPhi f (-(a : ℂ)))) =
      Complex.re
        (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) (a : ℂ)) := by
  have hphi :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) (a : ℂ) =
        zetaCompletedExplicitFormulaPhi f (a : ℂ) *
          star
            (zetaCompletedExplicitFormulaPhi f (-(a : ℂ))) :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair f a
  exact congrArg Complex.re hphi.symm

/-- The autocorrelation kernel is the time-boundary value of the convolution autocorrelation
probe, transported to real parts. -/
theorem completedPrimeAutocorrelationKernel_re_eq_timeBoundaryValue_re
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    Complex.re (convolutionAutocorrelationKernel f a) =
      Complex.re
        (zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) a) := by
  have htime :
    zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) a =
        convolutionAutocorrelationKernel f a :=
    zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_eq_kernel f a
  exact congrArg Complex.re htime.symm

/-!
The former HS:1903 pointwise Plancherel chain has been removed from this owner surface.
It asserted a false pointwise identification between the time-side autocorrelation kernel and
real-axis Laplace samples.  The finite physical and contour-realized prime windows are not
identified directly; the honest finite relation keeps the contour-transport remainder visible.
-/

/-- Finite prime transport is the additive remainder accounting identity between the time/log
window and the contour-realized spectral window. -/
theorem finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow_ownerPrimeTransport
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportCoordinateRemainderWindow N f =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) := by
  exact finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow N f

/-- The selected finite coordinate-remainder window remains as the exact additive difference
between the time/log and contour-realized prime windows. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_ownerTransport
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportCoordinateRemainderWindow N f =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) := by
  exact
    finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow_ownerPrimeTransport
      N f

/-- Finite time/log and contour-realized windows are related by the named additive
coordinate-remainder transport. -/
theorem finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow_coordinateRemainderTransport
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportCoordinateRemainderWindow N f =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) := by
  exact
    finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow_ownerPrimeTransport
      N f

/-- The completed two-face boundary coefficient has the opposite real scalar from the finite
reconstructed prime convolution contribution.

This is the signed finite/completed normalization for the prime two-face packet.  The
boundary coefficient is the explicit-formula signed coefficient, while the reconstructed
prime convolution contribution is the GNS two-face matrix coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_re_eq_neg_primeConvolutionContribution_re
    (f : ZetaAdmissibleFunction)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  let Tc : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let Tf : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  have hboundary :
      zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f = -Tc := by
    unfold Tc
    exact zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient f
  have hcontribution :
      zetaCompletedExplicitFormulaPrimeConvolutionContribution f = Tf := by
    unfold Tf
    exact zetaCompletedExplicitFormulaPrimeConvolutionContribution_eq_twoFaceMatrixCoefficient
      f
  calc
    Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) =
        Complex.re (-Tc) := by
      exact congrArg Complex.re hboundary
    _ = -Complex.re Tc := by
      exact Complex.neg_re Tc
    _ = -Complex.re Tf := by
      exact congrArg Neg.neg hmatrix
    _ = -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
      exact congrArg Neg.neg (congrArg Complex.re hcontribution.symm)

/-- Explicit owner gap: the completed time-side prime off-diagonal channel agrees with the
signed reconstructed prime convolution contribution after the summed completed explicit-formula
transport has replaced the legacy finite physical/spectral window equality. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have htransport :
      completedPrimeOffDiagonalChannel f =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    completedPrimeOffDiagonalChannel_eq_completedTwoFaceGNSBoundaryCoefficient_re_ownerDistributionTransport
      f D
  have hsigned :
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_re_eq_neg_primeConvolutionContribution_re
      f hmatrix
  exact htransport.trans hsigned

/-- The completed time-side prime off-diagonal channel agrees with the signed reconstructed
prime convolution contribution using the explicit summed contour/time transport provider. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have htransport :
      completedPrimeOffDiagonalChannel f =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    completedPrimeOffDiagonalChannel_eq_completedTwoFaceGNSBoundaryCoefficient_re_ownerSummedDistributionTransport
      f D
  have hsigned :
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_re_eq_neg_primeConvolutionContribution_re
      f hmatrix
  exact htransport.trans hsigned

/-- A completed off-diagonal reconstruction bridge gives the completed-vs-finite GNS
real-coefficient comparison.

This is the forward implication in the genuine completed-to-finite prime bridge: the completed
two-face coefficient is first transported to the completed off-diagonal channel, and the
finite side is then identified with the reconstructed prime convolution packet. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_finite_of_completedPrimeOffDiagonalBridge
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hbridge :
      completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f)) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  have hcompleted :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        -completedPrimeOffDiagonalChannel f :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedPrimeOffDiagonalChannel_ownerDistributionTransport
      f D
  have hfinite :
      Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
    zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_twoFaceMatrixCoefficient
      f
  calc
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        -completedPrimeOffDiagonalChannel f := by
      exact hcompleted
    _ = -(-Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f)) := by
      exact congrArg Neg.neg hbridge
    _ = Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
      exact neg_neg
        (Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f))
    _ = Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
      exact hfinite

/-- The visible-remainder summed transport version of the completed off-diagonal bridge
to the completed-vs-finite GNS real-coefficient comparison. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_finite_of_completedPrimeOffDiagonalBridge_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hbridge :
      completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f)) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  have hcompleted :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        -completedPrimeOffDiagonalChannel f :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedPrimeOffDiagonalChannel_ownerSummedDistributionTransport
      f D
  have hfinite :
      Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
    zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_twoFaceMatrixCoefficient
      f
  calc
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        -completedPrimeOffDiagonalChannel f := by
      exact hcompleted
    _ = -(-Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f)) := by
      exact congrArg Neg.neg hbridge
    _ = Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
      exact neg_neg
        (Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f))
    _ = Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
      exact hfinite

/-- The completed off-diagonal bridge to the finite reconstructed prime two-face packet is
equivalent to the completed-vs-finite GNS real-coefficient comparison.

The forward direction recovers the coefficient comparison from the transported completed
two-face sign and the finite convolution reconstruction.  The reverse direction is the
previous signed normalization. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_matrixComparison
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  constructor
  · intro hbridge
    exact
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_finite_of_completedPrimeOffDiagonalBridge
        f D hbridge
  · intro hmatrix
    exact completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re
      f D hmatrix

/-- The visible-remainder summed transport version of the completed off-diagonal bridge
equivalence. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_matrixComparison_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  constructor
  · intro hbridge
    exact
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_finite_of_completedPrimeOffDiagonalBridge_summedTransport
        f D hbridge
  · intro hmatrix
    exact completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_summedTransport
      f D hmatrix

/-- The prime boundary channel agrees with the signed reconstructed prime convolution
contribution once the completed time-distribution normalization is supplied. -/
theorem primeBoundaryChannel_convolutionAutocorrelation_re_eq_neg_primeConvolutionContribution
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have hboundary :
      completedPrimeOffDiagonalChannel f =
        Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) :=
    completedPrimeOffDiagonalChannel_eq_primeBoundaryChannel f
  have hnormalization :
      completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) :=
    completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re f D hmatrix
  exact hboundary.symm.trans hnormalization

/-- The prime boundary channel agrees with the signed reconstructed prime convolution
contribution from the explicit summed contour/time transport provider. -/
theorem primeBoundaryChannel_convolutionAutocorrelation_re_eq_neg_primeConvolutionContribution_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have hboundary :
      completedPrimeOffDiagonalChannel f =
        Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) :=
    completedPrimeOffDiagonalChannel_eq_primeBoundaryChannel f
  have hnormalization :
      completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) :=
    completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_summedTransport
      f D hmatrix
  exact hboundary.symm.trans hnormalization

/-- The finite prime diagonal-debt real scalar cancels in the completed two-face
normalization. -/
theorem zetaPrimeDefectKernelDiagonalDebt_re_eq_zero_of_lowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeDefectKernelDiagonalDebt f) = 0 := by
  exact
    zetaPrimeDefectKernelDiagonalDebt_re_eq_zero_of_completedLowerWeightNormalization
      f

/-- The reconstructed prime two-face channel has the opposite real scalar from the positive
prime-defect channel under lower-weight normalization. -/
theorem zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_positiveChannel_of_lowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) =
      -completedPrimeDefectKernelPositiveChannel f := by
  let P : ℝ := completedPrimeDefectKernelPositiveChannel f
  let T : ℝ := Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)
  have hpositive :
      P = Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
    unfold P
    exact completedPrimeDefectKernelPositiveChannel_eq_finitePositiveForm_re f
  have hexpansion :
      Complex.re (zetaPrimeDefectKernelPositiveForm f) +
          Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeDefectKernelDiagonalDebt f) :=
    zetaPrimeDefectKernelPositiveForm_re_add_twoFace_re_eq_diagonalDebt_re f
  have hdebt :
      Complex.re (zetaPrimeDefectKernelDiagonalDebt f) = 0 :=
    zetaPrimeDefectKernelDiagonalDebt_re_eq_zero_of_lowerWeightNormalization f
  have hsum :
      P + T = 0 := by
    calc
      P + T =
          Complex.re (zetaPrimeDefectKernelPositiveForm f) +
            Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
        exact congrArg
          (fun x : ℝ =>
            x + Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f))
          hpositive
      _ = Complex.re (zetaPrimeDefectKernelDiagonalDebt f) := by
        exact hexpansion
      _ = 0 := by
        exact hdebt
  have hsum_comm : T + P = 0 := by
    exact (add_comm T P).trans hsum
  have hsigned : T = -P :=
    eq_neg_of_add_eq_zero_left hsum_comm
  exact hsigned

/-- The explicit prime convolution contribution inherits the signed two-face normalization. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_neg_positiveChannel_of_lowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      -completedPrimeDefectKernelPositiveChannel f := by
  have htwoFace :
      Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
    zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_twoFaceMatrixCoefficient
      f
  have hsigned :
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) =
        -completedPrimeDefectKernelPositiveChannel f :=
    zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_positiveChannel_of_lowerWeightNormalization
      f
  exact htwoFace.trans hsigned

/-- The actual completed off-diagonal reconstruction bridge is equivalent to identifying the
completed off-diagonal prime channel with the positive prime-defect channel.

This isolates the remaining prime-only limit theorem: the finite reconstructed convolution
packet has real scalar `-completedPrimeDefectKernelPositiveChannel`, so the completed bridge
is exactly the assertion that the completed off-diagonal limit is the same positive channel. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_positiveChannel
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) ↔
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f := by
  constructor
  · intro hbridge
    have hfinite :
        Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
          -completedPrimeDefectKernelPositiveChannel f :=
      zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_neg_positiveChannel_of_lowerWeightNormalization
        f
    calc
      completedPrimeOffDiagonalChannel f =
          -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
        exact hbridge
      _ = -(-completedPrimeDefectKernelPositiveChannel f) := by
        exact congrArg Neg.neg hfinite
      _ = completedPrimeDefectKernelPositiveChannel f := by
        exact neg_neg (completedPrimeDefectKernelPositiveChannel f)
  · intro hpositive
    have hfinite :
        Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
          -completedPrimeDefectKernelPositiveChannel f :=
      zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_neg_positiveChannel_of_lowerWeightNormalization
        f
    calc
      completedPrimeOffDiagonalChannel f =
          completedPrimeDefectKernelPositiveChannel f := by
        exact hpositive
      _ = -(-completedPrimeDefectKernelPositiveChannel f) := by
        exact (neg_neg (completedPrimeDefectKernelPositiveChannel f)).symm
      _ = -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
        exact congrArg Neg.neg hfinite.symm

/-- The remaining prime-only completed limit theorem implies the completed off-diagonal
reconstruction bridge. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_positiveChannel
    (f : ZetaAdmissibleFunction)
    (hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  exact
    (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_positiveChannel
      f).mpr hpositive

/-- The completed off-diagonal/positive-channel comparison is equivalent to the
completed-vs-finite two-face GNS real-coefficient comparison. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_matrixComparison
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact
    (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_positiveChannel
      f).symm.trans
      (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_matrixComparison
        f D)

/-- The summed-transport version of the completed off-diagonal/positive-channel comparison
equivalence with the completed-vs-finite two-face GNS real-coefficient comparison. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_matrixComparison_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact
    (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_positiveChannel
      f).symm.trans
      (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_matrixComparison_of_summedTransport
        f D)

/-- The completed-vs-finite two-face GNS real-coefficient comparison gives the
completed off-diagonal/positive-channel comparison. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_of_matrixComparison
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_matrixComparison
      f D).mpr
      hmatrix

/-- The summed-transport version: the completed-vs-finite two-face GNS real-coefficient
comparison gives the completed off-diagonal/positive-channel comparison. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_of_matrixComparison_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_matrixComparison_of_summedTransport
      f D).mpr
      hmatrix

/-- Under the current finite-display lower-weight normalization, the completed-vs-finite
two-face GNS real-coefficient comparison is exactly vanishing of the completed two-face real
coefficient. -/
theorem matrixComparison_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero
    (f : ZetaAdmissibleFunction) :
    (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  constructor
  · intro hmatrix
    calc
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
          Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
        exact hmatrix
      _ = 0 := by
        exact zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
          f
  · intro hzero
    calc
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
        exact hzero
      _ = Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
        exact
          (zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
            f).symm

/-- Under the current finite-display lower-weight normalization, the completed
off-diagonal/positive-channel comparison is equivalent to vanishing of the completed two-face
real coefficient. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_matrixComparison
      f D).trans
      (matrixComparison_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero f)

/-- Summed-transport version of the lower-weight normalized two-face vanishing criterion for
the completed off-diagonal/positive-channel comparison. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_matrixComparison_of_summedTransport
      f D).trans
      (matrixComparison_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero f)

/-- Under the current finite-display lower-weight normalization, the completed
off-diagonal/positive-channel comparison is equivalent to vanishing of the completed
off-diagonal channel itself. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_completedPrimeOffDiagonalChannel_eq_zero
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f ↔
      completedPrimeOffDiagonalChannel f = 0 := by
  constructor
  · intro hpositive
    calc
      completedPrimeOffDiagonalChannel f =
          completedPrimeDefectKernelPositiveChannel f := by
        exact hpositive
      _ = 0 := by
        exact completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
          f
  · intro hoffZero
    calc
      completedPrimeOffDiagonalChannel f = 0 := by
        exact hoffZero
      _ = completedPrimeDefectKernelPositiveChannel f := by
        exact
          (completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
            f).symm

/-- Under summed transport, vanishing of the completed two-face real scalar is equivalent to
vanishing of the completed off-diagonal channel. -/
theorem completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_iff_completedPrimeOffDiagonalChannel_eq_zero_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 ↔
      completedPrimeOffDiagonalChannel f = 0 := by
  have htwoFace :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        -completedPrimeOffDiagonalChannel f :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedPrimeOffDiagonalChannel_ownerSummedDistributionTransport
      f D
  constructor
  · intro hzero
    have hneg_zero : -completedPrimeOffDiagonalChannel f = 0 :=
      htwoFace.symm.trans hzero
    calc
      completedPrimeOffDiagonalChannel f =
          -(-completedPrimeOffDiagonalChannel f) := by
        exact (neg_neg (completedPrimeOffDiagonalChannel f)).symm
      _ = -0 := by
        exact congrArg Neg.neg hneg_zero
      _ = 0 := by
        exact neg_zero
  · intro hoffZero
    calc
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
          -completedPrimeOffDiagonalChannel f := by
        exact htwoFace
      _ = -0 := by
        exact congrArg Neg.neg hoffZero
      _ = 0 := by
        exact neg_zero

/-- Under summed transport and the current finite-display lower-weight normalization, the
completed-vs-finite matrix comparison is equivalent to vanishing of the completed
off-diagonal channel. -/
theorem matrixComparison_iff_completedPrimeOffDiagonalChannel_eq_zero_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) ↔
      completedPrimeOffDiagonalChannel f = 0 := by
  exact
    (matrixComparison_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero
      f).trans
      (completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_iff_completedPrimeOffDiagonalChannel_eq_zero_of_summedTransport
        f D)

/-- Under summed transport and lower-weight normalization, the completed off-diagonal
reconstruction bridge is exactly vanishing of the completed off-diagonal channel. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_completedPrimeOffDiagonalChannel_eq_zero_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) ↔
      completedPrimeOffDiagonalChannel f = 0 := by
  exact
    (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_matrixComparison_of_summedTransport
      f D).trans
      (matrixComparison_iff_completedPrimeOffDiagonalChannel_eq_zero_of_summedTransport
        f D)

/-- Summed transport turns vanishing of the completed off-diagonal channel into the
completed off-diagonal reconstruction bridge. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_completedPrimeOffDiagonalChannel_eq_zero_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hoffZero : completedPrimeOffDiagonalChannel f = 0) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  exact
    (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_completedPrimeOffDiagonalChannel_eq_zero_summedTransport
      f D).mpr
      hoffZero

/-- The completed off-diagonal/positive-channel comparison is exactly the assertion that the
absorbed finite prime defect-square windows converge to the completed Hermitian positive
prime channel.

The square-ledger owner already proves that the same absorbed finite windows converge to the
completed off-diagonal channel.  This theorem is therefore pure uniqueness of the completed
finite-window limit, not a new reconstruction provider. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_absorbedPrimeDefectSquare_tendsto
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f ↔
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  constructor
  · intro hpositive
    have hoff :
        Tendsto
          (fun N : ℕ =>
            zetaPrimeTranslationDefectEnergy N f +
              finitePartDebtAbsorptionWindow N f)
          atTop
          (𝓝 (completedPrimeOffDiagonalChannel f)) :=
      zetaPrimeTranslationDefectEnergy_add_debtAbsorption_tendsto_completedPrimeOffDiagonalChannel
        f
    exact Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            zetaPrimeTranslationDefectEnergy N f +
              finitePartDebtAbsorptionWindow N f)
          atTop
          (𝓝 x))
      hpositive
      hoff
  · intro hpositiveLimit
    have hoff :
        Tendsto
          (fun N : ℕ =>
            zetaPrimeTranslationDefectEnergy N f +
              finitePartDebtAbsorptionWindow N f)
          atTop
          (𝓝 (completedPrimeOffDiagonalChannel f)) :=
      zetaPrimeTranslationDefectEnergy_add_debtAbsorption_tendsto_completedPrimeOffDiagonalChannel
        f
    exact tendsto_nhds_unique hoff hpositiveLimit

/-- The completed-vs-finite two-face GNS real-coefficient comparison supplies the positive
owner limit for the absorbed finite prime defect-square stream. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_of_matrixComparison
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  have hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeOffDiagonalChannel_eq_positiveChannel_of_matrixComparison
      f D hmatrix
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_absorbedPrimeDefectSquare_tendsto
      f).mp
      hpositive

/-- The summed-transport version of the positive owner limit for the absorbed finite prime
defect-square stream from the completed-vs-finite two-face GNS real comparison. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_of_matrixComparison_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  have hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeOffDiagonalChannel_eq_positiveChannel_of_matrixComparison_summedTransport
      f D hmatrix
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_absorbedPrimeDefectSquare_tendsto
      f).mp
      hpositive

/-- Vanishing of the completed two-face real coefficient supplies the positive owner limit
for the absorbed finite prime defect-square stream. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_of_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (htwoFaceZero :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  have hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
    (matrixComparison_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero
      f).mpr
      htwoFaceZero
  exact absorbedPrimeDefectSquare_tendsto_positiveChannel_of_matrixComparison
    f D hmatrix

/-- Summed-transport version: vanishing of the completed two-face real coefficient supplies
the positive owner limit for the absorbed finite prime defect-square stream. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_of_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (htwoFaceZero :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  have hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
    (matrixComparison_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero
      f).mpr
      htwoFaceZero
  exact absorbedPrimeDefectSquare_tendsto_positiveChannel_of_matrixComparison_summedTransport
    f D hmatrix

/-- Vanishing of the completed off-diagonal channel supplies the positive owner limit for the
absorbed finite prime defect-square stream under the current lower-weight normalization. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_of_completedPrimeOffDiagonalChannel_eq_zero
    (f : ZetaAdmissibleFunction)
    (hoffZero : completedPrimeOffDiagonalChannel f = 0) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  have hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_completedPrimeOffDiagonalChannel_eq_zero
      f).mpr
      hoffZero
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_absorbedPrimeDefectSquare_tendsto
      f).mp
      hpositive

/-- Under the current finite-display lower-weight normalization, the positive owner limit for
the absorbed finite prime defect-square stream is equivalent to vanishing of the completed
off-diagonal channel. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_iff_completedPrimeOffDiagonalChannel_eq_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) ↔
      completedPrimeOffDiagonalChannel f = 0 := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_absorbedPrimeDefectSquare_tendsto
      f).symm.trans
      (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_completedPrimeOffDiagonalChannel_eq_zero
        f)

/-- With summed transport, the positive owner limit for the absorbed finite prime
defect-square stream is equivalent to vanishing of the completed two-face real coefficient. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  exact
    (absorbedPrimeDefectSquare_tendsto_positiveChannel_iff_completedPrimeOffDiagonalChannel_eq_zero
      f).trans
      (completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_iff_completedPrimeOffDiagonalChannel_eq_zero_of_summedTransport
        f D).symm

/-- With summed transport, the positive owner limit for the absorbed finite prime
defect-square stream is equivalent to the completed off-diagonal reconstruction bridge. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_iff_completedPrimeOffDiagonalBridge_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) ↔
      completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  exact
    (absorbedPrimeDefectSquare_tendsto_positiveChannel_iff_completedPrimeOffDiagonalChannel_eq_zero
      f).trans
      (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_completedPrimeOffDiagonalChannel_eq_zero_summedTransport
        f D).symm

/-- The same square-ledger uniqueness statement with the raw completed positive
prime-power coordinate presentation as target. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_absorbedPrimeDefectSquare_tendsto
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f ↔
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) := by
  constructor
  · intro hcoordinate
    have hoff :
        Tendsto
          (fun N : ℕ =>
            zetaPrimeTranslationDefectEnergy N f +
              finitePartDebtAbsorptionWindow N f)
          atTop
          (𝓝 (completedPrimeOffDiagonalChannel f)) :=
      zetaPrimeTranslationDefectEnergy_add_debtAbsorption_tendsto_completedPrimeOffDiagonalChannel
        f
    exact Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            zetaPrimeTranslationDefectEnergy N f +
              finitePartDebtAbsorptionWindow N f)
          atTop
          (𝓝 x))
      hcoordinate
      hoff
  · intro hcoordinateLimit
    have hoff :
        Tendsto
          (fun N : ℕ =>
            zetaPrimeTranslationDefectEnergy N f +
              finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (completedPrimeOffDiagonalChannel f)) :=
      zetaPrimeTranslationDefectEnergy_add_debtAbsorption_tendsto_completedPrimeOffDiagonalChannel
        f
    exact tendsto_nhds_unique hoff hcoordinateLimit

/-- If the absorbed finite prime defect-square stream converges to the raw positive
coordinate presentation, then the completed off-diagonal channel is that presentation. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_absorbedPrimeDefectSquare_tendsto
    (f : ZetaAdmissibleFunction)
    (hcoordinateLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f))) :
    completedPrimeOffDiagonalChannel f =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_absorbedPrimeDefectSquare_tendsto
      f).mpr
      hcoordinateLimit

/-- Positive completed prime-power windows identify the raw positive coordinate presentation
with the owner positive channel by uniqueness of finite-window limits. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_positiveRealWindow_tendsto
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hpositiveLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f))) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f := by
  have hcoordinateLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
      f hmajorant
  exact tendsto_nhds_unique hcoordinateLimit hpositiveLimit

/-- The absorbed finite prime defect-square stream identifies the off-diagonal channel with
the owner positive channel once it has the owner positive-channel limit. -/
theorem completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_of_absorbedPrimeDefectSquare_tendsto
    (f : ZetaAdmissibleFunction)
    (hpositiveLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f))) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_absorbedPrimeDefectSquare_tendsto
      f).mpr
      hpositiveLimit

/-- If the absorbed finite prime defect-square stream has the raw positive-coordinate limit
and positive windows have the owner positive-channel limit, then the completed off-diagonal
and owner positive channels agree. -/
theorem completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_of_coordinate_and_positive_window_limits
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (habsorbedCoordinateLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)))
    (hpositiveLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f))) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f := by
  have hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_absorbedPrimeDefectSquare_tendsto
      f habsorbedCoordinateLimit
  have hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_positiveRealWindow_tendsto
      f hmajorant hpositiveLimit
  exact hoffCoordinate.trans hpositiveCoordinate

/-- Coordinate and positive-window limits give the completed off-diagonal reconstruction
bridge through the owner positive prime channel. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_coordinate_and_positive_window_limits
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (habsorbedCoordinateLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)))
    (hpositiveLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f))) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_of_coordinate_and_positive_window_limits
      f hmajorant habsorbedCoordinateLimit hpositiveLimit
  exact
    completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_positiveChannel
      f hpositive

/-- The absorbed coordinate limit and diagonal-debt owner limit identify the completed
off-diagonal channel with the owner positive prime channel. -/
theorem completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_of_absorbedCoordinate_and_diagonalDebt_limits
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (habsorbedCoordinateLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)))
    (hdiagonalOwnerLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)))) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f := by
  have hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_absorbedPrimeDefectSquare_tendsto
      f habsorbedCoordinateLimit
  have hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtRealWindow_tendsto
      f hmajorant hdiagonalOwnerLimit
  exact hoffCoordinate.trans hpositiveCoordinate

/-- The absorbed coordinate limit and diagonal-debt owner limit give the completed
off-diagonal reconstruction bridge. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_absorbedCoordinate_and_diagonalDebt_limits
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (habsorbedCoordinateLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)))
    (hdiagonalOwnerLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)))) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_of_absorbedCoordinate_and_diagonalDebt_limits
      f hmajorant habsorbedCoordinateLimit hdiagonalOwnerLimit
  exact
    completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_positiveChannel
      f hpositive

/-- The coordinate-presentation comparison and the off-diagonal/coordinate comparison
supply the remaining positive-channel convergence for the absorbed prime defect-square
stream. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_of_coordinateTsumRe_comparisons
    (f : ZetaAdmissibleFunction)
    (hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)
    (hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  have hcoordinateLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
    (completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_absorbedPrimeDefectSquare_tendsto
      f).mp
      hoffCoordinate
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 x))
    hpositiveCoordinate
    hcoordinateLimit

/-- The absorbed finite prime defect-square stream converges to the owner positive prime
channel once its positive-coordinate limit and the diagonal-debt owner limit are known. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_of_absorbedCoordinate_and_diagonalDebt_limits
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (habsorbedCoordinateLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)))
    (hdiagonalOwnerLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)))) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  have hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_absorbedPrimeDefectSquare_tendsto
      f habsorbedCoordinateLimit
  have hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtRealWindow_tendsto
      f hmajorant hdiagonalOwnerLimit
  exact
    absorbedPrimeDefectSquare_tendsto_positiveChannel_of_coordinateTsumRe_comparisons
      f hoffCoordinate hpositiveCoordinate

/-- The coordinate-presentation comparisons imply the completed off-diagonal reconstruction
bridge. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_coordinateTsumRe_comparisons
    (f : ZetaAdmissibleFunction)
    (hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)
    (hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
    have hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    hoffCoordinate.trans hpositiveCoordinate
  exact
    completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_positiveChannel
      f hpositive

/-- With the existing summed contour/time transport, the off-diagonal/positive-coordinate
comparison is exactly the vanishing of the completed diagonal-debt coordinate presentation.

This is the concrete upstream condition exposed by the completed defect-square expansion:
positive coordinate plus two-face equals diagonal debt, while summed transport identifies
the two-face real scalar with the negative completed off-diagonal channel. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_diagonalDebtCoordinateTsum_re_eq_zero_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f ↔
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) = 0 := by
  constructor
  · intro hoffCoordinate
    let O : ℝ := completedPrimeOffDiagonalChannel f
    let P : ℝ := zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f
    let T : ℝ := Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
    let Dcoord : ℝ :=
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)
    have htwoFace : T = -O := by
      unfold T
      unfold O
      exact
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedPrimeOffDiagonalChannel_ownerSummedDistributionTransport
          f D
    have hexpansion : P + T = Dcoord := by
      unfold P
      unfold T
      unfold Dcoord
      calc
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
            Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
            Complex.re
              (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) +
              Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
          rfl
        _ =
            Complex.re
              (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
                zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
          exact (Complex.add_re
            (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f)
            (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)).symm
        _ =
            Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) := by
          exact congrArg Complex.re
            (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
              f hmajorant)
    have hP : P = O := hoffCoordinate.symm
    calc
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
          Dcoord := by
        rfl
      _ = P + T := by
        exact hexpansion.symm
      _ = O + T := by
        exact congrArg (fun x : ℝ => x + T) hP
      _ = O + -O := by
        exact congrArg (fun x : ℝ => O + x) htwoFace
      _ = 0 := by
        exact add_neg_cancel O
  · intro hdiagonalZero
    let O : ℝ := completedPrimeOffDiagonalChannel f
    let P : ℝ := zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f
    let T : ℝ := Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
    let Dcoord : ℝ :=
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)
    have htwoFace : T = -O := by
      unfold T
      unfold O
      exact
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedPrimeOffDiagonalChannel_ownerSummedDistributionTransport
          f D
    have hexpansion : P + T = Dcoord := by
      unfold P
      unfold T
      unfold Dcoord
      calc
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
            Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
            Complex.re
              (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) +
              Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
          rfl
        _ =
            Complex.re
              (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
                zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
          exact (Complex.add_re
            (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f)
            (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)).symm
        _ =
            Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) := by
          exact congrArg Complex.re
            (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
              f hmajorant)
    have hsum : P + -O = 0 := by
      calc
        P + -O = P + T := by
          exact congrArg (fun x : ℝ => P + x) htwoFace.symm
        _ = Dcoord := by
          exact hexpansion
        _ = Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) := by
          rfl
        _ = 0 := by
          exact hdiagonalZero
    have hcancel :
        (P + -O) + O = 0 + O := by
      exact congrArg (fun x : ℝ => x + O) hsum
    have hleft : (P + -O) + O = P := by
      calc
        (P + -O) + O = P + (-O + O) := by
          exact add_assoc P (-O) O
        _ = P + 0 := by
          exact congrArg (fun x : ℝ => P + x) (neg_add_cancel O)
        _ = P := by
          exact add_zero P
    have hright : 0 + O = O := by
      exact zero_add O
    calc
      completedPrimeOffDiagonalChannel f = O := by
        rfl
      _ = 0 + O := by
        exact hright.symm
      _ = (P + -O) + O := by
        exact hcancel.symm
      _ = P := by
        exact hleft
      _ = zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f := by
        rfl

/-- The completed off-diagonal channel equals the raw positive coordinate real channel once
the completed diagonal-debt coordinate presentation has zero real scalar. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_diagonalDebtCoordinateTsum_re_eq_zero
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hdiagonalZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) = 0) :
    completedPrimeOffDiagonalChannel f =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_diagonalDebtCoordinateTsum_re_eq_zero_of_summedTransport
      f D hmajorant).mpr
      hdiagonalZero

/-- The completed off-diagonal/positive-coordinate comparison forces the completed
diagonal-debt coordinate presentation to have zero real scalar. -/
theorem diagonalDebtCoordinateTsum_re_eq_zero_of_completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) = 0 := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_diagonalDebtCoordinateTsum_re_eq_zero_of_summedTransport
      f D hmajorant).mp
      hoffCoordinate

/-- The completed diagonal-debt owner scalar vanishes when the completed/raw two-face real
coefficients agree. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_matrixCoefficient_re_eq
    (f : ZetaAdmissibleFunction)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 := by
  exact
    zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_twoFace_re_eq
      f hmatrix

/-- Vanishing of the raw diagonal-debt coordinate presentation identifies the raw positive
coordinate presentation with the owner positive channel, once the completed/raw two-face real
coefficients agree. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re_eq_zero_and_matrixCoefficient_re_eq
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hdiagonalCoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) = 0)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f := by
  have hownerZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 :=
    zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_matrixCoefficient_re_eq
      f hmatrix
  have hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    hdiagonalCoordinateZero.trans hownerZero.symm
  exact
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
      f hmajorant hdiagonal

/-- The diagonal-coordinate vanishing condition plus completed/raw two-face real comparison
gives the completed off-diagonal/positive-channel comparison. -/
theorem completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re_eq_zero_and_matrixCoefficient_re_eq
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hdiagonalCoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) = 0)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f := by
  have hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_diagonalDebtCoordinateTsum_re_eq_zero
      f D hmajorant hdiagonalCoordinateZero
  have hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re_eq_zero_and_matrixCoefficient_re_eq
      f hmajorant hdiagonalCoordinateZero hmatrix
  exact hoffCoordinate.trans hpositiveCoordinate

/-- The diagonal-coordinate vanishing condition plus completed/raw two-face real comparison
gives the completed off-diagonal reconstruction bridge. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_diagonalDebtCoordinateTsum_re_eq_zero_and_matrixCoefficient_re_eq
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hdiagonalCoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) = 0)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re_eq_zero_and_matrixCoefficient_re_eq
      f D hmajorant hdiagonalCoordinateZero hmatrix
  exact
    completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_positiveChannel
      f hpositive

/-- The diagonal-debt coordinate transport facts imply the completed off-diagonal
reconstruction bridge. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_diagonalDebtCoordinateTsum
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hdiagonalZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) = 0)
    (hdiagonalOwner :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    (completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_diagonalDebtCoordinateTsum_re_eq_zero_of_summedTransport
      f D hmajorant).mpr
      hdiagonalZero
  have hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
      f hmajorant hdiagonalOwner
  exact
    completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_coordinateTsumRe_comparisons
      f hoffCoordinate hpositiveCoordinate

/-- The requested completed off-diagonal reconstruction bridge is equivalent to the absorbed
finite prime defect-square windows converging to the completed Hermitian positive prime
channel. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_absorbedPrimeDefectSquare_tendsto
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) ↔
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  exact
    (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_positiveChannel
      f).trans
      (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_absorbedPrimeDefectSquare_tendsto
        f)

/-- The finite prime diagonal debt is the positive prime-defect channel plus the signed
two-face channel. -/
theorem zetaPrimeDefectKernelDiagonalDebt_re_eq_positiveChannel_add_twoFace
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeDefectKernelDiagonalDebt f) =
      completedPrimeDefectKernelPositiveChannel f +
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  let P : ℂ := zetaPrimeDefectKernelPositiveForm f
  let T : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  let D : ℂ := zetaPrimeDefectKernelDiagonalDebt f
  have hpositive :
      completedPrimeDefectKernelPositiveChannel f = Complex.re P :=
    completedPrimeDefectKernelPositiveChannel_eq_finitePositiveForm_re f
  have hexpansion :
      P + T = D :=
    zetaPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt f
  calc
    Complex.re D = Complex.re (P + T) := by
      exact congrArg Complex.re hexpansion.symm
    _ = Complex.re P + Complex.re T := by
      exact Complex.add_re P T
    _ =
        completedPrimeDefectKernelPositiveChannel f +
          Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
      exact congrArg
        (fun x : ℝ => x + Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f))
        hpositive.symm

/-- The prime boundary channel of an autocorrelation is the positive prime-defect kernel
channel once the time-distribution reconstruction and whole-channel two-face normalization
are supplied. -/
theorem primeBoundaryChannel_convolutionAutocorrelation_re_eq_positiveChannel_of_matrixComparison
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      completedPrimeDefectKernelPositiveChannel f := by
  have hsigned :
      Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) :=
    primeBoundaryChannel_convolutionAutocorrelation_re_eq_neg_primeConvolutionContribution
      f D hmatrix
  have hnormalization :
      Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
        -completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_neg_positiveChannel_of_lowerWeightNormalization
      f
  calc
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
      exact hsigned
    _ = -(-completedPrimeDefectKernelPositiveChannel f) := by
      exact congrArg Neg.neg hnormalization
    _ = completedPrimeDefectKernelPositiveChannel f := by
      exact neg_neg (completedPrimeDefectKernelPositiveChannel f)

/-- The prime boundary channel of an autocorrelation is the positive prime-defect kernel
channel using the explicit summed contour/time transport provider. -/
theorem primeBoundaryChannel_convolutionAutocorrelation_re_eq_positiveChannel_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      completedPrimeDefectKernelPositiveChannel f := by
  have hsigned :
      Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) :=
    primeBoundaryChannel_convolutionAutocorrelation_re_eq_neg_primeConvolutionContribution_of_summedTransport
      f D hmatrix
  have hnormalization :
      Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
        -completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_neg_positiveChannel_of_lowerWeightNormalization
      f
  calc
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
      exact hsigned
    _ = -(-completedPrimeDefectKernelPositiveChannel f) := by
      exact congrArg Neg.neg hnormalization
    _ = completedPrimeDefectKernelPositiveChannel f := by
      exact neg_neg (completedPrimeDefectKernelPositiveChannel f)

/-- The completed boundary channel is nonnegative on autocorrelations once the
prime channel has been identified with the positive prime-defect channel. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_matrixComparison
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    0 ≤ Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  have hpositive_eq :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
    completedBoundaryChannel_convolutionAutocorrelation_re_eq_positivePresentationScalar_of_prime
      f
      (primeBoundaryChannel_convolutionAutocorrelation_re_eq_positiveChannel_of_matrixComparison
        f D hmatrix)
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    hpositive_eq.symm
    (zetaCompletedGNSPositiveBoundaryPresentationScalar_nonnegative f)

/-- The completed boundary channel is nonnegative on autocorrelations using the explicit
summed contour/time transport provider. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    0 ≤ Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  have hpositive_eq :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
    completedBoundaryChannel_convolutionAutocorrelation_re_eq_positivePresentationScalar_of_prime
      f
      (primeBoundaryChannel_convolutionAutocorrelation_re_eq_positiveChannel_of_summedTransport
        f D hmatrix)
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    hpositive_eq.symm
    (zetaCompletedGNSPositiveBoundaryPresentationScalar_nonnegative f)

/-- The canonical completed Hilbert-source correction coordinate is normalized by the
centered-pole Hermitian correction packet. -/
theorem completedBoundaryHilbertSourcePacket_source_correction_sq_eq_hermitianCorrectionPacketGram
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryHilbertSource f).correctionCoordinate *
        (completedBoundaryHilbertSource f).correctionCoordinate =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact completedBoundaryHilbertSource_correctionCoordinate_sq f

/-- The ordered-heart GNS scalar of a canonical source is the completed Hermitian
positive-presentation scalar. -/
theorem completedBoundaryHermitianGNSScalar_source_eq_positivePresentationScalar_compat
    (f : ZetaAdmissibleFunction) :
    completedBoundaryHermitianGNSScalar (completedBoundaryHilbertSource f) =
      zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
  exact completedBoundaryHermitianGNSScalar_source_eq_positivePresentationScalar f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
