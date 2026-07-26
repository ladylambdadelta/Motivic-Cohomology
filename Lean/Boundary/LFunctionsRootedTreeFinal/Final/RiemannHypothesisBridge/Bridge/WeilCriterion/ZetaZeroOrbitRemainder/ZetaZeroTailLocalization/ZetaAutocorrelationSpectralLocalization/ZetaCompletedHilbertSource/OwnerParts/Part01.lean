import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletedBoundaryDefect.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.HermitianBoundaryDefect
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ConvolutionChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.ContourTomography
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
local notation "π" => Real.pi

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

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
