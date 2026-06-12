import Boundary.LFunctions.ZetaExplicitFormulaGeometry
import Boundary.LFunctions.ZetaZeroKreinGram
import Boundary.LFunctions.ZetaPacketComparison
import Boundary.LFunctions.ZetaHermitianPacket
import Boundary.LFunctions.ZetaCompletedBoundaryDescent

/-!
# Boundary explicit-formula transport

This file owns the proved transport between the explicit-formula boundary
package and the completed packet/boundary-defect package.

It deliberately does not prove the zero-side explicit formula

```lean
zetaCompletedZeroKreinGram f =
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f
```

That equality is the analytic contour-shift theorem. The owner theorem for it
belongs to the completed explicit-formula assembly layer, after the residue,
decay, and vertical-decomposition inputs are available.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

open Filter

/-- The Hilbert-source packet of the canonical source is the completed boundary-defect packet.
This is a comparison theorem, not the definition of the GNS kernel. -/
theorem completedBoundaryHilbertSourcePacket_eq_boundaryDefect
    (f : ZetaAdmissibleFunction) :
    completedBoundaryHilbertSourcePacket (completedBoundaryHilbertSource f) =
      zetaCompletedBoundaryDefect f := by
  rfl

/-- The real-shadow GNS norm-square compares with the completed boundary-defect Gram.  This
is a packet-comparison theorem; the completed ordered-heart scalar is the Hermitian
defect-kernel scalar. -/
theorem completedBoundaryRealShadowGNSNormSq_eq_boundaryDefectGram
    (f : ZetaAdmissibleFunction) :
    completedBoundaryRealShadowGNSNormSq f =
      zetaCompletedBoundaryDefectGram f := by
  have hpacket :
      completedBoundaryHilbertSourcePacket (completedBoundaryHilbertSource f) =
        zetaCompletedBoundaryDefect f :=
    completedBoundaryHilbertSourcePacket_eq_boundaryDefect f
  unfold completedBoundaryRealShadowGNSNormSq
  unfold completedBoundaryGNSKernel
  unfold zetaCompletedBoundaryDefectGram
  unfold ZetaPacketEnsemble.normSq
  exact congrArg₂ ZetaPacketEnsemble.dotProduct hpacket hpacket

/-- The completed boundary-defect Gram is the real-shadow GNS norm-square. -/
theorem zetaCompletedBoundaryDefectGram_eq_realShadowGNSNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectGram f =
      completedBoundaryRealShadowGNSNormSq f := by
  exact (completedBoundaryRealShadowGNSNormSq_eq_boundaryDefectGram f).symm

/-- The completed explicit-formula boundary sum in signed real form. -/
noncomputable def zetaCompletedExplicitFormulaBoundarySum
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedBoundaryDefectGram f

/-- The completed boundary-defect Krein Gram in signed form. -/
noncomputable def zetaCompletedBoundaryDefectKreinGram
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedBoundaryDefectGram f

/-- The boundary-defect Krein notation is the boundary-defect Gram. -/
theorem zetaCompletedBoundaryDefectKreinGram_eq_boundaryDefectGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectKreinGram f =
      zetaCompletedBoundaryDefectGram f := by
  rfl

/-- The completed explicit-formula boundary sum is the boundary-defect Krein Gram. -/
theorem zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectKreinGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySum f =
      zetaCompletedBoundaryDefectKreinGram f := by
  rfl

/-- The completed explicit-formula boundary sum is the boundary-defect Gram. -/
theorem zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySum f =
      zetaCompletedBoundaryDefectGram f := by
  rfl

/-- The boundary-defect Krein Gram is the centered completed packet norm square. -/
theorem zetaCompletedBoundaryDefectKreinGram_eq_completedPacketNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectKreinGram f =
      zetaCompletedPacketNormSq f 0 := by
  exact
    (zetaCompletedBoundaryDefectKreinGram_eq_boundaryDefectGram f).trans
      (zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq f)

/-- The explicit-formula boundary sum is the centered completed packet norm square. -/
theorem zetaCompletedExplicitFormulaBoundarySum_eq_completedPacketNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySum f =
      zetaCompletedPacketNormSq f 0 := by
  exact
    (zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectKreinGram f).trans
      (zetaCompletedBoundaryDefectKreinGram_eq_completedPacketNormSq f)

/-- The centered completed packet norm square is the explicit-formula boundary sum. -/
theorem zetaCompletedPacketNormSq_eq_explicitFormulaBoundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPacketNormSq f 0 =
      zetaCompletedExplicitFormulaBoundarySum f := by
  exact (zetaCompletedExplicitFormulaBoundarySum_eq_completedPacketNormSq f).symm

/-- The explicit-formula boundary sum is nonnegative through the packet norm square. -/
theorem zetaCompletedExplicitFormulaBoundarySum_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedExplicitFormulaBoundarySum f := by
  have hpacket : 0 ≤ zetaCompletedPacketNormSq f 0 :=
    zetaCompletedPacketNormSq_nonnegative f 0
  have hboundary :
      zetaCompletedExplicitFormulaBoundarySum f =
        zetaCompletedPacketNormSq f 0 :=
      zetaCompletedExplicitFormulaBoundarySum_eq_completedPacketNormSq f
  exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hboundary.symm hpacket

/-- The explicit-formula boundary sum is nonnegative through the real-shadow packet
norm-square comparison. -/
theorem zetaCompletedExplicitFormulaBoundarySum_nonnegative_of_realShadowGNSNormSq
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedExplicitFormulaBoundarySum f := by
  have hgns : 0 ≤ completedBoundaryRealShadowGNSNormSq f :=
    completedBoundaryRealShadowGNSNormSq_nonnegative f
  have hboundary :
      zetaCompletedExplicitFormulaBoundarySum f =
        completedBoundaryRealShadowGNSNormSq f := by
    exact
      (zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectGram f).trans
        (zetaCompletedBoundaryDefectGram_eq_realShadowGNSNormSq f)
  exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hboundary.symm hgns

/-- The completed boundary-defect Krein Gram is nonnegative. -/
theorem zetaCompletedBoundaryDefectKreinGram_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedBoundaryDefectKreinGram f := by
  have hboundary : 0 ≤ zetaCompletedBoundaryDefectGram f :=
    zetaCompletedBoundaryDefectGram_nonnegative f
  have hkrein :
      zetaCompletedBoundaryDefectKreinGram f =
        zetaCompletedBoundaryDefectGram f :=
    zetaCompletedBoundaryDefectKreinGram_eq_boundaryDefectGram f
  exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hkrein.symm hboundary

/-- The geometry-layer analytic boundary sum is the analytic-core boundary sum. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_core
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic f =
      zetaCompletedExplicitFormulaBoundarySumCore f := by
  exact
    (zetaCompletedExplicitFormulaBoundarySumAnalytic_eq f).trans
      (zetaCompletedExplicitFormulaBoundarySumCore_eq f).symm

/-- The real part of the analytic-core boundary expression. This is the linear explicit-formula
boundary functional before it is compared with the Krein/Gram packet normalization. -/
noncomputable def zetaCompletedExplicitFormulaBoundaryLinearRealSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedExplicitFormulaBoundarySumCore f)

/-- The analytic boundary sum has the same real part as the analytic-core boundary sum. -/
theorem zetaCompletedExplicitFormulaBoundaryLinearRealSum_eq_analytic
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryLinearRealSum f =
      Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
  exact congrArg Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_core f).symm

/-- The real linear boundary sum unfolds to the real parts of the prime, archimedean, and
correction contributions. -/
theorem zetaCompletedExplicitFormulaBoundaryLinearRealSum_eq_components
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryLinearRealSum f =
      Complex.re (zetaCompletedExplicitFormulaPrimeContribution f) +
        Complex.re (zetaCompletedExplicitFormulaArchimedeanContribution f) +
        Complex.re (zetaCompletedExplicitFormulaCorrectionContribution f) := by
  exact congrArg Complex.re (zetaCompletedExplicitFormulaBoundarySumCore_eq f)

/-- The Krein/Gram boundary expression attached to the explicit-formula packets. -/
noncomputable def zetaCompletedExplicitFormulaBoundaryKreinSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedBoundaryDefectGram f

/-- The Krein boundary sum is the signed real boundary sum used downstream. -/
theorem zetaCompletedExplicitFormulaBoundaryKreinSum_eq_realBoundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryKreinSum f =
      zetaCompletedExplicitFormulaBoundarySum f := by
  rfl

/-- The Krein boundary sum is the completed packet norm square. -/
theorem zetaCompletedExplicitFormulaBoundaryKreinSum_eq_completedPacketNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryKreinSum f =
      zetaCompletedPacketNormSq f 0 := by
  exact zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq f

/-- The Krein boundary sum is the real-shadow packet norm-square. -/
theorem zetaCompletedExplicitFormulaBoundaryKreinSum_eq_realShadowGNSNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryKreinSum f =
      completedBoundaryRealShadowGNSNormSq f := by
  exact zetaCompletedBoundaryDefectGram_eq_realShadowGNSNormSq f

/-- The packet Krein boundary sum is the real-shadow packet norm-square. -/
theorem zetaCompletedExplicitFormulaBoundaryKreinSum_eq_realShadowNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryKreinSum f =
      completedBoundaryRealShadowGNSNormSq f := by
  exact zetaCompletedExplicitFormulaBoundaryKreinSum_eq_realShadowGNSNormSq f

/-- The convolution-autocorrelation boundary Krein sum is the real part of the completed
boundary channel on the convolution autocorrelation probe.  Positivity is supplied by the
completed-square descent theorem, not by collapsing paired spectral coordinates. -/
noncomputable def zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryKreinSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (completedBoundaryChannel (ZetaAdmissibleFunction.convolutionAutocorrelation f))

/-- Historical name for the convolution-autocorrelation boundary Krein sum. -/
abbrev zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryKreinSum f

/-- The time-side autocorrelation Krein scalar is the completed finite-part boundary channel.
This is the raw finite-part realization before passing to the positive Hermitian
defect-kernel representative in the ordered heart. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_eq_completedFinitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f =
      completedFinitePartBoundaryChannel f := by
  exact completedBoundaryChannel_convolutionAutocorrelation_re_eq_completedFinitePartBoundaryChannel f

/-- The completed finite-part boundary channel is the public autocorrelation Krein scalar. -/
theorem completedFinitePartBoundaryChannel_eq_autocorrelationBoundaryKreinSum
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f =
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  exact
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_eq_completedFinitePartBoundaryChannel
      f).symm

/-- The completed renormalized positive defect-kernel channel is the completed
ordered-heart GNS norm-square. -/
theorem zetaCompletedExplicitFormulaRenormalizedDefectKernelBoundaryChannel_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedRenormalizedDefectKernelBoundaryChannel f =
      completedBoundaryGNSNormSq f := by
  exact completedRenormalizedDefectKernelBoundaryChannel_eq_GNSNormSq f

/-- The real scalar attached to the positive completed GNS boundary class.

The owner scalar is the completed ordered-heart/GNS norm-square.  The complex positive
boundary form is a comparison presentation, not the definition of positivity. -/
noncomputable def zetaCompletedGNSPositiveBoundaryScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedBoundaryGNSNormSq f

/-- The completed ordered-heart GNS norm-square is the positive Hermitian defect-kernel
boundary scalar. -/
theorem completedBoundaryGNSNormSq_eq_GNSPositiveBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryGNSNormSq f =
      zetaCompletedGNSPositiveBoundaryScalar f := by
  unfold zetaCompletedGNSPositiveBoundaryScalar
  rfl

/-- The completed renormalized positive defect-kernel channel is the positive Hermitian GNS
boundary scalar. -/
theorem zetaCompletedExplicitFormulaRenormalizedDefectKernelBoundaryChannel_eq_GNSPositiveBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedRenormalizedDefectKernelBoundaryChannel f =
      zetaCompletedGNSPositiveBoundaryScalar f := by
  exact
    (completedRenormalizedDefectKernelBoundaryChannel_eq_GNSNormSq f).trans
      (completedBoundaryGNSNormSq_eq_GNSPositiveBoundaryScalar f)

/-- The positive Hermitian defect-kernel boundary scalar is nonnegative. -/
theorem zetaCompletedGNSPositiveBoundaryScalar_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedGNSPositiveBoundaryScalar f := by
  unfold zetaCompletedGNSPositiveBoundaryScalar
  exact completedBoundaryGNSNormSq_nonnegative f

/-- The convolution-autocorrelation boundary real form carries the completed positive-class
certificate constructed by finite defect-square descent. -/
def zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryPositiveClass
    (f : ZetaAdmissibleFunction) : CompletedPositiveBoundaryPreconeElement :=
  completedPositiveBoundaryPreconeElement f

/-- Historical name for the convolution-autocorrelation completed positive-class certificate. -/
abbrev zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass
    (f : ZetaAdmissibleFunction) : CompletedPositiveBoundaryPreconeElement :=
  zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryPositiveClass f

/-- The positive representative in the convolution-autocorrelation boundary class is
pointwise nonnegative. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).positiveRepresentative
        N := by
  exact completedPositiveBoundaryPreconeElement_positiveRepresentative_nonnegative N f

/-- The positive representative in the convolution-autocorrelation boundary class is the
finite defect-square representative. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_positive_eq_weightSquare
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).positiveRepresentative
        N =
      FiniteBoundaryWeightObject.squareRepresentative
        (finiteBoundaryWeightObject N f) := by
  exact completedPositiveBoundaryPreconeElement_positiveRepresentative_eq_weightSquare N f

/-- The absorption defect in the convolution-autocorrelation boundary class is the negative
finite diagonal-debt face. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_absorptionDefect_eq_neg_diagonalDebt
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).absorptionDefect N =
      - (finiteBoundaryWeightObject N f).diagonalDebt := by
  exact completedPositiveBoundaryPreconeElement_absorptionDefect_eq_neg_diagonalDebt N f

/-- Weight-triangular transport for the convolution-autocorrelation boundary class: adding the
lower-weight absorption defect transports the positive square representative to the finite-part
boundary representative. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_weightTriangularTransport
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).positiveRepresentative
        N +
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).absorptionDefect
          N =
      FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  exact completedPositiveBoundaryPreconeElement_weightTriangularTransport N f

/-- The same transport with the diagonal face written explicitly. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_positive_sub_diagonalDebt_eq_weightFinitePart
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).positiveRepresentative
        N -
        (finiteBoundaryWeightObject N f).diagonalDebt =
      FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  exact completedPositiveBoundaryPreconeElement_positive_sub_diagonalDebt_eq_weightFinitePart
    N f

/-- The absorbed representative in the positive class is the finite-part boundary
representative. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_absorbed_eq_weightFinitePart
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).absorbedRepresentative
        N =
      FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  exact completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_weightFinitePart
    N f

/-- The absorbed representative in the convolution-autocorrelation boundary class realizes to
the boundary Krein scalar. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_tendsto
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).absorbedRepresentative
      atTop
      (𝓝 (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f)) := by
  exact completedPositiveBoundaryPreconeElement_absorbedRepresentative_tendsto_scalar f

/-- The finite-part representatives obtained by triangular transport converge to the boundary
Krein scalar. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_weightFinitePart_tendsto
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        FiniteBoundaryWeightObject.finitePartRepresentative
          (finiteBoundaryWeightObject N f))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f)) := by
  have habsorbed :
      Tendsto
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).absorbedRepresentative
        atTop
        (𝓝 (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f)) :=
    zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_tendsto f
  have htransport :
      (fun N : ℕ =>
        FiniteBoundaryWeightObject.finitePartRepresentative
          (finiteBoundaryWeightObject N f)) =
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).absorbedRepresentative := by
    funext N
    exact
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_absorbed_eq_weightFinitePart
        N f).symm
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop
        (𝓝 (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f)))
    htransport.symm
    habsorbed

/-- The scalar of the convolution-autocorrelation positive class is the boundary Krein scalar. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_scalar_eq_KreinSum
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).scalar =
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  rfl

/-- The scalar of the convolution-autocorrelation positive class is the completed finite-part
boundary channel. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_scalar_eq_completedFinitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).scalar =
      completedFinitePartBoundaryChannel f := by
  exact
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_scalar_eq_KreinSum
      f).trans
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_eq_completedFinitePartBoundaryChannel
        f)

/-- The completed positive precone scalar is the same completed finite-part boundary scalar
without passing through the public Krein abbreviation. -/
theorem completedPositiveBoundaryPreconeElement_scalar_eq_completedFinitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).scalar =
      completedFinitePartBoundaryChannel f := by
  exact
    zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_scalar_eq_completedFinitePartBoundaryChannel
      f

/-- The convolution-autocorrelation positive class scalar is the reduced time-pairing scalar
of its completed ordered-heart representative. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_scalar_eq_timePairingScalar
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).scalar =
      completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  exact completedPositiveBoundaryPreconeElement_scalar_eq_timePairingScalar f

/-- The absorption defect of the autocorrelation boundary positive class is lower-weight
radical in the completed ordered-heart quotient. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_absorptionDefect_lowerWeightRadical
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertSource.LowerWeightRadical
      (completedPositiveBoundaryAbsorptionDefectOrderedHeartClass f) := by
  exact completedPositiveBoundaryAbsorptionDefectOrderedHeartClass_lowerWeightRadical f

/-- The positive square ordered-heart scalar is the completed GNS norm-square. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveSquare_scalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedPositiveSquareBoundaryOrderedHeartClass f) =
      completedBoundaryGNSNormSq f := by
  exact completedPositiveSquareBoundaryOrderedHeartScalar_eq_GNSNormSq f

/-- GNS tomography transports the absorbed positive-boundary ordered-heart scalar to the
square-only ordered-heart scalar. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_orderedHeartScalar_eq_square
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedOrderedHeartScalar
        (completedPositiveSquareBoundaryOrderedHeartClass f) := by
  exact completedPositiveBoundaryOrderedHeartScalar_eq_square_by_GNSTomography f

/-- The absorbed positive-boundary ordered-heart scalar is the completed GNS norm-square. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_orderedHeartScalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedBoundaryGNSNormSq f := by
  exact
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_orderedHeartScalar_eq_square
      f).trans
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveSquare_scalar_eq_GNSNormSq
        f)

/-- The completed finite-part boundary ordered-heart class is tomographically the positive
square class. -/
theorem zetaCompletedExplicitFormulaFinitePartBoundaryClass_GNSTomographicallyEquivalent_positiveSquare
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent
      (completedFinitePartBoundaryOrderedHeartClass f)
      (completedPositiveSquareBoundaryOrderedHeartClass f) := by
  exact completedFinitePartBoundaryClass_GNSTomographicallyEquivalent_positiveSquare f

/-- The completed finite-part boundary ordered-heart scalar is the completed GNS norm-square. -/
theorem zetaCompletedExplicitFormulaFinitePartBoundaryOrderedHeartScalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      completedBoundaryGNSNormSq f := by
  exact completedFinitePartBoundaryOrderedHeartScalar_eq_GNSNormSq f

/-- The completed finite-part boundary ordered-heart scalar is represented by the completed
renormalized positive defect-kernel channel. -/
theorem zetaCompletedExplicitFormulaFinitePartBoundaryOrderedHeartScalar_eq_renormalizedDefectKernel
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  exact completedFinitePartBoundaryOrderedHeartScalar_eq_renormalizedDefectKernel f

/-- The completed finite-part boundary ordered-heart quotient class is the positive square
quotient class. -/
theorem zetaCompletedExplicitFormulaFinitePartBoundaryQuotientClass_eq_positiveSquare
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryOrderedHeartQuotientClass f =
      completedPositiveSquareBoundaryOrderedHeartQuotientClass f := by
  exact completedFinitePartBoundaryOrderedHeartQuotientClass_eq_positiveSquare f

/-- The completed finite-part boundary quotient scalar is the completed GNS norm-square. -/
theorem zetaCompletedExplicitFormulaFinitePartBoundaryQuotientScalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
      completedBoundaryGNSNormSq f := by
  exact completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_GNSNormSq f

/-- The completed finite-part boundary quotient scalar is represented by the completed
renormalized positive defect-kernel channel. -/
theorem zetaCompletedExplicitFormulaFinitePartBoundaryQuotientScalar_eq_renormalizedDefectKernel
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  exact completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_renormalizedDefectKernel f

/-- The completed finite-part boundary quotient scalar is nonnegative. -/
theorem zetaCompletedExplicitFormulaFinitePartBoundaryQuotientScalar_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤
      completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) := by
  exact completedFinitePartBoundaryOrderedHeartQuotientScalar_nonnegative f

/-- The descended ordered-heart scalar of the completed finite-part autocorrelation boundary
class.  This is the quotient-level scalar, not the raw time-side finite-part number. -/
noncomputable def zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedBoundaryOrderedHeartClassScalar
    (completedFinitePartBoundaryOrderedHeartQuotientClass f)

/-- The descended ordered-heart autocorrelation boundary scalar is the completed GNS
norm-square. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f =
      completedBoundaryGNSNormSq f := by
  exact completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_GNSNormSq f

/-- The descended ordered-heart autocorrelation boundary scalar is represented by the
completed renormalized positive defect-kernel channel. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar_eq_renormalizedDefectKernel
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  exact completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_renormalizedDefectKernel f

/-- The raw autocorrelation Krein scalar plus prime diagonal debt is the completed
ordered-heart scalar.  This is the honest debt-visible comparison between the time-side
explicit-formula scalar and the quotient/GNS scalar. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_add_primeDiagonalDebt_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f := by
  have hkrein :
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f =
        completedFinitePartBoundaryChannel f :=
    zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_eq_completedFinitePartBoundaryChannel
      f
  have hfinite :
      completedFinitePartBoundaryChannel f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedAnalyticBoundaryRealizationScalar f :=
    completedFinitePartBoundaryChannel_add_primeDiagonalDebt_eq_completedAnalyticBoundaryRealizationScalar
      f
  have hordered :
      completedAnalyticBoundaryRealizationScalar f =
        zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f :=
    by
      unfold completedAnalyticBoundaryRealizationScalar
      unfold completedAnalyticBoundaryRealizationClass
      unfold zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar
      rfl
  have hkrein_debt :
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedFinitePartBoundaryChannel f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    congrArg
      (fun x : ℝ =>
        x + Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      hkrein
  exact hkrein_debt.trans (hfinite.trans hordered)

/-- The descended ordered-heart autocorrelation boundary scalar is nonnegative. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f := by
  exact completedFinitePartBoundaryOrderedHeartQuotientScalar_nonnegative f

/-- The explicit-formula ordered-heart scalar is the owner analytic boundary realization
scalar. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar_eq_realizationScalar
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f =
      completedAnalyticBoundaryRealizationScalar f := by
  rfl

/-- The owner analytic boundary realization scalar is the explicit-formula ordered-heart
scalar. -/
theorem completedAnalyticBoundaryRealizationScalar_eq_explicitFormulaOrderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedAnalyticBoundaryRealizationScalar f =
      zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f := by
  rfl

/-- The raw completed finite-part boundary scalar is the time-pairing scalar of its
ordered-heart representative. -/
theorem zetaCompletedExplicitFormulaFinitePartBoundaryChannel_eq_timePairingScalar
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f =
      completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  exact completedFinitePartBoundaryChannel_eq_timePairingScalar f

/-- If the reduced time-pairing realization is reconstructed as the ordered-heart GNS scalar,
then the convolution-autocorrelation positive class scalar is the completed GNS norm-square. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_scalar_eq_GNSNormSq_of_timePairingScalar_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction)
    (hcomparison :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f)) :
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).scalar =
      completedBoundaryGNSNormSq f := by
  exact
    (completedPositiveBoundaryPreconeElement_scalar_eq_orderedHeartScalar_of_timePairingScalar_eq_orderedHeartScalar
      f
      hcomparison).trans
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_orderedHeartScalar_eq_GNSNormSq
        f)

/-- The final time-pairing/GNS reconstruction comparison is exactly the same statement as
transporting the completed finite-part boundary channel to the completed ordered-heart GNS
norm-square. -/
theorem completedBoundaryTimePairingScalar_eq_orderedHeartScalar_iff_completedFinitePartGNSTransport
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) ↔
    completedFinitePartBoundaryChannel f =
      completedBoundaryGNSNormSq f := by
  constructor
  · intro hcomparison
    have hfinite_time :
        completedFinitePartBoundaryChannel f =
          completedBoundaryTimePairingScalar
            (completedPositiveBoundaryOrderedHeartClass f) := by
      exact
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_scalar_eq_completedFinitePartBoundaryChannel
          f).symm.trans
          (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_scalar_eq_timePairingScalar
            f)
    have hordered_gns :
        completedOrderedHeartScalar
            (completedPositiveBoundaryOrderedHeartClass f) =
          completedBoundaryGNSNormSq f :=
      zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_orderedHeartScalar_eq_GNSNormSq
        f
    exact hfinite_time.trans (hcomparison.trans hordered_gns)
  · intro htransport
    have htime_finite :
        completedBoundaryTimePairingScalar
            (completedPositiveBoundaryOrderedHeartClass f) =
          completedFinitePartBoundaryChannel f := by
      exact
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_scalar_eq_timePairingScalar
          f).symm.trans
          (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_scalar_eq_completedFinitePartBoundaryChannel
            f)
    have hgns_ordered :
        completedBoundaryGNSNormSq f =
          completedOrderedHeartScalar
            (completedPositiveBoundaryOrderedHeartClass f) := by
      exact
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_orderedHeartScalar_eq_GNSNormSq
          f).symm
    exact htime_finite.trans (htransport.trans hgns_ordered)

/-- Completed finite-part transport proves the final time-pairing/GNS reconstruction
comparison. -/
theorem completedBoundaryTimePairingScalar_eq_orderedHeartScalar_of_completedFinitePartGNSTransport
    (f : ZetaAdmissibleFunction)
    (htransport :
      completedFinitePartBoundaryChannel f =
        completedBoundaryGNSNormSq f) :
    completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  exact
    (completedBoundaryTimePairingScalar_eq_orderedHeartScalar_iff_completedFinitePartGNSTransport
      f).2
      htransport

/-- The positive square ordered-heart scalar is nonnegative. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveSquare_scalar_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedOrderedHeartScalar
        (completedPositiveSquareBoundaryOrderedHeartClass f) := by
  have hgns : 0 ≤ completedBoundaryGNSNormSq f :=
    completedBoundaryGNSNormSq_nonnegative f
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveSquare_scalar_eq_GNSNormSq
      f).symm
    hgns

/-- Once the time-side autocorrelation Krein scalar is transported to the completed
ordered-heart GNS scalar, nonnegativity is immediate from the GNS positive kernel. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_nonnegative_of_GNSTransport
    (f : ZetaAdmissibleFunction)
    (htransport :
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f =
        completedBoundaryGNSNormSq f) :
    0 ≤ zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  have hgns : 0 ≤ completedBoundaryGNSNormSq f :=
    completedBoundaryGNSNormSq_nonnegative f
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    htransport.symm
    hgns

/-- Once the time-side autocorrelation Krein scalar descends to the completed ordered-heart
finite-part quotient scalar, nonnegativity follows from the positive GNS square in that
quotient. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_nonnegative_of_orderedHeartQuotientTransport
    (f : ZetaAdmissibleFunction)
    (htransport :
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f =
        zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f) :
    0 ≤ zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  have hquotient :
      0 ≤ zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f :=
    zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar_nonnegative f
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    htransport.symm
    hquotient

/-- The ordered-heart quotient transport seam is equivalent to transporting the time-side
autocorrelation Krein scalar to the completed GNS norm-square, because the finite-part
quotient scalar has already been identified with the GNS scalar. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_eq_GNSNormSq_of_orderedHeartQuotientTransport
    (f : ZetaAdmissibleFunction)
    (htransport :
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f =
        zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f) :
    zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f =
      completedBoundaryGNSNormSq f := by
  exact htransport.trans
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar_eq_GNSNormSq f)

/-- Nonnegativity follows once the reduced time-pairing realization is reconstructed as the
ordered-heart GNS scalar.  This is the final comparison seam after finite triangular
transport and GNS tomography have been discharged. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_nonnegative_of_timePairingScalar_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction)
    (hcomparison :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f)) :
    0 ≤ zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  have hclass :
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).scalar =
        completedBoundaryGNSNormSq f :=
    zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_scalar_eq_GNSNormSq_of_timePairingScalar_eq_orderedHeartScalar
      f
      hcomparison
  have hkrein :
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f =
        completedBoundaryGNSNormSq f :=
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_scalar_eq_KreinSum
      f).symm.trans hclass
  exact zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_nonnegative_of_GNSTransport
    f
    hkrein

/-- Once the completed finite-part channel is transported through the completed ordered-heart
quotient to the GNS scalar, the time-side autocorrelation Krein scalar is nonnegative.  This
representative-level implication is retained as a compatibility route; the canonical route
uses `zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar`. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_nonnegative_of_completedFinitePartGNSTransport
    (f : ZetaAdmissibleFunction)
    (htransport :
      completedFinitePartBoundaryChannel f =
        completedBoundaryGNSNormSq f) :
    0 ≤ zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  have htimeToFinitePart :
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f =
        completedFinitePartBoundaryChannel f :=
    zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_eq_completedFinitePartBoundaryChannel f
  have htimeToGNS :
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f =
        completedBoundaryGNSNormSq f :=
    htimeToFinitePart.trans htransport
  exact zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_nonnegative_of_GNSTransport
    f
    htimeToGNS

/-- Once the completed finite-part channel is transported to the positive Hermitian GNS
boundary scalar, nonnegativity follows from the owned defect-square/Hermitian-packet
positivity theorem. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_nonnegative_of_weightTriangularPositiveGNSTransport
    (f : ZetaAdmissibleFunction)
    (htransport :
      completedFinitePartBoundaryChannel f =
        zetaCompletedGNSPositiveBoundaryScalar f) :
    0 ≤ zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  have htimeToFinitePart :
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f =
        completedFinitePartBoundaryChannel f :=
    zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_eq_completedFinitePartBoundaryChannel f
  have htimeToPositiveGNS :
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f =
        zetaCompletedGNSPositiveBoundaryScalar f :=
    htimeToFinitePart.trans htransport
  have hpositiveGNS :
      0 ≤ zetaCompletedGNSPositiveBoundaryScalar f :=
    zetaCompletedGNSPositiveBoundaryScalar_nonnegative f
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    htimeToPositiveGNS.symm
    hpositiveGNS

/-- Nonnegativity of the finite time-side positive-class scalar gives nonnegativity of the
boundary Krein scalar.  This is retained as a finite-precone wrapper; the ordered-heart/GNS
route goes through `zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_nonnegative_of_GNSTransport`. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_nonnegative_of_positiveClass
    (f : ZetaAdmissibleFunction)
    (hclass :
      0 ≤ (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).scalar) :
    0 ≤ zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_scalar_eq_KreinSum f)
    hclass

/-- A complex number is a real scalar once its real part is the scalar and its imaginary part
vanishes. -/
theorem complex_eq_of_re_eq_of_im_eq_zero
    (z : ℂ) (r : ℝ)
    (hre : Complex.re z = r)
    (him : Complex.im z = 0) :
    z = (r : ℂ) := by
  exact Complex.ext hre (him.trans (Complex.ofReal_im r).symm)

/-- Finite-display prime-channel holography: the finite display prime
convolution contribution is the finite two-face/GNS prime matrix coefficient.

The completed owner path uses `zetaCompletedPrimeTwoFaceGNSMatrixCoefficient`. -/
theorem zetaCompletedExplicitFormulaPrimeFiniteDisplayChannel_holographic
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact zetaCompletedExplicitFormulaPrimeConvolutionChannel_holographic_twoFace f

/-- Finite-display compatibility name for the prime linear boundary functional on the
convolution autocorrelation kernel. -/
theorem zetaCompletedExplicitFormulaPrimeFiniteDisplayConvolutionLinearReal_eq_twoFaceMatrixCoefficient
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact zetaCompletedExplicitFormulaPrimeFiniteDisplayChannel_holographic f

/-- Finite-display compatibility name for prime convolution-channel holography. -/
theorem zetaCompletedExplicitFormulaPrimeFiniteDisplayLinearReal_autocorrelation_eq_twoFaceMatrixCoefficient
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact
    zetaCompletedExplicitFormulaPrimeFiniteDisplayConvolutionLinearReal_eq_twoFaceMatrixCoefficient
      f

/-- Finite-display prime channel expansion: the finite explicit prime
contribution is the cross term in the finite positive prime defect-kernel square, and the
finite diagonal debt is the remaining square face. -/
theorem zetaCompletedExplicitFormulaPrimeFiniteDisplayConvolutionContribution_add_positiveDefectKernel_eq_diagonalDebt
    (f : ZetaAdmissibleFunction) :
    zetaPrimeDefectKernelPositiveForm f +
        zetaCompletedExplicitFormulaPrimeConvolutionContribution f =
      zetaPrimeDefectKernelDiagonalDebt f := by
  exact
    zetaCompletedExplicitFormulaPrimeConvolutionContribution_add_primeDefectKernelPositiveForm_eq_diagonalDebt
      f

/-- Real scalar form of the full positive/symmetrized GNS transport identity. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationForm_add_symmetrized_re_eq_diagonalDebt_add_archCorrection_re
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedGNSPositiveBoundaryPresentationForm f +
          zetaCompletedGNSSymmetrizedBoundaryForm f) =
      Complex.re
        (zetaCompletedGNSDiagonalDebtBoundaryForm f +
          ((ZetaHermitianPacketEnsemble.archimedeanPacketGram
              (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
            (ZetaHermitianPacketEnsemble.correctionPacketGram
              (zetaCompletedHermitianBoundaryDefect f) : ℂ))) := by
  exact congrArg Complex.re
    (zetaCompletedGNSPositiveBoundaryPresentationForm_add_symmetrized_eq_diagonalDebt_add_archCorrection
      f)

/-- The real scalar attached to the symmetrized two-face GNS boundary form. -/
noncomputable def zetaCompletedGNSSymmetrizedBoundaryScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedGNSSymmetrizedBoundaryForm f)

/-- The real scalar attached to the finite display-level symmetrized two-face boundary form. -/
noncomputable def zetaFiniteGNSSymmetrizedBoundaryScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaFiniteGNSSymmetrizedBoundaryForm f)

/-- The real scalar attached to the diagonal-debt GNS boundary face. -/
noncomputable def zetaCompletedGNSDiagonalDebtBoundaryScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedGNSDiagonalDebtBoundaryForm f)

/-- Component normal form for the positive GNS boundary scalar. -/
theorem zetaCompletedGNSPositiveBoundaryScalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryScalar f =
      completedBoundaryGNSNormSq f := by
  unfold zetaCompletedGNSPositiveBoundaryScalar
  rfl

/-- Component normal form for the symmetrized GNS boundary scalar. -/
theorem zetaCompletedGNSSymmetrizedBoundaryScalar_eq_primeTwoFace_add_archCorrection
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSSymmetrizedBoundaryScalar f =
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) +
        (ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f)) := by
  let S : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let A : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let C : ℝ :=
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  unfold zetaCompletedGNSSymmetrizedBoundaryScalar
  unfold zetaCompletedGNSSymmetrizedBoundaryForm
  change Complex.re (S + (A : ℂ) + (C : ℂ)) =
    Complex.re S + (A + C)
  calc
    Complex.re (S + (A : ℂ) + (C : ℂ)) =
        Complex.re (S + (A : ℂ)) + Complex.re (C : ℂ) := by
      exact Complex.add_re (S + (A : ℂ)) (C : ℂ)
    _ = (Complex.re S + Complex.re (A : ℂ)) + Complex.re (C : ℂ) := by
      exact congrArg (fun x : ℝ => x + Complex.re (C : ℂ))
        (Complex.add_re S (A : ℂ))
    _ = (Complex.re S + A) + C := by
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd rfl (Complex.ofReal_re A))
        (Complex.ofReal_re C)
    _ = Complex.re S + (A + C) := by
      exact add_assoc (Complex.re S) A C

/-- Component normal form for the diagonal-debt GNS boundary scalar. -/
theorem zetaCompletedGNSDiagonalDebtBoundaryScalar_eq_primeDebt_add_archCorrection
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSDiagonalDebtBoundaryScalar f =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) +
        (ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f)) := by
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  let A : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let C : ℝ :=
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  unfold zetaCompletedGNSDiagonalDebtBoundaryScalar
  unfold zetaCompletedGNSDiagonalDebtBoundaryForm
  change Complex.re (D + (A : ℂ) + (C : ℂ)) =
    Complex.re D + (A + C)
  calc
    Complex.re (D + (A : ℂ) + (C : ℂ)) =
        Complex.re (D + (A : ℂ)) + Complex.re (C : ℂ) := by
      exact Complex.add_re (D + (A : ℂ)) (C : ℂ)
    _ = (Complex.re D + Complex.re (A : ℂ)) + Complex.re (C : ℂ) := by
      exact congrArg (fun x : ℝ => x + Complex.re (C : ℂ))
        (Complex.add_re D (A : ℂ))
    _ = (Complex.re D + A) + C := by
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd rfl (Complex.ofReal_re A))
        (Complex.ofReal_re C)
    _ = Complex.re D + (A + C) := by
      exact add_assoc (Complex.re D) A C

/-- Real scalar form of adding the completed symmetrized two-face scalar to the positive
GNS scalar.  The positive scalar is owned by the ordered-heart GNS norm-square; spectral
defect-kernel expansion is a separate comparison theorem. -/
theorem zetaCompletedGNSPositiveBoundaryScalar_add_symmetrized_eq_GNSNormSq_add_symmetrized
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryScalar f +
        zetaCompletedGNSSymmetrizedBoundaryScalar f =
      completedBoundaryGNSNormSq f +
        zetaCompletedGNSSymmetrizedBoundaryScalar f := by
  unfold zetaCompletedGNSPositiveBoundaryScalar
  rfl

/-- Archimedean-channel holography: the archimedean explicit-formula functional evaluated
on the convolution autocorrelation kernel is the Hermitian archimedean packet Gram. -/
theorem zetaCompletedExplicitFormulaArchimedeanChannel_holographic
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaArchimedeanConvolutionChannel_holographic f

/-- The archimedean linear boundary functional on the convolution autocorrelation kernel is its
Hermitian archimedean packet contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionLinearReal_eq_archimedeanPacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaArchimedeanChannel_holographic f

/-- Historical name for archimedean convolution-channel holography. -/
theorem zetaCompletedExplicitFormulaArchimedeanLinearReal_autocorrelation_eq_archimedeanPacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaArchimedeanConvolutionLinearReal_eq_archimedeanPacketGram
    f

/-- Correction-channel holography: the correction explicit-formula functional evaluated on the
convolution autocorrelation kernel is the Hermitian correction packet Gram. -/
theorem zetaCompletedExplicitFormulaCorrectionChannel_holographic
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaCorrectionConvolutionChannel_holographic f

/-- The correction linear boundary functional on the convolution autocorrelation kernel is its
Hermitian correction packet contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionConvolutionLinearReal_eq_correctionPacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaCorrectionChannel_holographic f

/-- Historical name for correction convolution-channel holography. -/
theorem zetaCompletedExplicitFormulaCorrectionLinearReal_autocorrelation_eq_correctionPacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaCorrectionConvolutionLinearReal_eq_correctionPacketGram f

/-- The convolution-autocorrelation boundary functional in real channel form. -/
noncomputable def zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) +
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) +
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f)

/-- The convolution-autocorrelation boundary functional in complex channel form. -/
noncomputable def zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
    zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
    zetaCompletedExplicitFormulaCorrectionConvolutionContribution f

/-- The real part of the convolution boundary sum is the real channel sum. -/
theorem zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_re
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f) =
      zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum f := by
  unfold zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic
  unfold zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum
  calc
    Complex.re
        (zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
          zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
        Complex.re
            (zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
              zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) +
          Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) :=
      Complex.add_re
        (zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f)
        (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f)
    _ =
        (Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) +
          Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f)) +
          Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) := by
      exact congrArg
        (fun x : ℝ =>
          x + Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f))
        (Complex.add_re
          (zetaCompletedExplicitFormulaPrimeConvolutionContribution f)
          (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f))
    _ =
        Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) +
          Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) +
          Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) := by
      rfl

/-- The paired convolution boundary form. -/
noncomputable def zetaCompletedExplicitFormulaConvolutionBoundaryPairedForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPairedSpectralBoundaryForm f

/-- Historical name for the real part of the paired spectral convolution boundary form.
This is not the public completed time-side Krein scalar. -/
noncomputable def zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedExplicitFormulaConvolutionBoundaryPairedForm f)

/-- The real paired-spectral convolution boundary functional agrees with the real part of the
paired spectral boundary form. -/
theorem zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum f =
      zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum f := by
  have hsum :
      zetaCompletedPairedSpectralBoundaryForm f =
        zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
          zetaCompletedExplicitFormulaCorrectionConvolutionContribution f :=
    zetaCompletedPairedSpectralBoundaryForm_eq_convolutionContributions f
  have hre :
      Complex.re
          (zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
            zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
            zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
        Complex.re (zetaCompletedPairedSpectralBoundaryForm f) :=
    congrArg Complex.re hsum.symm
  have hleft :
      Complex.re (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f) =
        zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum f :=
    zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_re f
  unfold zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum
  unfold zetaCompletedExplicitFormulaConvolutionBoundaryPairedForm
  exact hleft.symm.trans hre

/-- Historical name for the real convolution boundary assembly theorem. -/
theorem zetaCompletedExplicitFormulaBoundaryLinearRealSum_autocorrelation_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum f =
      zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum f := by
  exact zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum_eq_seedKreinSum f

/-- The convolution boundary sum is real. -/
theorem zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f) = 0 := by
  have hsum :
      zetaCompletedPairedSpectralBoundaryForm f =
        zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
          zetaCompletedExplicitFormulaCorrectionConvolutionContribution f :=
    zetaCompletedPairedSpectralBoundaryForm_eq_convolutionContributions f
  have him :
      Complex.im
          (zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
            zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
            zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
        Complex.im (zetaCompletedPairedSpectralBoundaryForm f) :=
    congrArg Complex.im hsum.symm
  unfold zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic
  exact him.trans (zetaCompletedPairedSpectralBoundaryForm_im_eq_zero f)

/-- The complex convolution boundary sum agrees with the paired spectral boundary form. -/
theorem zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_eq_pairedForm
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f =
      zetaCompletedExplicitFormulaConvolutionBoundaryPairedForm f := by
  unfold zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic
  unfold zetaCompletedExplicitFormulaConvolutionBoundaryPairedForm
  exact (zetaCompletedPairedSpectralBoundaryForm_eq_convolutionContributions f).symm

/-- The paired spectral convolution Krein scalar is exactly the finite symmetrized boundary
scalar reconstructed by the finite packet presentation.  Completed GNS transport is owned by
the completed finite-part/ordered-heart route, not by this finite reconstruction theorem. -/
theorem zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum_eq_finiteGNSSymmetrizedBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum f =
      zetaFiniteGNSSymmetrizedBoundaryScalar f := by
  unfold zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum
  unfold zetaCompletedExplicitFormulaConvolutionBoundaryPairedForm
  unfold zetaFiniteGNSSymmetrizedBoundaryScalar
  exact congrArg Complex.re
    (zetaCompletedBoundaryReconstruction_pairedForm_eq_finiteGNSSymmetrizedBoundaryForm f)

/-- The complex convolution boundary presentation has real part equal to the finite
symmetrized boundary scalar. -/
theorem zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_re_eq_finiteGNSSymmetrizedBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f) =
      zetaFiniteGNSSymmetrizedBoundaryScalar f := by
  have hpaired :
      zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f =
        zetaCompletedExplicitFormulaConvolutionBoundaryPairedForm f :=
    zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_eq_pairedForm f
  calc
    Complex.re (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f) =
        Complex.re (zetaCompletedExplicitFormulaConvolutionBoundaryPairedForm f) := by
      exact congrArg Complex.re hpaired
    _ = zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum f := by
      unfold zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum
    _ = zetaFiniteGNSSymmetrizedBoundaryScalar f := by
      exact zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum_eq_finiteGNSSymmetrizedBoundaryScalar
        f

/-- The real two-face prime presentation is the realized prime GNS channel. -/
theorem zetaRealPrimePresentation_eq_realizedPrimeGram
    (f : ZetaAdmissibleFunction) :
    (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
        (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
          ((zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter ℓ.1 ℓ.2) *
              star
                (zetaCompletedExplicitFormulaPhi f
                  (-(zetaPrimePacketCenter ℓ.1 ℓ.2 : ℂ)))) +
            star
              (zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter ℓ.1 ℓ.2) *
                star
                  (zetaCompletedExplicitFormulaPhi f
                    (-(zetaPrimePacketCenter ℓ.1 ℓ.2 : ℂ)))))) =
      zetaCompletedPrimeBoundaryRealizedGram f := by
  unfold zetaCompletedPrimeBoundaryRealizedGram
  unfold zetaCompletedPrimeBoundaryRealizedCoordinateGram
  refine Finset.sum_congr rfl ?_
  intro ℓ hℓ
  have hface :
      zetaCompletedAutocorrelationPrimePositiveFace ℓ.1 ℓ.2
          (zetaCompletedAutocorrelationProbe f) =
        zetaCompletedPrimeHermitianSeedAmplitude ℓ.1 ℓ.2 f *
          star (zetaCompletedPrimeHermitianNegativeSeedAmplitude ℓ.1 ℓ.2 f) := by
    unfold zetaCompletedAutocorrelationPrimePositiveFace
    unfold zetaCompletedAutocorrelationProbe
    unfold ZetaCompletedAutocorrelationProbe.toAdmissible
    unfold zetaCompletedPrimeHermitianSeedAmplitude
    unfold zetaCompletedPrimeHermitianNegativeSeedAmplitude
    exact zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair
      f (zetaPrimePacketCenter ℓ.1 ℓ.2)
  calc
    (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
        ((zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter ℓ.1 ℓ.2) *
            star
              (zetaCompletedExplicitFormulaPhi f
                (-(zetaPrimePacketCenter ℓ.1 ℓ.2 : ℂ)))) +
          star
            (zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter ℓ.1 ℓ.2) *
              star
                (zetaCompletedExplicitFormulaPhi f
                  (-(zetaPrimePacketCenter ℓ.1 ℓ.2 : ℂ))))) =
        (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
          ((zetaCompletedPrimeHermitianSeedAmplitude ℓ.1 ℓ.2 f *
              star (zetaCompletedPrimeHermitianNegativeSeedAmplitude ℓ.1 ℓ.2 f)) +
            star
              (zetaCompletedPrimeHermitianSeedAmplitude ℓ.1 ℓ.2 f *
                star (zetaCompletedPrimeHermitianNegativeSeedAmplitude ℓ.1 ℓ.2 f))) := by
      unfold zetaCompletedPrimeHermitianSeedAmplitude
      unfold zetaCompletedPrimeHermitianNegativeSeedAmplitude
      rfl
    _ =
        (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
          (zetaCompletedAutocorrelationPrimePositiveFace ℓ.1 ℓ.2
              (zetaCompletedAutocorrelationProbe f) +
            star
              (zetaCompletedAutocorrelationPrimePositiveFace ℓ.1 ℓ.2
                (zetaCompletedAutocorrelationProbe f))) := by
      exact congrArg
        (fun z : ℂ =>
          (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
            (z + star z))
        hface.symm

/-- Archimedean analytic convolution transform bridge before self-paired folding. -/
theorem zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_weightedPaired
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      (2 : ℂ) *
        (zetaCompletedExplicitFormulaPhi f 0 *
          star (zetaCompletedExplicitFormulaPhi f 0)) := by
  unfold zetaCompletedExplicitFormulaArchimedeanContribution
  exact congrArg (fun z : ℂ => (2 : ℂ) * z)
    (by
      simpa using zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair f 0)

/-- The paired archimedean spectral packet contribution is the weighted paired product. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution_eq_weightedPaired
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution f =
      (2 : ℂ) *
        (zetaCompletedExplicitFormulaPhi f 0 *
          star (zetaCompletedExplicitFormulaPhi f 0)) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution_eq_weightedPaired_owner f

theorem zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_pairedSpectral
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution f := by
  exact
    (zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_weightedPaired
      f).trans
      (zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution_eq_weightedPaired
        f).symm

/-- Archimedean spectral convolution bridge after self-paired folding. -/
theorem zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f := by
  exact
    zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_pairedSpectral f

/-- The usual correction contribution of the admissible convolution autocorrelation probe is the
convolution-channel correction contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_convolutionAutocorrelation_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaCorrectionConvolutionContribution f := by
  exact Boundary.LFunctions.zetaCompletionCorrection_zero.symm

/-- The usual analytic boundary sum of the admissible convolution autocorrelation probe is the
completed time-side boundary channel. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_completedBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      completedBoundaryChannel (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  unfold completedBoundaryChannel
  exact zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_core
    (ZetaAdmissibleFunction.convolutionAutocorrelation f)

/-- The prime contribution is real on convolution-autocorrelation probes when the two-face/GNS
matrix coefficient is real-valued. -/
theorem zetaCompletedExplicitFormulaPrimeContribution_autocorrelation_im_eq_zero_of_twoFace_real
    (f : ZetaAdmissibleFunction)
    (hreal : Complex.im (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0) :
    Complex.im
        (zetaCompletedExplicitFormulaPrimeContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  unfold zetaCompletedExplicitFormulaPrimeContribution
  unfold zetaCompletedExplicitFormulaPrimePowerContribution
  exact Complex.ofReal_im
    (∑' ι : ZetaPrimePowerIndex,
      -(ι.weight *
        Complex.re
          (zetaCompletedTimeBoundaryValue
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedTimeBoundaryValue
                (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center))))

/-- The prime contribution is real on convolution-autocorrelation probes because the owner
prime channel is the time-side real distribution coerced to `ℂ`. -/
theorem zetaCompletedExplicitFormulaPrimeContribution_autocorrelation_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im
        (zetaCompletedExplicitFormulaPrimeContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  unfold zetaCompletedExplicitFormulaPrimeContribution
  unfold zetaCompletedExplicitFormulaPrimePowerContribution
  exact Complex.ofReal_im
    (∑' ι : ZetaPrimePowerIndex,
      -(ι.weight *
        Complex.re
          (zetaCompletedTimeBoundaryValue
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedTimeBoundaryValue
                (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center))))

/-- The archimedean contribution is real on convolution-autocorrelation probes by completed
boundary reconstruction, not by a self-duality condition on the seed. -/
theorem zetaCompletedExplicitFormulaArchimedeanContribution_autocorrelation_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im
        (zetaCompletedExplicitFormulaArchimedeanContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  have h :
      zetaCompletedExplicitFormulaArchimedeanContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f :=
    zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq f
  exact (congrArg Complex.im h).trans
    (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_im_eq_zero f)

/-- The correction contribution is real on convolution-autocorrelation probes. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_autocorrelation_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im
        (zetaCompletedExplicitFormulaCorrectionContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  have hcorrection :
      zetaCompletedExplicitFormulaCorrectionContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaCompletionCorrection 0 :=
    Boundary.LFunctions.zetaCompletionCorrection_zero.symm
  exact (congrArg Complex.im hcorrection).trans
    Boundary.LFunctions.zetaCompletionCorrection_zero_im

/-- If the three explicit-formula boundary channels are real, then their analytic-core sum is
real. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_im_eq_zero_of_components
    (f : ZetaAdmissibleFunction)
    (hprime :
      Complex.im
          (zetaCompletedExplicitFormulaPrimeContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0)
    (harch :
      Complex.im
          (zetaCompletedExplicitFormulaArchimedeanContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0)
    (hcorrection :
      Complex.im
          (zetaCompletedExplicitFormulaCorrectionContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0) :
    Complex.im
        (zetaCompletedExplicitFormulaBoundarySumCore
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  let g : ZetaAdmissibleFunction := ZetaAdmissibleFunction.convolutionAutocorrelation f
  let p : ℂ := zetaCompletedExplicitFormulaPrimeContribution g
  let a : ℂ := zetaCompletedExplicitFormulaArchimedeanContribution g
  let c : ℂ := zetaCompletedExplicitFormulaCorrectionContribution g
  have hcore :
      Complex.im (zetaCompletedExplicitFormulaBoundarySumCore g) =
        Complex.im (p + a + c) :=
    congrArg Complex.im (zetaCompletedExplicitFormulaBoundarySumCore_eq g)
  have hp : Complex.im p = 0 := hprime
  have ha : Complex.im a = 0 := harch
  have hc : Complex.im c = 0 := hcorrection
  calc
    Complex.im (zetaCompletedExplicitFormulaBoundarySumCore g) =
        Complex.im (p + a + c) := hcore
    _ = Complex.im (p + a) + Complex.im c := Complex.add_im (p + a) c
    _ = (Complex.im p + Complex.im a) + Complex.im c := by
      exact congrArg (fun x : ℝ => x + Complex.im c) (Complex.add_im p a)
    _ = (0 + 0) + 0 := by
      exact congrArg₂ (fun x y : ℝ => x + y)
        (congrArg₂ (fun x y : ℝ => x + y) hp ha)
        hc
    _ = 0 + 0 := by
      exact add_zero (0 + 0)
    _ = 0 := by
      exact zero_add 0

/-- The analytic-core boundary expression attached to a convolution-autocorrelation probe has
vanishing imaginary part. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im
        (zetaCompletedExplicitFormulaBoundarySumCore
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  exact
    zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_im_eq_zero_of_components
      f
      (zetaCompletedExplicitFormulaPrimeContribution_autocorrelation_im_eq_zero f)
      (zetaCompletedExplicitFormulaArchimedeanContribution_autocorrelation_im_eq_zero f)
      (zetaCompletedExplicitFormulaCorrectionContribution_autocorrelation_im_eq_zero f)

/-- The analytic boundary sum of the admissible convolution autocorrelation probe agrees with
the completed time-side Krein scalar. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ) := by
  let g : ZetaAdmissibleFunction := ZetaAdmissibleFunction.convolutionAutocorrelation f
  apply Complex.ext
  · unfold zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum
    unfold zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryKreinSum
    have hboundary :
        zetaCompletedExplicitFormulaBoundarySumAnalytic g =
          completedBoundaryChannel g := by
      unfold g
      exact
        zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_completedBoundaryChannel
          f
    calc
      Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic g) =
          Complex.re (completedBoundaryChannel g) := by
        exact congrArg Complex.re hboundary
      _ =
          Complex.re ((Complex.re (completedBoundaryChannel g)) : ℂ) := by
        exact (Complex.ofReal_re (Complex.re (completedBoundaryChannel g))).symm
  · unfold zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum
    unfold zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryKreinSum
    have hanalytic :
        zetaCompletedExplicitFormulaBoundarySumAnalytic g =
          zetaCompletedExplicitFormulaBoundarySumCore g :=
      zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_core g
    calc
      Complex.im (zetaCompletedExplicitFormulaBoundarySumAnalytic g) =
          Complex.im (zetaCompletedExplicitFormulaBoundarySumCore g) := by
        exact congrArg Complex.im hanalytic
      _ = 0 := by
        unfold g
        exact zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_im_eq_zero f
      _ =
          Complex.im ((Complex.re (completedBoundaryChannel g)) : ℂ) := by
        exact (Complex.ofReal_im (Complex.re (completedBoundaryChannel g))).symm

/-- The analytic boundary sum of a convolution-autocorrelation probe is real-valued. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im
        (zetaCompletedExplicitFormulaBoundarySumAnalytic
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      0 := by
  have hanalytic :
      zetaCompletedExplicitFormulaBoundarySumAnalytic
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaCompletedExplicitFormulaBoundarySumCore
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
    zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_core
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
  calc
    Complex.im
        (zetaCompletedExplicitFormulaBoundarySumAnalytic
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
        Complex.im
          (zetaCompletedExplicitFormulaBoundarySumCore
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) := by
      exact congrArg Complex.im hanalytic
    _ = 0 := by
      exact zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_im_eq_zero f

/-- The real part of the analytic boundary sum of a convolution-autocorrelation probe is the
raw completed finite-part boundary scalar. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_re_eq_finitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaBoundarySumAnalytic
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      completedFinitePartBoundaryChannel f := by
  let g : ZetaAdmissibleFunction := ZetaAdmissibleFunction.convolutionAutocorrelation f
  have hboundary :
      zetaCompletedExplicitFormulaBoundarySumAnalytic g =
        completedBoundaryChannel g := by
    unfold g
    exact
      zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_completedBoundaryChannel
        f
  calc
    Complex.re
        (zetaCompletedExplicitFormulaBoundarySumAnalytic
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
        Complex.re
          (zetaCompletedExplicitFormulaBoundarySumAnalytic g) := by
      rfl
    _ = Complex.re (completedBoundaryChannel g) := by
      exact congrArg Complex.re hboundary
    _ = completedFinitePartBoundaryChannel f := by
      unfold g
      exact completedBoundaryChannel_convolutionAutocorrelation_re_eq_completedFinitePartBoundaryChannel f

/-- The real part of the analytic boundary sum of a convolution-autocorrelation probe plus
the completed prime diagonal debt is the owner completed analytic boundary realization
scalar. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_re_add_primeDiagonalDebt_eq_realizationScalar
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaBoundarySumAnalytic
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedAnalyticBoundaryRealizationScalar f := by
  have hfinite :
      Complex.re
          (zetaCompletedExplicitFormulaBoundarySumAnalytic
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
        completedFinitePartBoundaryChannel f :=
    zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_re_eq_finitePartBoundaryChannel
      f
  have hrealization :
      completedFinitePartBoundaryChannel f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedAnalyticBoundaryRealizationScalar f :=
    completedFinitePartBoundaryChannel_add_primeDiagonalDebt_eq_completedAnalyticBoundaryRealizationScalar
      f
  exact
    (congrArg
      (fun x : ℝ =>
        x + Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      hfinite).trans
      hrealization

/-- The analytic boundary sum of the admissible convolution autocorrelation probe realizes
as the owner completed analytic boundary scalar.

This is the owner-level boundary normalization needed by the positive GNS route.  It is not
the raw time-side equality
`completedFinitePartBoundaryChannel f = completedBoundaryGNSNormSq f`; it is the statement
that the contour boundary realization is evaluated in the completed ordered-heart quotient. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_realizationScalar
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
        (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ) =
      (completedAnalyticBoundaryRealizationScalar f : ℂ) := by
  apply Complex.ext
  · calc
      Complex.re
          (zetaCompletedExplicitFormulaBoundarySumAnalytic
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
            (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ)) =
          Complex.re
              (zetaCompletedExplicitFormulaBoundarySumAnalytic
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)) +
            Complex.re
              (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ) := by
        exact Complex.add_re
          (zetaCompletedExplicitFormulaBoundarySumAnalytic
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))
          (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ)
      _ =
          Complex.re
              (zetaCompletedExplicitFormulaBoundarySumAnalytic
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)) +
            Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) := by
        exact congrArg
          (fun x : ℝ =>
            Complex.re
                (zetaCompletedExplicitFormulaBoundarySumAnalytic
                  (ZetaAdmissibleFunction.convolutionAutocorrelation f)) + x)
          (Complex.ofReal_re
            (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)))
      _ = completedAnalyticBoundaryRealizationScalar f := by
        exact
          zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_re_add_primeDiagonalDebt_eq_realizationScalar
            f
      _ = Complex.re (completedAnalyticBoundaryRealizationScalar f : ℂ) := by
        exact (Complex.ofReal_re (completedAnalyticBoundaryRealizationScalar f)).symm
  · calc
      Complex.im
          (zetaCompletedExplicitFormulaBoundarySumAnalytic
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
            (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ)) =
          Complex.im
              (zetaCompletedExplicitFormulaBoundarySumAnalytic
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)) +
            Complex.im
              (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ) := by
        exact Complex.add_im
          (zetaCompletedExplicitFormulaBoundarySumAnalytic
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))
          (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ)
      _ = 0 + 0 := by
        exact congrArg₂ HAdd.hAdd
          (zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_im_eq_zero f)
          (Complex.ofReal_im
            (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)))
      _ = 0 := by
        exact zero_add 0
      _ = Complex.im (completedAnalyticBoundaryRealizationScalar f : ℂ) := by
        exact (Complex.ofReal_im (completedAnalyticBoundaryRealizationScalar f)).symm

/-- The analytic boundary sum of the admissible convolution autocorrelation probe descends
to the completed ordered-heart scalar. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
        (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ) =
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f : ℂ) := by
  exact
    (zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_realizationScalar
      f).trans
      (congrArg
        (fun x : ℝ => (x : ℂ))
        (completedAnalyticBoundaryRealizationScalar_eq_explicitFormulaOrderedHeartScalar f))

/-- Compatibility wrapper name for the corrected convolution-boundary normalization. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ) := by
  exact zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_seedKreinSum f

/-- Compatibility wrapper name for the corrected convolution-boundary analytic normalization. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_autocorrelation_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ) := by
  exact zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_seedKreinSum f

/-- The analytic equality still required to complete the explicit formula. -/
def zetaCompletedExplicitFormulaAutocorrelationTarget
    (f : ZetaAdmissibleFunction) : Prop :=
  zetaCompletedZeroKreinGram f =
    zetaCompletedExplicitFormulaBoundarySum f

/-- The target proposition unfolds to the zero-side/boundary equality. -/
theorem zetaCompletedExplicitFormulaAutocorrelationTarget_iff
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaAutocorrelationTarget f ↔
      zetaCompletedZeroKreinGram f =
        zetaCompletedExplicitFormulaBoundarySum f := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
