import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaCompletedPositiveBoundary.ZetaCompletedLowerWeight.Owner

/-!
# Completed positive boundary realization

This file owns the positive-boundary precone, ordered-heart quotient, and analytic
boundary realization scalar before the prime two-face tomography comparison.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- A completed positive-boundary precone element.

The positive representative is the finite square-energy window.  The absorbed representative
is the finite representative after applying the finite diagonal-debt absorption normalization.
The scalar is the completed realization of that absorbed representative. -/
structure CompletedPositiveBoundaryPreconeElement where
  scalar : ℝ
  positiveRepresentative : ℕ → ℝ
  absorbedRepresentative : ℕ → ℝ
  absorptionDefect : ℕ → ℝ
  positiveRepresentative_nonnegative :
    ∀ N : ℕ, 0 ≤ positiveRepresentative N
  absorbedRepresentative_tendsto_scalar :
    Tendsto absorbedRepresentative atTop (𝓝 scalar)
  absorptionDefect_eq :
    ∀ N : ℕ,
      absorptionDefect N =
        absorbedRepresentative N - positiveRepresentative N

/-- The completed positive-boundary precone element attached to a zeta admissible function. -/
def completedPositiveBoundaryPreconeElement
    (f : ZetaAdmissibleFunction) : CompletedPositiveBoundaryPreconeElement :=
  { scalar :=
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))
    positiveRepresentative :=
      fun N : ℕ => finitePositiveSquareEnergyWindow N f
    absorbedRepresentative :=
      fun N : ℕ => finitePositiveRenormalizedBoundaryWindow N f
    absorptionDefect :=
      fun N : ℕ => finiteDiagonalDebtAbsorptionDefect N f
    positiveRepresentative_nonnegative :=
      fun N : ℕ => finitePositiveSquareEnergyWindow_nonnegative N f
    absorbedRepresentative_tendsto_scalar :=
      finitePositiveRenormalizedBoundaryWindow_tendsto_boundaryChannel f
    absorptionDefect_eq := by
      intro N
      change
        finiteDiagonalDebtAbsorptionDefect N f =
          finitePositiveRenormalizedBoundaryWindow N f -
            finitePositiveSquareEnergyWindow N f
      rfl }

/-- The absorption defect of the completed positive-boundary precone element is the finite
debt-absorption channel. -/
theorem completedPositiveBoundaryPreconeElement_absorptionDefect_eq_debtAbsorption
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).absorptionDefect N =
      finitePartDebtAbsorptionWindow N f := by
  exact finiteDiagonalDebtAbsorptionDefect_eq_finitePartDebtAbsorptionWindow N f

/-- The scalar realization of the completed positive-boundary precone element is the real
completed boundary channel on the convolution-autocorrelation probe. -/
theorem completedPositiveBoundaryPreconeElement_scalar_eq_boundaryChannel_re
    (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).scalar =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  rfl

/-- The ordered-heart class represented by the completed positive-boundary object.  Its scalar
is induced by `completedBoundaryHilbertPairing`, not by a separate analytic packet norm. -/
def completedPositiveBoundaryOrderedHeartClass
    (f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertSource :=
  completedBoundaryHilbertSource f

/-- The scalar realization of the completed positive-boundary precone element is the reduced
time-pairing scalar of its completed Hilbert source. -/
theorem completedPositiveBoundaryPreconeElement_scalar_eq_timePairingScalar
    (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).scalar =
      completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  have hscalar :
      (completedPositiveBoundaryPreconeElement f).scalar =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    completedPositiveBoundaryPreconeElement_scalar_eq_boundaryChannel_re f
  have hpair :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
    change
      completedBoundaryHilbertPairing
          (completedBoundaryHilbertSource f)
          (completedBoundaryHilbertSource f) =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))
    exact completedBoundaryHilbertPairing_source_self_eq_boundaryChannel_re f
  exact hscalar.trans hpair.symm

/-- The ordered-heart class represented by the completed finite-part boundary channel.

The raw finite-part scalar is the time-side representative.  Its class in the completed
ordered heart is the absorbed positive-defect class after lower-weight diagonal-debt
transport. -/
def completedFinitePartBoundaryOrderedHeartClass
    (f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertSource :=
  completedPositiveBoundaryOrderedHeartClass f

/-- The raw finite-part scalar realizes as the time-pairing scalar of its ordered-heart
representative. -/
theorem completedFinitePartBoundaryChannel_eq_timePairingScalar
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f =
      completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  have hfinite :
      completedFinitePartBoundaryChannel f =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f
  have hpair :
      completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
    change
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))
    exact
      (completedPositiveBoundaryPreconeElement_scalar_eq_timePairingScalar f).symm.trans
        (completedPositiveBoundaryPreconeElement_scalar_eq_boundaryChannel_re f)
  exact hfinite.trans hpair.symm

/-- The ordered-heart class represented by the positive square object.  It has the same
completed Hilbert-source representative as the absorbed finite-part class; the difference is
carried by the lower-weight radical absorption face. -/
def completedPositiveSquareBoundaryOrderedHeartClass
    (f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertSource :=
  completedBoundaryHilbertSource f

/-- The ordered-heart class represented by the lower-weight absorption defect. -/
def completedPositiveBoundaryAbsorptionDefectOrderedHeartClass
    (_f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertSource :=
  0

/-- The lower-weight absorption defect is radical in the completed ordered-heart quotient. -/
theorem completedPositiveBoundaryAbsorptionDefectOrderedHeartClass_lowerWeightRadical
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertSource.LowerWeightRadical
      (completedPositiveBoundaryAbsorptionDefectOrderedHeartClass f) := by
  change CompletedBoundaryHilbertSource.LowerWeightRadical 0
  exact completedBoundaryHilbertSource_zero_lowerWeightRadical

/-- The absorbed positive-boundary class and square-only class have the same ordered-heart
representative. -/
theorem completedPositiveBoundaryOrderedHeartClass_eq_square
    (f : ZetaAdmissibleFunction) :
    completedPositiveBoundaryOrderedHeartClass f =
      completedPositiveSquareBoundaryOrderedHeartClass f := by
  rfl

/-- The absorbed positive-boundary class and square-only class are GNS-tomographically
equivalent in the completed ordered heart. -/
theorem completedPositiveBoundaryOrderedHeartClass_GNSTomographicallyEquivalent_square
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent
      (completedPositiveBoundaryOrderedHeartClass f)
      (completedPositiveSquareBoundaryOrderedHeartClass f) := by
  exact completedBoundaryHilbertSource_GNSTomography_of_eq
    (completedPositiveBoundaryOrderedHeartClass_eq_square f)

/-- The absorbed positive-boundary class and square-only class have the same ordered-heart
scalar by GNS tomography. -/
theorem completedPositiveBoundaryOrderedHeartScalar_eq_square_by_GNSTomography
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedOrderedHeartScalar
        (completedPositiveSquareBoundaryOrderedHeartClass f) := by
  exact completedOrderedHeartScalar_eq_of_GNSTomography
    (completedPositiveBoundaryOrderedHeartClass_GNSTomographicallyEquivalent_square f)

/-- The finite-part boundary class is the absorbed positive-boundary class in the completed
ordered heart. -/
theorem completedFinitePartBoundaryOrderedHeartClass_eq_positiveBoundary
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryOrderedHeartClass f =
      completedPositiveBoundaryOrderedHeartClass f := by
  rfl

/-- The finite-part boundary class is GNS-tomographically equivalent to the positive square
class.  This is the ordered-heart version of lower-weight diagonal-debt absorption. -/
theorem completedFinitePartBoundaryClass_GNSTomographicallyEquivalent_positiveSquare
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent
      (completedFinitePartBoundaryOrderedHeartClass f)
      (completedPositiveSquareBoundaryOrderedHeartClass f) := by
  exact CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.trans
    (completedBoundaryHilbertSource_GNSTomography_of_eq
      (completedFinitePartBoundaryOrderedHeartClass_eq_positiveBoundary f))
    (completedPositiveBoundaryOrderedHeartClass_GNSTomographicallyEquivalent_square f)

/-- The finite-part boundary class has the same ordered-heart scalar as the positive square
class. -/
theorem completedFinitePartBoundaryOrderedHeartScalar_eq_positiveSquare
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      completedOrderedHeartScalar
        (completedPositiveSquareBoundaryOrderedHeartClass f) := by
  exact completedOrderedHeartScalar_eq_of_GNSTomography
    (completedFinitePartBoundaryClass_GNSTomographicallyEquivalent_positiveSquare f)

/-- If the reduced time-pairing scalar is reconstructed as the ordered-heart GNS scalar, then
the completed positive precone scalar is the ordered-heart scalar.  This representative-level
comparison is kept separate from the quotient-level ordered-heart scalar descent. -/
theorem completedPositiveBoundaryPreconeElement_scalar_eq_orderedHeartScalar_of_timePairingScalar_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction)
    (hcomparison :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f)) :
    (completedPositiveBoundaryPreconeElement f).scalar =
      completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  exact
    (completedPositiveBoundaryPreconeElement_scalar_eq_timePairingScalar f).trans
      hcomparison

/-- The square-only ordered-heart scalar is the completed GNS norm-square. -/
theorem completedPositiveSquareBoundaryOrderedHeartScalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedPositiveSquareBoundaryOrderedHeartClass f) =
      completedBoundaryGNSNormSq f := by
  change
    completedOrderedHeartScalar (completedBoundaryHilbertSource f) =
      completedBoundaryGNSNormSq f
  exact (completedBoundaryGNSNormSq_eq_orderedHeartScalar f).symm

/-- The completed finite-part boundary class has GNS norm-square scalar in the completed
ordered heart. -/
theorem completedFinitePartBoundaryOrderedHeartScalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      completedBoundaryGNSNormSq f := by
  exact
    (completedFinitePartBoundaryOrderedHeartScalar_eq_positiveSquare f).trans
      (completedPositiveSquareBoundaryOrderedHeartScalar_eq_GNSNormSq f)

/-- The renormalized defect-kernel channel is the scalar of the positive GNS presentation.

This is only channel bookkeeping: the prime coordinate is the positive defect-square channel,
and the archimedean/correction coordinates are the corresponding packet Gram coordinates. -/
theorem completedRenormalizedDefectKernelBoundaryChannel_eq_positivePresentationScalar
    (f : ZetaAdmissibleFunction) :
    completedRenormalizedDefectKernelBoundaryChannel f =
      zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
  let P : ℝ := Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f)
  let A : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let C : ℝ :=
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  have hpresentation :
      zetaCompletedGNSPositiveBoundaryPresentationScalar f = P + A + C := by
    exact
      zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_primeDefect_add_archimedean_add_correction
        f
  change P + A + C = zetaCompletedGNSPositiveBoundaryPresentationScalar f
  exact hpresentation.symm

/-- The positive GNS presentation scalar and the completed symmetrized two-face scalar assemble
to the completed diagonal-debt presentation. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationScalar_add_symmetrized_eq_diagonalDebtPresentation
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationScalar f +
        Complex.re (zetaCompletedGNSSymmetrizedBoundaryForm f) =
      Complex.re
        (zetaCompletedGNSDiagonalDebtBoundaryForm f +
          ((ZetaHermitianPacketEnsemble.archimedeanPacketGram
              (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
            (ZetaHermitianPacketEnsemble.correctionPacketGram
              (zetaCompletedHermitianBoundaryDefect f) : ℂ))) := by
  have hform :
      zetaCompletedGNSPositiveBoundaryPresentationForm f +
          zetaCompletedGNSSymmetrizedBoundaryForm f =
        zetaCompletedGNSDiagonalDebtBoundaryForm f +
          ((ZetaHermitianPacketEnsemble.archimedeanPacketGram
              (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
            (ZetaHermitianPacketEnsemble.correctionPacketGram
              (zetaCompletedHermitianBoundaryDefect f) : ℂ)) :=
    zetaCompletedGNSPositiveBoundaryPresentationForm_add_symmetrized_eq_diagonalDebt_add_archCorrection
      f
  change
    Complex.re (zetaCompletedGNSPositiveBoundaryPresentationForm f) +
        Complex.re (zetaCompletedGNSSymmetrizedBoundaryForm f) =
      Complex.re
        (zetaCompletedGNSDiagonalDebtBoundaryForm f +
          ((ZetaHermitianPacketEnsemble.archimedeanPacketGram
              (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
            (ZetaHermitianPacketEnsemble.correctionPacketGram
              (zetaCompletedHermitianBoundaryDefect f) : ℂ)))
  calc
    Complex.re (zetaCompletedGNSPositiveBoundaryPresentationForm f) +
        Complex.re (zetaCompletedGNSSymmetrizedBoundaryForm f) =
        Complex.re
          (zetaCompletedGNSPositiveBoundaryPresentationForm f +
            zetaCompletedGNSSymmetrizedBoundaryForm f) := by
      exact
        (Complex.add_re
          (zetaCompletedGNSPositiveBoundaryPresentationForm f)
          (zetaCompletedGNSSymmetrizedBoundaryForm f)).symm
    _ =
        Complex.re
          (zetaCompletedGNSDiagonalDebtBoundaryForm f +
            ((ZetaHermitianPacketEnsemble.archimedeanPacketGram
                (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
              (ZetaHermitianPacketEnsemble.correctionPacketGram
                (zetaCompletedHermitianBoundaryDefect f) : ℂ))) := by
      exact congrArg Complex.re hform

/-- The positive GNS presentation scalar is the completed renormalized defect-kernel channel.

This is positive-side bookkeeping only.  The raw finite-part boundary scalar is connected to
this channel by the lower-weight diagonal-debt transport theorem in the descent layer. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_renormalizedDefectKernelBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationScalar f =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  exact (completedRenormalizedDefectKernelBoundaryChannel_eq_positivePresentationScalar f).symm

/-- The positive-boundary precone scalar is the finite-part time-pairing scalar. -/
theorem completedPositiveBoundaryPreconeElement_scalar_eq_finitePartBoundaryTimePairingScalar
    (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).scalar =
      completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  have hpositive :
      (completedPositiveBoundaryPreconeElement f).scalar =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    completedPositiveBoundaryPreconeElement_scalar_eq_timePairingScalar f
  have hclass :
      completedPositiveBoundaryOrderedHeartClass f =
        completedFinitePartBoundaryOrderedHeartClass f :=
    (completedFinitePartBoundaryOrderedHeartClass_eq_positiveBoundary f).symm
  exact hpositive.trans (congrArg completedBoundaryTimePairingScalar hclass)

/-- The positive GNS presentation scalar is the completed ordered-heart GNS norm-square.

This is the remaining positive-side packet comparison: the completed defect-square
presentation must be identified with the scalar induced by the completed Hilbert/GNS packet
kernel.  It is independent of the raw finite-part boundary scalar. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationScalar f =
      completedBoundaryGNSNormSq f := by
  have hsource :
      completedBoundaryHermitianGNSScalar (completedBoundaryHilbertSource f) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
    completedBoundaryHermitianGNSScalar_source_eq_positivePresentationScalar f
  have hgns :
      completedBoundaryGNSNormSq f =
        completedBoundaryHermitianGNSScalar (completedBoundaryHilbertSource f) :=
    completedBoundaryGNSNormSq_eq_hermitianGNSScalar f
  exact hsource.symm.trans hgns.symm

/-- The completed renormalized defect-kernel channel is the ordered-heart GNS norm-square.
This is the owner-level payoff of the weight-triangular realization: after finite
diagonal-debt absorption, the completed channel is represented by the positive Hermitian
defect kernel. -/
theorem completedRenormalizedDefectKernelBoundaryChannel_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedRenormalizedDefectKernelBoundaryChannel f =
      completedBoundaryGNSNormSq f := by
  exact
    (completedRenormalizedDefectKernelBoundaryChannel_eq_positivePresentationScalar
      f).trans
      (zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_GNSNormSq f)

/-- The completed finite-part boundary class has scalar represented by the completed
renormalized positive defect-kernel channel. -/
theorem completedFinitePartBoundaryOrderedHeartScalar_eq_renormalizedDefectKernel
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  exact
    (completedFinitePartBoundaryOrderedHeartScalar_eq_GNSNormSq f).trans
      (completedRenormalizedDefectKernelBoundaryChannel_eq_GNSNormSq f).symm

/-- The completed ordered-heart quotient class represented by the finite-part boundary
channel after lower-weight absorption. -/
def completedFinitePartBoundaryOrderedHeartQuotientClass
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryOrderedHeartClass :=
  completedBoundaryOrderedHeartClass
    (completedFinitePartBoundaryOrderedHeartClass f)

/-- The completed ordered-heart quotient class represented by the positive square boundary
object. -/
def completedPositiveSquareBoundaryOrderedHeartQuotientClass
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryOrderedHeartClass :=
  completedBoundaryOrderedHeartClass
    (completedPositiveSquareBoundaryOrderedHeartClass f)

/-- The completed finite-part boundary quotient class is the positive square quotient class. -/
theorem completedFinitePartBoundaryOrderedHeartQuotientClass_eq_positiveSquare
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryOrderedHeartQuotientClass f =
      completedPositiveSquareBoundaryOrderedHeartQuotientClass f := by
  exact completedBoundaryOrderedHeartClass_eq_of_GNSTomography
    (completedFinitePartBoundaryClass_GNSTomographicallyEquivalent_positiveSquare f)

/-- The finite-part boundary quotient scalar is the scalar of its representative. -/
theorem completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
      completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  rfl

/-- The positive square quotient scalar is the scalar of its representative. -/
theorem completedPositiveSquareBoundaryOrderedHeartQuotientScalar_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (completedPositiveSquareBoundaryOrderedHeartQuotientClass f) =
      completedOrderedHeartScalar
        (completedPositiveSquareBoundaryOrderedHeartClass f) := by
  rfl

/-- The completed finite-part boundary quotient scalar is the positive square quotient
scalar. -/
theorem completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_positiveSquare
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
      completedBoundaryOrderedHeartClassScalar
        (completedPositiveSquareBoundaryOrderedHeartQuotientClass f) := by
  exact congrArg completedBoundaryOrderedHeartClassScalar
    (completedFinitePartBoundaryOrderedHeartQuotientClass_eq_positiveSquare f)

/-- The completed finite-part boundary quotient scalar is the completed GNS norm-square. -/
theorem completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
      completedBoundaryGNSNormSq f := by
  exact
    (completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_orderedHeartScalar
      f).trans
      (completedFinitePartBoundaryOrderedHeartScalar_eq_GNSNormSq f)

/-- The completed finite-part boundary quotient scalar is represented by the completed
renormalized positive defect-kernel channel. -/
theorem completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_renormalizedDefectKernel
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  exact
    (completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_orderedHeartScalar
      f).trans
      (completedFinitePartBoundaryOrderedHeartScalar_eq_renormalizedDefectKernel f)

/-- The finite-part boundary quotient scalar is nonnegative by descent to the positive GNS
square. -/
theorem completedFinitePartBoundaryOrderedHeartQuotientScalar_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤
      completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) := by
  have hgns : 0 ≤ completedBoundaryGNSNormSq f :=
    completedBoundaryGNSNormSq_nonnegative f
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    (completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_GNSNormSq f).symm
    hgns

/-- The completed analytic boundary realization class attached to an admissible seed.

This is the owner object for evaluating the contour boundary representative in the completed
ordered-heart quotient.  It is the finite-part boundary class after lower-weight absorption,
not the raw time-side scalar. -/
def completedAnalyticBoundaryRealizationClass
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryOrderedHeartClass :=
  completedFinitePartBoundaryOrderedHeartQuotientClass f

/-- The scalar induced by the completed analytic boundary realization. -/
def completedAnalyticBoundaryRealizationScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedBoundaryOrderedHeartClassScalar
    (completedAnalyticBoundaryRealizationClass f)

/-- The analytic boundary realization class is the completed finite-part ordered-heart
quotient class. -/
theorem completedAnalyticBoundaryRealizationClass_eq_finitePartQuotient
    (f : ZetaAdmissibleFunction) :
    completedAnalyticBoundaryRealizationClass f =
      completedFinitePartBoundaryOrderedHeartQuotientClass f := by
  rfl

/-- The analytic boundary realization scalar is the completed finite-part quotient scalar. -/
theorem completedAnalyticBoundaryRealizationScalar_eq_finitePartQuotientScalar
    (f : ZetaAdmissibleFunction) :
    completedAnalyticBoundaryRealizationScalar f =
      completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) := by
  rfl

/-- The analytic boundary realization scalar is the completed GNS norm-square. -/
theorem completedAnalyticBoundaryRealizationScalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedAnalyticBoundaryRealizationScalar f =
      completedBoundaryGNSNormSq f := by
  exact
    (completedAnalyticBoundaryRealizationScalar_eq_finitePartQuotientScalar
      f).trans
      (completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_GNSNormSq f)

/-- The analytic boundary realization scalar is represented by the completed renormalized
positive defect-kernel channel. -/
theorem completedAnalyticBoundaryRealizationScalar_eq_renormalizedDefectKernel
    (f : ZetaAdmissibleFunction) :
    completedAnalyticBoundaryRealizationScalar f =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  exact
    (completedAnalyticBoundaryRealizationScalar_eq_finitePartQuotientScalar
      f).trans
      (completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_renormalizedDefectKernel f)

/-- The analytic boundary realization scalar is nonnegative by the completed GNS positive
cone. -/
theorem completedAnalyticBoundaryRealizationScalar_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedAnalyticBoundaryRealizationScalar f := by
  have hquotient :
      0 ≤
        completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) :=
    completedFinitePartBoundaryOrderedHeartQuotientScalar_nonnegative f
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    (completedAnalyticBoundaryRealizationScalar_eq_finitePartQuotientScalar f).symm
    hquotient

/-- The completed analytic boundary realization scalar is the ordered-heart scalar of the
finite-part boundary class. -/
theorem completedAnalyticBoundaryRealizationScalar_eq_finitePartOrderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedAnalyticBoundaryRealizationScalar f =
      completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  exact
    (completedAnalyticBoundaryRealizationScalar_eq_finitePartQuotientScalar
      f).trans
      (completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_orderedHeartScalar f)

/-- The raw completed time-side boundary scalar.  This is the scalar represented by the
completed explicit-formula boundary channel before passing through the positive GNS
ordered-heart realization. -/
noncomputable def completedRawTimeBoundaryScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))

/-- Compatibility name for the raw symmetrized boundary scalar used in lower-weight descent.
The owner scalar is time-side; spectral packet comparisons are separate realization theorems. -/
noncomputable def completedSymmetrizedTwoFaceBoundaryScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedRawTimeBoundaryScalar f

/-- The positive defect-kernel completed boundary scalar.

The owner scalar is the completed ordered-heart/GNS norm-square.  Complex defect-kernel
presentations compare to this scalar only through separate transport theorems. -/
noncomputable def completedPositiveDefectKernelBoundaryScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedBoundaryGNSNormSq f

/-- The completed renormalized defect-kernel channel is the positive GNS boundary scalar. -/
theorem completedRenormalizedDefectKernelBoundaryChannel_eq_positiveDefectKernelBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedRenormalizedDefectKernelBoundaryChannel f =
      completedPositiveDefectKernelBoundaryScalar f := by
  exact completedRenormalizedDefectKernelBoundaryChannel_eq_GNSNormSq f

/-- Archimedean raw-side transform bridge. -/
theorem archimedeanBoundaryChannel_convolutionAutocorrelation_eq_archimedeanConvolutionContribution
    (f : ZetaAdmissibleFunction) :
    archimedeanBoundaryChannel (convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f := by
  change
    zetaCompletedExplicitFormulaArchimedeanContribution
        (convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f
  exact
    zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_paired_owner
      f

/-- Correction raw-side transform bridge. -/
theorem poleBoundaryChannel_convolutionAutocorrelation_eq_correctionConvolutionContribution
    (f : ZetaAdmissibleFunction) :
    poleBoundaryChannel (convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaCorrectionConvolutionContribution f := by
  change
    zetaCompletedExplicitFormulaCorrectionContribution
        (convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaCorrectionConvolutionContribution f
  exact
    zetaCompletedExplicitFormulaCorrectionContribution_convolutionAutocorrelation_eq_owner
      f

/-- The raw completed time-side scalar is the real completed boundary channel. -/
theorem completedRawTimeBoundaryScalar_eq_completedBoundaryChannel_re
    (f : ZetaAdmissibleFunction) :
    completedRawTimeBoundaryScalar f =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  rfl

/-- The completed finite-part channel is the raw completed time-side boundary scalar.

This is the raw analytic reconstruction part of lower-weight descent.  It deliberately does
not compare the time-side prime distribution with the finite paired spectral packet. -/
theorem completedFinitePartBoundaryChannel_eq_symmetrizedTwoFaceBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f =
      completedSymmetrizedTwoFaceBoundaryScalar f := by
  have hfinite :
      completedFinitePartBoundaryChannel f =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f
  have hraw :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedRawTimeBoundaryScalar f :=
    (completedRawTimeBoundaryScalar_eq_completedBoundaryChannel_re f).symm
  have halias :
      completedRawTimeBoundaryScalar f =
        completedSymmetrizedTwoFaceBoundaryScalar f := by
    rfl
  exact hfinite.trans (hraw.trans halias)

/-- The finite-part time-pairing scalar is the absorbed positive-boundary precone scalar. -/
theorem completedFinitePartBoundaryTimePairingScalar_eq_positivePreconeScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      (completedPositiveBoundaryPreconeElement f).scalar := by
  have hclass :
      completedFinitePartBoundaryOrderedHeartClass f =
        completedPositiveBoundaryOrderedHeartClass f :=
    completedFinitePartBoundaryOrderedHeartClass_eq_positiveBoundary f
  have hpair :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        (completedPositiveBoundaryPreconeElement f).scalar :=
    (completedPositiveBoundaryPreconeElement_scalar_eq_timePairingScalar f).symm
  exact (congrArg completedBoundaryTimePairingScalar hclass).trans hpair

/-- The finite absorption defect is lower-weight radical in the completed ordered-heart
quotient.

This is not a pointwise real-limit statement.  The diagonal-debt absorption face may be large
as a real finite-window correction; it is harmless because it is killed by the completed
lower-weight radical. -/
theorem completedPositiveBoundaryPreconeElement_absorptionDefect_lowerWeightRadical
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertSource.LowerWeightRadical
      (completedPositiveBoundaryAbsorptionDefectOrderedHeartClass f) := by
  exact completedPositiveBoundaryAbsorptionDefectOrderedHeartClass_lowerWeightRadical f

/-- The absorbed positive-boundary ordered-heart class: positive square class plus the
lower-weight absorption face. -/
def completedPositiveBoundaryAbsorbedOrderedHeartClass
    (f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertSource :=
  completedPositiveBoundaryOrderedHeartClass f +
    completedPositiveBoundaryAbsorptionDefectOrderedHeartClass f

/-- The absorbed finite-window precone scalar is realized by the absorbed ordered-heart source.

This is the source-probe realization theorem for the scalar/window absorption certificate:
the scalar obtained as the limit of absorbed finite representatives is the time-pairing scalar
of the corresponding absorbed Hilbert source. -/
theorem completedPositiveBoundaryPreconeElement_scalar_eq_absorbedOrderedHeartTimePairingScalar
    (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).scalar =
      completedBoundaryTimePairingScalar
        (completedPositiveBoundaryAbsorbedOrderedHeartClass f) := by
  have hpositive :
      (completedPositiveBoundaryPreconeElement f).scalar =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    completedPositiveBoundaryPreconeElement_scalar_eq_timePairingScalar f
  have habsorbed :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryAbsorbedOrderedHeartClass f) := by
    change
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f + 0)
    exact
      (congrArg completedBoundaryTimePairingScalar
        (add_zero (completedPositiveBoundaryOrderedHeartClass f))).symm
  exact hpositive.trans habsorbed

/-- Radical absorption does not change the time-pairing scalar of the absorbed ordered-heart
source. -/
theorem completedPositiveBoundaryAbsorbedOrderedHeartTimePairingScalar_eq_positiveBoundaryTimePairingScalar
    (f : ZetaAdmissibleFunction)
    (_habsorption :
      CompletedBoundaryHilbertSource.LowerWeightRadical
        (completedPositiveBoundaryAbsorptionDefectOrderedHeartClass f)) :
    completedBoundaryTimePairingScalar
        (completedPositiveBoundaryAbsorbedOrderedHeartClass f) =
      completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  change
    completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f + 0) =
      completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f)
  exact congrArg completedBoundaryTimePairingScalar
    (add_zero (completedPositiveBoundaryOrderedHeartClass f))

/-- The positive-boundary time-pairing scalar is the raw completed time-side boundary scalar. -/
theorem completedPositiveBoundaryTimePairingScalar_eq_rawTimeBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedRawTimeBoundaryScalar f := by
  have hprecone :
      (completedPositiveBoundaryPreconeElement f).scalar =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    completedPositiveBoundaryPreconeElement_scalar_eq_timePairingScalar f
  have hscalar :
      (completedPositiveBoundaryPreconeElement f).scalar =
        completedRawTimeBoundaryScalar f := by
    exact (completedPositiveBoundaryPreconeElement_scalar_eq_boundaryChannel_re f).trans
      (completedRawTimeBoundaryScalar_eq_completedBoundaryChannel_re f).symm
  exact hprecone.symm.trans hscalar

/-- The positive ordered-heart scalar is the completed positive defect-kernel scalar. -/
theorem completedPositiveBoundaryOrderedHeartScalar_eq_positiveDefectKernelBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedPositiveDefectKernelBoundaryScalar f := by
  change
    completedOrderedHeartScalar (completedBoundaryHilbertSource f) =
      completedPositiveDefectKernelBoundaryScalar f
  have hgns :
      completedOrderedHeartScalar (completedBoundaryHilbertSource f) =
        completedBoundaryGNSNormSq f := by
    exact (completedBoundaryGNSNormSq_eq_orderedHeartScalar f).symm
  have hrenormalized :
      completedBoundaryGNSNormSq f =
        completedRenormalizedDefectKernelBoundaryChannel f :=
    (completedRenormalizedDefectKernelBoundaryChannel_eq_GNSNormSq f).symm
  have hpositive :
      completedRenormalizedDefectKernelBoundaryChannel f =
        completedPositiveDefectKernelBoundaryScalar f :=
    completedRenormalizedDefectKernelBoundaryChannel_eq_positiveDefectKernelBoundaryScalar
      f
  exact hgns.trans (hrenormalized.trans hpositive)

/-- The raw time-side scalar is the completed finite-part boundary channel. -/
theorem completedRawTimeBoundaryScalar_eq_finitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    completedRawTimeBoundaryScalar f =
      completedFinitePartBoundaryChannel f := by
  have hraw :
      completedRawTimeBoundaryScalar f =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    completedRawTimeBoundaryScalar_eq_completedBoundaryChannel_re f
  have hfinite :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedFinitePartBoundaryChannel f :=
    (completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f).symm
  exact hraw.trans hfinite

/-- The finite positive renormalized boundary windows converge to the completed finite-part
boundary channel. -/
theorem finitePositiveRenormalizedBoundaryWindow_tendsto_completedFinitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePositiveRenormalizedBoundaryWindow N f)
      atTop
      (𝓝 (completedFinitePartBoundaryChannel f)) := by
  have hfinite :
      (fun N : ℕ => finitePositiveRenormalizedBoundaryWindow N f) =
        (fun N : ℕ => finitePartBoundaryWindow N f) := by
    funext N
    exact finitePositiveRenormalizedBoundaryWindow_eq_finitePartBoundaryWindow N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop (𝓝 (completedFinitePartBoundaryChannel f)))
    hfinite.symm
    (finitePartBoundaryWindow_tendsto_completedFinitePartBoundaryChannel f)

/-- The scalar of the completed boundary weight stream is the completed finite-part boundary
channel. -/
theorem completedBoundaryWeightStream_scalar_eq_completedFinitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryWeightStream f).scalar =
      completedFinitePartBoundaryChannel f := by
  have hstream :
      (completedBoundaryWeightStream f).scalar =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    completedBoundaryWeightStream_scalar_eq_boundaryChannel_re f
  have hfinite :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedFinitePartBoundaryChannel f :=
    (completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f).symm
  exact hstream.trans hfinite

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
