import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaPrimeDistributionTransport.OwnerParts.Part02

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

def CompletedFiniteWindowPrimeDistributionReconstruction.toSummedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    CompletedSummedPrimeContourTimeTransport f where
  timeWindow := D.finiteWindow
  contourWindow := D.finiteWindow
  remainderWindow := fun _N : ℕ => 0
  timeWindow_eq := D.finiteWindow_eq_timeWindow
  contourWindow_eq := D.finiteWindow_eq_contourWindow
  finite_additive_transport := by
    intro N
    exact (add_zero (D.finiteWindow N)).trans rfl
  timeWindow_tendsto :=
    CompletedFiniteWindowPrimeDistributionReconstruction.finiteWindow_tendsto_timePairing
      f D
  remainderWindow_tendsto_zero := tendsto_const_nhds
  contourWindow_tendsto :=
    CompletedFiniteWindowPrimeDistributionReconstruction.finiteWindow_tendsto_contourPairing
      f D

/-- Completed prime-power transport from the time/log presentation to the spectral-sample
presentation on an autocorrelation probe.

This is the irreducible comparison content behind the prime transport bridge: the completed
time-side prime-power contribution and the completed contour/spectral prime-power
contribution are two presentations of the same completed finite-window prime transport. -/
theorem completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerDistributionTransport_core
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
      completedSpectralPrimeOffDiagonalChannel f := by
  have htime :
      completedPrimeOffDiagonalChannel f =
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) :=
    (completedPrimeTimeDistributionPairing_eq_completedPrimeOffDiagonalChannel f).symm
  have htransport :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) :=
    completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_ownerFiniteWindowTransport
      f D
  have hcontour :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        completedSpectralPrimeOffDiagonalChannel f := by
    have hrealized :
        completedPrimeContourRealizedTimeDistributionPairing
            (convolutionAutocorrelation f) =
          completedPrimeSpectralDistributionPairing
            (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f)) := by
      rfl
    have hspectral :
        completedSpectralPrimeOffDiagonalChannel f =
          completedPrimeSpectralDistributionPairing
            (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f)) :=
      completedSpectralPrimeOffDiagonalChannel_eq_spectralDistributionPairing
        f
    exact hrealized.trans hspectral.symm
  exact htime.trans (htransport.trans hcontour)

/-- Completed prime-power transport from the time/log presentation to the spectral-sample
presentation, using the visible summed contour/time transport provider. -/
theorem completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerSummedDistributionTransport_core
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeOffDiagonalChannel f =
      completedSpectralPrimeOffDiagonalChannel f := by
  have htime :
      completedPrimeOffDiagonalChannel f =
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) :=
    (completedPrimeTimeDistributionPairing_eq_completedPrimeOffDiagonalChannel f).symm
  have htransport :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) :=
    completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_ownerSummedTransport
      f D
  have hcontour :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        completedSpectralPrimeOffDiagonalChannel f := by
    have hrealized :
        completedPrimeContourRealizedTimeDistributionPairing
            (convolutionAutocorrelation f) =
          completedPrimeSpectralDistributionPairing
            (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f)) := by
      rfl
    have hspectral :
        completedSpectralPrimeOffDiagonalChannel f =
          completedPrimeSpectralDistributionPairing
            (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f)) :=
      completedSpectralPrimeOffDiagonalChannel_eq_spectralDistributionPairing
        f
    exact hrealized.trans hspectral.symm
  exact htime.trans (htransport.trans hcontour)

/-- Completed prime-power transport from the time/log presentation to the spectral-sample
presentation on an autocorrelation probe.

This is the irreducible comparison content behind the prime transport bridge: the completed
time-side prime-power contribution and the completed contour/spectral prime-power
contribution are two presentations of the same completed finite-window prime transport. -/
theorem zetaCompletedExplicitFormulaPrimePowerContribution_re_eq_spectralSampleContribution_re_ownerDistributionTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Complex.re
        (zetaCompletedExplicitFormulaPrimePowerContribution
          (convolutionAutocorrelation f)) =
      Complex.re
        (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
          (convolutionAutocorrelation f)) := by
  have hchannel :
      completedPrimeOffDiagonalChannel f =
        completedSpectralPrimeOffDiagonalChannel f :=
    completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerDistributionTransport_core
      f D
  have htime :
      completedPrimeOffDiagonalChannel f =
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f)) :=
    completedPrimeOffDiagonalChannel_eq_primePowerContribution_re f
  have hspectral :
      completedSpectralPrimeOffDiagonalChannel f =
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
            (convolutionAutocorrelation f)) :=
    rfl
  exact htime.symm.trans (hchannel.trans hspectral)

/-- Completed prime distribution transport from the physical/time presentation to the
spectral contour presentation.

This is the owner bridge comparing the completed time/log-side prime channel with the
completed spectral/Laplace-side prime channel.  It is not a pointwise identification of
time samples with Laplace samples; it is the completed finite-window transport statement. -/
theorem completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerDistributionTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
      completedSpectralPrimeOffDiagonalChannel f := by
  exact completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerDistributionTransport_core
    f D

/-- Completed prime distribution transport from the physical/time presentation to the
spectral contour presentation, using the summed contour/time provider. -/
theorem completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerSummedDistributionTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeOffDiagonalChannel f =
      completedSpectralPrimeOffDiagonalChannel f := by
  exact
    completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerSummedDistributionTransport_core
      f D

/-- Completed prime finite-window normalization reaches the two-face/GNS boundary scalar.

This is the owner bridge from the physical/time-side completed prime finite-part channel
to the completed two-face/GNS boundary coefficient.  It is the completed form of the
finite defect-square expansion plus diagonal-debt absorption. -/
theorem completedPrimeOffDiagonalChannel_eq_completedTwoFaceGNSBoundaryCoefficient_re_ownerDistributionTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  have hspectral :
      completedPrimeOffDiagonalChannel f =
        completedSpectralPrimeOffDiagonalChannel f :=
    completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerDistributionTransport
      f D
  unfold completedSpectralPrimeOffDiagonalChannel at hspectral
  unfold zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient
  exact hspectral

/-- Completed prime finite-window normalization reaches the two-face/GNS boundary scalar,
using the summed contour/time transport provider. -/
theorem completedPrimeOffDiagonalChannel_eq_completedTwoFaceGNSBoundaryCoefficient_re_ownerSummedDistributionTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeOffDiagonalChannel f =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  have hspectral :
      completedPrimeOffDiagonalChannel f =
        completedSpectralPrimeOffDiagonalChannel f :=
    completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerSummedDistributionTransport
      f D
  unfold completedSpectralPrimeOffDiagonalChannel at hspectral
  unfold zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient
  exact hspectral

/-- The transported completed prime channel is the negative real part of the completed
prime-power two-face/GNS matrix coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedPrimeOffDiagonalChannel_ownerDistributionTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      -completedPrimeOffDiagonalChannel f := by
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let B : ℂ := zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f
  have hboundary :
      B = -T := by
    unfold B
    unfold T
    exact zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient f
  have hboundary_re :
      Complex.re B = -Complex.re T := by
    calc
      Complex.re B = Complex.re (-T) := by
        exact congrArg Complex.re hboundary
      _ = -Complex.re T := by
        exact Complex.neg_re T
  have hchannel :
      completedPrimeOffDiagonalChannel f = Complex.re B := by
    unfold B
    exact
      completedPrimeOffDiagonalChannel_eq_completedTwoFaceGNSBoundaryCoefficient_re_ownerDistributionTransport
        f D
  calc
    Complex.re T = -(-Complex.re T) := by
      exact (neg_neg (Complex.re T)).symm
    _ = -Complex.re B := by
      exact congrArg Neg.neg hboundary_re.symm
    _ = -completedPrimeOffDiagonalChannel f := by
      exact congrArg Neg.neg hchannel.symm

/-- The summed visible-remainder transport identifies the completed prime-power two-face/GNS
matrix coefficient with the negative transported completed prime channel. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedPrimeOffDiagonalChannel_ownerSummedDistributionTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      -completedPrimeOffDiagonalChannel f := by
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let B : ℂ := zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f
  have hboundary :
      B = -T := by
    unfold B
    unfold T
    exact zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient f
  have hboundary_re :
      Complex.re B = -Complex.re T := by
    calc
      Complex.re B = Complex.re (-T) := by
        exact congrArg Complex.re hboundary
      _ = -Complex.re T := by
        exact Complex.neg_re T
  have hchannel :
      completedPrimeOffDiagonalChannel f = Complex.re B := by
    unfold B
    exact
      completedPrimeOffDiagonalChannel_eq_completedTwoFaceGNSBoundaryCoefficient_re_ownerSummedDistributionTransport
        f D
  calc
    Complex.re T = -(-Complex.re T) := by
      exact (neg_neg (Complex.re T)).symm
    _ = -Complex.re B := by
      exact congrArg Neg.neg hboundary_re.symm
    _ = -completedPrimeOffDiagonalChannel f := by
      exact congrArg Neg.neg hchannel.symm

/-- The negative prime boundary channel of the convolution pair is the raw
time-side prime distribution. -/
theorem neg_primeBoundaryChannel_convolutionPair_re_eq_timeDistributionPairing
    (f : ZetaAdmissibleFunction) :
    -Complex.re (primeBoundaryChannel (convolutionPair f f)) =
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) := by
  have hpair :
      convolutionPair f f = convolutionAutocorrelation f :=
    convolutionPair_self f
  have htime :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f)) :=
    completedPrimeTimeDistributionPairing_eq_primePowerContribution_re
      (convolutionAutocorrelation f)
  have hprime :
      zetaCompletedExplicitFormulaPrimePowerContribution
          (convolutionAutocorrelation f) =
        -primeBoundaryChannel (convolutionAutocorrelation f) :=
    Eq.trans
      (zetaCompletedExplicitFormulaPrimePowerContribution_eq_neg_primeContribution
        (convolutionAutocorrelation f))
      (congrArg Neg.neg
        (primeBoundaryChannel_unfold (convolutionAutocorrelation f)).symm)
  have hchannel :
      Complex.re (primeBoundaryChannel (convolutionPair f f)) =
        Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) :=
    congrArg
      (fun g : ZetaAdmissibleFunction => Complex.re (primeBoundaryChannel g))
      hpair
  have hnegChannel :
      -Complex.re (primeBoundaryChannel (convolutionPair f f)) =
        -Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) :=
    congrArg Neg.neg hchannel
  have hprimeRe :
      Complex.re
          (zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f)) =
        -Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) :=
    Eq.trans
      (congrArg Complex.re hprime)
      (Complex.neg_re (primeBoundaryChannel (convolutionAutocorrelation f)))
  exact hnegChannel.trans (hprimeRe.symm.trans htime.symm)

/-- The completed spectral prime channel is the real part of the contour-side spectral-sample
prime-power presentation. -/
theorem completedSpectralPrimeOffDiagonalChannel_eq_spectralSampleContribution_re
    (f : ZetaAdmissibleFunction) :
    completedSpectralPrimeOffDiagonalChannel f =
      Complex.re
        (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
          (convolutionAutocorrelation f)) := by
  rfl

/-- The completed spectral prime channel is the real part of the completed two-face boundary
coefficient.  This is the algebraic half of prime tomography after the contour-side spectral
sample has been formed. -/
theorem completedSpectralPrimeOffDiagonalChannel_eq_completedTwoFaceBoundaryCoefficient_re
    (f : ZetaAdmissibleFunction) :
    completedSpectralPrimeOffDiagonalChannel f =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  unfold completedSpectralPrimeOffDiagonalChannel
  unfold zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
  have hsum :
      (∑' ι : ZetaPrimePowerIndex,
          -((ι.weight : ℂ) *
            (zetaCompletedExplicitFormulaPhi
                (convolutionAutocorrelation f) ι.center +
              star
                (zetaCompletedExplicitFormulaPhi
                  (convolutionAutocorrelation f) ι.center)))) =
        zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
    calc
      (∑' ι : ZetaPrimePowerIndex,
          -((ι.weight : ℂ) *
            (zetaCompletedExplicitFormulaPhi
                (convolutionAutocorrelation f) ι.center +
              star
                (zetaCompletedExplicitFormulaPhi
                  (convolutionAutocorrelation f) ι.center)))) =
          ∑' ι : ZetaPrimePowerIndex,
            -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f := by
        exact tsum_congr
          (fun ι : ZetaPrimePowerIndex =>
            zetaCompletedPrimeSpectralSampleCoordinate_eq_neg_twoFaceBoundaryCoordinate
              ι f)
      _ = zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
        exact zetaCompletedPrimeTwoFaceGNSBoundaryCoordinate_tsum_eq_boundaryCoefficient f
  exact congrArg Complex.re hsum

/-- A finitely supported real prime-power family is bounded by a rectangular-height
polynomial majorant.

This is the finite-support owner lemma behind raw time-side prime-coordinate
localization: on the finite support choose one constant dominating the finitely many
ratios by the strictly positive height decay; off the support the family vanishes. -/
theorem exists_rawHeightPolynomialBound_of_finsetSupport
    (u : ZetaPrimePowerIndex → ℝ)
    (s : Finset ZetaPrimePowerIndex)
    (hsupport : ∀ ι : ZetaPrimePowerIndex, ι ∉ s → u ι = 0) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 < C ∧
      ∀ ι : ZetaPrimePowerIndex,
        ‖u ι‖ ≤ C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  let d : ZetaPrimePowerIndex → ℝ :=
    fun ι => ZetaPrimePowerIndex.polynomialHeightDecay 0 ι
  let q : ZetaPrimePowerIndex → ℝ :=
    fun ι => ‖u ι‖ / d ι
  let C : ℝ := (∑ ι in s, q ι) + 1
  have hq_nonnegative :
      ∀ ι : ZetaPrimePowerIndex, 0 ≤ q ι := by
    intro ι
    exact div_nonneg
      (norm_nonneg (u ι))
      (le_of_lt (ZetaPrimePowerIndex.polynomialHeightDecay_pos 0 ι))
  have hsum_nonnegative : 0 ≤ ∑ ι in s, q ι := by
    exact Finset.sum_nonneg
      (fun ι _hι => hq_nonnegative ι)
  have hC_positive : 0 < C := by
    exact add_pos_of_nonneg_of_pos hsum_nonnegative zero_lt_one
  exact Exists.intro C
    (Exists.intro 0
      (And.intro hC_positive
        (fun ι =>
          have hd_positive : 0 < d ι :=
            ZetaPrimePowerIndex.polynomialHeightDecay_pos 0 ι
          match Decidable.em (ι ∈ s) with
          | Or.inl hι =>
              have hq_le_sum : q ι ≤ ∑ η in s, q η := by
                exact Finset.single_le_sum
                  (fun η hη =>
                    (fun hmem : η ∈ s => hq_nonnegative η) hη)
                  hι
              have hq_le_C : q ι ≤ C := by
                exact le_trans hq_le_sum
                  (le_add_of_nonneg_right zero_le_one)
              have hscaled : q ι * d ι ≤ C * d ι := by
                exact mul_le_mul_of_nonneg_right hq_le_C (le_of_lt hd_positive)
              have hrecover : q ι * d ι = ‖u ι‖ := by
                exact div_mul_cancel₀ (‖u ι‖) (ne_of_gt hd_positive)
              calc
                ‖u ι‖ = q ι * d ι := by
                  exact hrecover.symm
                _ ≤ C * d ι := by
                  exact hscaled
          | Or.inr hι =>
              have hu_zero : u ι = 0 :=
                hsupport ι hι
              have hnorm_zero : ‖u ι‖ = 0 :=
                (congrArg norm hu_zero).trans (show ‖(0 : ℝ)‖ = 0 from norm_zero)
              have hright_nonnegative : 0 ≤ C * d ι :=
                mul_nonneg (le_of_lt hC_positive) (le_of_lt hd_positive)
              calc
                ‖u ι‖ = 0 := by
                  exact hnorm_zero
                _ ≤ C * d ι := by
                  exact hright_nonnegative)))

/-- Raw height-polynomial localization for the time-side prime distribution coordinate. -/
theorem exists_completedPrimeTimeDistributionCoordinate_rawHeightBound
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 < C ∧
      ∀ ι : ZetaPrimePowerIndex,
        ‖completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f)‖ ≤
          C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  exact
    match exists_convolutionAutocorrelationKernelSupportUpperBound f with
    | ⟨B, hB⟩ =>
      exists_rawHeightPolynomialBound_of_finsetSupport
        (fun ι : ZetaPrimePowerIndex =>
          completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f))
        (zetaPrimeOffDiagonalSupportFinsetOfBound f B)
        (fun ι hι =>
          (completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical
            ι f).trans
            (zetaPrimeOffDiagonalCoordinate_eq_zero_of_not_mem_supportFinsetOfBound
              ι f hB hι))

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
