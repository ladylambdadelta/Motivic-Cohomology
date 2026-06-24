import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanVerticalAnalyticEstimates

/-!
# Archimedean vertical-channel transport estimate

This file owns the Gamma/completion vertical-channel transport estimate.  The
projection layer consumes this theorem but does not own its proof.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Algebraic extraction of the archimedean packet from the inverse-Gamma completion
packet and the correction packet along the scheduled contour heights.

The analytic content remains in the two input limits.  This lemma only transports
the already proved fixed-height identity
`inverseGammaCompletion = archimedean + correction` through `Tendsto`. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_of_inverseGammaCompletion_and_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hinverse :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel
            f F (h.height_schedule.height u))
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    (hcorrection :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannel
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  let A : ℂ := zetaCompletedExplicitFormulaArchimedeanContribution f
  let C : ℂ := zetaCompletedExplicitFormulaCorrectionStandardContourContribution f
  have hdiff :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionVerticalChannel
              f F (h.height_schedule.height u))
        atTop
        (𝓝 ((A + C) - C)) :=
    hinverse.sub hcorrection
  have htarget : (A + C) - C = A := by
    exact add_sub_cancel A C
  have harch_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionVerticalChannel
            f F (h.height_schedule.height u)) := by
    funext u
    let T : ℝ := h.height_schedule.height u
    let A_u : ℂ := zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T
    let C_u : ℂ := zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T
    let G_u : ℂ := zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel f F T
    have hdecomp : G_u = A_u + C_u :=
      zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel_eq_archimedean_add_correction
        f h.phi_control F T (h.height_schedule.avoids_boundary u)
    change A_u = G_u - C_u
    calc
      A_u = A_u + C_u - C_u := by
        exact (add_sub_cancel A_u C_u).symm
      _ = G_u - C_u := by
        exact congrArg (fun z : ℂ => z - C_u) hdecomp.symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)))
    harch_fun.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionVerticalChannel
                f F (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hdiff)

/-- Algebraic extraction of the archimedean packet from the named scheduled
inverse-Gamma completion channel and named scheduled correction channel. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_of_scheduledInverseGammaCompletion_and_scheduledCorrection
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hinverse :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
            f F h u)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    (hcorrection :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
            f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  let A : ℂ := zetaCompletedExplicitFormulaArchimedeanContribution f
  let C : ℂ := zetaCompletedExplicitFormulaCorrectionStandardContourContribution f
  have hdiff :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
              f F h u -
            zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
              f F h u)
        atTop
        (𝓝 ((A + C) - C)) :=
    hinverse.sub hcorrection
  have htarget : (A + C) - C = A := by
    exact add_sub_cancel A C
  have harch_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
            f F h u -
          zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
            f F h u) := by
    funext u
    exact
      zetaCompletedExplicitFormulaScheduledArchimedean_eq_inverseGammaCompletion_sub_correction
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)))
    harch_fun.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
                f F h u -
              zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
                f F h u)
          atTop
          (𝓝 z))
      htarget
      hdiff)

/-- Algebraic extraction of the scheduled inverse-Gamma completion limit from
the archimedean vertical-channel limit and the scheduled correction limit.

This is the reverse assembly direction: after the archimedean channel has been
proved independently, the fixed-height identity
`archimedean = inverseGammaCompletion - correction` gives
`inverseGammaCompletion = archimedean + correction`. -/
theorem zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_tendsto_of_archimedean_and_scheduledCorrection
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (harch :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannel
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)))
    (hcorrection :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
            f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
          f F h u)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  let A : ℂ := zetaCompletedExplicitFormulaArchimedeanContribution f
  let C : ℂ := zetaCompletedExplicitFormulaCorrectionStandardContourContribution f
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannel
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
              f F h u)
        atTop
        (𝓝 (A + C)) :=
    harch.add hcorrection
  have hinverse_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
          f F h u) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
            f F h u) := by
    funext u
    let A_u : ℂ :=
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel
        f F (h.height_schedule.height u)
    let C_u : ℂ :=
      zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
        f F h u
    let G_u : ℂ :=
      zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
        f F h u
    have hdecomp : A_u = G_u - C_u :=
      zetaCompletedExplicitFormulaScheduledArchimedean_eq_inverseGammaCompletion_sub_correction
        f F h u
    change G_u = A_u + C_u
    calc
      G_u = (G_u - C_u) + C_u := by
        exact (sub_add_cancel G_u C_u).symm
      _ = A_u + C_u := by
        exact congrArg (fun z : ℂ => z + C_u) hdecomp.symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 (A + C)))
    hinverse_fun.symm
    hsum

/-- Archimedean channel transport after replacing the correction-channel analytic
estimate by its pole-face owner theorem.  The remaining analytic input is the
inverse-Gamma completion vertical-channel convergence and the upstream
right-one-pole decay needed by the correction channel. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_of_scheduledInverseGammaCompletion_and_rightOnePoleDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hinverse :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
            f F h u)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  have hcorrection :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
            f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
    zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_concrete_ownerChannelTransportAnalytic
      f F h hone
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_of_scheduledInverseGammaCompletion_and_scheduledCorrection
      f F h hinverse hcorrection

/-- Owner analytic leaf: the scheduled Gamma/completion vertical channel
converges to the completed archimedean contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerArchimedeanTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  have hestimates :
      Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
              f F h u)
          atTop
          (𝓝
            (zetaCompletedExplicitFormulaArchimedeanContribution f +
              zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
              f F h u)
          atTop
          (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
    exact
      zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto
        f F h hregular hcoh hvalue
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_of_scheduledInverseGammaCompletion_and_scheduledCorrection
      f F h hestimates.1 hestimates.2

/-- Vertically regular archimedean-channel transport with Gamma regularity
supplied by the contour owner.  The remaining analytic input is the whole-line
inverse-Gamma value identity. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_verticallyRegular_gammaBinet_integral_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  have hestimates :
      Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
              f F.toContourFamily h u)
          atTop
          (𝓝
            (zetaCompletedExplicitFormulaArchimedeanContribution f +
              zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
              f F.toContourFamily h u)
          atTop
          (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
    zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto_of_verticallyRegular_gammaBinet_integral_eq
      f F h hcoh hvalue
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_of_scheduledInverseGammaCompletion_and_scheduledCorrection
      f F.toContourFamily h hestimates.1 hestimates.2

/-- Owner transport-remainder form of the archimedean Gamma/completion vertical
channel estimate.  The analytic content is the channel convergence theorem
above; this theorem only subtracts the boundary contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_of_channel_tendsto_archimedeanContribution
      f F h
      (zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerArchimedeanTransport
        f F h hregular hcoh hvalue)

/-- Vertically regular transport-remainder form of the archimedean channel
estimate.  The whole-line inverse-Gamma value identity remains explicit. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_of_verticallyRegular_gammaBinet_integral_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_of_channel_tendsto_archimedeanContribution
      f F.toContourFamily h
      (zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_verticallyRegular_gammaBinet_integral_eq
        f F h hcoh hvalue)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
