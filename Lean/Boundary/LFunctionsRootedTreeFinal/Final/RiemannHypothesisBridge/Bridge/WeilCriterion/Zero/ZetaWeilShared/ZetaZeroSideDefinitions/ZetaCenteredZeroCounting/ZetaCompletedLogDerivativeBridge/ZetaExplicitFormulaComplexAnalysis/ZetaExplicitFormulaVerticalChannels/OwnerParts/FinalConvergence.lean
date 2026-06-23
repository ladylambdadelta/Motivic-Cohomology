import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleResidueTransport

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

/-- Coefficient accounting for the oriented right-minus-left pole faces. -/
theorem zetaCompletedExplicitFormulaCorrectionPoleCoefficient_sub_neg_eq_centeredPoleCoefficient
    (z : ℂ) :
    (1 / (1 / 2 : ℂ)) * z -
        (-(1 / (1 - (1 / 2 : ℂ)) * z)) =
      (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) * z := by
  let a : ℂ := 1 / (1 / 2 : ℂ)
  let b : ℂ := 1 / (1 - (1 / 2 : ℂ))
  change a * z - (-(b * z)) = (a + b) * z
  calc
    a * z - (-(b * z)) = a * z + b * z := by
      exact sub_neg_eq_add (a * z) (b * z)
    _ = (a + b) * z := by
      exact (add_mul a b z).symm

/-- Core correction-channel transport theorem after the contribution normalization:
the explicit two-pole vertical kernel converges to the centered pole coefficient at
`s = 1 / 2`, evaluated against `Φ_f 0`.

This is the remaining analytic orientation/basepoint theorem for the correction channel. -/
theorem zetaCompletedExplicitFormulaCorrectionPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          (-1 / zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t -
              1 / (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            (-1 / zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t -
                1 / (zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
      atTop
      (𝓝
        (((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) -
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))) := by
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0)) :=
    zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
      f F h
  have hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) :=
    zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral_tendsto_standardContourResidue_ownerChannelTransportAnalytic
      f F h
  have hsub :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
              f F (h.height_schedule.height u))
        atTop
        (𝓝
          (((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) -
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))) :=
    Tendsto.sub hright hleft
  have hpointwise :
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          (-1 / zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t -
              1 / (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            (-1 / zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t -
                1 / (zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
              f F (h.height_schedule.height u)) := by
    funext u
    exact Eq.refl _
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝
          (((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) -
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))))
    hpointwise.symm
    hsub

/-- Concrete correction-channel analytic transport with the standard-contour
single-pole normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_concrete_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  have hkernel :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            (-1 / zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t -
                1 / (zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
            ∫ t in Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
              (-1 / zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t -
                  1 / (zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t - 1)) *
                zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        atTop
        (𝓝
          (((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) -
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))) :=
    zetaCompletedExplicitFormulaCorrectionPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
      f F h
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            (-1 / zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t -
                1 / (zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
            ∫ t in Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
              (-1 / zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t -
                  1 / (zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t - 1)) *
                  zetaCompletedExplicitFormulaPhi f
                    (zetaCompletedExplicitFormulaLeftPath
                      (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) := by
      funext u
      exact
        zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_poleCorrectionVerticalIntegral
          f F (h.height_schedule.height u)
    have hlimit :
        ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) -
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) =
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f :=
      (zetaCompletedExplicitFormulaCorrectionStandardContourContribution_eq f).symm
    exact Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop
          (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
      hpointwise.symm
      (Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun u : ℝ =>
              (∫ t in Set.Icc
                  (-(F.rectangle (h.height_schedule.height u)).T)
                  (F.rectangle (h.height_schedule.height u)).T,
                (-1 / zetaCompletedExplicitFormulaRightPath
                      (F.rectangle (h.height_schedule.height u)) t -
                    1 / (zetaCompletedExplicitFormulaRightPath
                      (F.rectangle (h.height_schedule.height u)) t - 1)) *
                  zetaCompletedExplicitFormulaPhi f
                    (zetaCompletedExplicitFormulaRightPath
                      (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
                ∫ t in Set.Icc
                    (-(F.rectangle (h.height_schedule.height u)).T)
                    (F.rectangle (h.height_schedule.height u)).T,
                  (-1 / zetaCompletedExplicitFormulaLeftPath
                        (F.rectangle (h.height_schedule.height u)) t -
                      1 / (zetaCompletedExplicitFormulaLeftPath
                        (F.rectangle (h.height_schedule.height u)) t - 1)) *
                    zetaCompletedExplicitFormulaPhi f
                      (zetaCompletedExplicitFormulaLeftPath
                        (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
            atTop
            (𝓝 z))
        hlimit
        hkernel)

/-- Correction-channel analytic transport: the scheduled pole-face vertical integral
converges to the standard-contour correction boundary value. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction)
      atTop
      (𝓝
        (explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.correction)) := by
    have hconcrete :
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
              (h.height_schedule.height u))
          atTop
          (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
      zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_concrete_ownerChannelTransportAnalytic
        f F h
    have hpointwise :
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction) =
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
              (h.height_schedule.height u)) := by
      funext u
      exact explicitFormulaSelectedScheduledVerticalChannel_correction_eq f F h u
    have htarget :
        explicitFormulaSelectedVerticalBoundaryChannel
            f ExplicitFormulaScheduledVerticalChannelProjection.correction =
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f :=
      explicitFormulaSelectedVerticalBoundaryChannel_correction_eq f
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝
          (explicitFormulaSelectedVerticalBoundaryChannel
            f ExplicitFormulaScheduledVerticalChannelProjection.correction)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
              (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget.symm
      hconcrete)

/-- Owner analytic theorem: the prime vertical-channel transport remainder vanishes along
the scheduled contour heights.  This is the channel-specific logarithmic-derivative
transport estimate; the corresponding convergence to the completed prime contribution is
only the algebraic consequence below. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeLogDerivativeTransport
      f F h

/-- Owner analytic theorem: the archimedean vertical-channel transport remainder vanishes
along the scheduled contour heights.  This is the Gamma/completion channel transport
estimate; the contribution limit is a formal consequence. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hprojection :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_tendsto_zero_of_selectedChannel_tendsto_boundary
      f F h ExplicitFormulaScheduledVerticalChannelProjection.archimedean
      (zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerChannelTransportAnalytic
        f F h)
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.archimedean) := by
    funext u
    exact
      (explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_archimedean_eq
        f F (h.height_schedule.height u)).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hprojection

/-- Owner analytic theorem: the correction vertical-channel transport remainder vanishes
along the scheduled contour heights.  This is the pole-face transport estimate; the
convergence to the correction contribution is a formal consequence. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hprojection :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.correction)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_tendsto_zero_of_selectedChannel_tendsto_boundary
      f F h ExplicitFormulaScheduledVerticalChannelProjection.correction
      (zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerChannelTransportAnalytic
        f F h)
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.correction) := by
    funext u
    exact
      (explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_correction_eq
        f F (h.height_schedule.height u)).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hprojection

/-- Prime vertical-channel convergence from its scheduled transport-remainder estimate. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (htransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (zetaCompletedExplicitFormulaPrimeContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F
          (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_contribution_add_transportRemainder
          f F (h.height_schedule.height u))
      htransport

/-- Archimedean vertical-channel convergence from its scheduled transport-remainder
estimate. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (htransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (zetaCompletedExplicitFormulaArchimedeanContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F
          (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel_eq_contribution_add_transportRemainder
          f F (h.height_schedule.height u))
      htransport

/-- Correction vertical-channel convergence from its scheduled standard-contour
transport-remainder estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
      (htransport :
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
              f F (h.height_schedule.height u))
          atTop
          (𝓝 0)) :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
    exact
      explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
        (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
          (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_contribution_add_transportRemainder
          f F (h.height_schedule.height u))
      htransport

/-- Owner theorem: the prime vertical channel converges to the completed prime
contribution along the scheduled contour heights. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_transportRemainder
      f F h
      (zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
        f F h)

/-- Owner theorem: the archimedean vertical channel converges to the completed
archimedean contribution along the scheduled contour heights. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_transportRemainder
      f F h
      (zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
        f F h)

/-- Owner theorem: the pole-correction vertical channel converges to the
standard-contour correction boundary value along the scheduled contour heights. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
      (h : ExplicitFormulaFamilyAnalyticPackage f F) :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_of_transportRemainder
      f F h
      (zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
        f F h)

/-- The prime transport remainder vanishes once the prime channel has been transported
to its completed contribution. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
      f F h

/-- The archimedean transport remainder vanishes once the archimedean channel has been
transported to its completed contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
      f F h

/-- The correction transport remainder vanishes once the correction channel has been
transported to its completed contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
      f F h


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
