import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CenteredZeros.CriticalStrip.Owner

/-!
# Explicit-formula vertical channels

This owner layer contains vertical-channel regularity, integrability, realization, and boundary-sum convergence.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The vertical-boundary remainder along the contour family, still complex-valued. -/
noncomputable def zetaCompletedExplicitFormulaVerticalBoundaryRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) -
      zetaCompletedExplicitFormulaBoundarySumAnalytic f

/-- The vertical side difference is the analytic boundary sum plus its complex remainder. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_eq_boundarySum_add_boundaryRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
      zetaCompletedExplicitFormulaBoundarySumAnalytic f +
        zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F T := by
  let V : ℂ :=
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)
  let B : ℂ := zetaCompletedExplicitFormulaBoundarySumAnalytic f
  change V = B + (V - B)
  calc
    V = V + 0 := by
      exact (add_zero V).symm
    _ = V + (-B + B) := by
      exact congrArg (fun x : ℂ => V + x) (neg_add_cancel B).symm
    _ = (V + -B) + B := by
      exact (add_assoc V (-B) B).symm
    _ = B + (V + -B) := by
      exact add_comm (V + -B) B
    _ = B + (V - B) := by
      exact congrArg (fun x : ℂ => B + x) (sub_eq_add_neg V B).symm

/-- If the complex vertical-boundary remainder vanishes, then the vertical side difference
converges to the analytic boundary sum. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_of_boundaryRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hremainder :
      Tendsto
        (fun T : ℝ => zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F T)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  have hconst :
      Tendsto
        (fun _T : ℝ => zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaBoundarySumAnalytic f +
            zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F T)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f + 0)) :=
    hconst.add hremainder
  have htarget :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f + 0 =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
    add_zero _
  have hpointwise :
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)) =
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaBoundarySumAnalytic f +
            zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F T) := by
    funext T
    exact
      zetaCompletedExplicitFormulaVerticalDifference_eq_boundarySum_add_boundaryRemainder
        f F T
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            zetaCompletedExplicitFormulaBoundarySumAnalytic f +
              zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F T)
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- If the vertical side difference converges to the analytic boundary sum, then the named
vertical-boundary remainder vanishes. -/
theorem zetaCompletedExplicitFormulaVerticalBoundaryRemainder_tendsto_zero_of_verticalDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hvertical :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f))) :
    Tendsto
      (fun T : ℝ => zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F T)
      atTop
      (𝓝 0) := by
  have hconst :
      Tendsto
        (fun _T : ℝ => zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun T : ℝ =>
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)) -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaBoundarySumAnalytic f -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    hvertical.sub hconst
  have htarget :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f -
          zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        0 := by
    exact sub_self _
  have hpointwise :
      (fun T : ℝ => zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F T) =
        (fun T : ℝ =>
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)) -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
    funext T
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
                zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)) -
              zetaCompletedExplicitFormulaBoundarySumAnalytic f)
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- Prime vertical-channel convergence from its scheduled transport-remainder estimate. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (htransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (zetaCompletedExplicitFormulaPrimeContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_contribution_add_transportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      htransport

/-- Archimedean vertical-channel convergence from its scheduled transport-remainder estimate. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (htransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (zetaCompletedExplicitFormulaArchimedeanContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel_eq_contribution_add_transportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      htransport

/-- Correction vertical-channel convergence from its scheduled transport-remainder estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (htransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) := by
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (zetaCompletedExplicitFormulaCorrectionContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_contribution_add_transportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      htransport

/-- The three named vertical channels converge to the analytic boundary sum once their
component transport remainders vanish. -/
theorem zetaCompletedExplicitFormulaVerticalChannelSum_tendsto_boundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hprimeTransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 0))
    (harchTransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 0))
    (hcorrTransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
          (h.height_schedule.height u))
      atTop
          (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  have hprime :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) :=
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_transportRemainder
      f F h hprimeTransport
  have harch :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_transportRemainder
      f F h harchTransport
  have hcorr :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) :=
    zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_of_transportRemainder
      f F h hcorrTransport
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
              (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
              (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
                (h.height_schedule.height u))
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaPrimeContribution f +
            zetaCompletedExplicitFormulaArchimedeanContribution f +
              zetaCompletedExplicitFormulaCorrectionContribution f)) :=
    (hprime.add harch).add hcorr
  have htarget :
      zetaCompletedExplicitFormulaPrimeContribution f +
          zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionContribution f =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
    rfl
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
              (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
              (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
                (h.height_schedule.height u)) := by
    funext u
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
                (h.height_schedule.height T) +
              zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
                (h.height_schedule.height T) +
                zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
                  (h.height_schedule.height T))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-! ## Completed vertical packet realization owner -/

/-- Pointwise packet decomposition after the completed log-derivative normalization:
the completed boundary object splits into prime, archimedean, and correction channels. -/
theorem zetaCompletedExplicitFormulaVerticalIntegrand_eq_channelIntegrands_ownerCompletedLogDerivativeDecomposition
    (f : ZetaAdmissibleFunction) (s : ℂ) :
    completedZetaNegLogDeriv s * zetaCompletedExplicitFormulaPhi f (s - 1 / 2) =
      explicitFormulaPrimeLogDerivative s * zetaCompletedExplicitFormulaPhi f (s - 1 / 2) +
        explicitFormulaArchimedeanLogDerivative s *
          zetaCompletedExplicitFormulaPhi f (s - 1 / 2) +
        explicitFormulaCorrectionLogDerivative s *
          zetaCompletedExplicitFormulaPhi f (s - 1 / 2) := by
  let Φ : ℂ := zetaCompletedExplicitFormulaPhi f (s - 1 / 2)
  let P : ℂ := explicitFormulaPrimeLogDerivative s
  let A : ℂ := explicitFormulaArchimedeanLogDerivative s
  let C : ℂ := explicitFormulaCorrectionLogDerivative s
  have hlog :
      completedZetaNegLogDeriv s = P + A + C := by
    exact completedZetaNegLogDeriv_eq_explicitFormulaCompletedLogDerivative_ownerCompletedLogDerivativeDecomposition
      s
  change completedZetaNegLogDeriv s * Φ = P * Φ + A * Φ + C * Φ
  calc
    completedZetaNegLogDeriv s * Φ = (P + A + C) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hlog
    _ = (P + A) * Φ + C * Φ := by
      exact add_mul (P + A) C Φ
    _ = (P * Φ + A * Φ) + C * Φ := by
      exact congrArg (fun z : ℂ => z + C * Φ) (add_mul P A Φ)
    _ = P * Φ + A * Φ + C * Φ := by
      rfl

/-- The completed vertical realization remainder after subtracting the realized channel
packet from the completed vertical boundary object. -/
noncomputable def zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)) -
    zetaCompletedExplicitFormulaVerticalChannelSum f F T

/-- Subtracting two three-term sums is the sum of the three component differences. -/
theorem complex_three_add_sub_three_add_eq
    (a b c d e g : ℂ) :
    (a + b + c) - (d + e + g) =
      (a - d) + (b - e) + (c - g) := by
  calc
    (a + b + c) - (d + e + g) =
        (a + (b + c)) - (d + (e + g)) := by
      exact congrArg₂ Sub.sub
        (add_assoc a b c)
        (add_assoc d e g)
    _ = (a - d) + ((b + c) - (e + g)) := by
      exact add_sub_add_comm a (b + c) d (e + g)
    _ = (a - d) + ((b - e) + (c - g)) := by
      exact congrArg (fun z : ℂ => (a - d) + z)
        (add_sub_add_comm b c e g)
    _ = (a - d) + (b - e) + (c - g) := by
      exact (add_assoc (a - d) (b - e) (c - g)).symm

/-- Set-integral additivity for a three-term complex-valued sum. -/
theorem complex_setIntegral_three_add_eq_sum_integrals
    (S : Set ℝ) (P A C : ℝ → ℂ)
    (hP : IntegrableOn P S)
    (hA : IntegrableOn A S)
    (hC : IntegrableOn C S) :
    (∫ t in S, P t + A t + C t) =
      (∫ t in S, P t) + (∫ t in S, A t) + (∫ t in S, C t) := by
  have hPA : IntegrableOn (fun t : ℝ => P t + A t) S :=
    hP.add hA
  calc
    (∫ t in S, P t + A t + C t) =
        (∫ t in S, P t + A t) + ∫ t in S, C t := by
      exact integral_add hPA hC
    _ = ((∫ t in S, P t) + ∫ t in S, A t) + ∫ t in S, C t := by
      exact congrArg (fun z : ℂ => z + ∫ t in S, C t) (integral_add hP hA)
    _ = (∫ t in S, P t) + (∫ t in S, A t) + (∫ t in S, C t) := by
      rfl

/-- Continuous complex-valued functions on a compact real interval are integrable on that
interval.  This is the generic compact-regularity bridge used by the vertical channel
packet; analytic channel regularity is kept in the packet-continuity owner theorem below. -/
theorem complex_continuousOn_Icc_integrableOn
    {a b : ℝ} {g : ℝ → ℂ}
    (hg : ContinuousOn g (Set.Icc a b)) :
    IntegrableOn g (Set.Icc a b) := by
  exact hg.integrableOn_compact isCompact_Icc

/-- Right vertical realization of the pointwise completed channel-packet decomposition before
distributing the interval integral over the three channel summands. -/
theorem zetaCompletedExplicitFormulaRightLineIntegral_eq_integral_channelSum_ownerVerticalPointwiseTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) =
      ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) := by
  exact integral_congr_ae
    (Filter.Eventually.of_forall
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaVerticalIntegrand_eq_channelIntegrands_ownerCompletedLogDerivativeDecomposition
          f (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t)))

/-- The three completed vertical channel summands in the boundary packet. -/
inductive ExplicitFormulaVerticalChannel where
  | prime
  | archimedean
  | correction

/-- The two vertical sides realizing a completed boundary packet. -/
inductive ExplicitFormulaVerticalSide where
  | right
  | left

/-- The path associated to a vertical side of the rectangle. -/
def explicitFormulaVerticalSidePath
    (side : ExplicitFormulaVerticalSide) (r : ExplicitFormulaRectangle) (t : ℝ) : ℂ :=
  match side with
  | ExplicitFormulaVerticalSide.right => zetaCompletedExplicitFormulaRightPath r t
  | ExplicitFormulaVerticalSide.left => zetaCompletedExplicitFormulaLeftPath r t

/-- The logarithmic derivative associated to a vertical channel of the completed packet. -/
def explicitFormulaVerticalChannelLogDerivative
    (channel : ExplicitFormulaVerticalChannel) (s : ℂ) : ℂ :=
  match channel with
  | ExplicitFormulaVerticalChannel.prime => explicitFormulaPrimeLogDerivative s
  | ExplicitFormulaVerticalChannel.archimedean => explicitFormulaArchimedeanLogDerivative s
  | ExplicitFormulaVerticalChannel.correction => explicitFormulaCorrectionLogDerivative s

/-- A single realized channel integrand on a chosen vertical side. -/
def explicitFormulaVerticalChannelIntegrand
    (f : ZetaAdmissibleFunction) (side : ExplicitFormulaVerticalSide)
    (channel : ExplicitFormulaVerticalChannel) (r : ExplicitFormulaRectangle) (t : ℝ) : ℂ :=
  explicitFormulaVerticalChannelLogDerivative channel
      (explicitFormulaVerticalSidePath side r t) *
    zetaCompletedExplicitFormulaPhi f
      (explicitFormulaVerticalSidePath side r t - 1 / 2)

/-- The vertical side parametrizations are affine, hence continuous. -/
theorem explicitFormulaVerticalSidePath_continuous
    (side : ExplicitFormulaVerticalSide) (r : ExplicitFormulaRectangle) :
    Continuous (fun t : ℝ => explicitFormulaVerticalSidePath side r t) := by
  cases side
  · exact continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  · exact continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)

/-- The shifted completed explicit-formula transform is continuous. -/
theorem zetaCompletedExplicitFormulaPhi_shift_continuous
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f) :
    Continuous
      (fun s : ℂ => zetaCompletedExplicitFormulaPhi f (s - 1 / 2)) := by
  exact continuous_iff_continuousAt.2
    (fun s =>
      (zetaCompletedExplicitFormulaPhi_shift_differentiableAt
        hPhi s).continuousAt)

/-- A point on a vertical side image is a point on the contour-family boundary. -/
theorem explicitFormulaVerticalSidePath_mem_boundary_of_mem_image
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (side : ExplicitFormulaVerticalSide) {z : ℂ}
    (hz :
      z ∈ explicitFormulaVerticalSidePath side (F.rectangle T) ''
        Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :
    z ∈ explicitFormulaContourFamilyBoundary F T := by
  match hz with
  | ⟨t, ht, hzt⟩ =>
      cases side
      · exact Eq.subst
          (motive := fun w : ℂ => w ∈ explicitFormulaContourFamilyBoundary F T)
          hzt
          (Or.inl ⟨t, ht, rfl⟩)
      · exact Eq.subst
          (motive := fun w : ℂ => w ∈ explicitFormulaContourFamilyBoundary F T)
          hzt
          (Or.inr (Or.inl ⟨t, ht, rfl⟩))

/-- The scheduled vertical side image avoids the pole at `0`. -/
theorem explicitFormulaVerticalSidePath_image_ne_zero_of_avoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ∀ z : ℂ,
      z ∈ explicitFormulaVerticalSidePath side (F.rectangle T) ''
          Set.Icc (-(F.rectangle T).T) (F.rectangle T).T →
        z ≠ 0 := by
  intro z hz hz0
  exact havoid z
    (Or.inl hz0)
    (explicitFormulaVerticalSidePath_mem_boundary_of_mem_image F T side hz)

/-- The scheduled vertical side image avoids the pole at `1`. -/
theorem explicitFormulaVerticalSidePath_image_ne_one_of_avoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ∀ z : ℂ,
      z ∈ explicitFormulaVerticalSidePath side (F.rectangle T) ''
          Set.Icc (-(F.rectangle T).T) (F.rectangle T).T →
        z ≠ 1 := by
  intro z hz hz1
  exact havoid z
    (Or.inr (Or.inl hz1))
    (explicitFormulaVerticalSidePath_mem_boundary_of_mem_image F T side hz)

/-- The scheduled vertical side image avoids Gamma-normalization zeros. -/
theorem explicitFormulaVerticalSidePath_image_Gammaℝ_ne_zero_of_avoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ∀ z : ℂ,
      z ∈ explicitFormulaVerticalSidePath side (F.rectangle T) ''
          Set.Icc (-(F.rectangle T).T) (F.rectangle T).T →
        Gammaℝ z ≠ 0 := by
  intro z hz hΓ
  exact havoid z
    (Or.inr (Or.inr (Or.inl hΓ)))
    (explicitFormulaVerticalSidePath_mem_boundary_of_mem_image F T side hz)

/-- The scheduled vertical side image avoids the archimedean half-argument Gamma zeros. -/
theorem explicitFormulaVerticalSidePath_image_Gammaℝ_half_ne_zero_of_avoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ∀ z : ℂ,
      z ∈ explicitFormulaVerticalSidePath side (F.rectangle T) ''
          Set.Icc (-(F.rectangle T).T) (F.rectangle T).T →
        Gammaℝ (z / 2) ≠ 0 := by
  intro z hz hΓ
  exact havoid z
    (Or.inr (Or.inr (Or.inr (Or.inl hΓ))))
    (explicitFormulaVerticalSidePath_mem_boundary_of_mem_image F T side hz)

/-- The scheduled vertical side image avoids completed-zeta zeros. -/
theorem explicitFormulaVerticalSidePath_image_completedRiemannZeta_ne_zero_of_avoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ∀ z : ℂ,
      z ∈ explicitFormulaVerticalSidePath side (F.rectangle T) ''
          Set.Icc (-(F.rectangle T).T) (F.rectangle T).T →
        completedRiemannZeta z ≠ 0 := by
  intro z hz hΛ
  have hz0 : z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_ne_zero_of_avoidsSingularBoundary
      F T havoid side z hz
  have hz1 : z ≠ 1 :=
    explicitFormulaVerticalSidePath_image_ne_one_of_avoidsSingularBoundary
      F T havoid side z hz
  exact havoid z
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨hz0, hz1, hΛ⟩))))
    (explicitFormulaVerticalSidePath_mem_boundary_of_mem_image F T side hz)

/-- Prime-channel log-derivative continuity on a scheduled vertical side image. -/
theorem explicitFormulaPrimeLogDerivative_continuousOn_of_avoidsBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ContinuousOn
      explicitFormulaPrimeLogDerivative
      (explicitFormulaVerticalSidePath side (F.rectangle T) ''
        Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  intro z hz
  have hz0 : z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_ne_zero_of_avoidsSingularBoundary
      F T havoid side z hz
  have hz1 : z ≠ 1 :=
    explicitFormulaVerticalSidePath_image_ne_one_of_avoidsSingularBoundary
      F T havoid side z hz
  have hΛ : completedRiemannZeta z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_completedRiemannZeta_ne_zero_of_avoidsSingularBoundary
      F T havoid side z hz
  have hΓ : Gammaℝ z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_Gammaℝ_ne_zero_of_avoidsSingularBoundary
      F T havoid side z hz
  exact
    (explicitFormulaPrimeLogDerivative_continuousAt_of_regular z hz0 hz1 hΛ hΓ).continuousWithinAt

/-- Archimedean-channel log-derivative continuity on a scheduled vertical side image. -/
theorem explicitFormulaArchimedeanLogDerivative_continuousOn_of_avoidsBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ContinuousOn
      explicitFormulaArchimedeanLogDerivative
      (explicitFormulaVerticalSidePath side (F.rectangle T) ''
        Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  intro z hz
  have hz0 : z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_ne_zero_of_avoidsSingularBoundary
      F T havoid side z hz
  have hz1 : z ≠ 1 :=
    explicitFormulaVerticalSidePath_image_ne_one_of_avoidsSingularBoundary
      F T havoid side z hz
  have hΛ : completedRiemannZeta z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_completedRiemannZeta_ne_zero_of_avoidsSingularBoundary
      F T havoid side z hz
  have hΓ : Gammaℝ z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_Gammaℝ_ne_zero_of_avoidsSingularBoundary
      F T havoid side z hz
  exact
    (explicitFormulaArchimedeanLogDerivative_continuousAt_of_regular
      z hz0 hz1 hΛ hΓ).continuousWithinAt

/-- Correction-channel log-derivative continuity on a scheduled vertical side image. -/
theorem explicitFormulaCorrectionLogDerivative_continuousOn_of_avoidsBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ContinuousOn
      explicitFormulaCorrectionLogDerivative
      (explicitFormulaVerticalSidePath side (F.rectangle T) ''
        Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  let S : Set ℂ :=
    explicitFormulaVerticalSidePath side (F.rectangle T) ''
      Set.Icc (-(F.rectangle T).T) (F.rectangle T).T
  have hne0 : ∀ z : ℂ, z ∈ S → z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_ne_zero_of_avoidsSingularBoundary
      F T havoid side
  have hne1 : ∀ z : ℂ, z ∈ S → z - 1 ≠ 0 := by
    intro z hz hzsub
    have hz1 : z = 1 := sub_eq_zero.mp hzsub
    exact
      explicitFormulaVerticalSidePath_image_ne_one_of_avoidsSingularBoundary
        F T havoid side z hz hz1
  have hconst_neg_one : ContinuousOn (fun _z : ℂ => (-(1 : ℂ))) S :=
    continuous_const.continuousOn
  have hconst_one : ContinuousOn (fun _z : ℂ => (1 : ℂ)) S :=
    continuous_const.continuousOn
  have hid : ContinuousOn (fun z : ℂ => z) S :=
    continuous_id.continuousOn
  have hsub_one : ContinuousOn (fun z : ℂ => z - 1) S :=
    hid.sub hconst_one
  have hfirst : ContinuousOn (fun z : ℂ => -(1 : ℂ) / z) S :=
    hconst_neg_one.div hid hne0
  have hsecond : ContinuousOn (fun z : ℂ => (1 : ℂ) / (z - 1)) S :=
    hconst_one.div hsub_one hne1
  change ContinuousOn (fun z : ℂ => -(1 : ℂ) / z - (1 : ℂ) / (z - 1)) S
  exact hfirst.sub hsecond

/-- Channel log-derivative continuity on the scheduled vertical-edge image, with the
zero/pole boundary exclusions supplied uniformly by the contour-family certificate. -/
theorem explicitFormulaVerticalChannelLogDerivative_continuousOn_of_avoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) (channel : ExplicitFormulaVerticalChannel) :
    ContinuousOn
      (fun s : ℂ => explicitFormulaVerticalChannelLogDerivative channel s)
      (explicitFormulaVerticalSidePath side (F.rectangle T) ''
        Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  cases channel
  · exact explicitFormulaPrimeLogDerivative_continuousOn_of_avoidsBoundary F T havoid side
  · exact explicitFormulaArchimedeanLogDerivative_continuousOn_of_avoidsBoundary F T havoid side
  · exact explicitFormulaCorrectionLogDerivative_continuousOn_of_avoidsBoundary F T havoid side

/-- Compact finite-edge continuity for one realized channel on one vertical side.

This is the single channel-regularity owner theorem.  The correction channel consumes the
same boundary-avoidance certificate as the residue theorem; prime and archimedean channels
are handled by the same statement so they do not become separate roots. -/
theorem explicitFormulaVerticalChannelIntegrand_continuousOn_ownerCompactRegularity
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) (channel : ExplicitFormulaVerticalChannel) :
    ContinuousOn
      (fun t : ℝ =>
        explicitFormulaVerticalChannelIntegrand f side channel (F.rectangle T) t)
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  let S : Set ℝ := Set.Icc (-(F.rectangle T).T) (F.rectangle T).T
  let γ : ℝ → ℂ := fun t => explicitFormulaVerticalSidePath side (F.rectangle T) t
  have hγ : Continuous γ := by
    exact explicitFormulaVerticalSidePath_continuous side (F.rectangle T)
  have hγS : ContinuousOn γ S := hγ.continuousOn
  have hlog_on_image :
      ContinuousOn
        (fun s : ℂ => explicitFormulaVerticalChannelLogDerivative channel s)
        (γ '' S) := by
    exact
      explicitFormulaVerticalChannelLogDerivative_continuousOn_of_avoidsSingularBoundary
        F T havoid side channel
  have hlog :
      ContinuousOn
        (fun t : ℝ => explicitFormulaVerticalChannelLogDerivative channel (γ t))
        S := by
    exact hlog_on_image.comp hγS (fun t ht => ⟨t, ht, rfl⟩)
  have hphi_cont :
      Continuous
        (fun s : ℂ => zetaCompletedExplicitFormulaPhi f (s - 1 / 2)) :=
    zetaCompletedExplicitFormulaPhi_shift_continuous hPhi
  have hphi :
      ContinuousOn
        (fun t : ℝ => zetaCompletedExplicitFormulaPhi f (γ t - 1 / 2))
        S := by
    exact (hphi_cont.comp hγ).continuousOn
  change
    ContinuousOn
      (fun t : ℝ =>
        explicitFormulaVerticalChannelLogDerivative channel (γ t) *
          zetaCompletedExplicitFormulaPhi f (γ t - 1 / 2))
      S
  exact hlog.mul hphi

/-- Compact finite-edge continuity of the realized vertical channel packet away from
singular boundary hits.

This is the single analytic regularity owner for the finite vertical edges.  The correction
channel uses `havoid`; the prime and archimedean channels are included in the same packet so
right/left and channel projections do not become independent roots. -/
theorem zetaCompletedExplicitFormulaVerticalChannelPacket_continuousOn_ownerCompactRegularity
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    (ContinuousOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)) ∧
    (ContinuousOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)) := by
  have hRP :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaVerticalChannelIntegrand f
            ExplicitFormulaVerticalSide.right
            ExplicitFormulaVerticalChannel.prime
            (F.rectangle T) t)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    explicitFormulaVerticalChannelIntegrand_continuousOn_ownerCompactRegularity
      hPhi F T havoid ExplicitFormulaVerticalSide.right ExplicitFormulaVerticalChannel.prime
  have hRA :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaVerticalChannelIntegrand f
            ExplicitFormulaVerticalSide.right
            ExplicitFormulaVerticalChannel.archimedean
            (F.rectangle T) t)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    explicitFormulaVerticalChannelIntegrand_continuousOn_ownerCompactRegularity
      hPhi F T havoid ExplicitFormulaVerticalSide.right ExplicitFormulaVerticalChannel.archimedean
  have hRC :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaVerticalChannelIntegrand f
            ExplicitFormulaVerticalSide.right
            ExplicitFormulaVerticalChannel.correction
            (F.rectangle T) t)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    explicitFormulaVerticalChannelIntegrand_continuousOn_ownerCompactRegularity
      hPhi F T havoid ExplicitFormulaVerticalSide.right ExplicitFormulaVerticalChannel.correction
  have hLP :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaVerticalChannelIntegrand f
            ExplicitFormulaVerticalSide.left
            ExplicitFormulaVerticalChannel.prime
            (F.rectangle T) t)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    explicitFormulaVerticalChannelIntegrand_continuousOn_ownerCompactRegularity
      hPhi F T havoid ExplicitFormulaVerticalSide.left ExplicitFormulaVerticalChannel.prime
  have hLA :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaVerticalChannelIntegrand f
            ExplicitFormulaVerticalSide.left
            ExplicitFormulaVerticalChannel.archimedean
            (F.rectangle T) t)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    explicitFormulaVerticalChannelIntegrand_continuousOn_ownerCompactRegularity
      hPhi F T havoid ExplicitFormulaVerticalSide.left ExplicitFormulaVerticalChannel.archimedean
  have hLC :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaVerticalChannelIntegrand f
            ExplicitFormulaVerticalSide.left
            ExplicitFormulaVerticalChannel.correction
            (F.rectangle T) t)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    explicitFormulaVerticalChannelIntegrand_continuousOn_ownerCompactRegularity
      hPhi F T havoid ExplicitFormulaVerticalSide.left ExplicitFormulaVerticalChannel.correction
  exact ⟨⟨hRP, hRA, hRC⟩, ⟨hLP, hLA, hLC⟩⟩

/-- Compact finite-edge regularity of the realized vertical channel packet away from
singular boundary hits.

This is the single owner regularity input for vertical channel realization.  The right and
left packet integrability lemmas, and their prime/archimedean/correction projections, are
thin consumers of this theorem. -/
theorem zetaCompletedExplicitFormulaVerticalChannelPacket_integrable_ownerCompactRegularity
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    (IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)) ∧
    (IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)) := by
  have hcont :
      (ContinuousOn
          (fun t : ℝ =>
            explicitFormulaPrimeLogDerivative
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
          (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
        ContinuousOn
          (fun t : ℝ =>
            explicitFormulaArchimedeanLogDerivative
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
          (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
        ContinuousOn
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
          (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)) ∧
      (ContinuousOn
          (fun t : ℝ =>
            explicitFormulaPrimeLogDerivative
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
          (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
        ContinuousOn
          (fun t : ℝ =>
            explicitFormulaArchimedeanLogDerivative
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
          (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
        ContinuousOn
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
          (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)) :=
    zetaCompletedExplicitFormulaVerticalChannelPacket_continuousOn_ownerCompactRegularity
      hPhi F T havoid
  exact
    ⟨⟨complex_continuousOn_Icc_integrableOn hcont.1.1,
        complex_continuousOn_Icc_integrableOn hcont.1.2.1,
        complex_continuousOn_Icc_integrableOn hcont.1.2.2⟩,
      ⟨complex_continuousOn_Icc_integrableOn hcont.2.1,
        complex_continuousOn_Icc_integrableOn hcont.2.2.1,
        complex_continuousOn_Icc_integrableOn hcont.2.2.2⟩⟩

/-- Scheduled compact finite-edge regularity of the realized vertical channel packet. -/
theorem zetaCompletedExplicitFormulaScheduledVerticalChannelPacket_integrable_ownerCompactRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        (Set.Icc (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        (Set.Icc (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        (Set.Icc (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T)) ∧
    (IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        (Set.Icc (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        (Set.Icc (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        (Set.Icc (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T)) :=
  zetaCompletedExplicitFormulaVerticalChannelPacket_integrable_ownerCompactRegularity
    h.phi_control F (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)

/-- Finite-edge regularity of the realized right vertical channel packet away from scheduled
singular boundary hits. -/
theorem zetaCompletedExplicitFormulaRightChannelPacket_integrable_ownerVerticalRegularity
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaVerticalChannelPacket_integrable_ownerCompactRegularity
      hPhi F T havoid).1

/-- Finite-edge integrability of the realized right prime channel. -/
theorem zetaCompletedExplicitFormulaRightPrimeChannelIntegrand_integrable_ownerVerticalIntegralTransport
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaRightChannelPacket_integrable_ownerVerticalRegularity
      hPhi F T havoid).1

/-- Finite-edge integrability of the realized right archimedean channel. -/
theorem zetaCompletedExplicitFormulaRightArchimedeanChannelIntegrand_integrable_ownerVerticalIntegralTransport
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaRightChannelPacket_integrable_ownerVerticalRegularity
      hPhi F T havoid).2.1

/-- Finite-edge integrability of the realized right correction channel. -/
theorem zetaCompletedExplicitFormulaRightCorrectionChannelIntegrand_integrable_ownerVerticalIntegralTransport
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaRightChannelPacket_integrable_ownerVerticalRegularity
      hPhi F T havoid).2.2

/-- Finite-edge integrability of the realized right vertical channel packet. -/
theorem zetaCompletedExplicitFormulaRightChannelIntegrands_integrable_ownerVerticalIntegralTransport
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact zetaCompletedExplicitFormulaRightChannelPacket_integrable_ownerVerticalRegularity
    hPhi F T havoid

/-- Right vertical realization preserves the finite direct sum of channel summands. -/
theorem zetaCompletedExplicitFormulaRightChannelIntegralSum_eq_sum_channelIntegrals_ownerIntervalIntegralAdditivity
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
  exact
    complex_setIntegral_three_add_eq_sum_integrals
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)
      (fun t : ℝ =>
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (zetaCompletedExplicitFormulaRightChannelIntegrands_integrable_ownerVerticalIntegralTransport
        hPhi F T havoid).1
      (zetaCompletedExplicitFormulaRightChannelIntegrands_integrable_ownerVerticalIntegralTransport
        hPhi F T havoid).2.1
      (zetaCompletedExplicitFormulaRightChannelIntegrands_integrable_ownerVerticalIntegralTransport
        hPhi F T havoid).2.2

/-- Right vertical realization transport from the completed boundary object to the channel
packet. -/
theorem zetaCompletedExplicitFormulaRightLineIntegral_eq_channelIntegrals_ownerVerticalIntegralTransport
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
  exact
    (zetaCompletedExplicitFormulaRightLineIntegral_eq_integral_channelSum_ownerVerticalPointwiseTransport
      f F T).trans
      (zetaCompletedExplicitFormulaRightChannelIntegralSum_eq_sum_channelIntegrals_ownerIntervalIntegralAdditivity
        hPhi F T havoid)

/-- Left vertical realization of the pointwise completed channel-packet decomposition before
distributing the interval integral over the three channel summands. -/
theorem zetaCompletedExplicitFormulaLeftLineIntegral_eq_integral_channelSum_ownerVerticalPointwiseTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
      ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) := by
  exact integral_congr_ae
    (Filter.Eventually.of_forall
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaVerticalIntegrand_eq_channelIntegrands_ownerCompletedLogDerivativeDecomposition
          f (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t)))

/-- Finite-edge regularity of the realized left vertical channel packet away from scheduled
singular boundary hits. -/
theorem zetaCompletedExplicitFormulaLeftChannelPacket_integrable_ownerVerticalRegularity
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaVerticalChannelPacket_integrable_ownerCompactRegularity
      hPhi F T havoid).2

/-- Finite-edge integrability of the realized left prime channel. -/
theorem zetaCompletedExplicitFormulaLeftPrimeChannelIntegrand_integrable_ownerVerticalIntegralTransport
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaLeftChannelPacket_integrable_ownerVerticalRegularity
      hPhi F T havoid).1

/-- Finite-edge integrability of the realized left archimedean channel. -/
theorem zetaCompletedExplicitFormulaLeftArchimedeanChannelIntegrand_integrable_ownerVerticalIntegralTransport
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaLeftChannelPacket_integrable_ownerVerticalRegularity
      hPhi F T havoid).2.1

/-- Finite-edge integrability of the realized left correction channel. -/
theorem zetaCompletedExplicitFormulaLeftCorrectionChannelIntegrand_integrable_ownerVerticalIntegralTransport
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaLeftChannelPacket_integrable_ownerVerticalRegularity
      hPhi F T havoid).2.2

/-- Finite-edge integrability of the realized left vertical channel packet. -/
theorem zetaCompletedExplicitFormulaLeftChannelIntegrands_integrable_ownerVerticalIntegralTransport
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact zetaCompletedExplicitFormulaLeftChannelPacket_integrable_ownerVerticalRegularity
    hPhi F T havoid

/-- Left vertical realization preserves the finite direct sum of channel summands. -/
theorem zetaCompletedExplicitFormulaLeftChannelIntegralSum_eq_sum_channelIntegrals_ownerIntervalIntegralAdditivity
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
  exact
    complex_setIntegral_three_add_eq_sum_integrals
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)
      (fun t : ℝ =>
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (zetaCompletedExplicitFormulaLeftChannelIntegrands_integrable_ownerVerticalIntegralTransport
        hPhi F T havoid).1
      (zetaCompletedExplicitFormulaLeftChannelIntegrands_integrable_ownerVerticalIntegralTransport
        hPhi F T havoid).2.1
      (zetaCompletedExplicitFormulaLeftChannelIntegrands_integrable_ownerVerticalIntegralTransport
        hPhi F T havoid).2.2

/-- Left vertical realization transport from the completed boundary object to the channel
packet. -/
theorem zetaCompletedExplicitFormulaLeftLineIntegral_eq_channelIntegrals_ownerVerticalIntegralTransport
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
  exact
    (zetaCompletedExplicitFormulaLeftLineIntegral_eq_integral_channelSum_ownerVerticalPointwiseTransport
      f F T).trans
      (zetaCompletedExplicitFormulaLeftChannelIntegralSum_eq_sum_channelIntegrals_ownerIntervalIntegralAdditivity
        hPhi F T havoid)

/-- The right-minus-left vertical realization of the completed object is the realized channel
packet. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_eq_channelSum_of_right_left_transport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hright :
      zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) =
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) +
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) +
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)))
    (hleft :
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) +
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) +
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))) :
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
      zetaCompletedExplicitFormulaVerticalChannelSum f F T := by
  let RP : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaPrimeLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)
  let RA : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)
  let RC : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)
  let LP : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaPrimeLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
  let LA : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
  let LC : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
  have hright' :
      zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) =
        RP + RA + RC := hright
  have hleft' :
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
        LP + LA + LC := hleft
  calc
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
        (RP + RA + RC) - (LP + LA + LC) := by
      exact congrArg₂ Sub.sub hright' hleft'
    _ = (RP - LP) + (RA - LA) + (RC - LC) := by
      exact complex_three_add_sub_three_add_eq RP RA RC LP LA LC
    _ = zetaCompletedExplicitFormulaVerticalChannelSum f F T := by
      rfl

/-- The completed log-derivative decomposition transported through the right and left
vertical integrals gives the channel-sum identity at a fixed height. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_eq_channelSum_ownerCompletedLogDerivativeDecomposition
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
      zetaCompletedExplicitFormulaVerticalChannelSum f F T := by
  exact
    zetaCompletedExplicitFormulaVerticalDifference_eq_channelSum_of_right_left_transport
      f F T
      (zetaCompletedExplicitFormulaRightLineIntegral_eq_channelIntegrals_ownerVerticalIntegralTransport
        hPhi F T havoid)
      (zetaCompletedExplicitFormulaLeftLineIntegral_eq_channelIntegrals_ownerVerticalIntegralTransport
        hPhi F T havoid)

/-- The vertical-channel comparison remainder is pointwise zero. -/
theorem zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder_eq_zero
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder f F T = 0 := by
  exact sub_eq_zero.mpr
    (zetaCompletedExplicitFormulaVerticalDifference_eq_channelSum_ownerCompletedLogDerivativeDecomposition
      hPhi F T havoid)

/-- The scheduled completed vertical-channel comparison remainder is pointwise zero. -/
theorem zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder_scheduled_eq_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder f F
        (h.height_schedule.height u) = 0 :=
  zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder_eq_zero
    h.phi_control F (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)

/-- The scheduled completed vertical-channel comparison remainder tends to zero. -/
theorem zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder f F
          (h.height_schedule.height u)) =
        (fun _T : ℝ => (0 : ℂ)) := by
    funext u
    exact zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder_scheduled_eq_zero f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    tendsto_const_nhds

/-- The actual completed log-derivative vertical side is asymptotic to the sum of the
prime, archimedean, and correction channels. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_sub_channelSum_tendsto_zero_ownerCompletedVerticalChannelComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaRightLineIntegral f
              (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
              (F.rectangle (h.height_schedule.height u))) -
          zetaCompletedExplicitFormulaVerticalChannelSum f F
            (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder_tendsto_zero f F h

/-- Public wrapper for the completed vertical side/channel-sum comparison. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_sub_channelSum_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaRightLineIntegral f
              (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
              (F.rectangle (h.height_schedule.height u))) -
          zetaCompletedExplicitFormulaVerticalChannelSum f F
            (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaVerticalDifference_sub_channelSum_tendsto_zero_ownerCompletedVerticalChannelComparison
      f F h

/-- Core vertical-decomposition owner theorem.

This is the vertical contour theorem to prove by decomposing the completed negative
log-derivative into its prime, archimedean, and correction terms: the right-minus-left
vertical contour contribution converges to the analytic boundary sum. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_core_ownerVerticalDecomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hchannels :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) -
          zetaCompletedExplicitFormulaLeftLineIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  have hcomparison :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaRightLineIntegral f
                (F.toContourFamily.rectangle (h.height_schedule.height u)) -
              zetaCompletedExplicitFormulaLeftLineIntegral f
                (F.toContourFamily.rectangle (h.height_schedule.height u))) -
            zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
              (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaVerticalDifference_sub_channelSum_tendsto_zero
      f F.toContourFamily h
  have hchannels :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    hchannels
  have hsum :
      Tendsto
        (fun u : ℝ =>
          ((zetaCompletedExplicitFormulaRightLineIntegral f
                  (F.toContourFamily.rectangle (h.height_schedule.height u)) -
                zetaCompletedExplicitFormulaLeftLineIntegral f
                  (F.toContourFamily.rectangle (h.height_schedule.height u))) -
              zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
                (h.height_schedule.height u)) +
            zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
              (h.height_schedule.height u))
        atTop
        (𝓝 (0 + zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    hcomparison.add hchannels
  have htarget :
      0 + zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
    zero_add _
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) -
          zetaCompletedExplicitFormulaLeftLineIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u))) =
        (fun u : ℝ =>
          ((zetaCompletedExplicitFormulaRightLineIntegral f
                  (F.toContourFamily.rectangle (h.height_schedule.height u)) -
                zetaCompletedExplicitFormulaLeftLineIntegral f
                  (F.toContourFamily.rectangle (h.height_schedule.height u))) -
              zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
                (h.height_schedule.height u)) +
            zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
              (h.height_schedule.height u)) := by
    funext u
    exact (sub_add_cancel
      (zetaCompletedExplicitFormulaRightLineIntegral f
          (F.toContourFamily.rectangle (h.height_schedule.height u)) -
        zetaCompletedExplicitFormulaLeftLineIntegral f
          (F.toContourFamily.rectangle (h.height_schedule.height u)))
      (zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
        (h.height_schedule.height u))).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            ((zetaCompletedExplicitFormulaRightLineIntegral f
                    (F.toContourFamily.rectangle (h.height_schedule.height T)) -
                  zetaCompletedExplicitFormulaLeftLineIntegral f
                    (F.toContourFamily.rectangle (h.height_schedule.height T))) -
                zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
                  (h.height_schedule.height T)) +
              zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
                (h.height_schedule.height T))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Two scheduled vertically regular contour realizations reconstruct the same completed
boundary scalar.

This is the contour-realization invariance surface used by downstream assembly: the
chosen scheduled vertical measurements are not erased, but each is transported to the same
completed boundary object. -/
theorem zetaCompletedExplicitFormulaScheduledVerticalRealizations_reconstruct_sameBoundaryScalar
    (f : ZetaAdmissibleFunction)
    (F₁ F₂ : ExplicitFormulaVerticallyRegularContourFamily)
    (h₁ : ExplicitFormulaFamilyAnalyticPackage f F₁.toContourFamily)
    (h₂ : ExplicitFormulaFamilyAnalyticPackage f F₂.toContourFamily)
    (hchannels₁ :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaVerticalChannelSum f F₁.toContourFamily
            (h₁.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
    (hchannels₂ :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaVerticalChannelSum f F₂.toContourFamily
            (h₂.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f))) :
    (Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral f
            (F₁.toContourFamily.rectangle (h₁.height_schedule.height u)) -
          zetaCompletedExplicitFormulaLeftLineIntegral f
            (F₁.toContourFamily.rectangle (h₁.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f))) ∧
    (Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral f
            (F₂.toContourFamily.rectangle (h₂.height_schedule.height u)) -
          zetaCompletedExplicitFormulaLeftLineIntegral f
            (F₂.toContourFamily.rectangle (h₂.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f))) := by
  constructor
  · exact
      zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_core_ownerVerticalDecomposition
        f F₁ h₁ hchannels₁
  · exact
      zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_core_ownerVerticalDecomposition
        f F₂ h₂ hchannels₂

/-- Owner vertical-boundary remainder theorem.

This is the algebraic remainder form of the vertical decomposition theorem. -/
theorem zetaCompletedExplicitFormulaVerticalBoundaryRemainder_tendsto_zero_ownerVerticalDecomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hchannels :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral f
              (F.toContourFamily.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
              (F.toContourFamily.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_core_ownerVerticalDecomposition
      f F h hchannels
  have hconst :
      Tendsto
        (fun _u : ℝ => zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaRightLineIntegral f
                (F.toContourFamily.rectangle (h.height_schedule.height u)) -
              zetaCompletedExplicitFormulaLeftLineIntegral f
                (F.toContourFamily.rectangle (h.height_schedule.height u))) -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaBoundarySumAnalytic f -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    hvertical.sub hconst
  have htarget :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f -
          zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        0 := by
    exact sub_self _
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F.toContourFamily
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaRightLineIntegral f
                (F.toContourFamily.rectangle (h.height_schedule.height u)) -
              zetaCompletedExplicitFormulaLeftLineIntegral f
                (F.toContourFamily.rectangle (h.height_schedule.height u))) -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
    funext u
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            (zetaCompletedExplicitFormulaRightLineIntegral f
                  (F.toContourFamily.rectangle (h.height_schedule.height u)) -
                zetaCompletedExplicitFormulaLeftLineIntegral f
                  (F.toContourFamily.rectangle (h.height_schedule.height u))) -
              zetaCompletedExplicitFormulaBoundarySumAnalytic f)
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- Owner vertical-channel decomposition limit.

This is the vertical-line integration theorem for the completed negative log-derivative
decomposition: the right-minus-left vertical contour contribution converges to the analytic
prime/archimedean/correction boundary sum. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_ownerVerticalDecomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hchannels :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) -
          zetaCompletedExplicitFormulaLeftLineIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  exact
    zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_core_ownerVerticalDecomposition
      f F h hchannels

/-- The autocorrelation contour right edge is strictly to the right of `1`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_contourFamily_rightEdge_gt_one
    (f : ZetaAdmissibleFunction) :
    (1 : ℝ) <
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c := by
  exact lt_add_of_pos_left (1 : ℝ) one_half_pos

/-- The autocorrelation contour left edge is strictly in the left half-plane. -/
theorem zetaCompletedExplicitFormula_autocorrelation_contourFamily_leftEdge_lt_zero
    (f : ZetaAdmissibleFunction) :
    1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c < (0 : ℝ) := by
  have hleft_eq :
      1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c =
        -(1 / 2 : ℝ) := by
    calc
      1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c =
          1 - ((1 / 2 : ℝ) + 1) := rfl
      _ = 1 - (1 + (1 / 2 : ℝ)) := by
        exact congrArg (fun x : ℝ => 1 - x) (add_comm (1 / 2 : ℝ) 1)
      _ = 1 - 1 - (1 / 2 : ℝ) := by
        exact sub_add_eq_sub_sub 1 1 (1 / 2 : ℝ)
      _ = 0 - (1 / 2 : ℝ) := by
        exact congrArg (fun x : ℝ => x - (1 / 2 : ℝ)) (sub_self 1)
      _ = -(1 / 2 : ℝ) := by
        exact zero_sub (1 / 2 : ℝ)
  exact Eq.symm hleft_eq ▸ neg_lt_zero.mpr one_half_pos

/-- Points on the autocorrelation right vertical side have real part strictly greater
than `1`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_rightPath_one_lt_re
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    (1 : ℝ) <
      (zetaCompletedExplicitFormulaRightPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re := by
  exact
    Eq.symm
      (zetaCompletedExplicitFormulaRightPath_re
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) ▸
      zetaCompletedExplicitFormula_autocorrelation_contourFamily_rightEdge_gt_one f

/-- Points on the autocorrelation left vertical side lie strictly in the left half-plane. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_re_lt_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re <
      (0 : ℝ) := by
  exact
    Eq.symm
      (zetaCompletedExplicitFormulaLeftPath_re
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) ▸
      zetaCompletedExplicitFormula_autocorrelation_contourFamily_leftEdge_lt_zero f

/-- The completed zeta factor is nonzero on the autocorrelation right vertical side. -/
theorem zetaCompletedExplicitFormula_autocorrelation_rightPath_completedZeta_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    completedRiemannZeta
      (zetaCompletedExplicitFormulaRightPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) ≠ 0 :=
  completedRiemannZeta_ne_zero_of_one_lt_re
    (zetaCompletedExplicitFormulaRightPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t)
    (zetaCompletedExplicitFormula_autocorrelation_rightPath_one_lt_re f T t)

/-- The completed zeta factor is nonzero on the autocorrelation left vertical side. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_completedZeta_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    completedRiemannZeta
      (zetaCompletedExplicitFormulaLeftPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) ≠ 0 :=
  completedRiemannZeta_ne_zero_of_re_lt_zero
    (zetaCompletedExplicitFormulaLeftPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t)
    (zetaCompletedExplicitFormula_autocorrelation_leftPath_re_lt_zero f T t)

/-- `Gammaℝ` is nonzero on the autocorrelation right vertical side. -/
theorem zetaCompletedExplicitFormula_autocorrelation_rightPath_Gammaℝ_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaRightPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos
    (zetaCompletedExplicitFormulaRightPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t)
    (lt_trans zero_lt_one
      (zetaCompletedExplicitFormula_autocorrelation_rightPath_one_lt_re f T t))

/-- The doubled Gamma argument is nonzero on the autocorrelation right vertical side. -/
theorem zetaCompletedExplicitFormula_autocorrelation_rightPath_half_Gammaℝ_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaRightPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t / 2) ≠ 0 := by
  have hre_pos :
      0 <
        (zetaCompletedExplicitFormulaRightPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re / 2 :=
    div_pos
      (lt_trans zero_lt_one
        (zetaCompletedExplicitFormula_autocorrelation_rightPath_one_lt_re f T t))
      two_pos
  have hre :
      (zetaCompletedExplicitFormulaRightPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t / 2).re =
        (zetaCompletedExplicitFormulaRightPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re / 2 := by
    exact RCLike.div_re_ofReal
      (z :=
        zetaCompletedExplicitFormulaRightPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t)
      (r := (2 : ℝ))
  exact Gammaℝ_ne_zero_of_re_pos
    (zetaCompletedExplicitFormulaRightPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t / 2)
    (Eq.symm hre ▸ hre_pos)

/-- The left autocorrelation path is not the normalization point `0`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t ≠ 0 := by
  intro hzero
  have hre_zero :
      (zetaCompletedExplicitFormulaLeftPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re =
        (0 : ℝ) := by
    exact congrArg Complex.re hzero
  have hre_lt_zero :
      (zetaCompletedExplicitFormulaLeftPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re <
        (0 : ℝ) :=
    zetaCompletedExplicitFormula_autocorrelation_leftPath_re_lt_zero f T t
  exact (not_lt_of_ge (le_of_eq hre_zero.symm)) hre_lt_zero

/-- Negative even real points have real coordinate at most `-2`. -/
theorem negativeEven_complex_re_le_neg_two
    (n : ℕ) :
    (((-2 : ℂ) * (((n + 1 : ℕ) : ℂ))).re : ℝ) ≤ (-2 : ℝ) := by
  have hone_le_nat : (1 : ℕ) ≤ n + 1 :=
    Nat.succ_le_succ (Nat.zero_le n)
  have hone_le_real : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr hone_le_nat
  have hneg_two_nonpos : (-2 : ℝ) ≤ 0 :=
    neg_nonpos.mpr (le_of_lt zero_lt_two)
  have hmul :
      (-2 : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ (-2 : ℝ) * 1 :=
    mul_le_mul_of_nonpos_left hone_le_real hneg_two_nonpos
  have hright :
      (-2 : ℝ) * 1 = (-2 : ℝ) :=
    mul_one (-2 : ℝ)
  have hre :
      (((-2 : ℂ) * (((n + 1 : ℕ) : ℂ))).re : ℝ) =
        (-2 : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    calc
      (((-2 : ℂ) * (((n + 1 : ℕ) : ℂ))).re : ℝ) =
          ((((-2 : ℝ) : ℂ) * (((n + 1 : ℕ) : ℝ) : ℂ)).re : ℝ) := by
        rfl
      _ = ((((-2 : ℝ) * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ).re : ℝ) := by
        exact congrArg Complex.re (Complex.ofReal_mul (-2 : ℝ) ((n + 1 : ℕ) : ℝ))
      _ = (-2 : ℝ) * ((n + 1 : ℕ) : ℝ) := by
        exact Complex.ofReal_re ((-2 : ℝ) * ((n + 1 : ℕ) : ℝ))
  exact Eq.symm hre ▸ hmul.trans (le_of_eq hright)

/-- The real number `-2` lies strictly to the left of `-1/2`. -/
theorem neg_two_lt_neg_half : (-2 : ℝ) < -(1 / 2 : ℝ) :=
  lt_trans
    (neg_lt_neg (show (1 : ℝ) < 2 from one_lt_two))
    (neg_lt_neg one_half_lt_one)

/-- A point with real part `-1/2` is not a negative nonzero even point. -/
theorem not_negativeEven_of_re_eq_neg_half
    {z : ℂ}
    (hzre : z.re = -(1 / 2 : ℝ)) :
    ¬ ∃ n : ℕ, z = (-2 : ℂ) * (((n + 1 : ℕ) : ℂ)) := by
  intro hnegative
  match hnegative with
  | ⟨n, hn⟩ =>
      have hre_negative :
          z.re =
            (((-2 : ℂ) * (((n + 1 : ℕ) : ℂ))).re : ℝ) :=
        congrArg Complex.re hn
      have hneg_half_le_neg_two :
          -(1 / 2 : ℝ) ≤ (-2 : ℝ) := by
        exact
          Eq.symm hzre ▸
            hre_negative ▸
              negativeEven_complex_re_le_neg_two n
      exact (not_lt_of_ge hneg_half_le_neg_two) neg_two_lt_neg_half

/-- `Gammaℝ` is nonzero at every point with real part `-1/2`. -/
theorem Gammaℝ_ne_zero_of_re_eq_neg_half
    {z : ℂ}
    (hzre : z.re = -(1 / 2 : ℝ)) :
    Complex.Gammaℝ z ≠ 0 := by
  have hz_ne_zero : z ≠ 0 := by
    intro hz_zero
    have hre_zero : z.re = (0 : ℝ) :=
      congrArg Complex.re hz_zero
    have hneg_half_eq_zero : -(1 / 2 : ℝ) = (0 : ℝ) :=
      Eq.symm hzre ▸ hre_zero
    exact (ne_of_lt (neg_lt_zero.mpr one_half_pos)) hneg_half_eq_zero
  exact
    Gammaℝ_ne_zero_of_ne_zero_and_not_negative_even
      hz_ne_zero
      (not_negativeEven_of_re_eq_neg_half hzre)

/-- `Gammaℝ` is nonzero on the autocorrelation left vertical side. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_Gammaℝ_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaLeftPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) ≠ 0 := by
  have hre :
      (zetaCompletedExplicitFormulaLeftPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re =
        -(1 / 2 : ℝ) := by
    have hpath :=
      zetaCompletedExplicitFormulaLeftPath_re
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t
    have hedge :
        1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c =
          -(1 / 2 : ℝ) := by
      calc
        1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c =
            1 - ((1 / 2 : ℝ) + 1) := rfl
        _ = 1 - (1 + (1 / 2 : ℝ)) := by
          exact congrArg (fun x : ℝ => 1 - x) (add_comm (1 / 2 : ℝ) 1)
        _ = 1 - 1 - (1 / 2 : ℝ) := by
          exact sub_add_eq_sub_sub 1 1 (1 / 2 : ℝ)
        _ = 0 - (1 / 2 : ℝ) := by
          exact congrArg (fun x : ℝ => x - (1 / 2 : ℝ)) (sub_self 1)
        _ = -(1 / 2 : ℝ) := by
          exact zero_sub (1 / 2 : ℝ)
    exact hpath.trans hedge
  exact Gammaℝ_ne_zero_of_re_eq_neg_half hre

/-- `Gammaℝ` is nonzero in the horizontal strip `-1 < Re z < 0`, since its zero
locus in the left half-plane starts at the negative even points. -/
theorem Gammaℝ_ne_zero_of_neg_one_lt_re_and_re_lt_zero
    {z : ℂ}
    (hzre_low : (-1 : ℝ) < z.re)
    (hzre_high : z.re < (0 : ℝ)) :
    Complex.Gammaℝ z ≠ 0 := by
  have hz_ne_zero : z ≠ 0 := by
    intro hz_zero
    have hre_zero : z.re = (0 : ℝ) :=
      congrArg Complex.re hz_zero
    exact (not_lt_of_ge (le_of_eq hre_zero.symm)) hzre_high
  have hnot_negative :
      ¬ ∃ n : ℕ, z = (-2 : ℂ) * (((n + 1 : ℕ) : ℂ)) := by
    intro hnegative
    match hnegative with
    | ⟨n, hn⟩ =>
        have hre_negative :
            z.re =
              (((-2 : ℂ) * (((n + 1 : ℕ) : ℂ))).re : ℝ) :=
          congrArg Complex.re hn
        have hzre_le_neg_two : z.re ≤ (-2 : ℝ) :=
          hre_negative ▸ negativeEven_complex_re_le_neg_two n
        have hneg_two_lt_re : (-2 : ℝ) < z.re :=
          lt_trans
            (neg_lt_neg (show (1 : ℝ) < 2 from one_lt_two))
            hzre_low
        exact (not_lt_of_ge hzre_le_neg_two) hneg_two_lt_re
  exact Gammaℝ_ne_zero_of_ne_zero_and_not_negative_even hz_ne_zero hnot_negative

/-- The half-argument of the autocorrelation left path lies in the strip
`-1 < Re z < 0`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_half_re_strip
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    (-1 : ℝ) <
        (zetaCompletedExplicitFormulaLeftPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t / 2).re ∧
      (zetaCompletedExplicitFormulaLeftPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t / 2).re <
        (0 : ℝ) := by
  let z : ℂ :=
    zetaCompletedExplicitFormulaLeftPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t
  have hz_re_neg :
      z.re < (0 : ℝ) :=
    zetaCompletedExplicitFormula_autocorrelation_leftPath_re_lt_zero f T t
  have hz_re_eq :
      z.re = -(1 / 2 : ℝ) := by
    have hpath :=
      zetaCompletedExplicitFormulaLeftPath_re
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t
    have hedge :
        1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c =
          -(1 / 2 : ℝ) := by
      calc
        1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c =
            1 - ((1 / 2 : ℝ) + 1) := rfl
        _ = 1 - (1 + (1 / 2 : ℝ)) := by
          exact congrArg (fun x : ℝ => 1 - x) (add_comm (1 / 2 : ℝ) 1)
        _ = 1 - 1 - (1 / 2 : ℝ) := by
          exact sub_add_eq_sub_sub 1 1 (1 / 2 : ℝ)
        _ = 0 - (1 / 2 : ℝ) := by
          exact congrArg (fun x : ℝ => x - (1 / 2 : ℝ)) (sub_self 1)
        _ = -(1 / 2 : ℝ) := by
          exact zero_sub (1 / 2 : ℝ)
    exact hpath.trans hedge
  have hneg_two_lt_zre : (-2 : ℝ) < z.re :=
    Eq.symm hz_re_eq ▸ neg_two_lt_neg_half
  have hneg_two_div_two_eq_neg_one :
      (-2 : ℝ) / 2 = (-1 : ℝ) := by
    calc
      (-2 : ℝ) / 2 = -(2 / 2 : ℝ) := by
        exact neg_div (2 : ℝ) 2
      _ = -(1 : ℝ) := by
        exact congrArg Neg.neg (div_self (two_ne_zero : (2 : ℝ) ≠ 0))
      _ = (-1 : ℝ) := rfl
  have hre_div :
      (z / 2).re = z.re / 2 :=
    RCLike.div_re_ofReal (z := z) (r := (2 : ℝ))
  have hlow_div :
      (-2 : ℝ) / 2 < z.re / 2 :=
    div_lt_div_of_pos_right hneg_two_lt_zre two_pos
  have hlow :
      (-1 : ℝ) < (z / 2).re :=
    Eq.symm hre_div ▸
      (Eq.symm hneg_two_div_two_eq_neg_one ▸ hlow_div)
  have hhigh_div :
      z.re / 2 < (0 : ℝ) / 2 :=
    div_lt_div_of_pos_right hz_re_neg two_pos
  have hzero_div :
      (0 : ℝ) / 2 = (0 : ℝ) :=
    zero_div 2
  have hhigh :
      (z / 2).re < (0 : ℝ) :=
    hre_div ▸ (hzero_div ▸ hhigh_div)
  exact And.intro hlow hhigh

/-- `Gammaℝ` is nonzero at the half-argument on the autocorrelation left vertical side. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_half_Gammaℝ_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaLeftPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t / 2) ≠ 0 := by
  have hstrip :=
    zetaCompletedExplicitFormula_autocorrelation_leftPath_half_re_strip f T t
  exact Gammaℝ_ne_zero_of_neg_one_lt_re_and_re_lt_zero hstrip.1 hstrip.2

/-- The autocorrelation right vertical side never meets `0`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_rightPath_ne_zero
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t ≠ 0 := by
  intro hzero
  have hre_zero :
      (zetaCompletedExplicitFormulaRightPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re =
        (0 : ℝ) :=
    congrArg Complex.re hzero
  have hone_lt_zero : (1 : ℝ) < 0 :=
    Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) < x)
      hre_zero
      (zetaCompletedExplicitFormula_autocorrelation_rightPath_one_lt_re f T t)
  exact (not_lt_of_ge zero_le_one) hone_lt_zero

/-- The autocorrelation right vertical side never meets `1`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_rightPath_ne_one
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t ≠ 1 := by
  intro hone
  have hre_one :
      (zetaCompletedExplicitFormulaRightPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re =
        (1 : ℝ) :=
    congrArg Complex.re hone
  have hone_lt_one : (1 : ℝ) < 1 :=
    Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) < x)
      hre_one
      (zetaCompletedExplicitFormula_autocorrelation_rightPath_one_lt_re f T t)
  exact (lt_irrefl (1 : ℝ)) hone_lt_one

/-- The autocorrelation left vertical side never meets `1`. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_ne_one
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t ≠ 1 := by
  intro hone
  have hre_one :
      (zetaCompletedExplicitFormulaLeftPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t).re =
        (1 : ℝ) :=
    congrArg Complex.re hone
  have hone_lt_zero : (1 : ℝ) < 0 :=
    Eq.symm hre_one ▸
      zetaCompletedExplicitFormula_autocorrelation_leftPath_re_lt_zero f T t
  exact (not_lt_of_ge zero_le_one) hone_lt_zero

/-- The autocorrelation right vertical side avoids every completed-zeta contour singularity. -/
theorem zetaCompletedExplicitFormula_autocorrelation_rightPath_not_singular
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    ¬ explicitFormulaContourSingularPoint
      (zetaCompletedExplicitFormulaRightPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) := by
  intro hsingular
  match hsingular with
  | Or.inl hzero =>
      exact zetaCompletedExplicitFormula_autocorrelation_rightPath_ne_zero f T t hzero
  | Or.inr (Or.inl hone) =>
      exact zetaCompletedExplicitFormula_autocorrelation_rightPath_ne_one f T t hone
  | Or.inr (Or.inr (Or.inl hgamma)) =>
      exact
        zetaCompletedExplicitFormula_autocorrelation_rightPath_Gammaℝ_ne_zero
          f T t hgamma
  | Or.inr (Or.inr (Or.inr (Or.inl hgamma_half))) =>
      exact
        zetaCompletedExplicitFormula_autocorrelation_rightPath_half_Gammaℝ_ne_zero
          f T t hgamma_half
  | Or.inr (Or.inr (Or.inr (Or.inr hzeta))) =>
      exact
        zetaCompletedExplicitFormula_autocorrelation_rightPath_completedZeta_ne_zero
          f T t hzeta.2.2

/-- The autocorrelation left vertical side avoids every completed-zeta contour singularity. -/
theorem zetaCompletedExplicitFormula_autocorrelation_leftPath_not_singular
    (f : ZetaAdmissibleFunction) (T t : ℝ) :
    ¬ explicitFormulaContourSingularPoint
      (zetaCompletedExplicitFormulaLeftPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle T) t) := by
  intro hsingular
  match hsingular with
  | Or.inl hzero =>
      exact zetaCompletedExplicitFormula_autocorrelation_leftPath_ne_zero f T t hzero
  | Or.inr (Or.inl hone) =>
      exact zetaCompletedExplicitFormula_autocorrelation_leftPath_ne_one f T t hone
  | Or.inr (Or.inr (Or.inl hgamma)) =>
      exact
        zetaCompletedExplicitFormula_autocorrelation_leftPath_Gammaℝ_ne_zero
          f T t hgamma
  | Or.inr (Or.inr (Or.inr (Or.inl hgamma_half))) =>
      exact
        zetaCompletedExplicitFormula_autocorrelation_leftPath_half_Gammaℝ_ne_zero
          f T t hgamma_half
  | Or.inr (Or.inr (Or.inr (Or.inr hzeta))) =>
      exact
        zetaCompletedExplicitFormula_autocorrelation_leftPath_completedZeta_ne_zero
          f T t hzeta.2.2

/-- The autocorrelation contour family has no vertical-side completed-zeta singularities. -/
theorem zetaCompletedExplicitFormula_autocorrelation_vertical_avoids
    (f : ZetaAdmissibleFunction) (T : ℝ) :
    explicitFormulaContourFamilyVerticalAvoidsSingularBoundary
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) T := by
  intro z hsingular hvertical
  match hvertical with
  | Or.inl hright =>
      match hright with
      | ⟨t, _ht, hzpath⟩ =>
          exact
            zetaCompletedExplicitFormula_autocorrelation_rightPath_not_singular f T t
              (Eq.symm hzpath ▸ hsingular)
  | Or.inr hleft =>
      match hleft with
      | ⟨t, _ht, hzpath⟩ =>
          exact
            zetaCompletedExplicitFormula_autocorrelation_leftPath_not_singular f T t
              (Eq.symm hzpath ▸ hsingular)

/-- The autocorrelation contour family equipped with the vertical regularity needed by the
vertical-channel owner theorem. -/
def zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily
    (f : ZetaAdmissibleFunction) :
    ExplicitFormulaVerticallyRegularContourFamily := by
  exact
    { toContourFamily := zetaCompletedExplicitFormula_autocorrelation_contourFamily f
      vertical_avoids :=
        zetaCompletedExplicitFormula_autocorrelation_vertical_avoids f }

/-- The analytic package for the autocorrelation contour family.  This is the package
which supplies the cofinal height schedule used by the vertical-channel decomposition,
from an explicitly supplied horizontal-bad-height avoiding schedule. -/
def zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) := by
  exact
    ExplicitFormulaFamilyAnalyticPackage.of_horizontalAvoidingSchedule
      (zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily f)
      schedule hPhi hLog

/-- The regular autocorrelation family projects to the contour family used downstream. -/
theorem zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily_toContourFamily
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily f).toContourFamily =
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f := by
  rfl

/-- Prime-channel transport remainder for the autocorrelation family. -/
theorem zetaCompletedExplicitFormula_autocorrelation_primeVerticalChannelTransportRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
            f schedule hPhi hLog).height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransport
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
      (zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
        f schedule hPhi hLog)

/-- Archimedean-channel transport remainder for the autocorrelation family. -/
theorem zetaCompletedExplicitFormula_autocorrelation_archimedeanVerticalChannelTransportRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
            f schedule hPhi hLog).height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransport
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
      (zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
        f schedule hPhi hLog)

/-- Correction-channel transport remainder for the autocorrelation family. -/
theorem zetaCompletedExplicitFormula_autocorrelation_correctionVerticalChannelTransportRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f))
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
            f schedule hPhi hLog).height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransport
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
      (zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
        f schedule hPhi hLog)
      hone

/-- The autocorrelation vertical-channel sum converges to the analytic boundary sum along
the analytic package schedule. -/
theorem zetaCompletedExplicitFormula_autocorrelation_verticalChannelSum_tendsto_boundarySum
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f))
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaVerticalChannelSum
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
            f schedule hPhi hLog).height_schedule.height u))
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaBoundarySumAnalytic
          (convolutionAutocorrelation f))) := by
  let F : ExplicitFormulaVerticallyRegularContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily f
  let h : ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      F.toContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f schedule hPhi hLog
  have hprime :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
            (convolutionAutocorrelation f)
            F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 0) := by
    exact
      zetaCompletedExplicitFormula_autocorrelation_primeVerticalChannelTransportRemainder_tendsto_zero
        f schedule hPhi hLog
  have harch :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
            (convolutionAutocorrelation f)
            F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 0) := by
    exact
      zetaCompletedExplicitFormula_autocorrelation_archimedeanVerticalChannelTransportRemainder_tendsto_zero
        f schedule hPhi hLog
  have hcorr :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
            (convolutionAutocorrelation f)
            F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 0) := by
    exact
      zetaCompletedExplicitFormula_autocorrelation_correctionVerticalChannelTransportRemainder_tendsto_zero
        f schedule hPhi hLog hone
  have hscheduled :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaVerticalChannelSum
            (convolutionAutocorrelation f)
            F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaBoundarySumAnalytic
            (convolutionAutocorrelation f))) :=
    zetaCompletedExplicitFormulaVerticalChannelSum_tendsto_boundarySum
      (convolutionAutocorrelation f) F h hprime harch hcorr
  exact hscheduled

/-- The autocorrelation vertical difference converges to the analytic boundary sum along
the analytic package schedule. -/
theorem zetaCompletedExplicitFormula_autocorrelation_scheduledVertical_tendsto_boundarySum
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f))
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral
            (convolutionAutocorrelation f)
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f schedule hPhi hLog).height_schedule.height u)) -
          zetaCompletedExplicitFormulaLeftLineIntegral
            (convolutionAutocorrelation f)
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f schedule hPhi hLog).height_schedule.height u)))
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaBoundarySumAnalytic
          (convolutionAutocorrelation f))) := by
  let F : ExplicitFormulaVerticallyRegularContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily f
  let h : ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      F.toContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f schedule hPhi hLog
  have hchannels :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaVerticalChannelSum
            (convolutionAutocorrelation f)
            F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaBoundarySumAnalytic
            (convolutionAutocorrelation f))) := by
    exact
      zetaCompletedExplicitFormula_autocorrelation_verticalChannelSum_tendsto_boundarySum
        f schedule hPhi hLog hone
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral
              (convolutionAutocorrelation f)
              (F.toContourFamily.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral
              (convolutionAutocorrelation f)
              (F.toContourFamily.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaBoundarySumAnalytic
            (convolutionAutocorrelation f))) :=
    zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_ownerVerticalDecomposition
      (convolutionAutocorrelation f) F h hchannels
  exact hvertical

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
