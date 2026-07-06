import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.BasicChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionContribution

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

/-- A scheduled vertical-channel limit is equivalent to vanishing of its
transport remainder.  This is the forward direction, used to keep analytic
channel estimates separate from the final remainder bookkeeping. -/
theorem explicitFormulaScheduledVerticalChannelTransportRemainder_tendsto_zero_of_channel_tendsto
    (channel : ℝ → ℂ) (boundary : ℂ)
    (hchannel : Tendsto channel atTop (𝓝 boundary)) :
    Tendsto (fun u : ℝ => channel u - boundary) atTop (𝓝 0) := by
  have hboundary :
      Tendsto (fun _u : ℝ => boundary) atTop (𝓝 boundary) :=
    tendsto_const_nhds
  have hdiff :
      Tendsto (fun u : ℝ => channel u - boundary) atTop (𝓝 (boundary - boundary)) :=
    hchannel.sub hboundary
  have hzero : boundary - boundary = (0 : ℂ) := by
    exact sub_self boundary
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => channel u - boundary) atTop (𝓝 z))
      hzero
      hdiff

/-- Vanishing of a scheduled vertical-channel transport remainder gives the
corresponding scheduled channel limit. -/
theorem explicitFormulaScheduledVerticalChannel_tendsto_of_transportRemainder_tendsto_zero
    (channel : ℝ → ℂ) (boundary : ℂ)
    (hremainder :
      Tendsto (fun u : ℝ => channel u - boundary) atTop (𝓝 0)) :
    Tendsto channel atTop (𝓝 boundary) := by
  have hsum :
      Tendsto (fun u : ℝ => (channel u - boundary) + boundary)
        atTop
        (𝓝 (0 + boundary)) :=
    hremainder.add tendsto_const_nhds
  have hsum_boundary :
      Tendsto (fun u : ℝ => (channel u - boundary) + boundary)
        atTop
        (𝓝 boundary) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => (channel u - boundary) + boundary)
          atTop
          (𝓝 z))
      (zero_add boundary)
      hsum
  have hfun :
      channel = fun u : ℝ => (channel u - boundary) + boundary := by
    funext u
    exact (sub_add_cancel (channel u) boundary).symm
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 boundary))
      hfun.symm
      hsum_boundary

/-- Limit projection for a component of an additive channel decomposition.

If a scheduled total channel is pointwise `component + remainder`, the total
has limit `componentBoundary + remainderBoundary`, and the remainder has limit
`remainderBoundary`, then the component has limit `componentBoundary`.  This is
pure limit algebra; the analytic work is in proving the two input limits. -/
theorem explicitFormulaScheduledComponent_tendsto_of_total_add_remainder
    (total component remainder : ℝ → ℂ)
    (componentBoundary remainderBoundary : ℂ)
    (hdecomp : ∀ u : ℝ, total u = component u + remainder u)
    (htotal :
      Tendsto total atTop (𝓝 (componentBoundary + remainderBoundary)))
    (hremainder :
      Tendsto remainder atTop (𝓝 remainderBoundary)) :
    Tendsto component atTop (𝓝 componentBoundary) := by
  have htotal_sub :
      Tendsto (fun u : ℝ => total u - remainder u)
        atTop
        (𝓝 ((componentBoundary + remainderBoundary) - remainderBoundary)) :=
    htotal.sub hremainder
  have hlimit :
      (componentBoundary + remainderBoundary) - remainderBoundary =
        componentBoundary := by
    calc
      (componentBoundary + remainderBoundary) - remainderBoundary =
          (componentBoundary + remainderBoundary) + -remainderBoundary := by
        exact sub_eq_add_neg
          (componentBoundary + remainderBoundary) remainderBoundary
      _ = componentBoundary + (remainderBoundary + -remainderBoundary) := by
        exact add_assoc componentBoundary remainderBoundary (-remainderBoundary)
      _ = componentBoundary + 0 := by
        exact congrArg
          (fun z : ℂ => componentBoundary + z)
          (add_neg_cancel remainderBoundary)
      _ = componentBoundary := by
        exact add_zero componentBoundary
  have htotal_sub_component :
      Tendsto (fun u : ℝ => total u - remainder u)
        atTop
        (𝓝 componentBoundary) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => total u - remainder u) atTop (𝓝 z))
      hlimit
      htotal_sub
  have hpoint :
      component = fun u : ℝ => total u - remainder u := by
    funext u
    have hu : total u = component u + remainder u :=
      hdecomp u
    calc
      component u = (component u + remainder u) - remainder u := by
        calc
          component u =
              component u + 0 := by
            exact (add_zero (component u)).symm
          _ = component u + (remainder u + -remainder u) := by
            exact congrArg
              (fun z : ℂ => component u + z)
              (add_neg_cancel (remainder u)).symm
          _ = (component u + remainder u) + -remainder u := by
            exact (add_assoc (component u) (remainder u) (-(remainder u))).symm
          _ = (component u + remainder u) - remainder u := by
            exact (sub_eq_add_neg
              (component u + remainder u) (remainder u)).symm
      _ = total u - remainder u := by
        exact congrArg (fun z : ℂ => z - remainder u) hu.symm
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 componentBoundary))
      hpoint.symm
      htotal_sub_component

/-- Limit projection for a component of a subtractive channel decomposition.

This is the same algebra as
`explicitFormulaScheduledComponent_tendsto_of_total_add_remainder`, stated in
the common form `component = total - remainder`. -/
theorem explicitFormulaScheduledComponent_tendsto_of_eq_total_sub_remainder
    (total component remainder : ℝ → ℂ)
    (totalBoundary componentBoundary remainderBoundary : ℂ)
    (hboundary : componentBoundary = totalBoundary - remainderBoundary)
    (hdecomp : ∀ u : ℝ, component u = total u - remainder u)
    (htotal : Tendsto total atTop (𝓝 totalBoundary))
    (hremainder : Tendsto remainder atTop (𝓝 remainderBoundary)) :
    Tendsto component atTop (𝓝 componentBoundary) := by
  have hsub :
      Tendsto (fun u : ℝ => total u - remainder u)
        atTop
        (𝓝 (totalBoundary - remainderBoundary)) :=
    htotal.sub hremainder
  have htarget :
      Tendsto (fun u : ℝ => total u - remainder u)
        atTop
        (𝓝 componentBoundary) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => total u - remainder u) atTop (𝓝 z))
      hboundary.symm
      hsub
  have hfun :
      component = fun u : ℝ => total u - remainder u := by
    funext u
    exact hdecomp u
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 componentBoundary))
      hfun.symm
      htarget

/-- Prime-channel convergence is exactly the prime transport-remainder
vanishing statement. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_of_channel_tendsto_primeContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hchannel :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaScheduledVerticalChannelTransportRemainder_tendsto_zero_of_channel_tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F (h.height_schedule.height u))
      (zetaCompletedExplicitFormulaPrimeContribution f)
      hchannel

/-- Archimedean-channel convergence is exactly the archimedean
transport-remainder vanishing statement. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_of_channel_tendsto_archimedeanContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hchannel :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannel
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaScheduledVerticalChannelTransportRemainder_tendsto_zero_of_channel_tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u))
      (zetaCompletedExplicitFormulaArchimedeanContribution f)
      hchannel

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
