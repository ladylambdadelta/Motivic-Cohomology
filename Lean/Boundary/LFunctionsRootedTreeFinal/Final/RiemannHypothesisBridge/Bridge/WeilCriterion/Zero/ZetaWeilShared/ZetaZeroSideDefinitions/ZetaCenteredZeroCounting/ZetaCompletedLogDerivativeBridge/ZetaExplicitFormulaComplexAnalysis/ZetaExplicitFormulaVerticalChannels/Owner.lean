import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaLogDerivative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaResidueRegularity.Owner
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Boundary explicit-formula vertical channel owner API

This file owns the vertical realization of the prime, archimedean, and
correction channel packets.  The scheduled contour is the analytic
normalization procedure: it transports a chosen vertical measurement into the
completed boundary-channel object.  The complex-analysis contour assembly file
imports these channel objects and treats the corresponding transport theorems
as owner facts.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The prime logarithmic-derivative vertical channel. -/
noncomputable def zetaCompletedExplicitFormulaPrimeVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    explicitFormulaPrimeLogDerivative (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaPrimeLogDerivative (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- The archimedean logarithmic-derivative vertical channel. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    explicitFormulaArchimedeanLogDerivative
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- The pole-correction logarithmic-derivative vertical channel. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- The sum of the three vertical logarithmic-derivative channels. -/
noncomputable def zetaCompletedExplicitFormulaVerticalChannelSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaPrimeVerticalChannel f F T +
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T +
      zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T

/-! ## Channel transport remainders -/

/-- Prime vertical-channel transport remainder.

The channel-specific convergence theorem is not a consequence of the total residue
identity alone.  The analytic content is the vanishing of this scheduled remainder. -/
noncomputable def zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaPrimeVerticalChannel f F T -
    zetaCompletedExplicitFormulaPrimeContribution f

/-- The prime vertical channel is its completed contribution plus its transport remainder. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_contribution_add_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaPrimeVerticalChannel f F T =
      zetaCompletedExplicitFormulaPrimeContribution f +
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder f F T := by
  let V : ℂ := zetaCompletedExplicitFormulaPrimeVerticalChannel f F T
  let P : ℂ := zetaCompletedExplicitFormulaPrimeContribution f
  change V = P + (V - P)
  calc
    V = V + 0 := by
      exact (add_zero V).symm
    _ = V + (-P + P) := by
      exact congrArg (fun x : ℂ => V + x) (neg_add_cancel P).symm
    _ = (V + -P) + P := by
      exact (add_assoc V (-P) P).symm
    _ = P + (V + -P) := by
      exact add_comm (V + -P) P
    _ = P + (V - P) := by
      exact congrArg (fun x : ℂ => P + x) (sub_eq_add_neg V P).symm

/-- Archimedean vertical-channel transport remainder.

The channel-specific convergence theorem is the vanishing of this scheduled remainder,
after the Gamma/completion channel has been normalized. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T -
    zetaCompletedExplicitFormulaArchimedeanContribution f

/-- The archimedean vertical channel is its completed contribution plus its transport remainder. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_eq_contribution_add_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T =
      zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder f F T := by
  let V : ℂ := zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T
  let A : ℂ := zetaCompletedExplicitFormulaArchimedeanContribution f
  change V = A + (V - A)
  calc
    V = V + 0 := by
      exact (add_zero V).symm
    _ = V + (-A + A) := by
      exact congrArg (fun x : ℂ => V + x) (neg_add_cancel A).symm
    _ = (V + -A) + A := by
      exact (add_assoc V (-A) A).symm
    _ = A + (V + -A) := by
      exact add_comm (V + -A) A
    _ = A + (V - A) := by
      exact congrArg (fun x : ℂ => A + x) (sub_eq_add_neg V A).symm

/-- Pole-correction vertical-channel transport remainder.

The channel-specific convergence theorem is the vanishing of this scheduled remainder,
after the pole faces have been transported through the vertical contour. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T -
    zetaCompletedExplicitFormulaCorrectionContribution f

/-- The pole-correction vertical channel is its completed contribution plus its transport remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_contribution_add_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T =
      zetaCompletedExplicitFormulaCorrectionContribution f +
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder f F T := by
  let V : ℂ := zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T
  let C : ℂ := zetaCompletedExplicitFormulaCorrectionContribution f
  change V = C + (V - C)
  calc
    V = V + 0 := by
      exact (add_zero V).symm
    _ = V + (-C + C) := by
      exact congrArg (fun x : ℂ => V + x) (neg_add_cancel C).symm
    _ = (V + -C) + C := by
      exact (add_assoc V (-C) C).symm
    _ = C + (V + -C) := by
      exact add_comm (V + -C) C
    _ = C + (V - C) := by
      exact congrArg (fun x : ℂ => C + x) (sub_eq_add_neg V C).symm

/-! ## Channel realization limit owners -/

/-- The three scheduled vertical channel projections owned by this file. -/
inductive ExplicitFormulaScheduledVerticalChannelProjection where
  | prime
  | archimedean
  | correction

/-- The realized vertical contour integral attached to a scheduled channel projection. -/
noncomputable def explicitFormulaScheduledVerticalChannelProjectionIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  match channel with
  | ExplicitFormulaScheduledVerticalChannelProjection.prime =>
      zetaCompletedExplicitFormulaPrimeVerticalChannel f F T
  | ExplicitFormulaScheduledVerticalChannelProjection.archimedean =>
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T
  | ExplicitFormulaScheduledVerticalChannelProjection.correction =>
      zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T

/-- The boundary contribution attached to a scheduled channel projection. -/
noncomputable def explicitFormulaScheduledVerticalChannelProjectionContribution
    (f : ZetaAdmissibleFunction)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  match channel with
  | ExplicitFormulaScheduledVerticalChannelProjection.prime =>
      zetaCompletedExplicitFormulaPrimeContribution f
  | ExplicitFormulaScheduledVerticalChannelProjection.archimedean =>
      zetaCompletedExplicitFormulaArchimedeanContribution f
  | ExplicitFormulaScheduledVerticalChannelProjection.correction =>
      zetaCompletedExplicitFormulaCorrectionContribution f

/-- The transport remainder attached to a scheduled vertical channel projection. -/
noncomputable def explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledVerticalChannelProjectionIntegral f F T channel -
    explicitFormulaScheduledVerticalChannelProjectionContribution f channel

/-- The scheduled projected vertical-decomposition error is exactly the selected channel
transport remainder already defined from the concrete vertical channel integrals. -/
noncomputable def explicitFormulaScheduledProjectedVerticalDecompositionError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
    f F (h.height_schedule.height u) channel

/-- The selected-channel projected vertical decomposition is definitionally the scheduled
transport remainder at the chosen height. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_eq_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    explicitFormulaScheduledProjectedVerticalDecompositionError f F h u channel =
      explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
        f F (h.height_schedule.height u) channel := by
  rfl

/-- The prime scheduled projection transport remainder is the concrete prime
vertical-channel transport remainder. -/
theorem explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_prime_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
        f F T ExplicitFormulaScheduledVerticalChannelProjection.prime =
      zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder f F T := by
  rfl

/-- The archimedean scheduled projection transport remainder is the concrete
archimedean vertical-channel transport remainder. -/
theorem explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_archimedean_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
        f F T ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
      zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder f F T := by
  rfl

/-- The correction scheduled projection transport remainder is the concrete
correction vertical-channel transport remainder. -/
theorem explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_correction_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
        f F T ExplicitFormulaScheduledVerticalChannelProjection.correction =
      zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder f F T := by
  rfl

/-- The projected prime vertical-decomposition error is the scheduled concrete prime
transport remainder at the analytic-package height. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_prime_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledProjectedVerticalDecompositionError
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime =
      zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
        f F (h.height_schedule.height u) := by
  calc
    explicitFormulaScheduledProjectedVerticalDecompositionError
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime =
      explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
        f F (h.height_schedule.height u)
          ExplicitFormulaScheduledVerticalChannelProjection.prime := by
        exact
          explicitFormulaScheduledProjectedVerticalDecompositionError_eq_transportRemainder
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime
    _ = zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
        f F (h.height_schedule.height u) := by
        exact
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_prime_eq
            f F (h.height_schedule.height u)

/-- The projected archimedean vertical-decomposition error is the scheduled concrete
archimedean transport remainder at the analytic-package height. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_archimedean_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledProjectedVerticalDecompositionError
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
      zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
        f F (h.height_schedule.height u) := by
  calc
    explicitFormulaScheduledProjectedVerticalDecompositionError
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
      explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
        f F (h.height_schedule.height u)
          ExplicitFormulaScheduledVerticalChannelProjection.archimedean := by
        exact
          explicitFormulaScheduledProjectedVerticalDecompositionError_eq_transportRemainder
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean
    _ = zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
        f F (h.height_schedule.height u) := by
        exact
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_archimedean_eq
            f F (h.height_schedule.height u)

/-- The projected correction vertical-decomposition error is the scheduled concrete
correction transport remainder at the analytic-package height. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_correction_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledProjectedVerticalDecompositionError
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction =
      zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
        f F (h.height_schedule.height u) := by
  calc
    explicitFormulaScheduledProjectedVerticalDecompositionError
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction =
      explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
        f F (h.height_schedule.height u)
          ExplicitFormulaScheduledVerticalChannelProjection.correction := by
        exact
          explicitFormulaScheduledProjectedVerticalDecompositionError_eq_transportRemainder
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction
    _ = zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
        f F (h.height_schedule.height u) := by
        exact
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_correction_eq
            f F (h.height_schedule.height u)

/-- Prime projected vertical-decomposition convergence follows from the exact concrete
prime transport-remainder convergence, by pointwise projection only. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_prime_tendsto_zero_of_transportRemainder
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
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
            f F (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaScheduledProjectedVerticalDecompositionError_prime_eq f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    htransport

/-- Archimedean projected vertical-decomposition convergence follows from the exact
concrete archimedean transport-remainder convergence, by pointwise projection only. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_archimedean_tendsto_zero_of_transportRemainder
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
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
            f F (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaScheduledProjectedVerticalDecompositionError_archimedean_eq f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    htransport

/-- Correction projected vertical-decomposition convergence follows from the exact
concrete correction transport-remainder convergence, by pointwise projection only. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_correction_tendsto_zero_of_transportRemainder
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
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
            f F (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaScheduledProjectedVerticalDecompositionError_correction_eq f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    htransport

/-! ## Component contour-estimate analytic inputs -/

/-- The scheduled rectangle boundary integral at the package height. -/
noncomputable def explicitFormulaScheduledRectangleContourIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f
    (F.rectangle (h.height_schedule.height u))

/-- The scheduled finite completed-zero residue sum at the package height. -/
noncomputable def explicitFormulaScheduledRectangleResidueSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  explicitFormulaCompletedZeroHeightWindowResidueSum f
    (h.height_schedule.height u)

/-- The finite rectangle residue equality along the selected schedule. -/
theorem explicitFormulaScheduledRectangleContourIntegral_eq_residueSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily)
    (u : ℝ)
    (hfinite :
      let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
      zetaCompletedExplicitFormulaContourIntegral f
          (F.toContourFamily.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u)) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    explicitFormulaScheduledRectangleContourIntegral f F.toContourFamily h u =
      explicitFormulaScheduledRectangleResidueSum f F.toContourFamily h u := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  calc
    explicitFormulaScheduledRectangleContourIntegral f F.toContourFamily h u =
      zetaCompletedExplicitFormulaContourIntegral f
        (F.toContourFamily.rectangle (h.height_schedule.height u)) := by
        rfl
    _ = explicitFormulaCompletedZeroHeightWindowResidueSum f
        (h.height_schedule.height u) := by
        exact hfinite
    _ = explicitFormulaScheduledRectangleResidueSum f F.toContourFamily h u := by
        rfl

/-- The scheduled horizontal-side contribution of the rectangle. -/
noncomputable def explicitFormulaScheduledHorizontalSideDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral f
      (F.rectangle (h.height_schedule.height u)) -
    zetaCompletedExplicitFormulaBottomLineIntegral f
      (F.rectangle (h.height_schedule.height u))

/-- The scheduled full vertical-side contribution of the rectangle. -/
noncomputable def explicitFormulaScheduledCompletedVerticalSideDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f
      (F.rectangle (h.height_schedule.height u)) -
    zetaCompletedExplicitFormulaLeftLineIntegral f
      (F.rectangle (h.height_schedule.height u))

/-- The scheduled rectangle integral decomposes into vertical and horizontal sides. -/
theorem explicitFormulaScheduledRectangleContourIntegral_eq_vertical_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledRectangleContourIntegral f F h u =
      explicitFormulaScheduledCompletedVerticalSideDifference f F h u +
        explicitFormulaScheduledHorizontalSideDifference f F h u := by
  rfl

/-- The horizontal-side decay target along the selected schedule.

This is the horizontal estimate in the contour-integral-to-boundary path; it is
recorded as a named step consumed by the selected-channel convergence primitive. -/
def explicitFormulaScheduledHorizontalSideDifferenceTendstoZero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) : Prop :=
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledHorizontalSideDifference f F.toContourFamily h u)
      atTop
      (𝓝 0)

/-- The selected scheduled vertical contour realization. -/
noncomputable def explicitFormulaSelectedScheduledVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledVerticalChannelProjectionIntegral
    f F (h.height_schedule.height u) channel

/-- The selected boundary channel contribution. -/
noncomputable def explicitFormulaSelectedVerticalBoundaryChannel
    (f : ZetaAdmissibleFunction)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledVerticalChannelProjectionContribution f channel

/-- The selected projected decomposition error is the finite selected channel minus its
limiting boundary channel. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_eq_selectedChannel_sub_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    explicitFormulaScheduledProjectedVerticalDecompositionError f F h u channel =
      explicitFormulaSelectedScheduledVerticalChannel f F h u channel -
        explicitFormulaSelectedVerticalBoundaryChannel f channel := by
  rfl

/-- The selected finite channel is exactly the scheduled projection integral. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_eq_projectionIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    explicitFormulaSelectedScheduledVerticalChannel f F h u channel =
      explicitFormulaScheduledVerticalChannelProjectionIntegral
        f F (h.height_schedule.height u) channel := by
  rfl

/-- The selected limiting channel is exactly the scheduled projection contribution. -/
theorem explicitFormulaSelectedVerticalBoundaryChannel_eq_projectionContribution
    (f : ZetaAdmissibleFunction)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    explicitFormulaSelectedVerticalBoundaryChannel f channel =
      explicitFormulaScheduledVerticalChannelProjectionContribution f channel := by
  rfl

/-- The selected prime finite channel is the concrete prime vertical channel. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_prime_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaSelectedScheduledVerticalChannel
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime =
      zetaCompletedExplicitFormulaPrimeVerticalChannel
        f F (h.height_schedule.height u) := by
  rfl

/-- The selected archimedean finite channel is the concrete archimedean vertical channel. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_archimedean_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaSelectedScheduledVerticalChannel
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel
        f F (h.height_schedule.height u) := by
  rfl

/-- The selected correction finite channel is the concrete correction vertical channel. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_correction_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaSelectedScheduledVerticalChannel
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction =
      zetaCompletedExplicitFormulaCorrectionVerticalChannel
        f F (h.height_schedule.height u) := by
  rfl

/-- The selected prime boundary channel is the completed prime contribution. -/
theorem explicitFormulaSelectedVerticalBoundaryChannel_prime_eq
    (f : ZetaAdmissibleFunction) :
    explicitFormulaSelectedVerticalBoundaryChannel
        f ExplicitFormulaScheduledVerticalChannelProjection.prime =
      zetaCompletedExplicitFormulaPrimeContribution f := by
  rfl

/-- The selected archimedean boundary channel is the completed archimedean contribution. -/
theorem explicitFormulaSelectedVerticalBoundaryChannel_archimedean_eq
    (f : ZetaAdmissibleFunction) :
    explicitFormulaSelectedVerticalBoundaryChannel
        f ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
      zetaCompletedExplicitFormulaArchimedeanContribution f := by
  rfl

/-- The selected correction boundary channel is the completed correction contribution. -/
theorem explicitFormulaSelectedVerticalBoundaryChannel_correction_eq
    (f : ZetaAdmissibleFunction) :
    explicitFormulaSelectedVerticalBoundaryChannel
        f ExplicitFormulaScheduledVerticalChannelProjection.correction =
      zetaCompletedExplicitFormulaCorrectionContribution f := by
  rfl

/-! ## Component contour-to-boundary roots -/

/-- Shared algebraic passage from a scheduled component transport remainder to the
corresponding boundary-channel convergence. -/
theorem explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
    (contribution : ℂ)
    (remainder : ℝ → ℂ)
    (channel : ℝ → ℂ)
    (hchannel : ∀ u : ℝ, channel u = contribution + remainder u)
    (hremainder : Tendsto remainder atTop (𝓝 0)) :
    Tendsto channel atTop (𝓝 contribution) := by
  have hconst :
      Tendsto (fun _u : ℝ => contribution) atTop (𝓝 contribution) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun u : ℝ => contribution + remainder u)
        atTop
        (𝓝 (contribution + 0)) :=
    hconst.add hremainder
  have htarget :
      contribution + 0 = contribution :=
    add_zero contribution
  have hpointwise :
      channel = fun u : ℝ => contribution + remainder u := by
    funext u
    exact hchannel u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 contribution))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => contribution + remainder u) atTop (𝓝 z))
      htarget
      hsum)

/-- Prime component analytic input: the scheduled prime transport remainder vanishes.

Intended proof chain:
finite rectangle residue equality -> horizontal decay -> vertical-side decomposition ->
prime logarithmic-derivative projection -> prime transport remainder convergence. -/
theorem explicitFormulaScheduledPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeContourToBoundaryInput
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hprojection :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F.toContourFamily (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.prime)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_tendsto_zero_ownerProjectedContourSpine
      f F hSchedule ExplicitFormulaScheduledVerticalChannelProjection.prime
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F.toContourFamily (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.prime) := by
    funext u
    exact
      (explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_prime_eq
        f F.toContourFamily (h.height_schedule.height u)).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hprojection

/-- Archimedean component analytic input: the scheduled archimedean transport remainder
vanishes.

Intended proof chain:
finite rectangle residue equality -> horizontal decay -> vertical-side decomposition ->
Gamma/completion projection -> archimedean transport remainder convergence. -/
theorem explicitFormulaScheduledArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanContourToBoundaryInput
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hprojection :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F.toContourFamily (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_tendsto_zero_ownerProjectedContourSpine
      f F hSchedule ExplicitFormulaScheduledVerticalChannelProjection.archimedean
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F.toContourFamily (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.archimedean) := by
    funext u
    exact
      (explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_archimedean_eq
        f F.toContourFamily (h.height_schedule.height u)).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hprojection

/-- Correction component analytic input: the scheduled pole-correction transport remainder
vanishes.

Intended proof chain:
finite rectangle residue equality -> horizontal decay -> vertical-side decomposition ->
pole-face projection -> correction transport remainder convergence. -/
theorem explicitFormulaScheduledCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerCorrectionContourToBoundaryInput
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hprojection :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F.toContourFamily (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.correction)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_tendsto_zero_ownerProjectedContourSpine
      f F hSchedule ExplicitFormulaScheduledVerticalChannelProjection.correction
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F.toContourFamily (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.correction) := by
    funext u
    exact
      (explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_correction_eq
        f F.toContourFamily (h.height_schedule.height u)).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hprojection

/-- Prime contour-to-boundary convergence after residue evaluation, horizontal decay,
vertical-side decomposition, and projection to the prime logarithmic-derivative channel. -/
theorem explicitFormulaScheduledPrimeVerticalChannel_tendsto_boundaryContribution_ownerPrimeContourToBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (zetaCompletedExplicitFormulaPrimeContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      (fun u =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_contribution_add_transportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      (explicitFormulaScheduledPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeContourToBoundaryInput
        f F hSchedule)

/-- Archimedean contour-to-boundary convergence after residue evaluation,
horizontal decay, vertical-side decomposition, and projection to the Gamma channel. -/
theorem explicitFormulaScheduledArchimedeanVerticalChannel_tendsto_boundaryContribution_ownerArchimedeanContourToBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (zetaCompletedExplicitFormulaArchimedeanContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      (fun u =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel_eq_contribution_add_transportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      (explicitFormulaScheduledArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanContourToBoundaryInput
        f F hSchedule)

/-- Correction contour-to-boundary convergence after residue evaluation,
horizontal decay, vertical-side decomposition, and projection to the pole channel. -/
theorem explicitFormulaScheduledCorrectionVerticalChannel_tendsto_boundaryContribution_ownerCorrectionContourToBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (zetaCompletedExplicitFormulaCorrectionContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      (fun u =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_contribution_add_transportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      (explicitFormulaScheduledCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerCorrectionContourToBoundaryInput
        f F hSchedule)

/-- Selected-channel contour-to-boundary convergence by component projection.

The analytic work is owned by the three concrete component contour-to-boundary
theorems above.  This theorem only projects the selected finite channel and the
selected boundary channel to the matching concrete component. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_tendsto_boundaryChannel_ownerContourToBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F.toContourFamily h u channel)
      atTop
      (𝓝 (explicitFormulaSelectedVerticalBoundaryChannel f channel)) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  match channel with
  | ExplicitFormulaScheduledVerticalChannelProjection.prime =>
      exact
        explicitFormulaScheduledPrimeVerticalChannel_tendsto_boundaryContribution_ownerPrimeContourToBoundary
          f F hSchedule
  | ExplicitFormulaScheduledVerticalChannelProjection.archimedean =>
      exact
        explicitFormulaScheduledArchimedeanVerticalChannel_tendsto_boundaryContribution_ownerArchimedeanContourToBoundary
          f F hSchedule
  | ExplicitFormulaScheduledVerticalChannelProjection.correction =>
      exact
        explicitFormulaScheduledCorrectionVerticalChannel_tendsto_boundaryContribution_ownerCorrectionContourToBoundary
          f F hSchedule

/-- The selected projected error is the difference between a convergent selected finite
channel and its limiting boundary channel. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_tendsto_zero_of_selectedChannel_tendsto_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection)
    (hchannel :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel f F h u channel)
        atTop
        (𝓝 (explicitFormulaSelectedVerticalBoundaryChannel f channel))) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError f F h u channel)
      atTop
      (𝓝 0) := by
  have hconst :
      Tendsto
        (fun _u : ℝ => explicitFormulaSelectedVerticalBoundaryChannel f channel)
        atTop
        (𝓝 (explicitFormulaSelectedVerticalBoundaryChannel f channel)) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel f F h u channel -
            explicitFormulaSelectedVerticalBoundaryChannel f channel)
        atTop
        (𝓝
          (explicitFormulaSelectedVerticalBoundaryChannel f channel -
            explicitFormulaSelectedVerticalBoundaryChannel f channel)) :=
    hchannel.sub hconst
  have hzero :
      explicitFormulaSelectedVerticalBoundaryChannel f channel -
        explicitFormulaSelectedVerticalBoundaryChannel f channel = 0 :=
    sub_self _
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError f F h u channel) =
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel f F h u channel -
            explicitFormulaSelectedVerticalBoundaryChannel f channel) := by
    funext u
    exact
      explicitFormulaScheduledProjectedVerticalDecompositionError_eq_selectedChannel_sub_boundary
        f F h u channel
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaSelectedScheduledVerticalChannel f F h u channel -
              explicitFormulaSelectedVerticalBoundaryChannel f channel)
          atTop
          (𝓝 z))
      hzero
      hsub)

/-- Shared scheduled vertical-decomposition analytic spine.

This is the single component-level analytic input left for the contour proof chain:
finite rectangle residue equality, horizontal decay, vertical decomposition, and
projection to the selected channel identify the scheduled channel transport error
and show that it vanishes.  The prime, archimedean, and correction public
component theorems below are wrappers over this selected-channel statement. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_tendsto_zero_ownerSelectedVerticalDecompositionSpine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F.toContourFamily h u channel)
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hchannel :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel
            f F.toContourFamily h u channel)
        atTop
        (𝓝 (explicitFormulaSelectedVerticalBoundaryChannel f channel)) :=
    explicitFormulaSelectedScheduledVerticalChannel_tendsto_boundaryChannel_ownerContourToBoundary
      f F hSchedule channel
  exact
    explicitFormulaScheduledProjectedVerticalDecompositionError_tendsto_zero_of_selectedChannel_tendsto_boundary
      f F.toContourFamily h channel hchannel

/-- Prime channel vertical-decomposition analytic input.

This is the exact component theorem left by the contour proof chain: after the
prime logarithmic-derivative residue equality and the prime horizontal decay
have isolated the vertical sides, the scheduled prime vertical decomposition
identifies the remaining contour transport error with zero in the limit. -/
theorem explicitFormulaScheduledPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeVerticalDecomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F.toContourFamily h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaScheduledProjectedVerticalDecompositionError_tendsto_zero_ownerSelectedVerticalDecompositionSpine
      f F hSchedule ExplicitFormulaScheduledVerticalChannelProjection.prime

/-- Archimedean channel vertical-decomposition analytic input.

This is the exact Gamma/completion component theorem left by the contour proof
chain: archimedean residue equality plus archimedean horizontal decay reduce
the component estimate to this scheduled vertical-decomposition limit. -/
theorem explicitFormulaScheduledArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanVerticalDecomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F.toContourFamily h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaScheduledProjectedVerticalDecompositionError_tendsto_zero_ownerSelectedVerticalDecompositionSpine
      f F hSchedule ExplicitFormulaScheduledVerticalChannelProjection.archimedean

/-- Pole-correction channel vertical-decomposition analytic input.

This is the exact pole-face component theorem left by the contour proof chain:
correction residue equality plus correction horizontal decay reduce the
component estimate to this scheduled vertical-decomposition limit. -/
theorem explicitFormulaScheduledCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerCorrectionVerticalDecomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F.toContourFamily h u ExplicitFormulaScheduledVerticalChannelProjection.correction)
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaScheduledProjectedVerticalDecompositionError_tendsto_zero_ownerSelectedVerticalDecompositionSpine
      f F hSchedule ExplicitFormulaScheduledVerticalChannelProjection.correction

/-- Prime contour-to-boundary transport remainder estimate.

This is the non-circular owner theorem for the prime vertical channel: the
analytic estimates on the scheduled vertical contour identify the residual
contour-to-prime-boundary transport term and show that it vanishes. -/
theorem explicitFormulaScheduledPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeContourEstimate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeVerticalDecomposition
      f F hSchedule
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u ExplicitFormulaScheduledVerticalChannelProjection.prime) := by
    funext u
    exact
      (explicitFormulaScheduledProjectedVerticalDecompositionError_eq_transportRemainder
        f F.toContourFamily h u ExplicitFormulaScheduledVerticalChannelProjection.prime).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hvertical

/-- Archimedean contour-to-boundary transport remainder estimate.

This is the non-circular owner sink for the Gamma/completion vertical channel:
after projecting the rectangle residue equality to the archimedean channel and
using the contour-integral-to-boundary convergence path, the scheduled residual
transport term vanishes. -/
theorem explicitFormulaScheduledArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanContourEstimate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanVerticalDecomposition
      f F hSchedule
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean) := by
    funext u
    exact
      (explicitFormulaScheduledProjectedVerticalDecompositionError_eq_transportRemainder
        f F.toContourFamily h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hvertical

/-- Pole-correction contour-to-boundary transport remainder estimate.

This is the non-circular owner sink for the pole-face correction channel: after
projecting the rectangle residue equality to the correction channel and using
the contour-integral-to-boundary convergence path, the scheduled residual
transport term vanishes. -/
theorem explicitFormulaScheduledCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerCorrectionContourEstimate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u ExplicitFormulaScheduledVerticalChannelProjection.correction)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerCorrectionVerticalDecomposition
      f F hSchedule
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u ExplicitFormulaScheduledVerticalChannelProjection.correction) := by
    funext u
    exact
      (explicitFormulaScheduledProjectedVerticalDecompositionError_eq_transportRemainder
        f F.toContourFamily h u ExplicitFormulaScheduledVerticalChannelProjection.correction).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hvertical

/-- Shared scheduled vertical-channel contour estimate.

This is the common analytic sink for the three concrete channels.  Its proof is
the contour-integral-to-boundary-sum convergence path, projected to the selected
channel: finite rectangle residue equality, horizontal decay, vertical
decomposition, and channel projection. -/
theorem explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_tendsto_zero_ownerContourEstimate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
          f F.toContourFamily (h.height_schedule.height u) channel)
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  match channel with
  | ExplicitFormulaScheduledVerticalChannelProjection.prime =>
      exact
        explicitFormulaScheduledPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeContourEstimate
          f F hSchedule
  | ExplicitFormulaScheduledVerticalChannelProjection.archimedean =>
      exact
        explicitFormulaScheduledArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanContourEstimate
          f F hSchedule
  | ExplicitFormulaScheduledVerticalChannelProjection.correction =>
      exact
        explicitFormulaScheduledCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerCorrectionContourEstimate
          f F hSchedule

/-- Projected vertical decomposition for a selected vertical channel.

This is the lower owner theorem consumed by the contour-spine assembly: after the selected
vertical channel has been transported to its boundary contribution, the corresponding
projected vertical-decomposition error vanishes. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_tendsto_zero_ownerProjectedVerticalDecomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F.toContourFamily h u channel)
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaScheduledProjectedVerticalDecompositionError_tendsto_zero_ownerSelectedVerticalDecompositionSpine
      f F hSchedule channel

/-- Prime vertical convergence spine.

This is the exact owner-level consequence of the prime contour estimate: the
scheduled prime logarithmic-derivative vertical contour integral realizes the
completed real-side prime-power distribution. -/
theorem explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_primeContribution_ownerPrimeVerticalConvergenceSpine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hrem :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeContourEstimate
      f F hSchedule
  have hconst :
      Tendsto
        (fun _u : ℝ => zetaCompletedExplicitFormulaPrimeContribution f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeContribution f +
            zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f + 0)) :=
    hconst.add hrem
  have htarget :
      zetaCompletedExplicitFormulaPrimeContribution f + 0 =
        zetaCompletedExplicitFormulaPrimeContribution f :=
    add_zero _
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeContribution f +
            zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u)) := by
    funext u
    exact
      zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_contribution_add_transportRemainder
        f F.toContourFamily (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeContribution f +
              zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
                f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Prime scheduled vertical contour realization limit.

This is the channel-specific vertical transport theorem: the scheduled prime
contour integral realizes the completed prime boundary distribution. -/
theorem explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_primeContribution_ownerPrimeVerticalLimit
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_primeContribution_ownerPrimeVerticalConvergenceSpine
      f F hSchedule

/-- Archimedean vertical convergence spine.

This is the exact algebraic consequence of the archimedean contour estimate:
the scheduled Gamma/completion logarithmic-derivative vertical contour integral
realizes the completed archimedean boundary contribution. -/
theorem explicitFormulaScheduledArchimedeanVerticalContourRealization_tendsto_archimedeanContribution_ownerArchimedeanVerticalConvergenceSpine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hrem :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanContourEstimate
      f F hSchedule
  have hconst :
      Tendsto
        (fun _u : ℝ => zetaCompletedExplicitFormulaArchimedeanContribution f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f + 0)) :=
    hconst.add hrem
  have htarget :
      zetaCompletedExplicitFormulaArchimedeanContribution f + 0 =
        zetaCompletedExplicitFormulaArchimedeanContribution f :=
    add_zero _
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u)) := by
    funext u
    exact
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel_eq_contribution_add_transportRemainder
        f F.toContourFamily (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanContribution f +
              zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
                f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Archimedean scheduled vertical contour realization limit.

This is the Gamma/completion channel transport theorem: the scheduled archimedean
contour integral realizes the completed archimedean boundary contribution. -/
theorem explicitFormulaScheduledArchimedeanVerticalContourRealization_tendsto_archimedeanContribution_ownerArchimedeanVerticalLimit
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    explicitFormulaScheduledArchimedeanVerticalContourRealization_tendsto_archimedeanContribution_ownerArchimedeanVerticalConvergenceSpine
      f F hSchedule

/-- Pole-correction vertical convergence spine.

This is the exact algebraic consequence of the correction contour estimate:
the scheduled pole-face logarithmic-derivative vertical contour integral
realizes the completed correction boundary contribution. -/
theorem explicitFormulaScheduledCorrectionVerticalContourRealization_tendsto_correctionContribution_ownerCorrectionVerticalConvergenceSpine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hrem :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerCorrectionContourEstimate
      f F hSchedule
  have hconst :
      Tendsto
        (fun _u : ℝ => zetaCompletedExplicitFormulaCorrectionContribution f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionContribution f +
            zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f + 0)) :=
    hconst.add hrem
  have htarget :
      zetaCompletedExplicitFormulaCorrectionContribution f + 0 =
        zetaCompletedExplicitFormulaCorrectionContribution f :=
    add_zero _
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionContribution f +
            zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u)) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_contribution_add_transportRemainder
        f F.toContourFamily (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionContribution f +
              zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
                f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Pole-correction scheduled vertical contour realization limit.

This is the pole-face channel transport theorem: the scheduled correction contour
integral realizes the completed correction boundary contribution. -/
theorem explicitFormulaScheduledCorrectionVerticalContourRealization_tendsto_correctionContribution_ownerCorrectionVerticalLimit
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) := by
  exact
    explicitFormulaScheduledCorrectionVerticalContourRealization_tendsto_correctionContribution_ownerCorrectionVerticalConvergenceSpine
      f F hSchedule

/-- The scheduled prime vertical-channel transport remainder tends to zero. -/
theorem explicitFormulaScheduledPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeVerticalTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaScheduledPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeContourEstimate
      f F hSchedule

/-- The scheduled archimedean vertical-channel transport remainder tends to zero. -/
theorem explicitFormulaScheduledArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanVerticalTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaScheduledArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanContourEstimate
      f F hSchedule

/-- The scheduled pole-correction vertical-channel transport remainder tends to zero. -/
theorem explicitFormulaScheduledCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerCorrectionVerticalTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaScheduledCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerCorrectionContourEstimate
      f F hSchedule

/-! ## Scheduled channel transport consumers -/

/-- Prime scheduled vertical contour transport to the completed prime channel.

This consumer is downstream of the acyclic finite rectangle residue owner theorem. -/
theorem explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_primeContribution_ownerPrimeVerticalTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hrem :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeVerticalTransport
      f F hSchedule
  have hconst :
      Tendsto
        (fun _u : ℝ => zetaCompletedExplicitFormulaPrimeContribution f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeContribution f +
            zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f + 0)) :=
    hconst.add hrem
  have htarget :
      zetaCompletedExplicitFormulaPrimeContribution f + 0 =
        zetaCompletedExplicitFormulaPrimeContribution f :=
    add_zero _
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeContribution f +
            zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u)) := by
    funext u
    exact
      zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_contribution_add_transportRemainder
        f F.toContourFamily (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaPrimeContribution f +
              zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
                f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- The scheduled prime vertical contour realization transports to the completed prime
GNS/defect-kernel channel. -/
theorem explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_primeGNSDefectKernelChannel_ownerPrimeTransportComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_primeContribution_ownerPrimeVerticalTransport
      f F hSchedule

/-- The scheduled prime vertical contour realization transports to the completed prime
boundary channel. -/
theorem explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_completedPrimeChannel_ownerPrimeTransportComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_primeGNSDefectKernelChannel_ownerPrimeTransportComparison
      f F hSchedule

/-- Prime vertical-channel comparison with the prime boundary contribution, owned by the
prime transport/distribution layer. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_ownerPrimeTransportComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_completedPrimeChannel_ownerPrimeTransportComparison
      f F hSchedule

/-- Prime vertical-channel convergence, owned by the prime channel normalization/transport. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_ownerPrimeVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_ownerPrimeTransportComparison
      f F hSchedule

/-- Archimedean scheduled vertical contour transport to the completed archimedean channel. -/
theorem explicitFormulaScheduledArchimedeanVerticalContourRealization_tendsto_archimedeanContribution_ownerArchimedeanVerticalTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hrem :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanVerticalTransport
      f F hSchedule
  have hconst :
      Tendsto
        (fun _u : ℝ => zetaCompletedExplicitFormulaArchimedeanContribution f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f + 0)) :=
    hconst.add hrem
  have htarget :
      zetaCompletedExplicitFormulaArchimedeanContribution f + 0 =
        zetaCompletedExplicitFormulaArchimedeanContribution f :=
    add_zero _
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u)) := by
    funext u
    exact
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel_eq_contribution_add_transportRemainder
        f F.toContourFamily (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanContribution f +
              zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
                f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- The scheduled archimedean vertical contour realization transports to the completed
archimedean boundary channel. -/
theorem explicitFormulaScheduledArchimedeanVerticalContourRealization_tendsto_completedArchimedeanChannel_ownerArchimedeanNormalizationComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    explicitFormulaScheduledArchimedeanVerticalContourRealization_tendsto_archimedeanContribution_ownerArchimedeanVerticalTransport
      f F hSchedule

/-- Archimedean vertical-channel comparison with the archimedean boundary contribution,
owned by the completed normalization layer. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerArchimedeanNormalizationComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    explicitFormulaScheduledArchimedeanVerticalContourRealization_tendsto_completedArchimedeanChannel_ownerArchimedeanNormalizationComparison
      f F hSchedule

/-- Archimedean vertical-channel convergence, owned by the archimedean normalization. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerArchimedeanVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerArchimedeanNormalizationComparison
      f F hSchedule

/-- Correction scheduled vertical contour transport to the completed correction channel. -/
theorem explicitFormulaScheduledCorrectionVerticalContourRealization_tendsto_correctionContribution_ownerCorrectionVerticalTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hrem :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerCorrectionVerticalTransport
      f F hSchedule
  have hconst :
      Tendsto
        (fun _u : ℝ => zetaCompletedExplicitFormulaCorrectionContribution f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionContribution f +
            zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f + 0)) :=
    hconst.add hrem
  have htarget :
      zetaCompletedExplicitFormulaCorrectionContribution f + 0 =
        zetaCompletedExplicitFormulaCorrectionContribution f :=
    add_zero _
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionContribution f +
            zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
              f F.toContourFamily (h.height_schedule.height u)) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_contribution_add_transportRemainder
        f F.toContourFamily (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionContribution f +
              zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
                f F.toContourFamily (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- The scheduled pole-correction vertical contour realization transports to the completed
correction boundary channel. -/
theorem explicitFormulaScheduledCorrectionVerticalContourRealization_tendsto_completedCorrectionChannel_ownerPoleCorrectionComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) := by
  exact
    explicitFormulaScheduledCorrectionVerticalContourRealization_tendsto_correctionContribution_ownerCorrectionVerticalTransport
      f F hSchedule

/-- Correction vertical-channel comparison with the correction boundary contribution, owned
by the pole-correction normalization layer. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerPoleCorrectionComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) := by
  exact
    explicitFormulaScheduledCorrectionVerticalContourRealization_tendsto_completedCorrectionChannel_ownerPoleCorrectionComparison
      f F hSchedule

/-- Correction vertical-channel convergence, owned by the pole-correction normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerCorrectionVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerPoleCorrectionComparison
      f F hSchedule

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
