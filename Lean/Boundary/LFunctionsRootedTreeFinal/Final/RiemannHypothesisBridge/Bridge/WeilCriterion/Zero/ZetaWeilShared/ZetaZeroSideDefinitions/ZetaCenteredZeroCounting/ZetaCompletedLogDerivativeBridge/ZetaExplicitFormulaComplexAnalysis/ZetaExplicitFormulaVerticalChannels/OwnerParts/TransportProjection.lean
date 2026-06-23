import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.BasicChannels

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

/-- The standard-contour correction boundary value obtained from the separated
`s = 0` and `s = 1` pole-face transports.  This is intentionally distinct from
the older centered contribution normalization until the contour-side basepoint
transport theorem identifies them. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionStandardContourContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) -
    (((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)

/-- The standard-contour correction boundary value unfolds to the separated
right-minus-left pole-face residue expression. -/
theorem zetaCompletedExplicitFormulaCorrectionStandardContourContribution_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionStandardContourContribution f =
      ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) -
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) :=
  rfl

/-- Pole-correction vertical-channel transport remainder, normalized by the
standard-contour correction boundary value. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T -
    zetaCompletedExplicitFormulaCorrectionStandardContourContribution f

/-- The pole-correction vertical channel is its standard-contour boundary value
plus its transport remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_contribution_add_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T =
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f +
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder f F T := by
  let V : ℂ := zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T
  let C : ℂ := zetaCompletedExplicitFormulaCorrectionStandardContourContribution f
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
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f

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
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (u : ℝ)
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.toContourFamily.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u)) :
    explicitFormulaScheduledRectangleContourIntegral f F.toContourFamily h u =
      explicitFormulaScheduledRectangleResidueSum f F.toContourFamily h u := by
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
  let r : ExplicitFormulaRectangle := F.rectangle (h.height_schedule.height u)
  calc
    explicitFormulaScheduledRectangleContourIntegral f F h u =
        zetaCompletedExplicitFormulaRightLineIntegral f r -
          zetaCompletedExplicitFormulaLeftLineIntegral f r +
          zetaCompletedExplicitFormulaTopLineIntegral f r -
          zetaCompletedExplicitFormulaBottomLineIntegral f r := by
      exact zetaCompletedExplicitFormulaContourIntegral_eq f r
    _ =
        (zetaCompletedExplicitFormulaRightLineIntegral f r -
          zetaCompletedExplicitFormulaLeftLineIntegral f r) +
          (zetaCompletedExplicitFormulaTopLineIntegral f r -
            zetaCompletedExplicitFormulaBottomLineIntegral f r) := by
      let R : ℂ := zetaCompletedExplicitFormulaRightLineIntegral f r
      let L : ℂ := zetaCompletedExplicitFormulaLeftLineIntegral f r
      let T : ℂ := zetaCompletedExplicitFormulaTopLineIntegral f r
      let B : ℂ := zetaCompletedExplicitFormulaBottomLineIntegral f r
      calc
        R - L + T - B = (R - L + T) + -B := by
          exact sub_eq_add_neg (R - L + T) B
        _ = (R - L) + T + -B := rfl
        _ = (R - L) + (T + -B) := by
          exact add_assoc (R - L) T (-B)
        _ = (R - L) + (T - B) := by
          exact congrArg (fun x : ℂ => (R - L) + x)
            (sub_eq_add_neg T B).symm
    _ =
        explicitFormulaScheduledCompletedVerticalSideDifference f F h u +
          explicitFormulaScheduledHorizontalSideDifference f F h u := rfl

/-- The horizontal-side decay target along the selected schedule.

This is the horizontal estimate in the contour-integral-to-boundary path; it is
recorded as a named step consumed by the selected-channel convergence primitive. -/
def explicitFormulaScheduledHorizontalSideDifferenceTendstoZero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) : Prop :=
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

/-- The selected scheduled archimedean channel is its selected boundary
contribution plus the concrete archimedean transport remainder. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_archimedean_eq_boundary_add_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaSelectedScheduledVerticalChannel
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
      explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.archimedean +
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u) := by
  calc
    explicitFormulaSelectedScheduledVerticalChannel
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel
        f F (h.height_schedule.height u) := by
      exact explicitFormulaSelectedScheduledVerticalChannel_archimedean_eq f F h u
    _ =
      zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u) := by
      exact
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel_eq_contribution_add_transportRemainder
          f F (h.height_schedule.height u)
    _ =
      explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.archimedean +
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u) := by
      exact
        congrArg
          (fun z : ℂ =>
            z +
              zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
                f F (h.height_schedule.height u))
          (explicitFormulaSelectedVerticalBoundaryChannel_archimedean_eq f).symm

/-- The selected correction boundary channel is the standard-contour correction
boundary value. -/
theorem explicitFormulaSelectedVerticalBoundaryChannel_correction_eq
    (f : ZetaAdmissibleFunction) :
    explicitFormulaSelectedVerticalBoundaryChannel
        f ExplicitFormulaScheduledVerticalChannelProjection.correction =
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
  rfl

/-! ## Vertical-channel algebraic transport roots -/

/-- Shared algebraic passage from a scheduled component transport remainder to the
corresponding boundary-channel convergence.

This lemma is deliberately conditional: the analytic convergence of the transport
remainder belongs to the contour assembly layer, after finite-rectangle residue
equality and horizontal decay have both been supplied. -/
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

/-! ## Channel-specific transport owner surfaces -/

/-- A selected channel transport remainder vanishes once the scheduled selected channel
has been analytically identified with its limiting boundary contribution. -/
theorem explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_tendsto_zero_of_selectedChannel_tendsto_boundary
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
        explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
          f F (h.height_schedule.height u) channel)
      atTop
      (𝓝 0) := by
  have herror :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F h u channel)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledProjectedVerticalDecompositionError_tendsto_zero_of_selectedChannel_tendsto_boundary
      f F h channel hchannel
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
          f F (h.height_schedule.height u) channel) =
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F h u channel) := by
    funext u
    exact
      (explicitFormulaScheduledProjectedVerticalDecompositionError_eq_transportRemainder
        f F h u channel).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    herror

/-- Owner analytic leaf: the prime logarithmic-derivative vertical-channel transport
remainder vanishes along the scheduled contour heights. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeLogDerivativeTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  sorry

/-- Selected prime-channel analytic transport: the scheduled selected prime channel
converges to its selected boundary contribution. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_prime_tendsto_boundary_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
      atTop
      (𝓝
        (explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.prime)) := by
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (explicitFormulaSelectedVerticalBoundaryChannel
        f ExplicitFormulaScheduledVerticalChannelProjection.prime)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
      (fun u : ℝ =>
        calc
          explicitFormulaSelectedScheduledVerticalChannel
              f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime =
            zetaCompletedExplicitFormulaPrimeVerticalChannel
              f F (h.height_schedule.height u) := by
              exact explicitFormulaSelectedScheduledVerticalChannel_prime_eq f F h u
          _ =
            zetaCompletedExplicitFormulaPrimeContribution f +
              zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
                f F (h.height_schedule.height u) := by
              exact
                zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_contribution_add_transportRemainder
                  f F (h.height_schedule.height u)
          _ =
            explicitFormulaSelectedVerticalBoundaryChannel
                f ExplicitFormulaScheduledVerticalChannelProjection.prime +
              zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
                f F (h.height_schedule.height u) := by
              exact
                congrArg
                  (fun z : ℂ =>
                    z +
                      zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
                        f F (h.height_schedule.height u))
                  (explicitFormulaSelectedVerticalBoundaryChannel_prime_eq f).symm)
      (zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeLogDerivativeTransport
        f F h)

/-- Concrete prime-channel analytic transport: the scheduled prime logarithmic-derivative
vertical integral converges to the completed prime contribution. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_concrete_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  have hselected :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
        atTop
        (𝓝
          (explicitFormulaSelectedVerticalBoundaryChannel
            f ExplicitFormulaScheduledVerticalChannelProjection.prime)) :=
    explicitFormulaSelectedScheduledVerticalChannel_prime_tendsto_boundary_ownerChannelTransportAnalytic
      f F h
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel f F
            (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaSelectedScheduledVerticalChannel_prime_eq f F h u
  have htarget :
      explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.prime =
        zetaCompletedExplicitFormulaPrimeContribution f :=
    explicitFormulaSelectedVerticalBoundaryChannel_prime_eq f
  have hselectedConcreteTarget :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaSelectedScheduledVerticalChannel
              f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
          atTop
          (𝓝 z))
      htarget
      hselected
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)))
    hpointwise
    hselectedConcreteTarget

/-- Prime-channel analytic transport: the scheduled prime vertical integral converges to
the completed prime boundary contribution. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
      atTop
      (𝓝
        (explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.prime)) := by
  exact
    explicitFormulaSelectedScheduledVerticalChannel_prime_tendsto_boundary_ownerChannelTransportAnalytic
      f F h

/-- Owner analytic leaf: the archimedean Gamma/completion vertical-channel
transport remainder vanishes along the scheduled contour heights. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  sorry

/-- Selected archimedean-channel analytic transport: the scheduled selected
archimedean channel converges to its selected boundary contribution. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_archimedean_tendsto_boundary_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
      atTop
      (𝓝
        (explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.archimedean)) := by
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (explicitFormulaSelectedVerticalBoundaryChannel
        f ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel_archimedean_eq_boundary_add_transportRemainder
          f F h u)
      (zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanTransport
        f F h)

/-- Concrete archimedean-channel analytic transport: the scheduled Gamma/completion
vertical integral converges to the completed archimedean contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_concrete_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  have hselected :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
        atTop
        (𝓝
          (explicitFormulaSelectedVerticalBoundaryChannel
            f ExplicitFormulaScheduledVerticalChannelProjection.archimedean)) :=
    explicitFormulaSelectedScheduledVerticalChannel_archimedean_tendsto_boundary_ownerChannelTransportAnalytic
      f F h
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F
            (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaSelectedScheduledVerticalChannel_archimedean_eq f F h u
  have htarget :
      explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
        zetaCompletedExplicitFormulaArchimedeanContribution f :=
    explicitFormulaSelectedVerticalBoundaryChannel_archimedean_eq f
  have hselectedConcreteTarget :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaSelectedScheduledVerticalChannel
              f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
          atTop
          (𝓝 z))
      htarget
      hselected
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)))
    hpointwise
    hselectedConcreteTarget

/-- Archimedean-channel analytic transport: the scheduled Gamma/completion vertical
integral converges to the completed archimedean boundary contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
      atTop
      (𝓝
        (explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.archimedean)) := by
  exact
    explicitFormulaSelectedScheduledVerticalChannel_archimedean_tendsto_boundary_ownerChannelTransportAnalytic
      f F h

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
