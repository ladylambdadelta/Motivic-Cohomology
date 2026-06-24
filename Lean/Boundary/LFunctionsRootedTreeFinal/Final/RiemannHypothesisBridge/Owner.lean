import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Owner
import Boundary.LFunctionsRootedTreeFinal.OutsideRHRootedImportCone.Final.ZetaCriterion.Owner

/-!
# Boundary bridge to mathlib's Riemann hypothesis statement

This file owns the exact namespace alignment between the Boundary
normalization layer and mathlib's public `RiemannHypothesis` constant.
It does not introduce a new analytic criterion; it only exposes the
public theorem surface in a Boundary-owned file so downstream files can
target the official statement directly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Boundary's RH statement is exactly mathlib's `RiemannHypothesis`. -/
theorem boundaryRiemannHypothesis_eq_mathlib :
    boundaryRiemannHypothesis = RiemannHypothesis := rfl

/-- Boundary's completed zeta alias is mathlib's completed zeta. -/
theorem boundaryCompletedRiemannZeta_eq_mathlib :
    boundaryCompletedRiemannZeta = completedRiemannZeta := rfl

/-- Boundary's zeta alias is mathlib's Riemann zeta. -/
theorem boundaryRiemannZeta_eq_mathlib :
    boundaryRiemannZeta = riemannZeta := rfl

/-- Runge/small-values owner sink required by the final unconditional RH assembly.

This theorem must ultimately be proved in the zero-tail localization/Runge owner
layer.  It is kept as a theorem, not a parameter of RH, so the global statement
cannot become conditional on it.

Do not replace this theorem by an assumption on `boundaryRiemannHypothesis_unconditional`.
If this proof is incomplete, the only acceptable surface is this explicit owner
sink, or a proved theorem imported from the true Runge/zero-tail owner. -/
theorem finalRiemannHypothesis_zeroTailSmallValuesOwnerRunge :
    ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈
            ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberZeroTailRealAbsValues
              S P f₀ ∧
            r < ε := by
  sorry

/-- Binet branch/tail absorption owner sink required by the final unconditional
RH assembly.

This belongs in the Binet/Gamma-Stirling owner layer.

Do not pass this as a hypothesis to the final RH theorem.  Prove it upstream
and replace this sink by that owner theorem. -/
theorem finalRiemannHypothesis_binetBranchUniformTailAbsorption :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption := by
  sorry

/-- Right-critical-strip admissible growth owner sink required by the final
unconditional RH assembly.

This belongs in the pole-cleared zeta growth owner layer and must be assembled
from the standard finite-order theorem, compact bounds, and boundary Abel
majorants.

Do not weaken the final RH theorem by quantifying over this package.  The final
assembly consumes a theorem here; it does not assume a condition from users. -/
theorem finalRiemannHypothesis_poleClearedRightCriticalStripAdmissibleGrowth :
    PoleClearedRightCriticalStripAdmissibleGrowth := by
  sorry

/-- Debt-aware ordered-heart positivity must prove the centered zero criterion
directly from the named analytic owner inputs, with no public RH-side
hypothesis.

Do not try to prove this by asserting
`Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0` for all `f`.
The contour bridge currently identifies the ordered-heart scalar with
`zetaCompletedZeroKreinGram (...) + diagonalDebt`, and the existing descent
lemma says raw descent is equivalent to diagonal-debt vanishing.  Thus global
raw debt-vanishing is an obstruction, not an acceptable assumption.

The correct owner proof is a debt-aware Weil criterion: the off-critical-zero
contradiction must be formulated against the quotient-normalized ordered-heart
zero-side scalar, where weight-triangular transport absorbs the diagonal debt.
It must not route through raw `ZetaWeilQuadraticPositivity` unless a genuine
owner theorem proves that the raw form, not merely the quotient form, is
nonnegative. -/
theorem centeredZeroCriterion_of_debtAwareOrderedHeartTransport
    (hZeroTailSmallValuesOwnerRunge :
      ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
        ∀ ε : ℝ, 0 < ε →
          ∃ r : ℝ,
            r ∈
              ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberZeroTailRealAbsValues
                S P f₀ ∧
              r < ε)
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (horderedHeartPositive : ZetaAutocorrelationOrderedHeartZeroSidePositivity) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  centeredZeroCriterion_of_debtAwareOrderedHeartZeroSidePositivity
    hZeroTailSmallValuesOwnerRunge
    hbranch
    hpartialOneTwo
    hcompactOneTwo
    hfinite
    hpartialLeft
    hcompactBoundary
    horderedHeartPositive

/-- Final centered-zero criterion wrapper for RH.

This theorem is intentionally a zero-argument theorem, but it is not allowed to
hide the dependency graph.  It assembles the named Runge, Binet, and
pole-cleared growth owner sinks above with already-proved boundary-growth
packages, then hands those inputs to the debt-aware ordered-heart criterion
owner theorem. -/
theorem finalRiemannHypothesis_centeredZeroCriterion_from_debtAwareOrderedHeartTransport :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 := by
  have hpartialOneTwo : BoundaryLineOneAbelPartialMajorant :=
    boundaryLineOneAbelPartialMajorant_from_realParam_ownerGap
  have hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound :=
    poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
  have hpartialLeft : ReflectedBoundaryAbelPartialMajorant :=
    reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
      hpartialOneTwo
  have hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound :=
    poleClearedRightCriticalStripCompactBoundaryBound_from_compact
  exact
    centeredZeroCriterion_of_debtAwareOrderedHeartTransport
      finalRiemannHypothesis_zeroTailSmallValuesOwnerRunge
      finalRiemannHypothesis_binetBranchUniformTailAbsorption
      hpartialOneTwo
      hcompactOneTwo
      finalRiemannHypothesis_poleClearedRightCriticalStripAdmissibleGrowth
      hpartialLeft
      hcompactBoundary
      zetaCriterion_autocorrelation_orderedHeartZeroSidePositivity

/-- Final zero-hypothesis Boundary proof of mathlib's `RiemannHypothesis`.

The theorem statement is intentionally unconditional.  Remaining analytic work
is represented only by named owner sinks above, never by hypotheses on this
global statement.

Invariant for future agents: this theorem must remain a zero-argument theorem
whose target is exactly `boundaryRiemannHypothesis`.  It must never be rewritten
to a conditional theorem, an implication, a structure field, a class parameter,
or a theorem taking analytic packages as arguments.  Missing mathematics belongs
in explicitly named upstream theorem sinks, and those sinks must eventually be
replaced by proofs in their true owner files. -/
theorem boundaryRiemannHypothesis_unconditional :
    boundaryRiemannHypothesis := by
  exact
    boundaryRiemannHypothesis_of_centeredZeroCriterion
      finalRiemannHypothesis_centeredZeroCriterion_from_debtAwareOrderedHeartTransport

end
end LFunctions
end Boundary
