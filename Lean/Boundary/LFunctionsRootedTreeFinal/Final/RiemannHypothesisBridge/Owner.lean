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

The actual nonlinear autocorrelation-cone Runge theorem is owned in the
zero-tail localization layer; this final bridge only exposes the theorem to
the RH assembly. -/
theorem finalRiemannHypothesis_zeroTailSmallValuesOwnerRunge :
    ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈
            ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberZeroTailRealAbsValues
              S P f₀ ∧
            r < ε := by
  exact
    ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberZeroTailSmallValuesRunge_owner

/-- Corrected Binet endpoint-restored finite-height input currently owned by
the Gamma-Stirling layer.

The full branch-uniform tail absorption theorem still requires the paired
endpoint-return wall-cancellation estimate in the Binet owner file. -/
theorem finalRiemannHypothesis_binetEndpointRestoredFiniteHeightContourInputs :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs := by
  exact Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_owner

/-- Right-critical-strip admissible growth conditional on the genuine Binet
branch-uniform tail absorption theorem.

The pole-cleared growth layer remains non-circular: it consumes the actual
branch-tail theorem as an input instead of using the endpoint-restored
finite-height package as a substitute. -/
theorem finalRiemannHypothesis_poleClearedRightCriticalStripAdmissibleGrowth
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    PoleClearedRightCriticalStripAdmissibleGrowth := by
  exact poleClearedRightCriticalStripAdmissibleGrowth_owner hbranch hreflected

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

/-- Final centered-zero criterion wrapper for RH, conditional on the genuine
branch-uniform Binet tail absorption theorem and the pole-cleared
self-reflected zero-one strip envelope.

This bridge assembles all already-owned Runge and boundary-growth packages, but
it does not pretend that the endpoint-restored finite-height contour input is
the full branch-tail theorem. -/
theorem finalRiemannHypothesis_centeredZeroCriterion_from_debtAwareOrderedHeartTransport
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
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
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      (finalRiemannHypothesis_poleClearedRightCriticalStripAdmissibleGrowth
        hbranch hreflected)
      hpartialLeft
      hcompactBoundary
      zetaCriterion_autocorrelation_orderedHeartZeroSidePositivity

/-- Boundary proof of mathlib's `RiemannHypothesis`, conditional on the
remaining genuine Binet branch-tail theorem and pole-cleared self-reflected
zero-one strip envelope.

The missing analytic content belongs upstream in the Binet wall-cancellation
owner and in the pole-cleared reflected-envelope owner.  Once those two inputs
are proved, this wrapper can again be made zero-argument without changing the
downstream RH proof. -/
theorem boundaryRiemannHypothesis_of_binetBranchUniformTailAbsorption
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    boundaryRiemannHypothesis := by
  exact
    boundaryRiemannHypothesis_of_centeredZeroCriterion
      (finalRiemannHypothesis_centeredZeroCriterion_from_debtAwareOrderedHeartTransport
        hbranch hreflected)

end
end LFunctions
end Boundary
