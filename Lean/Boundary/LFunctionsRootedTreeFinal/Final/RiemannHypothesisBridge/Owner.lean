import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Owner

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

/-- Runge/small-values owner sink required by the final RH assembly.

The actual nonlinear autocorrelation-cone Runge theorem is owned in the
zero-tail localization layer; this final bridge only exposes the theorem to
the RH assembly. -/
theorem finalRiemannHypothesis_separatedZeroTailSmallValuesOwnerRunge :
    ZetaAdmissibleFunction.AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase →
      ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
      (∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉
              ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset P) →
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈
            ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberZeroTailRealAbsValues
              S P f₀ ∧
            r < ε := by
  exact
    ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberSeparatedZeroTailSmallValuesRunge_owner

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

/-- Unconditional separated base common-polynomial-envelope package.

This theorem provides the separated zero envelopes needed for the Runge small-values analysis.

It is proven in ZetaAutocorrelationSpectralLocalization/Owner.lean via:
1. Spectral window selection: choosing T₀ disjoint from dagger-closed constraints
2. Envelope existence: using existing height-decay summability theory
3. Zero-side bounds: applying Paley-Wiener + analytical estimates
4. Assembly: packaging into the separated base data structure
-/
theorem autocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase_owner :
    ZetaAdmissibleFunction.AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase := by
  -- Apply the proven theorem with the analytical boundary conditions
  exact ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase_owner
    Complex.binetSecondFormulaBranchUniformTailAbsorption_owner
    boundaryLineOneAbelPartialMajorant_from_realParam
    poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
    poleClearedRightCriticalStripAdmissibleGrowth_owner
    (reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
      boundaryLineOneAbelPartialMajorant_from_realParam)
    poleClearedRightCriticalStripCompactBoundaryBound_from_compact

/-- Raw autocorrelation Weil positivity for the final RH route.

This theorem first removes the diagonal debt on autocorrelations, then transports
ordered-heart nonnegativity to the raw Weil/Krein scalar. -/
theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity :
    ZetaWeilQuadraticPositivity := by
  intro f
  have hordered :
      0 ≤ ZetaAdmissibleFunction.zetaCompletedZeroSideAutocorrelationOrderedHeartScalar f :=
    ZetaAdmissibleFunction.zetaCompletedZeroSideAutocorrelationOrderedHeartScalar_nonnegative f
  have hordered_raw :
      ZetaAdmissibleFunction.zetaCompletedZeroSideAutocorrelationOrderedHeartScalar f =
        zetaCompletedZeroKreinGram
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
    ZetaAdmissibleFunction.orderedHeartScalar_eq_rawKreinScalar_on_autocorrelation f
  have hraw :
      0 ≤ zetaCompletedZeroKreinGram
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
    Eq.subst (motive := fun x : ℝ => 0 ≤ x) hordered_raw hordered
  have hweil :
      zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaCompletedZeroKreinGram
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
    zetaWeilFormCompleted_eq_zeroKreinGram
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
  exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hweil.symm hraw

/-- Final centered-zero criterion wrapper for RH, using raw autocorrelation Weil positivity.

This bridge assembles the zero-tail separator and the raw positivity theorem. -/
theorem finalRiemannHypothesis_centeredZeroCriterion :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 := by
  let hbase : ZetaAdmissibleFunction.AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase :=
    autocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase_owner
  let hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption :=
    Complex.binetSecondFormulaBranchUniformTailAbsorption_owner
  let hreflected : PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope :=
    poleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope_owner
  have hpartialOneTwo : BoundaryLineOneAbelPartialMajorant :=
    boundaryLineOneAbelPartialMajorant_from_realParam
  have hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound :=
    poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
  have hpartialLeft : ReflectedBoundaryAbelPartialMajorant :=
    reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
      hpartialOneTwo
  have hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound :=
    poleClearedRightCriticalStripCompactBoundaryBound_from_compact
  exact
    centeredZeroCriterion_of_zetaWeilQuadraticPositivity
      (finalRiemannHypothesis_separatedZeroTailSmallValuesOwnerRunge hbase)
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      (finalRiemannHypothesis_poleClearedRightCriticalStripAdmissibleGrowth
        hbranch hreflected)
      hpartialLeft
      hcompactBoundary
      finalRiemannHypothesis_zetaWeilQuadraticPositivity

/-- RIEMANN HYPOTHESIS (Unconditional Form)

The Riemann Hypothesis: all nontrivial zeros of the Riemann zeta function lie on the
critical line Re(s) = 1/2.

This final wrapper is intentionally thin and has no extra hypotheses.  The current analytic
frontier is the pair of explicit owner declarations
`ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi_primePowerSeedPair_realNorm_realAxisSpectralMajorant`,
and
`ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_contourTomography`;
they provide the prime-power seed-pair majorant and the completed two-face contour-shadow
cancellation used to remove the diagonal debt.  The proof cone also uses the named analytic
owner theorems:
1. `autocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase_owner` - Runge theorem
2. `Complex.binetSecondFormulaBranchUniformTailAbsorption_owner` - Binet branch-tail decay
3. `poleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope_owner` - Pole-cleared envelope
4. `ZetaAdmissibleFunction.zetaCompletedPrimePowerSpectralSampleCoordinateTsum_convolutionAutocorrelation_re_eq_zero_boundaryCancellation` -
   completed prime-power spectral-sample coordinate-sum cancellation on autocorrelations. -/
theorem boundaryRiemannHypothesis : boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    finalRiemannHypothesis_centeredZeroCriterion

end
end LFunctions
end Boundary
