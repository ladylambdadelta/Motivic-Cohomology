import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.Part03_QuantitativeTailEstimate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.TailSummability.Owner

/-!
# Concrete cardinal envelopes

This file obtains a polynomial completed-zero envelope after a particular finite
tomographic cardinal interpolant has been chosen.  The constants are intentionally
attached to that interpolant; no uniformity over a finite spectral fiber is claimed.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The concrete finite-cardinal interpolant together with its own completed-zero
polynomial envelope.  The constants belong to this particular finite fiber. -/
structure AutocorrelationSpectralEvalFiberCardinalEnvelopeData
    (S : Finset ℂ) (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction)
    (R : ℝ)
    (F :
      autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        ZetaAdmissibleFunction) where
  cardinal :
    ∀ z w : autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R,
      Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
        if w = z then 1 else 0
  envelopeConstant : ℝ
  envelopeOrder : ℕ
  envelopeConstant_nonnegative : 0 ≤ envelopeConstant
  envelopeSummable :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        envelopeConstant * zetaCompletedZeroCenteredHeight ρ ^
          (-(envelopeOrder + 3 : ℤ)))
  envelope :
    ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
      ‖zetaZeroSideContribution (ρ : ℂ)
          (convolutionAutocorrelation
            (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
              S P f₀ R F))‖ ≤
        envelopeConstant * zetaCompletedZeroCenteredHeight ρ ^
          (-(envelopeOrder + 3 : ℤ))

/-- Every fixed finite tomographic cardinal interpolant has a summable completed-zero
polynomial envelope, under the completed-zeta growth and transform-decay hypotheses. -/
theorem exists_autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_envelope
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (R : ℝ)
    (F :
      autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        ZetaAdmissibleFunction) :
    ∃ A : ℝ, ∃ k : ℕ,
      0 ≤ A ∧
        Summable
          (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
            A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) ∧
          ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
            ‖zetaZeroSideContribution (ρ : ℂ)
                (convolutionAutocorrelation
                  (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
                    S P f₀ R F))‖ ≤
              A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)) := by
  let f : ZetaAdmissibleFunction :=
    autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant S P f₀ R F
  match
      exists_zetaZeroMultiplicityTransformEnvelope_bound
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
        (convolutionAutocorrelation f) with
  | ⟨A, k, hApos, hsum, hmajorant⟩ =>
      exact
        ⟨A, k, le_of_lt hApos, hsum,
          fun ρ =>
            calc
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation
                    (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
                      S P f₀ R F))‖ =
                  ‖zetaZeroSideContribution (ρ : ℂ)
                    (convolutionAutocorrelation f)‖ :=
                    congrArg
                      (fun g : ZetaAdmissibleFunction =>
                        ‖zetaZeroSideContribution (ρ : ℂ)
                          (convolutionAutocorrelation g)‖)
                      (show
                        autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
                            S P f₀ R F = f from
                        Eq.symm (show f =
                          autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
                            S P f₀ R F from Eq.refl _))
              _ ≤ zetaZeroSideContributionMajorant
                    (convolutionAutocorrelation f) ρ :=
                    norm_zetaZeroSideContribution_le_majorant
                      (convolutionAutocorrelation f) ρ
              _ = zetaZeroMultiplicityTransformMajorant
                    (convolutionAutocorrelation f) ρ :=
                    zetaZeroSideContributionMajorant_eq_multiplicityTransformMajorant
                      (convolutionAutocorrelation f) ρ
              _ ≤ A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)) :=
                    hmajorant ρ⟩

/-- A fixed cardinal family has concrete envelope data.  This packages the exact
dependence of the constants on the chosen finite fiber for the diagonal step. -/
theorem exists_autocorrelationSpectralEvalFiberCardinalEnvelopeData_of_cardinal
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (R : ℝ)
    (F :
      autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        ZetaAdmissibleFunction)
    (hF :
      ∀ z w : autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0) :
    ∃ data : AutocorrelationSpectralEvalFiberCardinalEnvelopeData S P f₀ R F := by
  obtain ⟨A, k, hA, hsum, henvelope⟩ :=
    exists_autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_envelope
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀ R F
  exact ⟨⟨hF, A, k, hA, hsum, henvelope⟩⟩

/-- At each fixed finite tomography radius, Paley-Wiener interpolation and the
completed-zero growth estimate construct concrete cardinal-envelope data. -/
theorem exists_autocorrelationSpectralEvalFiberCardinalEnvelopeData_at_radius
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (R : ℝ) :
    ∃ F : autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        ZetaAdmissibleFunction,
      ∃ data : AutocorrelationSpectralEvalFiberCardinalEnvelopeData S P f₀ R F := by
  obtain ⟨F, hF⟩ :=
    exists_autocorrelationSpectralEvalFiberFiniteTomographyCardinalFamily S P R
  obtain ⟨data⟩ :=
    exists_autocorrelationSpectralEvalFiberCardinalEnvelopeData_of_cardinal
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀ R F hF
  exact ⟨F, data⟩

/-- The deterministic tomography tail theorem consumes concrete cardinal-envelope data
directly. -/
theorem autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_tail_lt_of_envelopeData
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (R : ℝ)
    (F :
      autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        ZetaAdmissibleFunction)
    (data : AutocorrelationSpectralEvalFiberCardinalEnvelopeData S P f₀ R F)
    (ε : ℝ)
    (htail :
      (∑' ρ : {ρ : ℂ //
        ZetaCompletedZero ρ ∧
          ρ ∉ S ∧
          ρ ∉ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R},
        data.envelopeConstant * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(data.envelopeOrder + 3 : ℤ))) < ε) :
    autocorrelationZeroTailRealAbs S
      (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
        S P f₀ R F) < ε := by
  exact
    autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_tail_lt
      S P f₀ ε R F data.cardinal data.envelopeConstant data.envelopeOrder
      data.envelopeConstant_nonnegative data.envelopeSummable
      (fun ρ => data.envelope ⟨(ρ : ℂ), ρ.2.1⟩)
      htail

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
