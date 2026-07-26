import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.Part01_FiniteGeometry
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.TailEstimates

/-!
# Quantitative cardinal tail estimate

This file owns the deterministic last step of finite tomography: an explicit envelope
for a concrete cardinal interpolant bounds its completed-zero tail.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- A common polynomial envelope for a concrete finite tomographic cardinal
interpolant bounds its completed-zero tail by the complementary envelope tail. -/
theorem autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_tail_norm_le
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
          if w = z then 1 else 0)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (hbound :
      ∀ ρ : {ρ : ℂ //
        ZetaCompletedZero ρ ∧
          ρ ∉ S ∧
          ρ ∉ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R},
        ‖zetaZeroSideContribution (ρ : ℂ)
            (convolutionAutocorrelation
              (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
                S P f₀ R F))‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
              (-(k + 3 : ℤ))) :
    ‖zetaZeroTail S
        (convolutionAutocorrelation
          (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
            S P f₀ R F))‖ ≤
      ∑' ρ : {ρ : ℂ //
        ZetaCompletedZero ρ ∧
          ρ ∉ S ∧
          ρ ∉ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(k + 3 : ℤ)) :=
  zetaZeroTail_norm_le_commonPolynomialEnvelope_complement_tsum
    S
    (autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R)
    A k hA hsum
    (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
      S P f₀ R F)
    (zetaZeroSideContribution_eq_zero_of_window_spectralEval_zero
      S
      (autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R)
      (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
        S P f₀ R F)
      (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_window_zero
        S P f₀ R F hF))
    hbound

/-- An explicit common envelope with complementary mass below `ε` gives a cardinal
interpolant whose real completed-zero tail is below `ε`. -/
theorem autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_tail_lt
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (R : ℝ)
    (F :
      autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        ZetaAdmissibleFunction)
    (hF :
      ∀ z w : autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (hbound :
      ∀ ρ : {ρ : ℂ //
        ZetaCompletedZero ρ ∧
          ρ ∉ S ∧
          ρ ∉ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R},
        ‖zetaZeroSideContribution (ρ : ℂ)
            (convolutionAutocorrelation
              (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
                S P f₀ R F))‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
              (-(k + 3 : ℤ)))
    (htail :
      (∑' ρ : {ρ : ℂ //
        ZetaCompletedZero ρ ∧
          ρ ∉ S ∧
          ρ ∉ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
            (-(k + 3 : ℤ))) < ε) :
    autocorrelationZeroTailRealAbs S
      (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
        S P f₀ R F) < ε :=
  autocorrelationZeroTailRealAbs_lt_of_zetaZeroTail_norm_lt
    S
    (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
      S P f₀ R F)
    ε
    (lt_of_le_of_lt
      (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_tail_norm_le
        S P f₀ R F hF A k hA hsum hbound)
      htail)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
