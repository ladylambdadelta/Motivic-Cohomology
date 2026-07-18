import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.NonDaggerComplement
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.PresentationParts.Part01_ValueDefinitions
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.CenteredCoordinates

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Common-polynomial-envelope finite-tail form of the Runge/tomography
theorem.

This is the analytic root of the finite-window tail-control theorem: after
forced dagger-constrained zero contributions are separated, the remaining
zero-side terms have a common summable polynomial height envelope, and a
finite completed-zero window cuts the complementary tail below any tolerance.
The finite interpolation step above then realizes that window inside the fixed
autocorrelation spectral fiber. -/
def AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeFiniteTailRunge : Prop :=
  ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
    ∀ ε : ℝ, 0 < ε →
      ∃ T₀ : Finset ℂ, ∃ T : Finset ℂ, ∃ A : ℝ, ∃ k : ℕ,
        T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        0 ≤ A ∧
        Summable
          (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
            A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) ∧
        (∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
            ∀ ρ : ℂ,
              ZetaCompletedZero ρ →
                ρ ∉ S →
                  ρ ∈ daggerClosedSpectralSampleFinset P →
                    zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0) ∧
        (∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
            (∀ ρ : ℂ, ρ ∈ T₀ →
              zetaSpectralEval (convolutionAutocorrelation f)
                ρ = 0) →
              ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
                ‖zetaZeroSideContribution (ρ : ℂ)
                    (convolutionAutocorrelation f)‖ ≤
                  A * zetaCompletedZeroCenteredHeight
                    (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) ∧
        (∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOfShifted
            (P.image (fun z : ℂ => z - (1 / 2 : ℂ)))
            (1 / 2 : ℝ) f₀ →
            ∀ ρ : ℂ, ZetaCompletedZero ρ → ρ ∉ S →
              zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
                zetaCenteredZeroSideContribution ρ
                  (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) = 0) ∧
        (∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOfShifted
            (P.image (fun z : ℂ => z - (1 / 2 : ℂ)))
            (1 / 2 : ℝ) f₀ →
            (∀ ρ : ℂ, ρ ∈ T₀ →
              zetaSpectralEval (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
                (zetaCenteredZero ρ) = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaCenteredZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
                    (-(k + 3 : ℤ))) ∧
        (∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
            ∀ T : Finset ℂ,
              (∀ ρ : ℂ, ρ ∈ T →
                zetaSpectralEval (convolutionAutocorrelation f)
                  (zetaCenteredZero ρ) = 0) →
              ∀ ρ : ℂ, ρ ∈ T →
                zetaSpectralEval
                  (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
                  (zetaCenteredZero ρ) = 0) ∧
        ∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
            (∀ ρ : ℂ, ρ ∈ T →
              zetaSpectralEval (convolutionAutocorrelation f)
                ρ = 0) →
              autocorrelationZeroTailRealAbs S f < ε

/-- Base common-polynomial-envelope package before finite tail truncation.

This owns the analytic common-envelope construction in a fixed finite
autocorrelation spectral-evaluation fiber.  It deliberately does not select
the final finite tail window: that is the separate summable-tail cutoff step
below, where dagger-constrained zeros are handled by forced vanishing rather
than by falsely excluding them from the completed-zero set. -/
def AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBase : Prop :=
  ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
    ∃ T₀ : Finset ℂ, ∃ A : ℝ, ∃ k : ℕ,
      (∀ ρ : ℂ, ρ ∈ T₀ →
        ρ ∉ daggerClosedSpectralSampleFinset P) ∧
      0 ≤ A ∧
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) ∧
      (∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          ∀ ρ : ℂ,
            ZetaCompletedZero ρ →
              ρ ∉ S →
                ρ ∈ daggerClosedSpectralSampleFinset P →
                  zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0) ∧
      (∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelation f)
              ρ = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) ∧
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          ∀ T : Finset ℂ,
            (∀ ρ : ℂ, ρ ∈ T →
              zetaSpectralEval (convolutionAutocorrelation f)
                (zetaCenteredZero ρ) = 0) →
            ∀ ρ : ℂ, ρ ∈ T →
              zetaSpectralEval
                (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
                (zetaCenteredZero ρ) = 0

/-- Fixed-fiber data carried by the base common-polynomial-envelope theorem. -/
def AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (T₀ : Finset ℂ)
    (A : ℝ)
    (k : ℕ) : Prop :=
  (∀ ρ : ℂ, ρ ∈ T₀ →
    ρ ∉ daggerClosedSpectralSampleFinset P) ∧
  0 ≤ A ∧
  Summable
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) ∧
  (∀ f : ZetaAdmissibleFunction,
    f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            ρ ∈ daggerClosedSpectralSampleFinset P →
              zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0) ∧
  (∀ f : ZetaAdmissibleFunction,
    f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
      (∀ ρ : ℂ, ρ ∈ T₀ →
        zetaSpectralEval (convolutionAutocorrelation f)
          ρ = 0) →
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
          ‖zetaZeroSideContribution (ρ : ℂ)
              (convolutionAutocorrelation f)‖ ≤
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) ∧
  ∀ f : ZetaAdmissibleFunction,
    f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
      ∀ T : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ T →
          zetaSpectralEval (convolutionAutocorrelation f)
            (zetaCenteredZero ρ) = 0) →
  ∀ ρ : ℂ, ρ ∈ T →
          zetaSpectralEval
            (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
            (zetaCenteredZero ρ) = 0

theorem AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.window_transport
    {S P : Finset ℂ} {f₀ : ZetaAdmissibleFunction}
    {T₀ : Finset ℂ} {A : ℝ} {k : ℕ}
    (hdata : AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData
      S P f₀ T₀ A k) :
    ∀ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
        ∀ T : Finset ℂ,
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
          ∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval
              (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
              (zetaCenteredZero ρ) = 0 := by
  exact hdata.2.2.2.2.2

/-- Separated fixed-fiber data carried by the common-polynomial-envelope theorem.

Unlike the older base package, this statement does not assert forced vanishing for
dagger-constrained tail zeros.  The caller supplies the separation hypothesis, so no
complementary completed zero has a centered coordinate in the dagger-closed preserved
sample set. -/
def AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (T₀ : Finset ℂ)
    (A : ℝ)
    (k : ℕ) : Prop :=
  (∀ ρ : ℂ, ρ ∈ T₀ →
    zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
  0 ≤ A ∧
  Summable
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) ∧
  (∀ f : ZetaAdmissibleFunction,
    f ∈ AutocorrelationSpectralEvalFiberOfShifted
      (translatedSpectralSampleFinset P (1 / 2 : ℝ))
      (1 / 2 : ℝ) f₀ →
      ∀ ρ : ℂ, ZetaCompletedZero ρ → ρ ∉ S →
        zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
          zetaCenteredZeroSideContribution ρ
            (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) = 0) ∧
  (∀ f : ZetaAdmissibleFunction,
    f ∈ AutocorrelationSpectralEvalFiberOfShifted
      (translatedSpectralSampleFinset P (1 / 2 : ℝ))
      (1 / 2 : ℝ) f₀ →
      (∀ ρ : ℂ, ρ ∈ T₀ →
        zetaSpectralEval (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
          (zetaCenteredZero ρ) = 0) →
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
          ‖zetaCenteredZeroSideContribution (ρ : ℂ)
              (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)‖ ≤
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))

/-- Separated base common-polynomial-envelope package before finite tail truncation. -/
def AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase : Prop :=
  ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
    (∀ ρ : ℂ,
      ZetaCompletedZero ρ →
        ρ ∉ S →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) →
      ∃ T₀ : Finset ℂ, ∃ A : ℝ, ∃ k : ℕ,
        AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData
          S P f₀ T₀ A k

/-- Projection of the dagger-disjoint base window from separated base data. -/
theorem AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData.baseWindow_disjoint
    {S P : Finset ℂ}
    {f₀ : ZetaAdmissibleFunction}
    {T₀ : Finset ℂ}
    {A : ℝ}
    {k : ℕ}
    (hdata :
      AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData
        S P f₀ T₀ A k) :
    ∀ ρ : ℂ, ρ ∈ T₀ →
      zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P := by
  exact hdata.1

/-- Projection of the nonnegative envelope constant from separated base data. -/
theorem AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData.constant_nonnegative
    {S P : Finset ℂ}
    {f₀ : ZetaAdmissibleFunction}
    {T₀ : Finset ℂ}
    {A : ℝ}
    {k : ℕ}
    (hdata :
      AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData
        S P f₀ T₀ A k) :
    0 ≤ A := by
  exact hdata.2.1

/-- Projection of the summable envelope from separated base data. -/
theorem AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData.envelope_summable
    {S P : Finset ℂ}
    {f₀ : ZetaAdmissibleFunction}
    {T₀ : Finset ℂ}
    {A : ℝ}
    {k : ℕ}
    (hdata :
      AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData
        S P f₀ T₀ A k) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) := by
  exact hdata.2.2.1

/-- Projection of the common envelope bound from separated base data. -/
theorem AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData.envelope_bound
    {S P : Finset ℂ}
    {f₀ : ZetaAdmissibleFunction}
    {T₀ : Finset ℂ}
    {A : ℝ}
    {k : ℕ}
    (hdata :
      AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData
        S P f₀ T₀ A k) :
    ∀ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOfShifted
        (translatedSpectralSampleFinset P (1 / 2 : ℝ))
        (1 / 2 : ℝ) f₀ →
        (∀ ρ : ℂ, ρ ∈ T₀ →
          zetaSpectralEval (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
            (zetaCenteredZero ρ) = 0) →
          ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
            ‖zetaCenteredZeroSideContribution (ρ : ℂ)
                (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)‖ ≤
              A * zetaCompletedZeroCenteredHeight
                (⟨(ρ : ℂ), ρ.2.1⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  exact hdata.2.2.2.2

theorem AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData.forcedDagger_vanishes
    {S P : Finset ℂ} {f₀ : ZetaAdmissibleFunction}
    {T₀ : Finset ℂ} {A : ℝ} {k : ℕ}
    (hdata :
      AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBaseData
        S P f₀ T₀ A k) :
    ∀ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOfShifted
        (translatedSpectralSampleFinset P (1 / 2 : ℝ))
        (1 / 2 : ℝ) f₀ →
        ∀ ρ : ℂ, ZetaCompletedZero ρ → ρ ∉ S →
          zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
            zetaCenteredZeroSideContribution ρ
              (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) = 0 := by
  exact hdata.2.2.2.1

/-- The base theorem supplies fixed-fiber base-envelope data. -/
theorem AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBase.exists_data
    (hbase : AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBase)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∃ T₀ : Finset ℂ, ∃ A : ℝ, ∃ k : ℕ,
      AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData
        S P f₀ T₀ A k := by
  match hbase S P f₀ with
  | ⟨T₀, A, k, hT₀, hA, hsum, hforced, henv, hwindow⟩ =>
      exact ⟨T₀, A, k, hT₀, hA, hsum, hforced, henv, hwindow⟩

/-- Fixed-fiber base-envelope data assembles into the global base theorem. -/
theorem AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBase.of_exists_data
    (hdata :
      ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
        ∃ T₀ : Finset ℂ, ∃ A : ℝ, ∃ k : ℕ,
          AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData
            S P f₀ T₀ A k) :
    AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBase := by
  intro S P f₀
  match hdata S P f₀ with
  | ⟨T₀, A, k, hT₀, hA, hsum, hforced, henv, hwindow⟩ =>
      exact ⟨T₀, A, k, hT₀, hA, hsum, hforced, henv, hwindow⟩

/-- The global base theorem is equivalent to fixed-fiber base-envelope data. -/
theorem AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBase.iff_exists_data :
    AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBase ↔
      ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
        ∃ T₀ : Finset ℂ, ∃ A : ℝ, ∃ k : ℕ,
          AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData
            S P f₀ T₀ A k := by
  exact
    ⟨fun hbase S P f₀ =>
        AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBase.exists_data
          hbase S P f₀,
      fun hdata =>
        AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBase.of_exists_data
          hdata⟩

/-- Projection of the dagger-disjoint base window from fixed-fiber base data. -/
theorem AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.baseWindow_disjoint
    {S P : Finset ℂ}
    {f₀ : ZetaAdmissibleFunction}
    {T₀ : Finset ℂ}
    {A : ℝ}
    {k : ℕ}
    (hdata :
      AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData
        S P f₀ T₀ A k) :
    ∀ ρ : ℂ, ρ ∈ T₀ →
        ρ ∉ daggerClosedSpectralSampleFinset P := by
  exact hdata.1

/-- Projection of the nonnegative envelope constant from fixed-fiber base data. -/
theorem AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.constant_nonnegative
    {S P : Finset ℂ}
    {f₀ : ZetaAdmissibleFunction}
    {T₀ : Finset ℂ}
    {A : ℝ}
    {k : ℕ}
    (hdata :
      AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData
        S P f₀ T₀ A k) :
    0 ≤ A := by
  exact hdata.2.1

/-- Projection of the summable envelope from fixed-fiber base data. -/
theorem AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.envelope_summable
    {S P : Finset ℂ}
    {f₀ : ZetaAdmissibleFunction}
    {T₀ : Finset ℂ}
    {A : ℝ}
    {k : ℕ}
    (hdata :
      AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData
        S P f₀ T₀ A k) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) := by
  exact hdata.2.2.1

/-- Projection of forced dagger-constrained contribution vanishing from fixed-fiber
base data. -/
theorem AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.forcedDagger_vanishes
    {S P : Finset ℂ}
    {f₀ : ZetaAdmissibleFunction}
    {T₀ : Finset ℂ}
    {A : ℝ}
    {k : ℕ}
    (hdata :
      AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData
        S P f₀ T₀ A k) :
    ∀ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
        ∀ ρ : ℂ,
          ZetaCompletedZero ρ →
            ρ ∉ S →
              ρ ∈ daggerClosedSpectralSampleFinset P →
                zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0 := by
  exact hdata.2.2.2.1

/-- Projection of the common envelope bound from fixed-fiber base data. -/
theorem AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData.envelope_bound
    {S P : Finset ℂ}
    {f₀ : ZetaAdmissibleFunction}
    {T₀ : Finset ℂ}
    {A : ℝ}
    {k : ℕ}
    (hdata :
      AutocorrelationSpectralEvalFiberCommonPolynomialEnvelopeBaseData
        S P f₀ T₀ A k) :
    ∀ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
        (∀ ρ : ℂ, ρ ∈ T₀ →
          zetaSpectralEval (convolutionAutocorrelation f)
            ρ = 0) →
          ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
            ‖zetaZeroSideContribution (ρ : ℂ)
                (convolutionAutocorrelation f)‖ ≤
              A * zetaCompletedZeroCenteredHeight
                (⟨(ρ : ℂ), ρ.2.1⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  exact hdata.2.2.2.2.1

/-- The owner Runge proposition specialized to a fixed finite autocorrelation
spectral-evaluation fiber. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_ownerRungeCore
    (hRunge : AutocorrelationSpectralEvalFiberZeroTailSmallValuesRunge)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hSeparated :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            ρ ∉ daggerClosedSpectralSampleFinset P) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε := by
  exact hRunge S P f₀ hSeparated

/-- Forced dagger-constrained completed-zero contributions outside the excluded set vanish.

These are the completed zeros whose centered samples already lie in the fixed finite
autocorrelation fiber constraints.  They cannot be inserted into a disjoint annihilation
window, so the Runge tail theorem must account for them at the owner level rather than
through finite interpolation. -/
theorem autocorrelationSpectralEvalFiber_forcedDaggerConstrainedZeroContribution_vanishes_ownerGap
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hdaggerExcluded :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
          ρ ∉ daggerClosedSpectralSampleFinset P) :
    ∀ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
        ∀ ρ : ℂ,
          ZetaCompletedZero ρ →
            ρ ∉ S →
              ρ ∈ daggerClosedSpectralSampleFinset P →
                  zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0 := by
  intro f hfFiber ρ hρ hρS hρDagger
  exact False.elim (hdaggerExcluded ρ hρ hρS hρDagger)

/-- Vanishing on an enlarged finite zero window supplies the base-window vanishing
hypothesis required by a polynomial envelope chosen before the enlargement. -/
theorem autocorrelationSpectralEvalFiber_baseWindowVanishes_of_enlargedWindowVanishes
    (P : Finset ℂ)
    (T₀ T : Finset ℂ)
    (hT₀T : T₀ ⊆ T)
    (f : ZetaAdmissibleFunction)
    (hfT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval (convolutionAutocorrelation f)
          ρ = 0) :
    ∀ ρ : ℂ, ρ ∈ T₀ →
      zetaSpectralEval (convolutionAutocorrelation f)
        ρ = 0 := by
  intro ρ hρT₀
  exact hfT ρ (hT₀T hρT₀)

/-- A common polynomial envelope selected on `T₀` remains available for probes which
vanish on any later finite window containing `T₀`. -/
theorem autocorrelationSpectralEvalFiber_envelope_of_enlargedWindowVanishes
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (T₀ T : Finset ℂ)
    (hT₀T : T₀ ⊆ T)
    (A : ℝ)
    (k : ℕ)
    (henv :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelation f)
              ρ = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
    (f : ZetaAdmissibleFunction)
    (hfFiber : f ∈ AutocorrelationSpectralEvalFiberOf P f₀)
    (hfT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval (convolutionAutocorrelation f)
        ρ = 0) :
    ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
      ‖zetaZeroSideContribution (ρ : ℂ)
          (convolutionAutocorrelation f)‖ ≤
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  exact
    henv f hfFiber
      (autocorrelationSpectralEvalFiber_baseWindowVanishes_of_enlargedWindowVanishes
        P T₀ T hT₀T f hfT)

/-- A zero spectral value at a completed-zero coordinate kills its contribution. -/
theorem zetaZeroSideContribution_eq_zero_of_spectralEval_zero
    (φ : ZetaAdmissibleFunction)
    (ρ : ℂ)
    (hρ :
      zetaSpectralEval φ ρ = 0) :
    zetaZeroSideContribution ρ φ = 0 := by
  have hunfold :
      zetaZeroSideContribution ρ φ =
        (-(zetaZeroMultiplicity ρ : ℂ)) * zetaSpectralEval φ ρ :=
    zetaZeroSideContribution_def ρ φ
  have hevalZero :
      (-(zetaZeroMultiplicity ρ : ℂ)) * zetaSpectralEval φ ρ =
        (-(zetaZeroMultiplicity ρ : ℂ)) * 0 :=
    congrArg
      (fun z : ℂ => (-(zetaZeroMultiplicity ρ : ℂ)) * z)
      hρ
  exact
    Eq.trans hunfold
      (Eq.trans hevalZero (mul_zero (-(zetaZeroMultiplicity ρ : ℂ))))

/-- Vanishing of the selected zero-window spectral samples kills the corresponding
zero-side contributions. -/
theorem zetaZeroSideContribution_eq_zero_of_window_spectralEval_zero
    (S : Finset ℂ)
    (T : Finset ℂ)
    (f : ZetaAdmissibleFunction)
    (hfT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval (convolutionAutocorrelation f)
          ρ = 0) :
    ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
      (ρ : ℂ) ∈ T →
        zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) = 0 := by
  intro ρ hρT
  exact
    zetaZeroSideContribution_eq_zero_of_spectralEval_zero
      (convolutionAutocorrelation f) (ρ : ℂ) (hfT (ρ : ℂ) hρT)

/-- If all completed-zero spectral samples outside `S` vanish, then every zero-tail
summand is zero. -/
theorem zetaZeroTail_summand_eq_zero_of_all_complement_spectralEval_zero
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction)
    (hfZero :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaSpectralEval (convolutionAutocorrelation f)
              ρ = 0) :
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
        zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)) =
      fun zeroElement : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} => 0 := by
  have hpointwise :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) = 0 :=
    fun ρ =>
      zetaZeroSideContribution_eq_zero_of_spectralEval_zero
        (convolutionAutocorrelation f)
        (ρ : ℂ)
        (hfZero (ρ : ℂ) ρ.2.1 ρ.2.2)
  exact funext hpointwise

/-- If all completed-zero spectral samples outside `S` vanish, the completed zero-tail
itself is zero. -/
theorem zetaZeroTail_eq_zero_of_all_complement_spectralEval_zero
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction)
    (hfZero :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaSpectralEval (convolutionAutocorrelation f)
              ρ = 0) :
    zetaZeroTail S (convolutionAutocorrelation f) = 0 := by
  have htail_unfold :
      zetaZeroTail S (convolutionAutocorrelation f) =
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) :=
    Eq.refl (zetaZeroTail S (convolutionAutocorrelation f))
  have hsummand_zero :
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)) =
        fun zeroElement : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} => 0 :=
    zetaZeroTail_summand_eq_zero_of_all_complement_spectralEval_zero
      S f hfZero
  have htsum_zero :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)) = 0 :=
    Eq.trans
      (congrArg
        (fun F : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} → ℂ =>
          ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}, F ρ)
        hsummand_zero)
      tsum_zero
  exact Eq.trans htail_unfold htsum_zero

/-- The common polynomial envelope also bounds zeros in the base finite window after the
enlarged window has been killed. -/
theorem zetaZeroSideContribution_norm_le_commonPolynomialEnvelope_of_window
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (T₀ T : Finset ℂ)
    (hT₀T : T₀ ⊆ T)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (henvT :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              ρ = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
    (f : ZetaAdmissibleFunction)
    (hfFiber : f ∈ AutocorrelationSpectralEvalFiberOf P f₀)
    (hfT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval (convolutionAutocorrelation f)
          ρ = 0)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}) :
    ‖zetaZeroSideContribution (ρ : ℂ)
        (convolutionAutocorrelation f)‖ ≤
      A * zetaCompletedZeroCenteredHeight
        (⟨(ρ : ℂ), ρ.2.1⟩ :
          {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  match (inferInstance : Decidable ((ρ : ℂ) ∈ T₀)) with
  | isTrue hρT₀ =>
      have hρT : (ρ : ℂ) ∈ T := hT₀T hρT₀
      have hcontribution_zero :
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) = 0 :=
        zetaZeroSideContribution_eq_zero_of_window_spectralEval_zero
          S T f hfT ρ hρT
      have hnorm_zero :
          ‖zetaZeroSideContribution (ρ : ℂ)
              (convolutionAutocorrelation f)‖ = 0 :=
        Eq.trans (congrArg norm hcontribution_zero) norm_zero
      have henvelope_nonneg :
          0 ≤
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) :=
        zetaZeroMultiplicityTransformEnvelope_nonnegative hA k
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ})
      exact Eq.subst
        (motive := fun x : ℝ =>
          x ≤
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
        hnorm_zero.symm
        henvelope_nonneg
  | isFalse hρT₀ =>
      exact henvT f hfFiber hfT
        (⟨(ρ : ℂ), ρ.2.1, ρ.2.2, hρT₀⟩ :
          {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀})

/-- Direct centered-coordinate envelope data for the active tail lane. -/
def AutocorrelationSpectralEvalFiberDirectCenteredSeparatedEnvelopeData
    (S P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (T₀ : Finset ℂ)
    (A : ℝ)
    (k : ℕ) : Prop :=
  (∀ ρ : ℂ, ρ ∈ T₀ →
    ρ ∉ daggerClosedSpectralSampleFinset P) ∧
  0 ≤ A ∧
  Summable
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) ∧
  (∀ f : ZetaAdmissibleFunction,
    f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
      ∀ ρ : ℂ, ZetaCompletedZero ρ → ρ ∉ S →
        ρ ∈ daggerClosedSpectralSampleFinset P →
          zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0) ∧
  ∀ f : ZetaAdmissibleFunction,
    f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
      (∀ ρ : ℂ, ρ ∈ T₀ →
        zetaSpectralEval (convolutionAutocorrelation f) ρ = 0) →
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
        ‖zetaZeroSideContribution (ρ : ℂ)
            (convolutionAutocorrelation f)‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
              (-(k + 3 : ℤ))

/-- Direct separated envelope existence for the active tail lane. -/
def AutocorrelationSpectralEvalFiberDirectCenteredSeparatedEnvelopeBase : Prop :=
  ∀ S P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
    (∀ ρ : ℂ, ZetaCompletedZero ρ → ρ ∉ S →
      ρ ∉ daggerClosedSpectralSampleFinset P) →
    ∃ T₀ : Finset ℂ, ∃ A : ℝ, ∃ k : ℕ,
      AutocorrelationSpectralEvalFiberDirectCenteredSeparatedEnvelopeData
        S P f₀ T₀ A k

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
