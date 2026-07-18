import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.Part01_FiniteGeometry
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.QuantitativeCardinalTail

/-!
# Finite tomography tail transport

Explicit owner lemmas for tail transport and Runge packaging.
-/

namespace Boundary
namespace LFunctions

namespace ZetaAdmissibleFunction

/-- Complex zero-tail norm control for a non-dagger height window implies real absolute
zero-tail control for that same window. -/
theorem autocorrelationSpectralEvalFiber_nonDaggerHeightWindow_realAbsTailForcing_of_normTailForcing
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (R : ℝ)
    (hnorm :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ,
            ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R →
              zetaSpectralEval (convolutionAutocorrelation f)
                ρ = 0) →
            ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε) :
    ∀ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
        (∀ ρ : ℂ,
          ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R →
            zetaSpectralEval (convolutionAutocorrelation f)
              ρ = 0) →
          autocorrelationZeroTailRealAbs S f < ε := by
  intro f hfFiber hfWindow
  exact
    autocorrelationZeroTailRealAbs_lt_of_zetaZeroTail_norm_lt
      S f ε
      (hnorm f hfFiber hfWindow)

/-- Existence of a non-dagger height radius with complex zero-tail norm forcing implies
existence of a radius with real absolute tail forcing. -/
theorem autocorrelationSpectralEvalFiber_nonDaggerHeightWindow_realAbsTailForcing_exists_of_normTailForcing_exists
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hR :
      ∃ R : ℝ,
        ∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
            (∀ ρ : ℂ,
              ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R →
                zetaSpectralEval (convolutionAutocorrelation f)
                  ρ = 0) →
              ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε) :
    ∃ R : ℝ,
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ,
            ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R →
              zetaSpectralEval (convolutionAutocorrelation f)
                ρ = 0) →
            autocorrelationZeroTailRealAbs S f < ε := by
  match hR with
  | ⟨R, hnorm⟩ =>
      exact
        ⟨R,
          autocorrelationSpectralEvalFiber_nonDaggerHeightWindow_realAbsTailForcing_of_normTailForcing
            S P f₀ ε R hnorm⟩

/-- The window-selection form of the Runge/tomographic tail theorem. -/
theorem autocorrelationSpectralEvalFiber_exists_finiteWindowTailControl_of_ownerTailPackage
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hε : 0 < ε)
    (hpackage :
      ∃ T : Finset ℂ,
        AutocorrelationSpectralEvalFiberFiniteWindowTailControl S P f₀ ε T) :
    ∃ T : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ T →
        ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        ∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
            (∀ ρ : ℂ, ρ ∈ T →
              zetaSpectralEval (convolutionAutocorrelation f)
                ρ = 0) →
              autocorrelationZeroTailRealAbs S f < ε := by
  match hpackage with
  | ⟨T, hT⟩ =>
      exact ⟨T,
        autocorrelationSpectralEvalFiberFiniteWindowTailControl.elim
          S P f₀ ε T hT⟩

/-- A tail-localized finite tomographic interpolant gives an attained small value in the
fixed autocorrelation fiber. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_nonDaggerHeightWindowTailLocalization
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hTailLocalization : AutocorrelationSpectralEvalFiberSeparatedNonDaggerHeightWindowTailLocalization)
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
  intro ε hε
  match hTailLocalization
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀ hSeparated ε hε with
  | ⟨f, hfFiber, htail⟩ =>
      exact
        ⟨autocorrelationZeroTailRealAbs S f,
          ⟨f, hfFiber, Eq.refl (autocorrelationZeroTailRealAbs S f)⟩,
          htail⟩

/-- Finite-window tail-control form of the nonlinear Runge/tomography theorem.

For every fixed finite autocorrelation spectral fiber and tolerance, there is
a finite completed-zero annihilation window, disjoint from the fixed spectral
constraints, whose annihilation forces the complementary zero-tail below the
tolerance. -/
def AutocorrelationSpectralEvalFiberFiniteWindowTailControlRunge : Prop :=
  ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
    ∀ ε : ℝ, 0 < ε →
      ∃ T : Finset ℂ,
        AutocorrelationSpectralEvalFiberFiniteWindowTailControl S P f₀ ε T

/-- Separated finite-window form of the nonlinear Runge/tomography theorem.

The preserved finite spectral samples must not pin any completed-zero coordinate in the
complementary tail.  Under that separation hypothesis, the theorem selects a finite
dagger-disjoint completed-zero window whose annihilation forces the complementary
zero-tail below the requested tolerance. -/
def AutocorrelationSpectralEvalFiberSeparatedFiniteWindowTailControlRunge : Prop :=
  ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
    (∀ ρ : ℂ,
      ZetaCompletedZero ρ →
        ρ ∉ S →
          ρ ∉ daggerClosedSpectralSampleFinset P) →
      ∀ ε : ℝ, 0 < ε →
        ∃ T : Finset ℂ,
          AutocorrelationSpectralEvalFiberFiniteWindowTailControl S P f₀ ε T

/-- Complex norm finite-window form of the Runge/tomographic tail theorem. -/
def AutocorrelationSpectralEvalFiberFiniteWindowNormTailControlRunge : Prop :=
  ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
    ∀ ε : ℝ, 0 < ε →
      ∃ T : Finset ℂ,
        AutocorrelationSpectralEvalFiberFiniteWindowNormTailControl S P f₀ ε T

/-- Complex norm finite-window tail control implies the real absolute finite-window
tail-control package. -/
theorem autocorrelationSpectralEvalFiberFiniteWindowTailControl_of_normTailControl
    (hRunge : AutocorrelationSpectralEvalFiberFiniteWindowNormTailControlRunge) :
    AutocorrelationSpectralEvalFiberFiniteWindowTailControlRunge := by
  intro S P f₀ ε hε
  match hRunge S P f₀ ε hε with
  | ⟨T, hT⟩ =>
      have hWindow :
          (∀ ρ : ℂ, ρ ∈ T → ZetaCompletedZero ρ) ∧
            (∀ ρ : ℂ, ρ ∈ T → ρ ∉ S) ∧
              (∀ ρ : ℂ, ρ ∈ T →
                ρ ∉ daggerClosedSpectralSampleFinset P) ∧
                ∀ f : ZetaAdmissibleFunction,
                  f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
                    (∀ ρ : ℂ, ρ ∈ T →
                      zetaSpectralEval (convolutionAutocorrelation f)
                        ρ = 0) →
                      ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε :=
        autocorrelationSpectralEvalFiberFiniteWindowNormTailControl.elim
          S P f₀ ε T hT
      exact
        ⟨T,
          autocorrelationSpectralEvalFiberFiniteWindowTailControl_intro
            S P f₀ ε T hWindow.2.2.1
            (fun f hfFiber hfT =>
              autocorrelationZeroTailRealAbs_lt_of_zetaZeroTail_norm_lt
                S f ε
                (hWindow.2.2.2 f hfFiber hfT))⟩

/-- Separated small-values form of nonlinear Runge/tomography for finite
autocorrelation spectral-evaluation fibers. -/
def AutocorrelationSpectralEvalFiberSeparatedZeroTailSmallValuesRunge : Prop :=
  ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
    (∀ ρ : ℂ,
      ZetaCompletedZero ρ →
        ρ ∉ S →
          ρ ∉ daggerClosedSpectralSampleFinset P) →
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
            r < ε

/-- Closure/radical form of nonlinear Runge/tomography for finite
autocorrelation spectral-evaluation fibers.

This is the canonical analytic form: in each fixed finite autocorrelation
spectral fiber, the zero-tail value set has `0` in its closure.  The concrete
small-values statement is a topological corollary using nonnegativity of the
zero-tail absolute value. -/
def AutocorrelationSpectralEvalFiberZeroTailClosureRunge : Prop :=
  ∀ (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ) (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction),
    (∀ ρ : ℂ,
      ZetaCompletedZero ρ →
        ρ ∉ S →
          ρ ∉ daggerClosedSpectralSampleFinset P) →
      (0 : ℝ) ∈ closure
        (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀)

/-- Quotient-level closure/radical form of nonlinear Runge/tomography for
finite autocorrelation spectral-evaluation fibers.

This is the canonical analytic form of the remaining Runge theorem: after
passing to the zero-tail ordered-heart quotient of the positive autocorrelation
cone, the named zero-tail value set has `0` in its closure. -/
def AutocorrelationSpectralFiberQuotientZeroTailClosureRunge : Prop :=
  ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
    (0 : ℝ) ∈ closure
      (autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
        S P f₀)

/-- Quotient-level arbitrarily-small-values form of nonlinear
Runge/tomography for finite autocorrelation spectral-evaluation fibers. -/
def AutocorrelationSpectralFiberQuotientZeroTailSmallValuesRunge : Prop :=
  ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
    (∀ ρ : ℂ,
      ZetaCompletedZero ρ →
        ρ ∉ S →
          ρ ∉ daggerClosedSpectralSampleFinset P) →
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈
            autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
              S P f₀ ∧
            r < ε




end ZetaAdmissibleFunction
end LFunctions
end Boundary
