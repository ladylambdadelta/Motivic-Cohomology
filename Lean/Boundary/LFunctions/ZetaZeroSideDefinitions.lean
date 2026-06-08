import Boundary.LFunctions.ZetaAdmissibleFunction
import Boundary.LFunctions.ZetaCenteredZero
import Boundary.LFunctions.ZetaTransformCalculus
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Boundary zero-side definitions

This file owns the explicit zero-side functional surface used by the
negative-probe branch.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The centered completed zeta zero predicate used by the zero-side definitions. -/
abbrev ZetaCompletedZero (ρ : ℂ) : Prop := centeredCompletedRiemannZeta ρ = 0

/-- The multiplicity of a completed zeta zero. -/
axiom completedZetaZeroMultiplicity : ℂ → ℕ

/-- The multiplicity of a centered completed zeta zero. -/
def zetaZeroMultiplicity (ρ : ℂ) : ℕ :=
  completedZetaZeroMultiplicity ρ

/-- The centered zero coordinate. -/
def zetaCenteredZero (ρ : ℂ) : ℂ :=
  ρ - (1 / 2 : ℂ)

/-- The spectral evaluation map for admissible test functions. -/
def zetaSpectralTransform : ZetaAdmissibleFunction → ℂ → ℂ :=
  zetaLaplaceTransform

/-- The spectral evaluation of an admissible test function. -/
abbrev zetaSpectralEval (φ : ZetaAdmissibleFunction) (z : ℂ) : ℂ :=
  zetaSpectralTransform φ z

/-- The spectral transform is the zeta Laplace transform. -/
theorem zetaSpectralTransform_eq_laplace
    (φ : ZetaAdmissibleFunction) :
    zetaSpectralTransform φ = zetaLaplaceTransform φ := by
  rfl

/-- The spectral evaluation is the zeta Laplace transform evaluation. -/
theorem zetaSpectralEval_eq_laplace
    (φ : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralEval φ z = zetaLaplaceTransform φ z := by
  rfl

/-- The spectral evaluation of an autocorrelation is the constructed Laplace transform. -/
theorem zetaSpectralEval_autocorrelation
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralEval (ZetaAdmissibleFunction.autocorrelation f) z =
      zetaLaplaceTransform (ZetaAdmissibleFunction.autocorrelation f) z := by
  rfl

/-- The single zero contribution to the completed zero side. -/
def zetaZeroSideContribution (ρ : ℂ) (φ : ZetaAdmissibleFunction) : ℂ :=
  - (zetaZeroMultiplicity ρ : ℂ) * zetaSpectralEval φ (zetaCenteredZero ρ)

/-- The functional-equation orbit of a centered zero. -/
def zetaZeroOrbitFinset (ρ : ℂ) : Finset ℂ :=
  insert ρ <| insert (1 - ρ) <| insert (star ρ) <| insert (1 - star ρ) ∅

/-- The orbit contribution attached to a centered zero. -/
def zetaZeroOrbitContribution (ρ : ℂ) (φ : ZetaAdmissibleFunction) : ℂ :=
  Finset.sum (zetaZeroOrbitFinset ρ) (fun η => zetaZeroSideContribution η φ)

/-- The zero tail away from a finite excluded set. -/
def zetaZeroTail (S : Finset ℂ) (φ : ZetaAdmissibleFunction) : ℂ :=
  tsum (fun η : {η : ℂ // ZetaCompletedZero η ∧ η ∉ S} =>
    zetaZeroSideContribution (η : ℂ) φ)

/-- The orbit remainder is the tail after removing the orbit of the chosen zero. -/
def zetaZeroOrbitRemainder (ρ : ℂ) (φ : ZetaAdmissibleFunction) : ℂ :=
  zetaZeroTail (zetaZeroOrbitFinset ρ) φ

/-- Real-valued projection of the single zero contribution. -/
def zetaZeroSideContributionRe (ρ : ℂ) (φ : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaZeroSideContribution ρ φ)

/-- Real-valued projection of the orbit contribution. -/
def zetaZeroOrbitContributionRe (ρ : ℂ) (φ : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaZeroOrbitContribution ρ φ)

/-- Real-valued projection of the zero tail. -/
def zetaZeroTailRe (S : Finset ℂ) (φ : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaZeroTail S φ)

/-- Real-valued projection of the orbit remainder. -/
def zetaZeroOrbitRemainderRe (ρ : ℂ) (φ : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaZeroOrbitRemainder ρ φ)

theorem zetaZeroSideContribution_def (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroSideContribution ρ φ =
      - (zetaZeroMultiplicity ρ : ℂ) * zetaSpectralEval φ (zetaCenteredZero ρ) := by
  rfl

/-- The spectral transform of an autocorrelation is the constructed Laplace transform. -/
theorem zetaSpectralTransform_autocorrelation
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralTransform (ZetaAdmissibleFunction.autocorrelation f) z =
      zetaLaplaceTransform (ZetaAdmissibleFunction.autocorrelation f) z := by
  rfl

/-- The spectral transform of an autocorrelation is the explicit Laplace integral. -/
theorem zetaSpectralTransform_autocorrelation_eq_integral
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralTransform (ZetaAdmissibleFunction.autocorrelation f) z =
      ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t) := by
  rw [zetaSpectralTransform_autocorrelation,
    LFunctions.ZetaTransformCalculus.zetaLaplaceTransform_autocorrelation]
  rfl

/-- The spectral evaluation of an autocorrelation is the explicit Laplace integral. -/
theorem zetaSpectralEval_autocorrelation_eq_integral
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralEval (ZetaAdmissibleFunction.autocorrelation f) z =
      ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t) := by
  rw [zetaSpectralEval_eq_laplace, LFunctions.ZetaTransformCalculus.zetaLaplaceTransform_autocorrelation]
  rfl

theorem zetaZeroOrbitContribution_eq_sum (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitContribution ρ φ =
      Finset.sum (zetaZeroOrbitFinset ρ) (fun η => zetaZeroSideContribution η φ) := by
  rfl

theorem zetaZeroOrbitRemainder_eq_tail (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitRemainder ρ φ =
      zetaZeroTail (zetaZeroOrbitFinset ρ) φ := by
  rfl

theorem zetaZeroTail_def (S : Finset ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroTail S φ =
      tsum (fun η : {η : ℂ // ZetaCompletedZero η ∧ η ∉ S} =>
        zetaZeroSideContribution (η : ℂ) φ) := by
  rfl

end
end LFunctions
end Boundary
