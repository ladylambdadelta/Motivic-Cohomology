import Boundary.LFunctions.ZetaAdmissibleFunction
import Boundary.LFunctions.ZetaCenteredZero
import Boundary.LFunctions.ZetaTransformCalculus
import Mathlib.Analysis.Analytic.IsolatedZeros
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

/-- The multiplicity of a completed zeta zero.

This is defined by the local analytic order at the centered completed zeta
function when it is analytic at the point, and `0` otherwise. This keeps the
zero-side bookkeeping tied to the canonical order-of-vanishing notion from
`Mathlib.Analysis.Analytic.IsolatedZeros`. -/
noncomputable def completedZetaZeroMultiplicity (ρ : ℂ) : ℕ :=
  if h : AnalyticAt ℂ centeredCompletedRiemannZeta ρ then h.order.toNat else 0

/-- The multiplicity of a centered completed zeta zero. -/
def zetaZeroMultiplicity (ρ : ℂ) : ℕ :=
  completedZetaZeroMultiplicity ρ

/-- At analytic points, the zero multiplicity is the local analytic order. -/
theorem completedZetaZeroMultiplicity_eq_order (ρ : ℂ)
    (h : AnalyticAt ℂ centeredCompletedRiemannZeta ρ) :
    completedZetaZeroMultiplicity ρ = h.order.toNat := by
  unfold completedZetaZeroMultiplicity
  exact dif_pos h

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

/-- The spectral transform is additive. -/
theorem zetaSpectralTransform_add
    (φ ψ : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralTransform (φ + ψ) z =
      zetaSpectralTransform φ z + zetaSpectralTransform ψ z := by
  change zetaLaplaceTransform (φ + ψ) z = zetaLaplaceTransform φ z + zetaLaplaceTransform ψ z
  exact zetaLaplaceTransform_add φ ψ z

/-- The spectral transform is homogeneous under scalar multiplication. -/
theorem zetaSpectralTransform_smul
    (a : ℂ) (φ : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralTransform (a • φ) z = a * zetaSpectralTransform φ z := by
  change zetaLaplaceTransform (a • φ) z = a * zetaLaplaceTransform φ z
  exact zetaLaplaceTransform_smul a φ z

/-- The spectral transform commutes with finite sums. -/
theorem zetaSpectralTransform_sum
    {α : Type*} (s : Finset α) (f : α → ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralTransform (∑ a in s, f a) z =
      ∑ a in s, zetaSpectralTransform (f a) z := by
  change zetaLaplaceTransform (∑ a in s, f a) z =
    ∑ a in s, zetaLaplaceTransform (f a) z
  exact zetaLaplaceTransform_sum s f z

/-- The spectral transform of an autocorrelation is the explicit Laplace integral. -/
theorem zetaSpectralTransform_autocorrelation_eq_integral
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralTransform (ZetaAdmissibleFunction.autocorrelation f) z =
      ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t) := by
  change zetaLaplaceTransform (ZetaAdmissibleFunction.autocorrelation f) z =
    ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t)
  exact LFunctions.ZetaTransformCalculus.zetaLaplaceTransform_autocorrelation f z

/-- The spectral evaluation of an autocorrelation is the explicit Laplace integral. -/
theorem zetaSpectralEval_autocorrelation_eq_integral
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralEval (ZetaAdmissibleFunction.autocorrelation f) z =
      ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t) := by
  change zetaLaplaceTransform (ZetaAdmissibleFunction.autocorrelation f) z =
    ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t)
  exact LFunctions.ZetaTransformCalculus.zetaLaplaceTransform_autocorrelation f z

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

/-- The centered zero set is countable. -/
theorem centeredZetaZeros_countable :
    centeredZetaZeros.Countable := by
  have hfin : ∀ z : CenteredZetaZero, ({x : ℂ | x ∈ orbit z}.Finite) := by
    intro z
    exact orbit_finite z
  classical
  refine countable_union (fun z => ?_)
  exact (hfin z).countable

end
end LFunctions
end Boundary
