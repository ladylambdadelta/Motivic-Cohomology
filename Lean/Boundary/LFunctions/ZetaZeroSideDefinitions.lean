import Boundary.LFunctions.ZetaAdmissibleFunction
import Boundary.LFunctions.ZetaCenteredZero
import Boundary.LFunctions.ZetaCenteredZeroOrbit
import Boundary.LFunctions.ZetaCenteredZeroCounting
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

open MeasureTheory

/-- The centered completed zeta zero predicate used by the zero-side definitions. -/
abbrev ZetaCompletedZero (ρ : ℂ) : Prop := centeredCompletedRiemannZeta ρ = 0

/-- The multiplicity of a completed zeta zero.

This is defined by the local analytic order at the centered completed zeta
function when it is analytic at the point, and `0` otherwise. This keeps the
zero-side bookkeeping tied to the canonical order-of-vanishing notion from
`Mathlib.Analysis.Analytic.IsolatedZeros`. -/
noncomputable def completedZetaZeroMultiplicity (ρ : ℂ) : ℕ :=
  by
    classical
    exact if h : AnalyticAt ℂ centeredCompletedRiemannZeta ρ then h.order.toNat else 0

/-- The multiplicity of a centered completed zeta zero. -/
def zetaZeroMultiplicity (ρ : ℂ) : ℕ :=
  completedZetaZeroMultiplicity ρ

/-- At analytic points, the zero multiplicity is the local analytic order. -/
theorem completedZetaZeroMultiplicity_eq_order (ρ : ℂ)
    (h : AnalyticAt ℂ centeredCompletedRiemannZeta ρ) :
    completedZetaZeroMultiplicity ρ = h.order.toNat := by
  classical
  unfold completedZetaZeroMultiplicity
  exact dif_pos h

/-- The centered zero coordinate. -/
def zetaCenteredZero (ρ : ℂ) : ℂ :=
  ρ - (1 / 2 : ℂ)

/-- Vertical height of a completed zero after centering. -/
noncomputable def zetaCompletedZeroCenteredHeight
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  1 + ‖(zetaCenteredZero (ρ : ℂ)).im‖

/-- Completed-zero centered height is at least one. -/
theorem zetaCompletedZeroCenteredHeight_ge_one
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    1 ≤ zetaCompletedZeroCenteredHeight ρ := by
  unfold zetaCompletedZeroCenteredHeight
  exact le_add_of_nonneg_right (norm_nonneg ((zetaCenteredZero (ρ : ℂ)).im))

/-- Completed-zero centered height is positive. -/
theorem zetaCompletedZeroCenteredHeight_pos
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    0 < zetaCompletedZeroCenteredHeight ρ := by
  exact lt_of_lt_of_le zero_lt_one (zetaCompletedZeroCenteredHeight_ge_one ρ)

/-- Completed-zero centered height is nonzero. -/
theorem zetaCompletedZeroCenteredHeight_ne_zero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaCompletedZeroCenteredHeight ρ ≠ 0 := by
  exact ne_of_gt (zetaCompletedZeroCenteredHeight_pos ρ)

/-- Completed zeros in the centered vertical height ball of radius `T`. -/
def completedZerosInCenteredHeightBall (T : ℝ) :
    Set {ρ : ℂ // ZetaCompletedZero ρ} :=
  {ρ | zetaCompletedZeroCenteredHeight ρ ≤ T}

/-- Completed zeros are locally finite in centered height balls. -/
theorem finite_completedZerosInCenteredHeightBall
    (T : ℝ) :
    (completedZerosInCenteredHeightBall T).Finite := by
  sorry

/-- The height-ball multiplicity summand. -/
noncomputable def completedZeroMultiplicityHeightBallSummand
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  if zetaCompletedZeroCenteredHeight ρ ≤ T then
    (zetaZeroMultiplicity (ρ : ℂ) : ℝ)
  else
    0

/-- Completed-zero multiplicity count in a centered height ball. -/
noncomputable def completedZeroMultiplicityCountingInCenteredHeightBall
    (T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
    completedZeroMultiplicityHeightBallSummand T ρ

/-- Coarse polynomial counting of completed zeros with multiplicity in centered height. -/
theorem exists_completedZeroMultiplicityCounting_height_bound :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  sorry

/-- Polynomial negative-height envelopes are summable over completed zeros once
the decay exponent is chosen beyond the counting degree. -/
theorem summable_completedZero_centeredHeight_negativePower_of_counting_bound
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) := by
  sorry

/-- The spectral transform of a test function. -/
def zetaSpectralTransform : ZetaTestFunction → ℂ → ℂ :=
  zetaLaplaceTransform

/-- The spectral evaluation of an admissible test function. -/
abbrev zetaSpectralEval (φ : ZetaAdmissibleFunction) (z : ℂ) : ℂ :=
  zetaSpectralTransform φ.toZetaTestFunction' z

/-- The spectral transform is the zeta Laplace transform. -/
theorem zetaSpectralTransform_eq_laplace
    (φ : ZetaTestFunction) :
    zetaSpectralTransform φ = Boundary.zetaLaplaceTransform φ := by
  exact Eq.refl _

/-- The spectral evaluation is the zeta Laplace transform evaluation. -/
theorem zetaSpectralEval_eq_laplace
    (φ : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralEval φ z = Boundary.zetaLaplaceTransform φ.toZetaTestFunction' z := by
  exact Eq.refl _

/-- The spectral evaluation of an autocorrelation is the constructed Laplace transform. -/
theorem zetaSpectralEval_autocorrelation
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralTransform (ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z =
      Boundary.zetaLaplaceTransform
        (ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z := by
  exact Eq.refl _

/-- The single zero contribution to the completed zero side. -/
def zetaZeroSideContribution (ρ : ℂ) (φ : ZetaAdmissibleFunction) : ℂ :=
  - (zetaZeroMultiplicity ρ : ℂ) * zetaSpectralEval φ (zetaCenteredZero ρ)

/-- The functional-equation orbit of a centered zero. -/
def zetaZeroOrbitFinset (ρ : ℂ) : Finset ℂ :=
  insert ρ <| insert (-ρ) ∅

/-- Membership in the centered zero orbit is membership in the two reflection faces. -/
theorem zetaZeroOrbitFinset_mem_iff (ρ η : ℂ) :
    η ∈ zetaZeroOrbitFinset ρ ↔ η = ρ ∨ η = -ρ := by
  constructor
  · intro hη
    unfold zetaZeroOrbitFinset at hη
    rcases Finset.mem_insert.mp hη with hleft | hright
    · exact Or.inl hleft
    · have hneg : η = -ρ := by
        exact Finset.mem_singleton.mp hright
      exact Or.inr hneg
  · intro hη
    unfold zetaZeroOrbitFinset
    rcases hη with hleft | hright
    · exact Finset.mem_insert.mpr (Or.inl hleft)
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr hright))

/-- The centered zero orbit contains its positive face. -/
theorem zetaZeroOrbitFinset_mem_self (ρ : ℂ) :
    ρ ∈ zetaZeroOrbitFinset ρ := by
  exact (zetaZeroOrbitFinset_mem_iff ρ ρ).2 (Or.inl rfl)

/-- The centered zero orbit contains its reflected face. -/
theorem zetaZeroOrbitFinset_mem_neg (ρ : ℂ) :
    -ρ ∈ zetaZeroOrbitFinset ρ := by
  exact (zetaZeroOrbitFinset_mem_iff ρ (-ρ)).2 (Or.inr rfl)

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
  exact Eq.refl _

/-- The spectral transform of an autocorrelation is the constructed Laplace transform. -/
theorem zetaSpectralTransform_autocorrelation
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralTransform (ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z =
      Boundary.zetaLaplaceTransform
        (ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z := by
  exact Eq.refl _

/-- The spectral transform is additive. -/
theorem zetaSpectralTransform_add
    (φ ψ : ZetaTestFunction) (z : ℂ)
    (hφ : Integrable (fun t : ℝ => φ t * Complex.exp (z * t)) (volume : Measure ℝ))
    (hψ : Integrable (fun t : ℝ => ψ t * Complex.exp (z * t)) (volume : Measure ℝ)) :
    zetaSpectralTransform (φ + ψ) z =
      zetaSpectralTransform φ z + zetaSpectralTransform ψ z := by
  exact Boundary.zetaLaplaceTransform_add φ ψ z hφ hψ

/-- The spectral transform is homogeneous under scalar multiplication. -/
theorem zetaSpectralTransform_smul
    (a : ℂ) (φ : ZetaTestFunction) (z : ℂ) :
    zetaSpectralTransform (a • φ) z = a * zetaSpectralTransform φ z := by
  exact Boundary.zetaLaplaceTransform_smul a φ z

/-- The spectral transform commutes with finite sums. -/
theorem zetaSpectralTransform_sum
    {α : Type*} [DecidableEq α] (s : Finset α) (φ : α → ZetaTestFunction) (z : ℂ)
    (h : ∀ a ∈ s, Integrable (fun t : ℝ => φ a t * Complex.exp (z * t)) (volume : Measure ℝ)) :
    zetaSpectralTransform (∑ a in s, φ a) z =
      ∑ a in s, zetaSpectralTransform (φ a) z := by
  exact Boundary.zetaLaplaceTransform_sum s φ z h

/-- The spectral transform of an autocorrelation is the explicit Laplace integral. -/
theorem zetaSpectralTransform_autocorrelation_eq_integral
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralTransform (ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z =
      ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t) := by
  change Boundary.zetaLaplaceTransform
      (ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z =
    ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t)
  exact Boundary.zetaLaplaceTransform_autocorrelation f z

/-- The spectral evaluation of an autocorrelation is the explicit Laplace integral. -/
theorem zetaSpectralEval_autocorrelation_eq_integral
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralTransform (ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z =
      ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t) := by
  change Boundary.zetaLaplaceTransform
      (ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z =
    ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t)
  exact Boundary.zetaLaplaceTransform_autocorrelation f z

theorem zetaZeroOrbitContribution_eq_sum (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitContribution ρ φ =
      Finset.sum (zetaZeroOrbitFinset ρ) (fun η => zetaZeroSideContribution η φ) := by
  exact Eq.refl _

theorem zetaZeroOrbitRemainder_eq_tail (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitRemainder ρ φ =
      zetaZeroTail (zetaZeroOrbitFinset ρ) φ := by
  exact Eq.refl _

theorem zetaZeroTail_def (S : Finset ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroTail S φ =
      tsum (fun η : {η : ℂ // ZetaCompletedZero η ∧ η ∉ S} =>
        zetaZeroSideContribution (η : ℂ) φ) := by
  exact Eq.refl _

end
end LFunctions
end Boundary
