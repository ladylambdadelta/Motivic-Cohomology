import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusBase.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusZeta.Owner

/-!
# Boundary zeta transform calculus

This file exposes the classical Mellin/Fourier and zeta-normalization lemmas
that the explicit-formula route needs as upstream transform calculus.

The statements here are not the RH theorem itself. They are the precise
transform and normalization lemmas that later owner files will consume.
-/

namespace Boundary

open scoped FourierTransform
open Real Complex Set MeasureTheory
open AddCircle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Mellin

/-- The zeta Laplace transform commutes with finite sums pointwise. -/
theorem zetaLaplaceTransform_sum_apply
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → LFunctions.ZetaTestFunction)
    (t : ℝ) :
    (∑ a in s, f a).toFun t = ∑ a in s, f a t := by
  induction s using Finset.induction_on with
  | empty =>
      exact rfl
  | @insert a s ha ih =>
      calc
        (∑ a in insert a s, f a).toFun t
            = (f a + ∑ b in s, f b).toFun t := by
                exact congrArg (fun g : LFunctions.ZetaTestFunction => g t)
                  (Finset.sum_insert ha)
        _ = f a t + (∑ b in s, f b).toFun t := by
              rfl
        _ = f a t + ∑ b in s, f b t := by
              exact congrArg (fun x : ℂ => f a t + x) ih
        _ = ∑ a in insert a s, f a t := by
              show f a t + ∑ b in s, f b t = ∑ a in insert a s, f a t
              exact (Finset.sum_insert ha (f := fun a => f a t)).symm

/-- The zeta Laplace transform integrand of a finite sum is the finite sum of integrands. -/
theorem zetaLaplaceTransform_sum_integrand
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → LFunctions.ZetaTestFunction)
    (z : ℂ) :
    (fun t : ℝ => (∑ a in s, f a).toFun t * Complex.exp (z * t)) =
      fun t : ℝ => ∑ a in s, f a t * Complex.exp (z * t) := by
  funext t
  calc
    (∑ a in s, f a).toFun t * Complex.exp (z * t)
        = (∑ a in s, f a t) * Complex.exp (z * t) := by
            exact congrArg (fun x => x * Complex.exp (z * t))
              (zetaLaplaceTransform_sum_apply (s := s) (f := f) t)
    _ = ∑ a in s, f a t * Complex.exp (z * t) := by
          exact Finset.sum_mul (s := s) (f := fun a => f a t) (a := Complex.exp (z * t))

/-- The zeta Laplace transform of the empty sum is zero. -/
theorem zetaLaplaceTransform_sum_empty
    {α : Type*} (f : α → LFunctions.ZetaTestFunction) (z : ℂ) :
    zetaLaplaceTransform (∑ a in (∅ : Finset α), f a) z = 0 := by
  change ∫ t : ℝ, (∑ a in (∅ : Finset α), f a).toFun t * Complex.exp (z * t) = 0
  calc
    ∫ t : ℝ, (∑ a in (∅ : Finset α), f a).toFun t * Complex.exp (z * t)
        = ∫ t : ℝ, (0 : ℂ) := by
            exact integral_congr_ae (Filter.Eventually.of_forall
              (fun t => by exact zero_mul _))
    _ = 0 := by
          exact (integral_zero (α := ℝ) (G := ℂ) (μ := (volume : Measure ℝ)))

/-- The zeta Laplace transform of a finite sum is the sum of transforms. -/
theorem zetaLaplaceTransform_sum_integral
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → LFunctions.ZetaTestFunction)
    (z : ℂ)
    (h : ∀ a ∈ s, Integrable (fun t : ℝ => f a t * Complex.exp (z * t)) (volume : Measure ℝ)) :
    ∫ t : ℝ, ∑ a in s, f a t * Complex.exp (z * t)
      = ∑ a in s, zetaLaplaceTransform (f a) z := by
  exact MeasureTheory.integral_finset_sum
    (s := s)
    (f := fun a t => f a t * Complex.exp (z * t))
    (fun a ha => h a ha)

/-- The zeta Laplace transform commutes with finite sums. -/
theorem zetaLaplaceTransform_sum
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → LFunctions.ZetaTestFunction) (z : ℂ)
    (h : ∀ a ∈ s, Integrable (fun t : ℝ => f a t * Complex.exp (z * t)) (volume : Measure ℝ)) :
    zetaLaplaceTransform (∑ a in s, f a) z =
      ∑ a in s, zetaLaplaceTransform (f a) z := by
  calc
    zetaLaplaceTransform (∑ a in s, f a) z
        = ∫ t : ℝ, (∑ a in s, f a).toFun t * Complex.exp (z * t) := by
            rfl
    _ = ∫ t : ℝ, ∑ a in s, f a t * Complex.exp (z * t) := by
          exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
            congrArg (fun g => g t) (zetaLaplaceTransform_sum_integrand (s := s) f z))
    _ = ∑ a in s, zetaLaplaceTransform (f a) z := by
          exact zetaLaplaceTransform_sum_integral s f z h

/-- The zeta Laplace transform is definitionally stable under pointwise equality. -/
theorem zetaLaplaceTransform_congr
    {φ ψ : LFunctions.ZetaTestFunction}
    (h : ∀ t : ℝ, φ t = ψ t) :
    zetaLaplaceTransform φ = zetaLaplaceTransform ψ := by
  funext z
  unfold zetaLaplaceTransform
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall fun t =>
    congrArg (fun x => x * Complex.exp (z * t)) (h t)

/-- Boundary name for mathlib's Mellin/Fourier bridge. -/
theorem boundary_mellin_eq_fourierIntegral (f : ℝ → E) {s : ℂ} :
    mellin f s =
      𝓕 (fun (u : ℝ) ↦ (Real.exp (-s.re * u) • f (Real.exp (-u)))) (s.im / (2 * π)) := by
  exact mellin_eq_fourierIntegral (f := f) (s := s)

/-- Boundary name for the inverse Mellin/Fourier bridge. -/
theorem boundary_mellinInv_eq_fourierIntegralInv (σ : ℝ) (f : ℂ → E) {x : ℝ} (hx : 0 < x) :
    mellinInv σ f x =
      (x : ℂ) ^ (-σ : ℂ) • 𝓕⁻ (fun (y : ℝ) ↦ f (σ + 2 * π * y * I)) (-Real.log x) := by
  exact mellinInv_eq_fourierIntegralInv (σ := σ) (f := f) (x := x) hx

/-- Boundary name for Mellin inversion. -/
theorem boundary_mellin_inversion (σ : ℝ) (f : ℝ → E) {x : ℝ} (hx : 0 < x)
    [CompleteSpace E] (hf : MellinConvergent f σ) (hFf : Complex.VerticalIntegrable (mellin f) σ)
    (hfx : ContinuousAt f x) :
    mellinInv σ (mellin f) x = f x := by
  exact mellin_inversion (σ := σ) (f := f) (x := x) hx hf hFf hfx

end Mellin

section FourierInterval

theorem boundary_fourierCoeffOn_of_hasDerivAt {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x, x ∈ Set.uIcc a b → HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n =
      1 / (-2 * π * I * n) *
        (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) -
          (b - a) * fourierCoeffOn hab f' n) := by
  exact fourierCoeffOn_of_hasDerivAt (a := a) (b := b)
    (f := f) (f' := f') hab hn hf hf'

/-- Boundary name for the interval version of the Fourier derivative identity. -/
theorem boundary_fourierCoeffOn_of_hasDerivAt_Ioo {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    {n : ℤ} (hn : n ≠ 0)
    (hf : ContinuousOn f (Set.uIcc a b))
    (hff' : ∀ x, x ∈ Set.Ioo (min a b) (max a b) → HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n =
      1 / (-2 * π * I * n) *
        (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) -
          (b - a) * fourierCoeffOn hab f' n) := by
  exact fourierCoeffOn_of_hasDerivAt_Ioo (a := a) (b := b)
    (f := f) (f' := f') hab hn hf hff' hf'

end FourierInterval

end
end Boundary
