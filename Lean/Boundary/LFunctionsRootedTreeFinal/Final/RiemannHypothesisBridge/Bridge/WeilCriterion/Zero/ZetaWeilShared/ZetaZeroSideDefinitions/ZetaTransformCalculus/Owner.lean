import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Inversion
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

/-- Pointwise exponential algebra behind the vertical-line Laplace/Fourier
identification. -/
theorem zetaLaplaceTransform_verticalLine_fourierIntegrand_eq
    (φ : LFunctions.ZetaTestFunction) (σ y t : ℝ) :
    φ t * Complex.exp ((σ + 2 * π * y * Complex.I) * (t : ℂ)) =
      Complex.exp (((-2 * π * t * (-y) : ℝ) : ℂ) * Complex.I) •
        (Complex.exp ((σ : ℂ) * (t : ℂ)) * φ t) := by
  rw [smul_eq_mul]
  simp [Complex.exp_add, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm]

/-- The vertical Laplace slice on `σ + 2π y i` is the real Fourier transform
of the exponentially twisted time kernel, evaluated at `-y`.

This records the sign convention in mathlib's real Fourier transform:
`𝓕 g w = ∫ exp (-2π i t w) • g t`.  Therefore the vertical line
`σ + 2π y i` corresponds to Fourier frequency `-y`. -/
theorem zetaLaplaceTransform_verticalLine_eq_fourierIntegral_expTwist
    (φ : LFunctions.ZetaTestFunction) (σ y : ℝ) :
    zetaLaplaceTransform φ (σ + 2 * π * y * Complex.I) =
      𝓕 (fun t : ℝ => Complex.exp ((σ : ℂ) * (t : ℂ)) * φ t) (-y) := by
  calc
    zetaLaplaceTransform φ (σ + 2 * π * y * Complex.I)
        = ∫ t : ℝ, φ t * Complex.exp ((σ + 2 * π * y * Complex.I) * (t : ℂ)) := by
            rfl
    _ =
        ∫ t : ℝ,
          Complex.exp (((-2 * π * t * (-y) : ℝ) : ℂ) * Complex.I) •
            (Complex.exp ((σ : ℂ) * (t : ℂ)) * φ t) := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
        zetaLaplaceTransform_verticalLine_fourierIntegrand_eq φ σ y t)
    _ =
        𝓕 (fun t : ℝ => Complex.exp ((σ : ℂ) * (t : ℂ)) * φ t) (-y) := by
      exact
        (Real.fourierIntegral_real_eq_integral_exp_smul
          (fun t : ℝ => Complex.exp ((σ : ℂ) * (t : ℂ)) * φ t)
          (-y)).symm

end Mellin

section FourierInversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {f : V → E} {v : V}

/-- Boundary name for Fourier inversion in the convention used by the explicit
formula transform calculus. -/
theorem boundary_fourier_inversion
    [CompleteSpace E]
    (hf : Integrable f)
    (hFf : Integrable (𝓕 f))
    (hfv : ContinuousAt f v) :
    𝓕⁻ (𝓕 f) v = f v := by
  exact MeasureTheory.Integrable.fourier_inversion hf hFf hfv

/-- Boundary name for inverse-Fourier inversion in the convention used by the
explicit formula transform calculus. -/
theorem boundary_fourier_inversion_inv
    [CompleteSpace E]
    (hf : Integrable f)
    (hFf : Integrable (𝓕⁻ f))
    (hfv : ContinuousAt f v) :
    𝓕 (𝓕⁻ f) v = f v := by
  exact MeasureTheory.Integrable.fourier_inversion_inv hf hFf hfv

/-- Real-line specialization of `boundary_fourier_inversion`.

The completed explicit formula uses the logarithmic real variable, so this
wrapper is the form consumed by Paley-Wiener sampling lemmas. -/
theorem boundary_real_fourier_inversion
    [CompleteSpace E]
    {f : ℝ → E} {x : ℝ}
    (hf : Integrable f)
    (hFf : Integrable (𝓕 f))
    (hfx : ContinuousAt f x) :
    𝓕⁻ (𝓕 f) x = f x := by
  exact boundary_fourier_inversion hf hFf hfx

/-- Real Fourier inversion with the reflected frequency convention.

The vertical explicit-formula line naturally produces `y ↦ 𝓕 f (-y)`.
Composing inverse Fourier with the real negation isometry reduces this to the
ordinary inversion theorem. -/
theorem boundary_real_fourier_inversion_reflected
    [CompleteSpace E]
    {f : ℝ → E} {x : ℝ}
    (hf : Integrable f)
    (hFf : Integrable (𝓕 f))
    (hfx : ContinuousAt f x) :
    𝓕⁻ (fun y : ℝ => 𝓕 f (-y)) (-x) = f x := by
  have hcomp :
      𝓕⁻ ((𝓕 f) ∘ LinearIsometryEquiv.neg ℝ) (-x) =
        (𝓕⁻ (𝓕 f)) (LinearIsometryEquiv.neg ℝ (-x)) :=
    fourierIntegralInv_comp_linearIsometry
      (A := LinearIsometryEquiv.neg ℝ)
      (f := 𝓕 f)
      (w := -x)
  have hneg :
      LinearIsometryEquiv.neg ℝ (-x) = x := by
    exact neg_neg x
  have hinv : 𝓕⁻ (𝓕 f) x = f x :=
    boundary_real_fourier_inversion hf hFf hfx
  calc
    𝓕⁻ (fun y : ℝ => 𝓕 f (-y)) (-x) =
        𝓕⁻ ((𝓕 f) ∘ LinearIsometryEquiv.neg ℝ) (-x) := by
      rfl
    _ = (𝓕⁻ (𝓕 f)) (LinearIsometryEquiv.neg ℝ (-x)) :=
      hcomp
    _ = 𝓕⁻ (𝓕 f) x := by
      exact congrArg (fun y : ℝ => 𝓕⁻ (𝓕 f) y) hneg
    _ = f x :=
      hinv

/-- Real-line specialization of `boundary_fourier_inversion_inv`.

This is the inverse-transform orientation useful when a vertical Laplace slice
has first been identified with an inverse Fourier transform. -/
theorem boundary_real_fourier_inversion_inv
    [CompleteSpace E]
    {f : ℝ → E} {x : ℝ}
    (hf : Integrable f)
    (hFf : Integrable (𝓕⁻ f))
    (hfx : ContinuousAt f x) :
    𝓕 (𝓕⁻ f) x = f x := by
  exact boundary_fourier_inversion_inv hf hFf hfx

end FourierInversion

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
