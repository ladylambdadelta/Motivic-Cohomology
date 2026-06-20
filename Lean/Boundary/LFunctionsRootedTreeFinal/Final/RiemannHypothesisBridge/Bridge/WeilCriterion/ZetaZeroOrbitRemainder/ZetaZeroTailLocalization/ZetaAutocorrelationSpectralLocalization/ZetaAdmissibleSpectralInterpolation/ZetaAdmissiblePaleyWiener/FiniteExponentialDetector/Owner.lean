import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusBase.Owner
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Finite exponential distribution detector

This file owns the translate reduction for finite Laplace/exponential
distributions. The remaining separation theorem is the Vandermonde/finite
avoidance step over real translation parameters.
-/

open scoped Real
open MeasureTheory

namespace Boundary
namespace LFunctions
namespace ZetaAdmissibleFunction

noncomputable section

/-- Evaluating a finite Laplace distribution on a translated admissible function rewrites
as the corresponding finite exponential-polynomial sum in the translation parameter. -/
theorem zetaLaplaceTransform_finiteDistribution_translate_sum
    (A : Finset ℂ) (coeff : ℂ → ℂ)
    (c : ℝ) (f : ZetaAdmissibleFunction) :
    (∑ s in A,
        coeff s *
          Boundary.zetaLaplaceTransform
            (ZetaAdmissibleFunction.translate c f).toZetaTestFunction' s) =
      ∑ s in A,
        coeff s *
          (Complex.exp (-(s * (c : ℂ))) *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' s) := by
  exact Finset.sum_congr rfl
    (fun s _hs =>
      calc
        coeff s *
            Boundary.zetaLaplaceTransform
              (ZetaAdmissibleFunction.translate c f).toZetaTestFunction' s =
            coeff s *
              (Complex.exp (-(s * (c : ℂ))) *
                Boundary.zetaLaplaceTransform f.toZetaTestFunction' s) := by
          exact congrArg
            (fun u : ℂ => coeff s * u)
            (Boundary.zetaLaplaceTransform_translate c f s))

/-- If the seed transform is nonzero at a sample, translation only multiplies that sample
by a nonzero exponential character. -/
theorem zetaLaplaceTransform_translate_sample_nonzero
    (c : ℝ) (f : ZetaAdmissibleFunction) (s : ℂ)
    (hf : Boundary.zetaLaplaceTransform f.toZetaTestFunction' s ≠ 0) :
    Boundary.zetaLaplaceTransform
        (ZetaAdmissibleFunction.translate c f).toZetaTestFunction' s ≠ 0 := by
  intro hzero
  have hfactor :
      Complex.exp (-(s * (c : ℂ))) *
          Boundary.zetaLaplaceTransform f.toZetaTestFunction' s = 0 := by
    exact
      (Boundary.zetaLaplaceTransform_translate c f s).symm.trans hzero
  have hexp :
      Complex.exp (-(s * (c : ℂ))) ≠ 0 :=
    Complex.exp_ne_zero (-(s * (c : ℂ)))
  have hfactor_comm :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' s *
          Complex.exp (-(s * (c : ℂ))) = 0 := by
    calc
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' s *
          Complex.exp (-(s * (c : ℂ))) =
          Complex.exp (-(s * (c : ℂ))) *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' s := by
        exact mul_comm
          (Boundary.zetaLaplaceTransform f.toZetaTestFunction' s)
          (Complex.exp (-(s * (c : ℂ))))
      _ = 0 := by
        exact hfactor
  exact hf (eq_zero_of_ne_zero_of_mul_right_eq_zero hexp hfactor_comm)

/-- A nonzero finite exponential-polynomial value for a seed gives an admissible
translate detected by the original finite Laplace distribution. -/
theorem zetaLaplaceTransform_finiteDistribution_detected_by_translate_value
    (A : Finset ℂ) (coeff : ℂ → ℂ)
    (c : ℝ) (f : ZetaAdmissibleFunction)
    (hvalue :
      (∑ s in A,
        coeff s *
          (Complex.exp (-(s * (c : ℂ))) *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' s)) ≠ 0) :
    (∑ s in A,
        coeff s *
          Boundary.zetaLaplaceTransform
            (ZetaAdmissibleFunction.translate c f).toZetaTestFunction' s) ≠ 0 := by
  intro hzero
  have hrewrite :
      (∑ s in A,
          coeff s *
            (Complex.exp (-(s * (c : ℂ))) *
              Boundary.zetaLaplaceTransform f.toZetaTestFunction' s)) = 0 := by
    exact
      (zetaLaplaceTransform_finiteDistribution_translate_sum
        A coeff c f).symm.trans hzero
  exact hvalue hrewrite

/-- If a coefficient and the seed transform at the same sample are both nonzero, their
seeded finite-distribution coefficient is nonzero. -/
theorem zetaLaplaceTransform_seededCoefficient_nonzero
    (coeff : ℂ → ℂ) (f : ZetaAdmissibleFunction) (s : ℂ)
    (hcoeff : coeff s ≠ 0)
    (hf : Boundary.zetaLaplaceTransform f.toZetaTestFunction' s ≠ 0) :
    coeff s * Boundary.zetaLaplaceTransform f.toZetaTestFunction' s ≠ 0 := by
  exact mul_ne_zero hcoeff hf

/-- The existential form of the translate detector once the exponential-polynomial
value has been separated at a real translate. -/
theorem exists_zetaLaplaceTransform_finiteDistribution_detected_by_translate_value
    (A : Finset ℂ) (coeff : ℂ → ℂ)
    (c : ℝ) (f : ZetaAdmissibleFunction)
    (hvalue :
      (∑ s in A,
        coeff s *
          (Complex.exp (-(s * (c : ℂ))) *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' s)) ≠ 0) :
    ∃ g : ZetaAdmissibleFunction,
      (∑ s in A,
          coeff s *
            Boundary.zetaLaplaceTransform g.toZetaTestFunction' s) ≠ 0 := by
  exact
    ⟨ZetaAdmissibleFunction.translate c f,
      zetaLaplaceTransform_finiteDistribution_detected_by_translate_value
        A coeff c f hvalue⟩

/-- Vandermonde finite-moment separation: if all first `n` moments of a seeded finite
exponential distribution vanish at an injective character family, then every seeded
coefficient is zero. -/
theorem zetaFiniteExponentialMoments_zero_forall_seededCoefficient_zero
    {n : ℕ} {χ seededCoeff : Fin n → ℂ}
    (hχ : Function.Injective χ)
    (hzero :
      ∀ k : Fin n,
        (∑ i : Fin n, seededCoeff i * χ i ^ (k : ℕ)) = 0) :
    ∀ i : Fin n, seededCoeff i = 0 := by
  have hcoeff :
      seededCoeff = 0 := by
    exact Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (f := χ) (v := seededCoeff) hχ hzero
  intro i
  exact congrFun hcoeff i

/-- Constructive contrapositive form of the Vandermonde detector: one nonzero seeded
coefficient prevents all first `n` moments from vanishing. -/
theorem zetaFiniteExponentialMoments_not_forall_zero_of_seededCoefficient_nonzero
    {n : ℕ} {χ seededCoeff : Fin n → ℂ}
    (hχ : Function.Injective χ)
    {i₀ : Fin n} (hcoeff : seededCoeff i₀ ≠ 0) :
    ¬
      ∀ k : Fin n,
        (∑ i : Fin n, seededCoeff i * χ i ^ (k : ℕ)) = 0 := by
  intro hzero
  have hcoeff_zero :
      seededCoeff i₀ = 0 :=
    zetaFiniteExponentialMoments_zero_forall_seededCoefficient_zero
      hχ hzero i₀
  exact hcoeff hcoeff_zero

/-- The Vandermonde detector applied to a Laplace-seeded coefficient vector. -/
theorem zetaFiniteExponentialMoments_not_forall_zero_of_laplaceSeed
    {n : ℕ} {χ : Fin n → ℂ} {sample : Fin n → ℂ}
    {coeff : Fin n → ℂ} (f : ZetaAdmissibleFunction)
    (hχ : Function.Injective χ)
    {i₀ : Fin n}
    (hcoeff : coeff i₀ ≠ 0)
    (hf :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i₀) ≠ 0) :
    ¬
      ∀ k : Fin n,
        (∑ i : Fin n,
          (coeff i *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) *
              χ i ^ (k : ℕ)) = 0 := by
  have hseeded :
      (fun i : Fin n =>
        coeff i *
          Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) i₀ ≠ 0 :=
    mul_ne_zero hcoeff hf
  exact
    zetaFiniteExponentialMoments_not_forall_zero_of_seededCoefficient_nonzero
      (χ := χ)
      (seededCoeff := fun i : Fin n =>
        coeff i *
          Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i))
      hχ hseeded

/-- Lagrange recombination of finitely many exponential moments isolates a chosen
seeded coefficient. This is the constructive replacement for extracting a witness from
the negation of universal moment-vanishing. -/
theorem zetaFiniteExponentialMoments_lagrange_recombine_finset
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {χ seededCoeff : ι → ℂ}
    (hχ : Set.InjOn χ (s : Set ι))
    {i₀ : ι} (hi₀ : i₀ ∈ s) :
    ∃ weights : Fin s.card → ℂ,
      (∑ k : Fin s.card,
          weights k *
            (∑ i in s, seededCoeff i * χ i ^ (k : ℕ))) =
        seededCoeff i₀ := by
  let target : ι → ℂ := fun i => if i = i₀ then 1 else 0
  let p : Polynomial ℂ := Lagrange.interpolate s χ target
  have hp : p ∈ Polynomial.degreeLT ℂ s.card := by
    exact Polynomial.mem_degreeLT.mpr
      (Lagrange.degree_interpolate_lt
        (s := s) (v := χ) (r := target) hχ)
  let weights : Fin s.card → ℂ :=
    Polynomial.degreeLTEquiv ℂ s.card ⟨p, hp⟩
  have hkronecker :
      ∀ i : ι,
        i ∈ s →
          (∑ k : Fin s.card, weights k * χ i ^ (k : ℕ)) =
            target i := by
    intro i hi
    calc
      (∑ k : Fin s.card, weights k * χ i ^ (k : ℕ)) =
          p.eval (χ i) := by
        exact (Polynomial.eval_eq_sum_degreeLTEquiv hp (χ i)).symm
      _ = target i := by
        exact
          Lagrange.eval_interpolate_at_node
            (s := s) (v := χ) (r := target) hχ hi
  have hswap :
      (∑ k : Fin s.card,
          weights k *
            (∑ i in s, seededCoeff i * χ i ^ (k : ℕ))) =
        ∑ i in s,
          seededCoeff i *
            (∑ k : Fin s.card, weights k * χ i ^ (k : ℕ)) := by
    calc
      (∑ k : Fin s.card,
          weights k *
            (∑ i in s, seededCoeff i * χ i ^ (k : ℕ))) =
          ∑ k : Fin s.card,
            ∑ i in s,
              weights k * (seededCoeff i * χ i ^ (k : ℕ)) := by
        exact Finset.sum_congr rfl
          (fun k _hk =>
            Finset.mul_sum s
              (fun i => seededCoeff i * χ i ^ (k : ℕ))
              (weights k))
      _ =
          ∑ i in s,
            ∑ k : Fin s.card,
              weights k * (seededCoeff i * χ i ^ (k : ℕ)) := by
        exact Finset.sum_comm
      _ =
          ∑ i in s,
            ∑ k : Fin s.card,
              seededCoeff i * (weights k * χ i ^ (k : ℕ)) := by
        exact Finset.sum_congr rfl
          (fun i _hi =>
            Finset.sum_congr rfl
              (fun k _hk =>
                mul_left_comm (weights k) (seededCoeff i)
                  (χ i ^ (k : ℕ))))
      _ =
          ∑ i in s,
            seededCoeff i *
              (∑ k : Fin s.card, weights k * χ i ^ (k : ℕ)) := by
        exact Finset.sum_congr rfl
          (fun i _hi =>
            (Finset.mul_sum Finset.univ
              (fun k : Fin s.card => weights k * χ i ^ (k : ℕ))
              (seededCoeff i)).symm)
  have htarget_sum :
      (∑ i in s, seededCoeff i * target i) = seededCoeff i₀ := by
    have hsingle :
        (∑ i in s, seededCoeff i * target i) =
          seededCoeff i₀ * target i₀ :=
      Finset.sum_eq_single i₀
        (fun i _hi hne =>
          calc
            seededCoeff i * target i =
                seededCoeff i * 0 := by
              exact congrArg
                (fun u : ℂ => seededCoeff i * u)
                (if_neg hne)
            _ = 0 := by
              exact mul_zero (seededCoeff i))
        (fun hnot => False.elim (hnot hi₀))
    calc
      (∑ i in s, seededCoeff i * target i) =
          seededCoeff i₀ * target i₀ := by
        exact hsingle
      _ = seededCoeff i₀ * 1 := by
        exact congrArg
          (fun u : ℂ => seededCoeff i₀ * u)
          (if_pos rfl)
      _ = seededCoeff i₀ := by
        exact mul_one (seededCoeff i₀)
  exact
    ⟨weights,
      calc
        (∑ k : Fin s.card,
            weights k *
              (∑ i in s, seededCoeff i * χ i ^ (k : ℕ))) =
            ∑ i in s,
              seededCoeff i *
                (∑ k : Fin s.card, weights k * χ i ^ (k : ℕ)) := by
          exact hswap
        _ = ∑ i in s, seededCoeff i * target i := by
          exact Finset.sum_congr rfl
            (fun i hi =>
              congrArg
                (fun u : ℂ => seededCoeff i * u)
                (hkronecker i hi))
        _ = seededCoeff i₀ := by
          exact htarget_sum⟩

/-- The real-translation character attached to a complex sample at unit step. -/
def zetaUnitTranslateCharacter (s : ℂ) : ℂ :=
  Complex.exp (-s)

/-- The real-translation character attached to a complex sample at scale `δ`. -/
def zetaScaledTranslateCharacter (δ : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-(s * (δ : ℂ)))

/-- The unit translate character is the scaled translate character at scale `1`. -/
theorem zetaUnitTranslateCharacter_eq_scaled_one (s : ℂ) :
    zetaUnitTranslateCharacter s = zetaScaledTranslateCharacter 1 s := by
  calc
    zetaUnitTranslateCharacter s =
        Complex.exp (-s) := by
      rfl
    _ = Complex.exp (-(s * (1 : ℂ))) := by
      exact congrArg Complex.exp
        (calc
          -s = -(s * (1 : ℂ)) := by
            exact congrArg Neg.neg (mul_one s).symm)
    _ = zetaScaledTranslateCharacter 1 s := by
      rfl

/-- Powers of the unit translate character are the exponential characters at integer
translation times. -/
theorem zetaUnitTranslateCharacter_pow
    (s : ℂ) (k : ℕ) :
    zetaUnitTranslateCharacter s ^ k =
      Complex.exp (-(s * (k : ℂ))) := by
  calc
    zetaUnitTranslateCharacter s ^ k =
        Complex.exp (-s) ^ k := by
      rfl
    _ = Complex.exp ((k : ℂ) * (-s)) := by
      exact (Complex.exp_nat_mul (-s) k).symm
    _ = Complex.exp (-(s * (k : ℂ))) := by
      exact congrArg Complex.exp
        (calc
          (k : ℂ) * (-s) = -(k * s) := by
            exact mul_neg (k : ℂ) s
          _ = -(s * (k : ℂ)) := by
            exact congrArg Neg.neg (mul_comm (k : ℂ) s))

/-- Vandermonde separation for the unit real-translation character. The remaining
analytic work is to build a seed nonzero on the finite sample support and prove the
character map is injective for the chosen real translation scale. -/
theorem zetaUnitTranslateMoments_not_forall_zero_of_laplaceSeed
    {n : ℕ} {sample : Fin n → ℂ}
    {coeff : Fin n → ℂ} (f : ZetaAdmissibleFunction)
    (hχ : Function.Injective (fun i : Fin n => zetaUnitTranslateCharacter (sample i)))
    {i₀ : Fin n}
    (hcoeff : coeff i₀ ≠ 0)
    (hf :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i₀) ≠ 0) :
    ¬
      ∀ k : Fin n,
        (∑ i : Fin n,
          (coeff i *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) *
              zetaUnitTranslateCharacter (sample i) ^ (k : ℕ)) = 0 := by
  exact
    zetaFiniteExponentialMoments_not_forall_zero_of_laplaceSeed
      (χ := fun i : Fin n => zetaUnitTranslateCharacter (sample i))
      (sample := sample)
      (coeff := coeff)
      f hχ hcoeff hf

/-- Powers of the scaled translate character are the exponential characters at integer
multiples of the chosen real scale. -/
theorem zetaScaledTranslateCharacter_pow
    (δ : ℝ) (s : ℂ) (k : ℕ) :
    zetaScaledTranslateCharacter δ s ^ k =
      Complex.exp (-(s * ((k : ℝ) * δ : ℝ))) := by
  calc
    zetaScaledTranslateCharacter δ s ^ k =
        Complex.exp (-(s * (δ : ℂ))) ^ k := by
      rfl
    _ = Complex.exp ((k : ℂ) * (-(s * (δ : ℂ)))) := by
      exact (Complex.exp_nat_mul (-(s * (δ : ℂ))) k).symm
    _ = Complex.exp (-(s * ((k : ℝ) * δ : ℝ))) := by
      exact congrArg Complex.exp
        (calc
          (k : ℂ) * (-(s * (δ : ℂ))) =
              -((k : ℂ) * (s * (δ : ℂ))) := by
            exact mul_neg (k : ℂ) (s * (δ : ℂ))
          _ = -(s * ((k : ℂ) * (δ : ℂ))) := by
            exact congrArg Neg.neg
              (calc
                (k : ℂ) * (s * (δ : ℂ)) =
                    s * ((k : ℂ) * (δ : ℂ)) := by
                  exact mul_left_comm (k : ℂ) s (δ : ℂ))
          _ = -(s * (((k : ℝ) * δ : ℝ) : ℂ)) := by
            exact congrArg (fun u : ℂ => -(s * u))
              (Complex.ofReal_mul (k : ℝ) δ).symm)

/-- Vandermonde separation for any real scale whose translate characters are injective
on the indexed finite sample. -/
theorem zetaScaledTranslateMoments_not_forall_zero_of_laplaceSeed
    {n : ℕ} {sample : Fin n → ℂ}
    {coeff : Fin n → ℂ} (δ : ℝ) (f : ZetaAdmissibleFunction)
    (hχ : Function.Injective (fun i : Fin n => zetaScaledTranslateCharacter δ (sample i)))
    {i₀ : Fin n}
    (hcoeff : coeff i₀ ≠ 0)
    (hf :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i₀) ≠ 0) :
    ¬
      ∀ k : Fin n,
        (∑ i : Fin n,
          (coeff i *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) *
              zetaScaledTranslateCharacter δ (sample i) ^ (k : ℕ)) = 0 := by
  exact
    zetaFiniteExponentialMoments_not_forall_zero_of_laplaceSeed
      (χ := fun i : Fin n => zetaScaledTranslateCharacter δ (sample i))
      (sample := sample)
      (coeff := coeff)
      f hχ hcoeff hf

/-- The scaled translate character on a real sample, written as a real exponential. -/
def zetaRealScaledTranslateCharacter (δ : ℝ) (x : ℝ) : ℂ :=
  (Real.exp (-(x * δ)) : ℂ)

/-- Real samples embedded in `ℂ` have the expected scaled translate character. -/
theorem zetaScaledTranslateCharacter_ofReal
    (δ x : ℝ) :
    zetaScaledTranslateCharacter δ (x : ℂ) =
      zetaRealScaledTranslateCharacter δ x := by
  calc
    zetaScaledTranslateCharacter δ (x : ℂ) =
        Complex.exp (-((x : ℂ) * (δ : ℂ))) := by
      rfl
    _ = Complex.exp (((-(x * δ) : ℝ) : ℂ)) := by
      exact congrArg Complex.exp
        (calc
          -((x : ℂ) * (δ : ℂ)) =
              -(((x * δ : ℝ) : ℂ)) := by
            exact congrArg Neg.neg (Complex.ofReal_mul x δ).symm
          _ = ((-(x * δ) : ℝ) : ℂ) := by
            exact (Complex.ofReal_neg (x * δ)).symm)
    _ = (Real.exp (-(x * δ)) : ℂ) := by
      exact (Complex.ofReal_exp (-(x * δ))).symm
    _ = zetaRealScaledTranslateCharacter δ x := by
      rfl

/-- The real scaled translate character is injective on an injective real finite sample
whenever the scale is nonzero. -/
theorem zetaRealScaledTranslateCharacter_injective
    {n : ℕ} {x : Fin n → ℝ} {δ : ℝ}
    (hx : Function.Injective x) (hδ : δ ≠ 0) :
    Function.Injective (fun i : Fin n => zetaRealScaledTranslateCharacter δ (x i)) := by
  intro i j hij
  have hre :
      Real.exp (-(x i * δ)) = Real.exp (-(x j * δ)) := by
    exact Complex.ofReal_injective hij
  have harg :
      -(x i * δ) = -(x j * δ) :=
    Real.exp_injective hre
  have hmul :
      x i * δ = x j * δ :=
    neg_injective harg
  have hxij :
      x i = x j :=
    mul_right_cancel₀ hδ hmul
  exact hx hxij

/-- Real-valued finite samples have injective scaled complex translate characters at
every nonzero real scale. -/
theorem zetaScaledTranslateCharacter_ofReal_injective
    {n : ℕ} {x : Fin n → ℝ} {δ : ℝ}
    (hx : Function.Injective x) (hδ : δ ≠ 0) :
    Function.Injective
      (fun i : Fin n => zetaScaledTranslateCharacter δ (x i : ℂ)) := by
  intro i j hij
  have hreal :
      zetaRealScaledTranslateCharacter δ (x i) =
        zetaRealScaledTranslateCharacter δ (x j) := by
    calc
      zetaRealScaledTranslateCharacter δ (x i) =
          zetaScaledTranslateCharacter δ (x i : ℂ) := by
        exact (zetaScaledTranslateCharacter_ofReal δ (x i)).symm
      _ = zetaScaledTranslateCharacter δ (x j : ℂ) := by
        exact hij
      _ = zetaRealScaledTranslateCharacter δ (x j) := by
        exact zetaScaledTranslateCharacter_ofReal δ (x j)
  exact zetaRealScaledTranslateCharacter_injective hx hδ hreal

/-- Vandermonde separation for real finite samples at any nonzero real translation scale. -/
theorem zetaRealScaledTranslateMoments_not_forall_zero_of_laplaceSeed
    {n : ℕ} {x : Fin n → ℝ}
    {coeff : Fin n → ℂ} (δ : ℝ) (f : ZetaAdmissibleFunction)
    (hx : Function.Injective x) (hδ : δ ≠ 0)
    {i₀ : Fin n}
    (hcoeff : coeff i₀ ≠ 0)
    (hf :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' (x i₀ : ℂ) ≠ 0) :
    ¬
      ∀ k : Fin n,
        (∑ i : Fin n,
          (coeff i *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' (x i : ℂ)) *
              zetaScaledTranslateCharacter δ (x i : ℂ) ^ (k : ℕ)) = 0 := by
  exact
    zetaScaledTranslateMoments_not_forall_zero_of_laplaceSeed
      (δ := δ)
      (sample := fun i : Fin n => (x i : ℂ))
      (coeff := coeff)
      f
      (zetaScaledTranslateCharacter_ofReal_injective hx hδ)
      hcoeff hf

/-- Real coordinate of the scaled translate exponent. -/
theorem zetaScaledTranslateExponent_re
    (δ : ℝ) (s : ℂ) :
    (-(s * (δ : ℂ))).re = -(s.re * δ) := by
  calc
    (-(s * (δ : ℂ))).re =
        -(s * (δ : ℂ)).re := by
      exact Complex.neg_re (s * (δ : ℂ))
    _ = -(s.re * (δ : ℂ).re - s.im * (δ : ℂ).im) := by
      exact congrArg Neg.neg (Complex.mul_re s (δ : ℂ))
    _ = -(s.re * δ - s.im * (δ : ℂ).im) := by
      exact congrArg
        (fun u : ℝ => -(s.re * u - s.im * (δ : ℂ).im))
        (Complex.ofReal_re δ)
    _ = -(s.re * δ - s.im * 0) := by
      exact congrArg
        (fun u : ℝ => -(s.re * δ - s.im * u))
        (Complex.ofReal_im δ)
    _ = -(s.re * δ - 0) := by
      exact congrArg
        (fun u : ℝ => -(s.re * δ - u))
        (mul_zero s.im)
    _ = -(s.re * δ) := by
      exact congrArg Neg.neg (sub_zero (s.re * δ))

/-- Equality of scaled translate characters at a nonzero scale forces equality of real
parts. -/
theorem zetaScaledTranslateCharacter_eq_forces_re_eq
    {δ : ℝ} (hδ : δ ≠ 0) {s t : ℂ}
    (h :
      zetaScaledTranslateCharacter δ s =
        zetaScaledTranslateCharacter δ t) :
    s.re = t.re := by
  have habs :
      Complex.abs (Complex.exp (-(s * (δ : ℂ)))) =
        Complex.abs (Complex.exp (-(t * (δ : ℂ)))) := by
    exact congrArg Complex.abs h
  have hre_exp :
      (-(s * (δ : ℂ))).re = (-(t * (δ : ℂ))).re :=
    Complex.abs_exp_eq_iff_re_eq.mp habs
  have hscaled_neg :
      -(s.re * δ) = -(t.re * δ) := by
    calc
      -(s.re * δ) =
          (-(s * (δ : ℂ))).re := by
        exact (zetaScaledTranslateExponent_re δ s).symm
      _ = (-(t * (δ : ℂ))).re := by
        exact hre_exp
      _ = -(t.re * δ) := by
        exact zetaScaledTranslateExponent_re δ t
  have hscaled :
      s.re * δ = t.re * δ :=
    neg_injective hscaled_neg
  exact mul_right_cancel₀ hδ hscaled

/-- Nonzero real scale separates any pair with distinct real parts. -/
theorem zetaScaledTranslateCharacter_ne_of_re_ne
    {δ : ℝ} (hδ : δ ≠ 0) {s t : ℂ}
    (hre : s.re ≠ t.re) :
    zetaScaledTranslateCharacter δ s ≠
      zetaScaledTranslateCharacter δ t := by
  intro h
  exact hre (zetaScaledTranslateCharacter_eq_forces_re_eq hδ h)

/-- Equality of scaled translate characters is exactly equality of scaled exponents
modulo an integral complex-exponential period. -/
theorem zetaScaledTranslateCharacter_eq_iff_exists_period
    (δ : ℝ) (s t : ℂ) :
    zetaScaledTranslateCharacter δ s =
        zetaScaledTranslateCharacter δ t ↔
      ∃ n : ℤ,
        -(s * (δ : ℂ)) =
          -(t * (δ : ℂ)) + n * (2 * Real.pi * Complex.I) := by
  exact Complex.exp_eq_exp_iff_exists_int

/-- If no distinct indexed samples have scaled exponents differing by an integral
`2πi` period, then their scaled translate characters are injective. -/
theorem zetaScaledTranslateCharacter_injective_of_no_period_collisions
    {n : ℕ} {sample : Fin n → ℂ} {δ : ℝ}
    (hno :
      ∀ i j : Fin n,
        i ≠ j →
          ∀ m : ℤ,
            -(sample i * (δ : ℂ)) ≠
              -(sample j * (δ : ℂ)) + m * (2 * Real.pi * Complex.I)) :
    Function.Injective
      (fun i : Fin n => zetaScaledTranslateCharacter δ (sample i)) := by
  intro i j hχ
  exact
    if hij : i = j then
      hij
    else
      match
        (zetaScaledTranslateCharacter_eq_iff_exists_period
          δ (sample i) (sample j)).mp hχ with
      | ⟨m, hm⟩ =>
          False.elim (hno i j hij m hm)

/-- A period collision between scaled translate exponents is equivalently a period
collision for the scaled sample difference. -/
theorem zetaScaledTranslateExponent_period_to_difference
    {δ : ℝ} {s t : ℂ} {m : ℤ}
    (h :
      -(s * (δ : ℂ)) =
        -(t * (δ : ℂ)) + m * (2 * Real.pi * Complex.I)) :
    (t - s) * (δ : ℂ) =
      m * (2 * Real.pi * Complex.I) := by
  let p : ℂ := m * (2 * Real.pi * Complex.I)
  have hadd :
      t * (δ : ℂ) + (-(s * (δ : ℂ))) = p := by
    calc
      t * (δ : ℂ) + (-(s * (δ : ℂ))) =
          t * (δ : ℂ) + (-(t * (δ : ℂ)) + p) := by
        exact congrArg (fun u : ℂ => t * (δ : ℂ) + u) h
      _ = (t * (δ : ℂ) + -(t * (δ : ℂ))) + p := by
        exact (add_assoc (t * (δ : ℂ)) (-(t * (δ : ℂ))) p).symm
      _ = 0 + p := by
        exact congrArg (fun u : ℂ => u + p) (add_neg_cancel (t * (δ : ℂ)))
      _ = p := by
        exact zero_add p
  calc
    (t - s) * (δ : ℂ) =
        t * (δ : ℂ) - s * (δ : ℂ) := by
      exact sub_mul t s (δ : ℂ)
    _ = t * (δ : ℂ) + (-(s * (δ : ℂ))) := by
      rfl
    _ = p := by
      exact hadd
    _ = m * (2 * Real.pi * Complex.I) := by
      rfl

/-- Real coordinate of a scaled complex difference. -/
theorem zetaScaledDifference_re
    (δ : ℝ) (d : ℂ) :
    (d * (δ : ℂ)).re = d.re * δ := by
  calc
    (d * (δ : ℂ)).re =
        d.re * (δ : ℂ).re - d.im * (δ : ℂ).im := by
      exact Complex.mul_re d (δ : ℂ)
    _ = d.re * δ - d.im * (δ : ℂ).im := by
      exact congrArg
        (fun u : ℝ => d.re * u - d.im * (δ : ℂ).im)
        (Complex.ofReal_re δ)
    _ = d.re * δ - d.im * 0 := by
      exact congrArg
        (fun u : ℝ => d.re * δ - d.im * u)
        (Complex.ofReal_im δ)
    _ = d.re * δ - 0 := by
      exact congrArg
        (fun u : ℝ => d.re * δ - u)
        (mul_zero d.im)
    _ = d.re * δ := by
      exact sub_zero (d.re * δ)

/-- Imaginary coordinate of a scaled complex difference. -/
theorem zetaScaledDifference_im
    (δ : ℝ) (d : ℂ) :
    (d * (δ : ℂ)).im = d.im * δ := by
  calc
    (d * (δ : ℂ)).im =
        d.re * (δ : ℂ).im + d.im * (δ : ℂ).re := by
      exact Complex.mul_im d (δ : ℂ)
    _ = d.re * 0 + d.im * (δ : ℂ).re := by
      exact congrArg
        (fun u : ℝ => d.re * u + d.im * (δ : ℂ).re)
        (Complex.ofReal_im δ)
    _ = 0 + d.im * (δ : ℂ).re := by
      exact congrArg
        (fun u : ℝ => u + d.im * (δ : ℂ).re)
        (mul_zero d.re)
    _ = d.im * (δ : ℂ).re := by
      exact zero_add (d.im * (δ : ℂ).re)
    _ = d.im * δ := by
      exact congrArg (fun u : ℝ => d.im * u) (Complex.ofReal_re δ)

/-- Real coordinate of the integral `2πi` period. -/
theorem zetaIntegerTwoPiIPeriod_re
    (m : ℤ) :
    (m * (2 * Real.pi * Complex.I) : ℂ).re = 0 := by
  let q : ℂ := ((2 * Real.pi : ℝ) : ℂ) * Complex.I
  have htwopi : ((2 * Real.pi : ℝ) : ℂ) = (2 * Real.pi : ℂ) :=
    Complex.ofReal_mul 2 Real.pi
  have hqre : q.re = 0 := by
    calc
      q.re =
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I).re := by
        rfl
      _ = -(((2 * Real.pi : ℝ) : ℂ).im) := by
        exact Complex.mul_I_re ((2 * Real.pi : ℝ) : ℂ)
      _ = -0 := by
        exact congrArg Neg.neg (Complex.ofReal_im (2 * Real.pi))
      _ = 0 := by
        exact neg_zero
  calc
    (m * (2 * Real.pi * Complex.I) : ℂ).re =
        ((m : ℂ) * q).re := by
      exact congrArg
        (fun u : ℂ => ((m : ℂ) * (u * Complex.I)).re)
        htwopi.symm
    _ = (m : ℂ).re * q.re - (m : ℂ).im * q.im := by
      exact Complex.mul_re (m : ℂ) q
    _ = (m : ℂ).re * 0 - (m : ℂ).im * q.im := by
      exact congrArg
        (fun u : ℝ => (m : ℂ).re * u - (m : ℂ).im * q.im)
        hqre
    _ = 0 - (m : ℂ).im * q.im := by
      exact congrArg
        (fun u : ℝ => u - (m : ℂ).im * q.im)
        (mul_zero (m : ℂ).re)
    _ = 0 - 0 * q.im := by
      exact congrArg (fun u : ℝ => 0 - u * q.im) (Complex.intCast_im m)
    _ = 0 - 0 := by
      exact congrArg (fun u : ℝ => 0 - u) (zero_mul q.im)
    _ = 0 := by
      exact sub_zero 0

/-- Imaginary coordinate of the integral `2πi` period. -/
theorem zetaIntegerTwoPiIPeriod_im
    (m : ℤ) :
    (m * (2 * Real.pi * Complex.I) : ℂ).im =
      (m : ℝ) * (2 * Real.pi) := by
  let q : ℂ := ((2 * Real.pi : ℝ) : ℂ) * Complex.I
  have htwopi : ((2 * Real.pi : ℝ) : ℂ) = (2 * Real.pi : ℂ) :=
    Complex.ofReal_mul 2 Real.pi
  have hqim : q.im = 2 * Real.pi := by
    calc
      q.im =
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I).im := by
        rfl
      _ = ((2 * Real.pi : ℝ) : ℂ).re := by
        exact Complex.mul_I_im ((2 * Real.pi : ℝ) : ℂ)
      _ = 2 * Real.pi := by
        exact Complex.ofReal_re (2 * Real.pi)
  calc
    (m * (2 * Real.pi * Complex.I) : ℂ).im =
        ((m : ℂ) * q).im := by
      exact congrArg
        (fun u : ℂ => ((m : ℂ) * (u * Complex.I)).im)
        htwopi.symm
    _ = (m : ℂ).re * q.im + (m : ℂ).im * q.re := by
      exact Complex.mul_im (m : ℂ) q
    _ = (m : ℂ).re * q.im + 0 * q.re := by
      exact congrArg
        (fun u : ℝ => (m : ℂ).re * q.im + u * q.re)
        (Complex.intCast_im m)
    _ = (m : ℂ).re * q.im + 0 := by
      exact congrArg (fun u : ℝ => (m : ℂ).re * q.im + u) (zero_mul q.re)
    _ = (m : ℂ).re * q.im := by
      exact add_zero ((m : ℂ).re * q.im)
    _ = (m : ℂ).re * (2 * Real.pi) := by
      exact congrArg (fun u : ℝ => (m : ℂ).re * u) hqim
    _ = (m : ℝ) * (2 * Real.pi) := by
      exact congrArg (fun u : ℝ => u * (2 * Real.pi)) (Complex.intCast_re m)

/-- Real-coordinate consequence of a scaled difference-period collision. -/
theorem zetaScaledDifference_period_re_eq_zero
    {δ : ℝ} {d : ℂ} {m : ℤ}
    (h :
      d * (δ : ℂ) = m * (2 * Real.pi * Complex.I)) :
    d.re * δ = 0 := by
  calc
    d.re * δ =
        (d * (δ : ℂ)).re := by
      exact (zetaScaledDifference_re δ d).symm
    _ = (m * (2 * Real.pi * Complex.I) : ℂ).re := by
      exact congrArg Complex.re h
    _ = 0 := by
      exact zetaIntegerTwoPiIPeriod_re m

/-- Imaginary-coordinate consequence of a scaled difference-period collision. -/
theorem zetaScaledDifference_period_im_eq_int_two_pi
    {δ : ℝ} {d : ℂ} {m : ℤ}
    (h :
      d * (δ : ℂ) = m * (2 * Real.pi * Complex.I)) :
    d.im * δ = (m : ℝ) * (2 * Real.pi) := by
  calc
    d.im * δ =
        (d * (δ : ℂ)).im := by
      exact (zetaScaledDifference_im δ d).symm
    _ = (m * (2 * Real.pi * Complex.I) : ℂ).im := by
      exact congrArg Complex.im h
    _ = (m : ℝ) * (2 * Real.pi) := by
      exact zetaIntegerTwoPiIPeriod_im m

/-- If a scaled difference is an integral `2πi` period at a nonzero real scale, then
the real coordinate of the difference is zero. -/
theorem zetaScaledDifference_period_forces_re_zero
    {δ : ℝ} {d : ℂ} {m : ℤ}
    (hδ : δ ≠ 0)
    (h :
      d * (δ : ℂ) = m * (2 * Real.pi * Complex.I)) :
    d.re = 0 := by
  have hscaled :
      d.re * δ = 0 :=
    zetaScaledDifference_period_re_eq_zero h
  have hscaled_zero :
      d.re * δ = 0 * δ := by
    calc
      d.re * δ = 0 := by
        exact hscaled
      _ = 0 * δ := by
        exact (zero_mul δ).symm
  exact mul_right_cancel₀ hδ hscaled_zero

/-- A nonzero real coordinate prevents a scaled difference from being an integral
`2πi` period. -/
theorem zetaScaledDifference_ne_period_of_re_ne_zero
    {δ : ℝ} {d : ℂ}
    (hδ : δ ≠ 0)
    (hre : d.re ≠ 0) :
    ∀ m : ℤ,
      d * (δ : ℂ) ≠ m * (2 * Real.pi * Complex.I) := by
  intro m hperiod
  exact hre (zetaScaledDifference_period_forces_re_zero hδ hperiod)

/-- If the real coordinate is zero, period avoidance is exactly the real imaginary
coordinate avoiding the integral `2π` lattice. -/
theorem zetaScaledDifference_ne_period_of_im_ne_int_two_pi
    {δ : ℝ} {d : ℂ}
    (him :
      ∀ m : ℤ,
        d.im * δ ≠ (m : ℝ) * (2 * Real.pi)) :
    ∀ m : ℤ,
      d * (δ : ℂ) ≠ m * (2 * Real.pi * Complex.I) := by
  intro m hperiod
  exact him m (zetaScaledDifference_period_im_eq_int_two_pi hperiod)

/-- A nonzero real number smaller in absolute value than every nonzero `2πℤ` lattice
point avoids the whole lattice. -/
theorem zetaReal_ne_int_two_pi_of_abs_lt_nonzero_lattice
    {x : ℝ}
    (hx : x ≠ 0)
    (hsmall :
      ∀ m : ℤ,
        m ≠ 0 →
          |x| < |(m : ℝ) * (2 * Real.pi)|) :
    ∀ m : ℤ,
      x ≠ (m : ℝ) * (2 * Real.pi) := by
  intro m hx_eq
  exact
    match eq_or_ne m 0 with
    | Or.inl hm =>
        have hm_cast_zero :
            (m : ℝ) = 0 := by
          calc
            (m : ℝ) = ((0 : ℤ) : ℝ) := by
              exact congrArg (fun u : ℤ => (u : ℝ)) hm
            _ = 0 := by
              exact Int.cast_zero
        have hlattice_zero :
            (m : ℝ) * (2 * Real.pi) = 0 := by
          calc
            (m : ℝ) * (2 * Real.pi) =
                0 * (2 * Real.pi) := by
              exact congrArg (fun u : ℝ => u * (2 * Real.pi)) hm_cast_zero
            _ = 0 := by
              exact zero_mul (2 * Real.pi)
        have hx_zero :
            x = 0 := by
          calc
            x = (m : ℝ) * (2 * Real.pi) := by
              exact hx_eq
            _ = 0 := by
              exact hlattice_zero
        False.elim (hx hx_zero)
    | Or.inr hm =>
        have habs_eq :
            |x| = |(m : ℝ) * (2 * Real.pi)| := by
          exact congrArg abs hx_eq
        have hlt :
            |(m : ℝ) * (2 * Real.pi)| <
              |(m : ℝ) * (2 * Real.pi)| := by
          exact Eq.subst
            (motive := fun u : ℝ =>
              u < |(m : ℝ) * (2 * Real.pi)|)
            habs_eq
            (hsmall m hm)
        False.elim ((lt_irrefl |(m : ℝ) * (2 * Real.pi)|) hlt)

/-- A small nonzero imaginary scaled coordinate avoids the integral `2π` lattice. -/
theorem zetaScaledDifference_im_ne_int_two_pi_of_abs_lt_nonzero_lattice
    {δ : ℝ} {d : ℂ}
    (himδ : d.im * δ ≠ 0)
    (hsmall :
      ∀ m : ℤ,
        m ≠ 0 →
          |d.im * δ| < |(m : ℝ) * (2 * Real.pi)|) :
    ∀ m : ℤ,
      d.im * δ ≠ (m : ℝ) * (2 * Real.pi) := by
  exact
    zetaReal_ne_int_two_pi_of_abs_lt_nonzero_lattice
      (x := d.im * δ)
      himδ
      hsmall

/-- A nonzero imaginary difference at a nonzero real scale gives a nonzero scaled
imaginary coordinate. -/
theorem zetaScaledDifference_im_mul_ne_zero
    {δ : ℝ} {d : ℂ}
    (him : d.im ≠ 0) (hδ : δ ≠ 0) :
    d.im * δ ≠ 0 := by
  exact mul_ne_zero him hδ

/-- A nonzero imaginary coordinate which is small relative to every nonzero lattice
point gives the imaginary-lattice separation branch. -/
theorem zetaScaledDifference_im_lattice_separated_of_small
    {δ : ℝ} {d : ℂ}
    (hδ : δ ≠ 0)
    (him : d.im ≠ 0)
    (hsmall :
      ∀ m : ℤ,
        m ≠ 0 →
          |d.im * δ| < |(m : ℝ) * (2 * Real.pi)|) :
    ∀ m : ℤ,
      d.im * δ ≠ (m : ℝ) * (2 * Real.pi) := by
  exact
    zetaScaledDifference_im_ne_int_two_pi_of_abs_lt_nonzero_lattice
      (δ := δ)
      (d := d)
      (zetaScaledDifference_im_mul_ne_zero him hδ)
      hsmall

/-- Every nonzero integral `2π` lattice point has absolute value at least `2π`. -/
theorem zetaIntegerTwoPi_abs_lower_bound
    (m : ℤ) (hm : m ≠ 0) :
    2 * Real.pi ≤ |(m : ℝ) * (2 * Real.pi)| := by
  have htwopi_nonneg :
      0 ≤ 2 * Real.pi :=
    Real.two_pi_pos.le
  have hone_int :
      (1 : ℤ) ≤ |m| :=
    Int.one_le_abs hm
  have hone_real :
      (1 : ℝ) ≤ |(m : ℝ)| := by
    calc
      (1 : ℝ) = ((1 : ℤ) : ℝ) := by
        exact Int.cast_one.symm
      _ ≤ ((|m| : ℤ) : ℝ) := by
        exact Int.cast_le.mpr hone_int
      _ = |(m : ℝ)| := by
        exact Int.cast_abs
  have hscaled :
      1 * (2 * Real.pi) ≤ |(m : ℝ)| * (2 * Real.pi) :=
    mul_le_mul_of_nonneg_right hone_real htwopi_nonneg
  calc
    2 * Real.pi = 1 * (2 * Real.pi) := by
      exact (one_mul (2 * Real.pi)).symm
    _ ≤ |(m : ℝ)| * (2 * Real.pi) := by
      exact hscaled
    _ = |(m : ℝ)| * |(2 * Real.pi)| := by
      exact congrArg
        (fun u : ℝ => |(m : ℝ)| * u)
        (abs_of_nonneg htwopi_nonneg).symm
    _ = |(m : ℝ) * (2 * Real.pi)| := by
      exact (abs_mul (m : ℝ) (2 * Real.pi)).symm

/-- A scaled imaginary coordinate of absolute value less than `2π` avoids the nonzero
integral lattice points. -/
theorem zetaScaledDifference_im_lattice_separated_of_abs_lt_two_pi
    {δ : ℝ} {d : ℂ}
    (hδ : δ ≠ 0)
    (him : d.im ≠ 0)
    (hsmall : |d.im * δ| < 2 * Real.pi) :
    ∀ m : ℤ,
      d.im * δ ≠ (m : ℝ) * (2 * Real.pi) := by
  exact
    zetaScaledDifference_im_lattice_separated_of_small
      (δ := δ)
      (d := d)
      hδ
      him
      (fun m hm =>
        lt_of_lt_of_le hsmall
          (zetaIntegerTwoPi_abs_lower_bound m hm))

/-- Injective samples with a small-scale bound on equal-real-coordinate differences
have no scaled integral `2πi` difference-period collisions. -/
theorem zetaScaledTranslateDifference_ne_period_of_equal_re_small
    {n : ℕ} {sample : Fin n → ℂ} {δ : ℝ}
    (hsample : Function.Injective sample)
    (hδ : δ ≠ 0)
    (hsmall :
      ∀ i j : Fin n,
        i ≠ j →
          (sample j - sample i).re = 0 →
            ∀ m : ℤ,
              m ≠ 0 →
                |(sample j - sample i).im * δ| <
                  |(m : ℝ) * (2 * Real.pi)|) :
    ∀ i j : Fin n,
      i ≠ j →
        ∀ m : ℤ,
          (sample j - sample i) * (δ : ℂ) ≠
            m * (2 * Real.pi * Complex.I) := by
  intro i j hij m hperiod
  let d : ℂ := sample j - sample i
  have hre_zero :
      d.re = 0 :=
    zetaScaledDifference_period_forces_re_zero
      (δ := δ)
      (d := d)
      hδ
      hperiod
  have him_ne :
      d.im ≠ 0 := by
    intro him_zero
    have hd_zero :
        d = 0 :=
      Complex.ext hre_zero him_zero
    have hsample_eq :
        sample j = sample i :=
      sub_eq_zero.mp hd_zero
    have hji :
        j = i :=
      hsample hsample_eq
    exact hij hji.symm
  have him_sep :
      ∀ q : ℤ,
        d.im * δ ≠ (q : ℝ) * (2 * Real.pi) :=
    zetaScaledDifference_im_lattice_separated_of_small
      (δ := δ)
      (d := d)
      hδ
      him_ne
      (hsmall i j hij hre_zero)
  exact him_sep m (zetaScaledDifference_period_im_eq_int_two_pi hperiod)

/-- Injective samples with `|imDiff * δ| < 2π` on equal-real-coordinate differences
have no scaled integral `2πi` difference-period collisions. -/
theorem zetaScaledTranslateDifference_ne_period_of_equal_re_abs_lt_two_pi
    {n : ℕ} {sample : Fin n → ℂ} {δ : ℝ}
    (hsample : Function.Injective sample)
    (hδ : δ ≠ 0)
    (hsmall :
      ∀ i j : Fin n,
        i ≠ j →
          (sample j - sample i).re = 0 →
            |(sample j - sample i).im * δ| < 2 * Real.pi) :
    ∀ i j : Fin n,
      i ≠ j →
        ∀ m : ℤ,
          (sample j - sample i) * (δ : ℂ) ≠
            m * (2 * Real.pi * Complex.I) := by
  exact
    zetaScaledTranslateDifference_ne_period_of_equal_re_small
      (sample := sample)
      (δ := δ)
      hsample
      hδ
      (fun i j hij hre_zero m hm =>
        lt_of_lt_of_le
          (hsmall i j hij hre_zero)
          (zetaIntegerTwoPi_abs_lower_bound m hm))

/-- A pairwise real-coordinate or imaginary-lattice separation condition implies
difference-period avoidance. -/
theorem zetaScaledDifference_ne_period_of_re_or_im_separated
    {δ : ℝ} {d : ℂ}
    (hδ : δ ≠ 0)
    (hsep :
      d.re ≠ 0 ∨
        ∀ m : ℤ,
          d.im * δ ≠ (m : ℝ) * (2 * Real.pi)) :
    ∀ m : ℤ,
      d * (δ : ℂ) ≠ m * (2 * Real.pi * Complex.I) := by
  exact
    match hsep with
    | Or.inl hre =>
        zetaScaledDifference_ne_period_of_re_ne_zero hδ hre
    | Or.inr him =>
        zetaScaledDifference_ne_period_of_im_ne_int_two_pi him

/-- Indexed pairwise real-coordinate or imaginary-lattice separation gives the
difference-period condition needed by the scaled translate detector. -/
theorem zetaScaledTranslateDifference_ne_period_of_re_or_im_separated
    {n : ℕ} {sample : Fin n → ℂ} {δ : ℝ}
    (hδ : δ ≠ 0)
    (hsep :
      ∀ i j : Fin n,
        i ≠ j →
          (sample j - sample i).re ≠ 0 ∨
            ∀ m : ℤ,
              (sample j - sample i).im * δ ≠
                (m : ℝ) * (2 * Real.pi)) :
    ∀ i j : Fin n,
      i ≠ j →
        ∀ m : ℤ,
          (sample j - sample i) * (δ : ℂ) ≠
            m * (2 * Real.pi * Complex.I) := by
  intro i j hij
  exact
    zetaScaledDifference_ne_period_of_re_or_im_separated
      (δ := δ)
      (d := sample j - sample i)
      hδ
      (hsep i j hij)

/-- Difference-period avoidance implies scaled translate character injectivity. -/
theorem zetaScaledTranslateCharacter_injective_of_difference_ne_period
    {n : ℕ} {sample : Fin n → ℂ} {δ : ℝ}
    (hdiff :
      ∀ i j : Fin n,
        i ≠ j →
          ∀ m : ℤ,
            (sample j - sample i) * (δ : ℂ) ≠
              m * (2 * Real.pi * Complex.I)) :
    Function.Injective
      (fun i : Fin n => zetaScaledTranslateCharacter δ (sample i)) := by
  exact
    zetaScaledTranslateCharacter_injective_of_no_period_collisions
      (sample := sample)
      (δ := δ)
      (fun i j hij m hperiod =>
        hdiff i j hij m
          (zetaScaledTranslateExponent_period_to_difference hperiod))

/-- Finset form of the scaled translate-character injectivity criterion. -/
theorem zetaScaledTranslateCharacter_injOn_of_difference_ne_period_finset
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {sample : ι → ℂ} {δ : ℝ}
    (hdiff :
      ∀ i j : ι,
        i ∈ s →
          j ∈ s →
            i ≠ j →
              ∀ m : ℤ,
                (sample j - sample i) * (δ : ℂ) ≠
                  m * (2 * Real.pi * Complex.I)) :
    Set.InjOn
      (fun i : ι => zetaScaledTranslateCharacter δ (sample i))
      (s : Set ι) := by
  intro i hi j hj hχ
  exact
    if hij : i = j then
      hij
    else
      match
        (zetaScaledTranslateCharacter_eq_iff_exists_period
          δ (sample i) (sample j)).mp hχ with
      | ⟨m, hm⟩ =>
          False.elim
            (hdiff i j hi hj hij m
              (zetaScaledTranslateExponent_period_to_difference hm))

/-- Finset form of equal-real-coordinate small-scale period avoidance. -/
theorem zetaScaledTranslateDifference_ne_period_of_equal_re_abs_lt_two_pi_finset
    {ι : Type*} {s : Finset ι} {sample : ι → ℂ} {δ : ℝ}
    (hsample : Set.InjOn sample (s : Set ι))
    (hδ : δ ≠ 0)
    (hsmall :
      ∀ i j : ι,
        i ∈ s →
          j ∈ s →
            i ≠ j →
              (sample j - sample i).re = 0 →
                |(sample j - sample i).im * δ| < 2 * Real.pi) :
    ∀ i j : ι,
      i ∈ s →
        j ∈ s →
          i ≠ j →
            ∀ m : ℤ,
              (sample j - sample i) * (δ : ℂ) ≠
                m * (2 * Real.pi * Complex.I) := by
  intro i j hi hj hij m hperiod
  let d : ℂ := sample j - sample i
  have hre_zero :
      d.re = 0 :=
    zetaScaledDifference_period_forces_re_zero
      (δ := δ)
      (d := d)
      hδ
      hperiod
  have him_ne :
      d.im ≠ 0 := by
    intro him_zero
    have hd_zero :
        d = 0 :=
      Complex.ext hre_zero him_zero
    have hsample_eq :
        sample j = sample i :=
      sub_eq_zero.mp hd_zero
    have hji :
        j = i :=
      hsample hj hi hsample_eq
    exact hij hji.symm
  have him_sep :
      ∀ q : ℤ,
        d.im * δ ≠ (q : ℝ) * (2 * Real.pi) :=
    zetaScaledDifference_im_lattice_separated_of_abs_lt_two_pi
      (δ := δ)
      (d := d)
      hδ
      him_ne
      (hsmall i j hi hj hij hre_zero)
  exact him_sep m (zetaScaledDifference_period_im_eq_int_two_pi hperiod)

/-- Vandermonde separation after checking that no scaled sample difference is an integral
`2πi` period. -/
theorem zetaScaledTranslateMoments_not_forall_zero_of_difference_ne_period
    {n : ℕ} {sample : Fin n → ℂ}
    {coeff : Fin n → ℂ} (δ : ℝ) (f : ZetaAdmissibleFunction)
    (hdiff :
      ∀ i j : Fin n,
        i ≠ j →
          ∀ m : ℤ,
            (sample j - sample i) * (δ : ℂ) ≠
              m * (2 * Real.pi * Complex.I))
    {i₀ : Fin n}
    (hcoeff : coeff i₀ ≠ 0)
    (hf :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i₀) ≠ 0) :
    ¬
      ∀ k : Fin n,
        (∑ i : Fin n,
          (coeff i *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) *
              zetaScaledTranslateCharacter δ (sample i) ^ (k : ℕ)) = 0 := by
  exact
    zetaScaledTranslateMoments_not_forall_zero_of_laplaceSeed
      (δ := δ)
      (sample := sample)
      (coeff := coeff)
      f
      (zetaScaledTranslateCharacter_injective_of_difference_ne_period hdiff)
      hcoeff hf

/-- Vandermonde separation under a purely real pairwise separation condition. -/
theorem zetaScaledTranslateMoments_not_forall_zero_of_re_or_im_separated
    {n : ℕ} {sample : Fin n → ℂ}
    {coeff : Fin n → ℂ} (δ : ℝ) (f : ZetaAdmissibleFunction)
    (hδ : δ ≠ 0)
    (hsep :
      ∀ i j : Fin n,
        i ≠ j →
          (sample j - sample i).re ≠ 0 ∨
            ∀ m : ℤ,
              (sample j - sample i).im * δ ≠
                (m : ℝ) * (2 * Real.pi))
    {i₀ : Fin n}
    (hcoeff : coeff i₀ ≠ 0)
    (hf :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i₀) ≠ 0) :
    ¬
      ∀ k : Fin n,
        (∑ i : Fin n,
          (coeff i *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) *
              zetaScaledTranslateCharacter δ (sample i) ^ (k : ℕ)) = 0 := by
  exact
    zetaScaledTranslateMoments_not_forall_zero_of_difference_ne_period
      (δ := δ)
      (sample := sample)
      (coeff := coeff)
      f
      (zetaScaledTranslateDifference_ne_period_of_re_or_im_separated
        hδ hsep)
      hcoeff hf

/-- Vandermonde separation from an injective finite sample and a small-scale bound on
the equal-real-coordinate imaginary differences. -/
theorem zetaScaledTranslateMoments_not_forall_zero_of_equal_re_small
    {n : ℕ} {sample : Fin n → ℂ}
    {coeff : Fin n → ℂ} (δ : ℝ) (f : ZetaAdmissibleFunction)
    (hsample : Function.Injective sample)
    (hδ : δ ≠ 0)
    (hsmall :
      ∀ i j : Fin n,
        i ≠ j →
          (sample j - sample i).re = 0 →
            ∀ m : ℤ,
              m ≠ 0 →
                |(sample j - sample i).im * δ| <
                  |(m : ℝ) * (2 * Real.pi)|)
    {i₀ : Fin n}
    (hcoeff : coeff i₀ ≠ 0)
    (hf :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i₀) ≠ 0) :
    ¬
      ∀ k : Fin n,
        (∑ i : Fin n,
          (coeff i *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) *
              zetaScaledTranslateCharacter δ (sample i) ^ (k : ℕ)) = 0 := by
  exact
    zetaScaledTranslateMoments_not_forall_zero_of_difference_ne_period
      (δ := δ)
      (sample := sample)
      (coeff := coeff)
      f
      (zetaScaledTranslateDifference_ne_period_of_equal_re_small
        hsample hδ hsmall)
      hcoeff hf

/-- Vandermonde separation from an injective finite sample and the concrete
`|imDiff * δ| < 2π` small-scale bound on equal-real-coordinate differences. -/
theorem zetaScaledTranslateMoments_not_forall_zero_of_equal_re_abs_lt_two_pi
    {n : ℕ} {sample : Fin n → ℂ}
    {coeff : Fin n → ℂ} (δ : ℝ) (f : ZetaAdmissibleFunction)
    (hsample : Function.Injective sample)
    (hδ : δ ≠ 0)
    (hsmall :
      ∀ i j : Fin n,
        i ≠ j →
          (sample j - sample i).re = 0 →
            |(sample j - sample i).im * δ| < 2 * Real.pi)
    {i₀ : Fin n}
    (hcoeff : coeff i₀ ≠ 0)
    (hf :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i₀) ≠ 0) :
    ¬
      ∀ k : Fin n,
        (∑ i : Fin n,
          (coeff i *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) *
              zetaScaledTranslateCharacter δ (sample i) ^ (k : ℕ)) = 0 := by
  exact
    zetaScaledTranslateMoments_not_forall_zero_of_difference_ne_period
      (δ := δ)
      (sample := sample)
      (coeff := coeff)
      f
      (zetaScaledTranslateDifference_ne_period_of_equal_re_abs_lt_two_pi
        hsample hδ hsmall)
      hcoeff hf

/-- Vandermonde separation after an explicit finite no-period collision check for the
chosen real scale. -/
theorem zetaScaledTranslateMoments_not_forall_zero_of_no_period_collisions
    {n : ℕ} {sample : Fin n → ℂ}
    {coeff : Fin n → ℂ} (δ : ℝ) (f : ZetaAdmissibleFunction)
    (hno :
      ∀ i j : Fin n,
        i ≠ j →
          ∀ m : ℤ,
            -(sample i * (δ : ℂ)) ≠
              -(sample j * (δ : ℂ)) + m * (2 * Real.pi * Complex.I))
    {i₀ : Fin n}
    (hcoeff : coeff i₀ ≠ 0)
    (hf :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i₀) ≠ 0) :
    ¬
      ∀ k : Fin n,
        (∑ i : Fin n,
          (coeff i *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) *
              zetaScaledTranslateCharacter δ (sample i) ^ (k : ℕ)) = 0 := by
  exact
    zetaScaledTranslateMoments_not_forall_zero_of_laplaceSeed
      (δ := δ)
      (sample := sample)
      (coeff := coeff)
      f
      (zetaScaledTranslateCharacter_injective_of_no_period_collisions hno)
      hcoeff hf

/-- A finite bound on equal-real-coordinate imaginary differences gives the concrete
small-scale condition used by the scaled translate detector. -/
theorem zetaEqualRealSmallScaleCondition_of_bound
    {n : ℕ} {sample : Fin n → ℂ} {B δ : ℝ}
    (hBpos : 0 < B)
    (hδpos : 0 < δ)
    (hδB : δ * B < 2 * Real.pi)
    (hbound :
      ∀ i j : Fin n,
        i ≠ j →
          (sample j - sample i).re = 0 →
            |(sample j - sample i).im| ≤ B) :
    ∀ i j : Fin n,
      i ≠ j →
        (sample j - sample i).re = 0 →
          |(sample j - sample i).im * δ| < 2 * Real.pi := by
  intro i j hij hre_zero
  have him_nonneg :
      0 ≤ |(sample j - sample i).im| :=
    abs_nonneg (sample j - sample i).im
  have hδ_nonneg :
      0 ≤ δ :=
    le_of_lt hδpos
  have hmul_le :
      |(sample j - sample i).im| * δ ≤ B * δ :=
    mul_le_mul_of_nonneg_right
      (hbound i j hij hre_zero)
      hδ_nonneg
  have hBδ :
      B * δ < 2 * Real.pi := by
    calc
      B * δ = δ * B := by
        exact mul_comm B δ
      _ < 2 * Real.pi := by
        exact hδB
  calc
    |(sample j - sample i).im * δ| =
        |(sample j - sample i).im| * |δ| := by
      exact abs_mul (sample j - sample i).im δ
    _ = |(sample j - sample i).im| * δ := by
      exact congrArg
        (fun u : ℝ => |(sample j - sample i).im| * u)
        (abs_of_nonneg hδ_nonneg)
    _ ≤ B * δ := by
      exact hmul_le
    _ < 2 * Real.pi := by
      exact hBδ

/-- The finite sum of absolute imaginary differences bounds every one of its summands. -/
theorem zetaFiniteImaginaryDifference_le_sum_bound
    {n : ℕ} (sample : Fin n → ℂ) (i j : Fin n) :
    |(sample j - sample i).im| ≤
      ∑ p : Fin n × Fin n, |(sample p.2 - sample p.1).im| := by
  let term : Fin n × Fin n → ℝ :=
    fun p => |(sample p.2 - sample p.1).im|
  have hmem :
      (i, j) ∈ (Finset.univ : Finset (Fin n × Fin n)) :=
    Finset.mem_univ (i, j)
  have hnonneg :
      ∀ p : Fin n × Fin n,
        p ∈ (Finset.univ : Finset (Fin n × Fin n)) →
          0 ≤ term p := by
    intro p _hp
    exact abs_nonneg (sample p.2 - sample p.1).im
  exact
    Finset.single_le_sum hnonneg hmem

/-- The explicit finite imaginary-difference bound is positive after adding one. -/
theorem zetaFiniteImaginaryDifference_bound_pos
    {n : ℕ} (sample : Fin n → ℂ) :
    0 <
      1 + ∑ p : Fin n × Fin n, |(sample p.2 - sample p.1).im| := by
  have hsum_nonneg :
      0 ≤ ∑ p : Fin n × Fin n, |(sample p.2 - sample p.1).im| :=
    Finset.sum_nonneg
      (fun p _hp => abs_nonneg (sample p.2 - sample p.1).im)
  exact add_pos_of_pos_of_nonneg zero_lt_one hsum_nonneg

/-- The explicit finite imaginary-difference bound dominates every imaginary difference. -/
theorem zetaFiniteImaginaryDifference_le_positive_bound
    {n : ℕ} (sample : Fin n → ℂ) (i j : Fin n) :
    |(sample j - sample i).im| ≤
      1 + ∑ p : Fin n × Fin n, |(sample p.2 - sample p.1).im| := by
  have hle_sum :
      |(sample j - sample i).im| ≤
        ∑ p : Fin n × Fin n, |(sample p.2 - sample p.1).im| :=
    zetaFiniteImaginaryDifference_le_sum_bound sample i j
  have hsum_le :
      ∑ p : Fin n × Fin n, |(sample p.2 - sample p.1).im| ≤
        1 + ∑ p : Fin n × Fin n, |(sample p.2 - sample p.1).im| :=
    le_add_of_nonneg_left zero_le_one
  exact le_trans hle_sum hsum_le

/-- An explicit positive finite scale whose product with the finite imaginary-difference
bound is strictly below `2π`. -/
def zetaFiniteImaginaryDifferenceScale
    {n : ℕ} (sample : Fin n → ℂ) : ℝ :=
  Real.pi /
    (1 + ∑ p : Fin n × Fin n, |(sample p.2 - sample p.1).im|)

/-- The explicit positive finite scale attached to a finset-indexed sample. -/
def zetaFiniteImaginaryDifferenceScaleFinset
    {ι : Type*} (s : Finset ι) (sample : ι → ℂ) : ℝ :=
  Real.pi /
    (1 + ∑ p in s.product s, |(sample p.2 - sample p.1).im|)

/-- The finset imaginary-difference bound is positive. -/
theorem zetaFiniteImaginaryDifference_bound_pos_finset
    {ι : Type*} (s : Finset ι) (sample : ι → ℂ) :
    0 < 1 + ∑ p in s.product s, |(sample p.2 - sample p.1).im| := by
  have hsum_nonneg :
      0 ≤ ∑ p in s.product s, |(sample p.2 - sample p.1).im| :=
    Finset.sum_nonneg
      (fun p _hp => abs_nonneg (sample p.2 - sample p.1).im)
  exact add_pos_of_pos_of_nonneg zero_lt_one hsum_nonneg

/-- The finset imaginary-difference bound dominates every indexed imaginary
difference. -/
theorem zetaFiniteImaginaryDifference_le_positive_bound_finset
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {sample : ι → ℂ}
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    |(sample j - sample i).im| ≤
      1 + ∑ p in s.product s, |(sample p.2 - sample p.1).im| := by
  have hmem :
      (i, j) ∈ s.product s :=
    Finset.mem_product.mpr ⟨hi, hj⟩
  have hle_sum :
      |(sample j - sample i).im| ≤
        ∑ p in s.product s, |(sample p.2 - sample p.1).im| :=
    Finset.single_le_sum
      (fun p _hp => abs_nonneg (sample p.2 - sample p.1).im)
      hmem
  have hsum_le :
      ∑ p in s.product s, |(sample p.2 - sample p.1).im| ≤
        1 + ∑ p in s.product s, |(sample p.2 - sample p.1).im| :=
    le_add_of_nonneg_left zero_le_one
  exact le_trans hle_sum hsum_le

/-- The explicit finset scale is positive. -/
theorem zetaFiniteImaginaryDifferenceScaleFinset_pos
    {ι : Type*} (s : Finset ι) (sample : ι → ℂ) :
    0 < zetaFiniteImaginaryDifferenceScaleFinset s sample := by
  exact div_pos
    Real.pi_pos
    (zetaFiniteImaginaryDifference_bound_pos_finset s sample)

/-- The explicit finset scale is nonzero. -/
theorem zetaFiniteImaginaryDifferenceScaleFinset_ne_zero
    {ι : Type*} (s : Finset ι) (sample : ι → ℂ) :
    zetaFiniteImaginaryDifferenceScaleFinset s sample ≠ 0 := by
  exact ne_of_gt (zetaFiniteImaginaryDifferenceScaleFinset_pos s sample)

/-- The explicit finset scale times the finset imaginary-difference bound is below
`2π`. -/
theorem zetaFiniteImaginaryDifferenceScaleFinset_mul_bound_lt_two_pi
    {ι : Type*} (s : Finset ι) (sample : ι → ℂ) :
    zetaFiniteImaginaryDifferenceScaleFinset s sample *
        (1 + ∑ p in s.product s, |(sample p.2 - sample p.1).im|) <
      2 * Real.pi := by
  let B : ℝ :=
    1 + ∑ p in s.product s, |(sample p.2 - sample p.1).im|
  have hBne : B ≠ 0 :=
    ne_of_gt (zetaFiniteImaginaryDifference_bound_pos_finset s sample)
  calc
    zetaFiniteImaginaryDifferenceScaleFinset s sample * B =
        (Real.pi / B) * B := by
      rfl
    _ = Real.pi := by
      exact div_mul_cancel₀ Real.pi hBne
    _ < 2 * Real.pi := by
      calc
        Real.pi = 1 * Real.pi := by
          exact (one_mul Real.pi).symm
        _ < 2 * Real.pi := by
          exact mul_lt_mul_of_pos_right one_lt_two Real.pi_pos

/-- The explicit finset scale supplies the equal-real-coordinate smallness condition. -/
theorem zetaFiniteImaginaryDifferenceScaleFinset_equal_re_abs_lt_two_pi
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (sample : ι → ℂ) :
    ∀ i j : ι,
      i ∈ s →
        j ∈ s →
          i ≠ j →
            (sample j - sample i).re = 0 →
              |(sample j - sample i).im *
                zetaFiniteImaginaryDifferenceScaleFinset s sample| < 2 * Real.pi := by
  intro i j hi hj _hij _hre
  let B : ℝ :=
    1 + ∑ p in s.product s, |(sample p.2 - sample p.1).im|
  let δ : ℝ := zetaFiniteImaginaryDifferenceScaleFinset s sample
  have hδ_nonneg : 0 ≤ δ :=
    (zetaFiniteImaginaryDifferenceScaleFinset_pos s sample).le
  have him_le :
      |(sample j - sample i).im| ≤ B :=
    zetaFiniteImaginaryDifference_le_positive_bound_finset
      (s := s) (sample := sample) hi hj
  have hmul_le :
      |(sample j - sample i).im| * δ ≤ B * δ :=
    mul_le_mul_of_nonneg_right him_le hδ_nonneg
  have hsmall :
      B * δ < 2 * Real.pi := by
    calc
      B * δ = δ * B := by
        exact mul_comm B δ
      _ < 2 * Real.pi := by
        exact zetaFiniteImaginaryDifferenceScaleFinset_mul_bound_lt_two_pi s sample
  calc
    |(sample j - sample i).im * δ| =
        |(sample j - sample i).im| * |δ| := by
      exact abs_mul (sample j - sample i).im δ
    _ = |(sample j - sample i).im| * δ := by
      exact congrArg
        (fun u : ℝ => |(sample j - sample i).im| * u)
        (abs_of_nonneg hδ_nonneg)
    _ ≤ B * δ := by
      exact hmul_le
    _ < 2 * Real.pi := by
      exact hsmall

/-- The explicit finset small scale makes the scaled translate character injective on
an injective finite sample. -/
theorem zetaScaledTranslateCharacter_injOn_finiteSmallScale_finset
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {sample : ι → ℂ}
    (hsample : Set.InjOn sample (s : Set ι)) :
    Set.InjOn
      (fun i : ι =>
        zetaScaledTranslateCharacter
          (zetaFiniteImaginaryDifferenceScaleFinset s sample)
          (sample i))
      (s : Set ι) := by
  exact
    zetaScaledTranslateCharacter_injOn_of_difference_ne_period_finset
      (s := s)
      (sample := sample)
      (δ := zetaFiniteImaginaryDifferenceScaleFinset s sample)
      (zetaScaledTranslateDifference_ne_period_of_equal_re_abs_lt_two_pi_finset
        (s := s)
        (sample := sample)
        hsample
        (zetaFiniteImaginaryDifferenceScaleFinset_ne_zero s sample)
        (zetaFiniteImaginaryDifferenceScaleFinset_equal_re_abs_lt_two_pi s sample))

/-- The explicit finite scale is positive. -/
theorem zetaFiniteImaginaryDifferenceScale_pos
    {n : ℕ} (sample : Fin n → ℂ) :
    0 < zetaFiniteImaginaryDifferenceScale sample := by
  exact div_pos
    Real.pi_pos
    (zetaFiniteImaginaryDifference_bound_pos sample)

/-- The explicit finite scale is nonzero. -/
theorem zetaFiniteImaginaryDifferenceScale_ne_zero
    {n : ℕ} (sample : Fin n → ℂ) :
    zetaFiniteImaginaryDifferenceScale sample ≠ 0 := by
  exact ne_of_gt (zetaFiniteImaginaryDifferenceScale_pos sample)

/-- Multiplying the explicit finite scale by the finite imaginary-difference bound is
strictly below `2π`. -/
theorem zetaFiniteImaginaryDifferenceScale_mul_bound_lt_two_pi
    {n : ℕ} (sample : Fin n → ℂ) :
    zetaFiniteImaginaryDifferenceScale sample *
        (1 + ∑ p : Fin n × Fin n, |(sample p.2 - sample p.1).im|) <
      2 * Real.pi := by
  let B : ℝ :=
    1 + ∑ p : Fin n × Fin n, |(sample p.2 - sample p.1).im|
  have hBpos : 0 < B :=
    zetaFiniteImaginaryDifference_bound_pos sample
  have hBne : B ≠ 0 :=
    ne_of_gt hBpos
  calc
    zetaFiniteImaginaryDifferenceScale sample * B =
        (Real.pi / B) * B := by
      rfl
    _ = Real.pi := by
      exact div_mul_cancel₀ Real.pi hBne
    _ < 2 * Real.pi := by
      calc
        Real.pi = 1 * Real.pi := by
          exact (one_mul Real.pi).symm
        _ < 2 * Real.pi := by
          exact mul_lt_mul_of_pos_right one_lt_two Real.pi_pos

/-- The explicit finite scale supplies the equal-real-coordinate smallness condition. -/
theorem zetaFiniteImaginaryDifferenceScale_equal_re_abs_lt_two_pi
    {n : ℕ} (sample : Fin n → ℂ) :
    ∀ i j : Fin n,
      i ≠ j →
        (sample j - sample i).re = 0 →
          |(sample j - sample i).im *
            zetaFiniteImaginaryDifferenceScale sample| < 2 * Real.pi := by
  exact
    zetaEqualRealSmallScaleCondition_of_bound
      (sample := sample)
      (B := 1 + ∑ p : Fin n × Fin n, |(sample p.2 - sample p.1).im|)
      (δ := zetaFiniteImaginaryDifferenceScale sample)
      (zetaFiniteImaginaryDifference_bound_pos sample)
      (zetaFiniteImaginaryDifferenceScale_pos sample)
      (zetaFiniteImaginaryDifferenceScale_mul_bound_lt_two_pi sample)
      (fun i j _hij _hre =>
        zetaFiniteImaginaryDifference_le_positive_bound sample i j)

/-- Vandermonde separation at the explicit finite small scale for a seed whose Laplace
transform is nonzero at one nonzero coefficient. -/
theorem zetaFiniteSmallScaleTranslateMoments_not_forall_zero_of_laplaceSeed
    {n : ℕ} {sample : Fin n → ℂ}
    {coeff : Fin n → ℂ} (f : ZetaAdmissibleFunction)
    (hsample : Function.Injective sample)
    {i₀ : Fin n}
    (hcoeff : coeff i₀ ≠ 0)
    (hf :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i₀) ≠ 0) :
    ¬
      ∀ k : Fin n,
        (∑ i : Fin n,
          (coeff i *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) *
              zetaScaledTranslateCharacter
                (zetaFiniteImaginaryDifferenceScale sample)
                (sample i) ^ (k : ℕ)) = 0 := by
  exact
    zetaScaledTranslateMoments_not_forall_zero_of_equal_re_abs_lt_two_pi
      (δ := zetaFiniteImaginaryDifferenceScale sample)
      (sample := sample)
      (coeff := coeff)
      f
      hsample
      (zetaFiniteImaginaryDifferenceScale_ne_zero sample)
      (zetaFiniteImaginaryDifferenceScale_equal_re_abs_lt_two_pi sample)
      hcoeff hf

/-- If a finite distribution annihilates every admissible probe, then it annihilates
every integer-step translate of any seed, written in scaled-character moment form. -/
theorem zetaFiniteDistribution_annihilates_all_forces_scaledTranslateMoments_zero
    {n : ℕ} {sample : Fin n → ℂ}
    {coeff : Fin n → ℂ} (δ : ℝ) (f : ZetaAdmissibleFunction)
    (hannihilate :
      ∀ g : ZetaAdmissibleFunction,
        (∑ i : Fin n,
          coeff i *
            Boundary.zetaLaplaceTransform g.toZetaTestFunction' (sample i)) = 0) :
    ∀ k : Fin n,
      (∑ i : Fin n,
        (coeff i *
          Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) *
            zetaScaledTranslateCharacter δ (sample i) ^ (k : ℕ)) = 0 := by
  intro k
  let c : ℝ := (k : ℝ) * δ
  let g : ZetaAdmissibleFunction := ZetaAdmissibleFunction.translate c f
  have htranslate_zero :
      (∑ i : Fin n,
        coeff i *
          Boundary.zetaLaplaceTransform g.toZetaTestFunction' (sample i)) = 0 :=
    hannihilate g
  have hmoment_eq_translate :
      (∑ i : Fin n,
        (coeff i *
          Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) *
            zetaScaledTranslateCharacter δ (sample i) ^ (k : ℕ)) =
      (∑ i : Fin n,
        coeff i *
          Boundary.zetaLaplaceTransform g.toZetaTestFunction' (sample i)) := by
    exact Finset.sum_congr rfl
      (fun i _hi =>
        calc
          (coeff i *
              Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) *
                zetaScaledTranslateCharacter δ (sample i) ^ (k : ℕ) =
              (coeff i *
                Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) *
                Complex.exp (-(sample i * (c : ℂ))) := by
            exact congrArg
              (fun u : ℂ =>
                (coeff i *
                  Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) * u)
              (zetaScaledTranslateCharacter_pow δ (sample i) (k : ℕ))
          _ =
              coeff i *
                (Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i) *
                  Complex.exp (-(sample i * (c : ℂ)))) := by
            exact mul_assoc
              (coeff i)
              (Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i))
              (Complex.exp (-(sample i * (c : ℂ))))
          _ =
              coeff i *
                (Complex.exp (-(sample i * (c : ℂ))) *
                  Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i)) := by
            exact congrArg
              (fun u : ℂ => coeff i * u)
              (mul_comm
                (Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i))
                (Complex.exp (-(sample i * (c : ℂ)))))
          _ =
              coeff i *
                Boundary.zetaLaplaceTransform g.toZetaTestFunction' (sample i) := by
            exact congrArg
              (fun u : ℂ => coeff i * u)
              (Boundary.zetaLaplaceTransform_translate c f (sample i)).symm)
  exact hmoment_eq_translate.trans htranslate_zero

/-- A seeded coefficient nonzero at the explicit small scale prevents the finite
distribution from annihilating every admissible probe. -/
theorem zetaFiniteDistribution_not_annihilates_all_of_smallScale_laplaceSeed
    {n : ℕ} {sample : Fin n → ℂ}
    {coeff : Fin n → ℂ} (f : ZetaAdmissibleFunction)
    (hsample : Function.Injective sample)
    {i₀ : Fin n}
    (hcoeff : coeff i₀ ≠ 0)
    (hf :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' (sample i₀) ≠ 0) :
    ¬
      ∀ g : ZetaAdmissibleFunction,
        (∑ i : Fin n,
          coeff i *
            Boundary.zetaLaplaceTransform g.toZetaTestFunction' (sample i)) = 0 := by
  intro hannihilate
  exact
    zetaFiniteSmallScaleTranslateMoments_not_forall_zero_of_laplaceSeed
      (sample := sample)
      (coeff := coeff)
      f hsample hcoeff hf
      (zetaFiniteDistribution_annihilates_all_forces_scaledTranslateMoments_zero
        (δ := zetaFiniteImaginaryDifferenceScale sample)
        (sample := sample)
        (coeff := coeff)
        f
        hannihilate)

end

end ZetaAdmissibleFunction
end LFunctions
end Boundary
