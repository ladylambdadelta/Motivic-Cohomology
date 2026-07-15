import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.BlockIntegrationByParts
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Normalization of the quadratic primitive by the second Bernoulli polynomial

This file proves, rather than assumes, the low-degree Bernoulli polynomial
normalizations needed to connect the project primitive to Mathlib's Fourier
series for `B₂`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The zeroth Mathlib Bernoulli function is the constant one function. -/
theorem bernoulliFun_zero_eq_one (x : ℝ) :
    bernoulliFun 0 x = 1 := by
  have hbernoulli_zero_cast :
      ((bernoulli 0 : ℚ) : ℝ) = 1 :=
    Eq.trans
      (congrArg (fun q : ℚ => (q : ℝ)) bernoulli_zero)
      Rat.cast_one
  have hvalue : bernoulliFun 0 0 = (1 : ℝ) :=
    Eq.trans (bernoulliFun_eval_zero 0) hbernoulli_zero_cast
  have hbernoulli_derivative :
      ∀ y : ℝ, HasDerivAt (bernoulliFun 0) 0 y := by
    intro y
    have hraw := hasDerivAt_bernoulliFun 0 y
    have hzero_cast : (((0 : ℕ) : ℝ)) = 0 :=
      Nat.cast_zero
    have hcoefficient :
        (((0 : ℕ) : ℝ)) * bernoulliFun (0 - 1) y = 0 :=
      Eq.trans
        (congrArg
          (fun r : ℝ => r * bernoulliFun (0 - 1) y)
          hzero_cast)
        (zero_mul (bernoulliFun (0 - 1) y))
    exact hraw.congr_deriv hcoefficient
  have hone_derivative :
      ∀ y : ℝ, HasDerivAt (fun _z : ℝ => (1 : ℝ)) 0 y :=
    fun y => hasDerivAt_const y 1
  have hbernoulli_differentiable : Differentiable ℝ (bernoulliFun 0) :=
    fun y => (hbernoulli_derivative y).differentiableAt
  have hone_differentiable :
      Differentiable ℝ (fun _z : ℝ => (1 : ℝ)) :=
    fun y => (hone_derivative y).differentiableAt
  have hfderiv :
      ∀ y : ℝ,
        fderiv ℝ (bernoulliFun 0) y =
          fderiv ℝ (fun _z : ℝ => (1 : ℝ)) y := by
    intro y
    exact Eq.trans
      (hbernoulli_derivative y).hasFDerivAt.fderiv
      (hone_derivative y).hasFDerivAt.fderiv.symm
  have hfunctions : bernoulliFun 0 = (fun _z : ℝ => (1 : ℝ)) :=
    eq_of_fderiv_eq
      hbernoulli_differentiable
      hone_differentiable
      hfderiv
      0
      hvalue
  exact congrFun hfunctions x

/-- Casting the first Bernoulli number to the reals gives `-1/2`. -/
theorem bernoulli_one_cast_real :
    ((bernoulli 1 : ℚ) : ℝ) = -(1 : ℝ) / 2 := by
  have hcast := congrArg (fun q : ℚ => (q : ℝ)) bernoulli_one
  have hone_cast : ((1 : ℚ) : ℝ) = (1 : ℝ) :=
    Rat.cast_one
  have hneg_cast : ((-(1 : ℚ) : ℚ) : ℝ) = -(1 : ℝ) :=
    Eq.trans (Rat.cast_neg 1) (congrArg Neg.neg hone_cast)
  have htwo_cast : ((2 : ℚ) : ℝ) = (2 : ℝ) :=
    Rat.cast_ofNat 2
  have hdivision :
      (((-(1 : ℚ)) / 2 : ℚ) : ℝ) = -(1 : ℝ) / 2 := by
    calc
      (((-(1 : ℚ)) / 2 : ℚ) : ℝ) =
          ((-(1 : ℚ) : ℚ) : ℝ) / ((2 : ℚ) : ℝ) :=
        Rat.cast_div (-(1 : ℚ)) 2
      _ = -(1 : ℝ) / ((2 : ℚ) : ℝ) :=
        congrArg (fun r : ℝ => r / ((2 : ℚ) : ℝ)) hneg_cast
      _ = -(1 : ℝ) / 2 :=
        congrArg (fun r : ℝ => -(1 : ℝ) / r) htwo_cast
  exact Eq.trans hcast hdivision

/-- The first Mathlib Bernoulli function has the project's affine
normalization. -/
theorem bernoulliFun_one_eq_affine (x : ℝ) :
    bernoulliFun 1 x = x - 1 / 2 := by
  have hvalue_bernoulli : bernoulliFun 1 0 = -(1 : ℝ) / 2 :=
    Eq.trans (bernoulliFun_eval_zero 1) bernoulli_one_cast_real
  have hzero_sub : (0 : ℝ) - 1 / 2 = -(1 : ℝ) / 2 := by
    exact Eq.trans
      (zero_sub ((1 : ℝ) / 2))
      (neg_div' (2 : ℝ) 1)
  have hvalue : bernoulliFun 1 0 = (0 : ℝ) - 1 / 2 :=
    Eq.trans hvalue_bernoulli hzero_sub.symm
  have hbernoulli_derivative :
      ∀ y : ℝ, HasDerivAt (bernoulliFun 1) 1 y := by
    intro y
    have hraw := hasDerivAt_bernoulliFun 1 y
    have hzero_value : bernoulliFun (1 - 1) y = 1 :=
      bernoulliFun_zero_eq_one y
    have hone_cast : (((1 : ℕ) : ℝ)) = 1 :=
      Nat.cast_one
    have hcoefficient : (((1 : ℕ) : ℝ)) * bernoulliFun (1 - 1) y = 1 := by
      calc
        (((1 : ℕ) : ℝ)) * bernoulliFun (1 - 1) y =
            1 * bernoulliFun (1 - 1) y :=
          congrArg
            (fun r : ℝ => r * bernoulliFun (1 - 1) y)
            hone_cast
        _ = 1 * 1 :=
          congrArg (fun r : ℝ => 1 * r) hzero_value
        _ = 1 := one_mul 1
    exact hraw.congr_deriv hcoefficient
  have haffine_derivative :
      ∀ y : ℝ, HasDerivAt (fun z : ℝ => z - 1 / 2) 1 y := by
    intro y
    have hid : HasDerivAt (fun z : ℝ => z) 1 y :=
      hasDerivAt_id y
    have hconstant : HasDerivAt (fun _z : ℝ => (1 : ℝ) / 2) 0 y :=
      hasDerivAt_const y ((1 : ℝ) / 2)
    have hsub := hid.sub hconstant
    exact hsub.congr_deriv (sub_zero 1)
  have hbernoulli_differentiable : Differentiable ℝ (bernoulliFun 1) :=
    fun y => (hbernoulli_derivative y).differentiableAt
  have haffine_differentiable :
      Differentiable ℝ (fun z : ℝ => z - 1 / 2) :=
    fun y => (haffine_derivative y).differentiableAt
  have hfderiv :
      ∀ y : ℝ,
        fderiv ℝ (bernoulliFun 1) y =
          fderiv ℝ (fun z : ℝ => z - 1 / 2) y := by
    intro y
    exact Eq.trans
      (hbernoulli_derivative y).hasFDerivAt.fderiv
      (haffine_derivative y).hasFDerivAt.fderiv.symm
  have hfunctions :
      bernoulliFun 1 = (fun z : ℝ => z - 1 / 2) :=
    eq_of_fderiv_eq
      hbernoulli_differentiable
      haffine_differentiable
      hfderiv
      0
      hvalue
  exact congrFun hfunctions x

/-- The second Bernoulli number is `1/6`, after casting to the reals. -/
theorem bernoulli_two_cast_real :
    ((bernoulli 2 : ℚ) : ℝ) = (1 : ℝ) / 6 := by
  have htwo_ne_one : (2 : ℕ) ≠ 1 :=
    OfNat.ofNat_ne_one 2
  have hbernoulli_two : bernoulli 2 = (1 : ℚ) / 6 :=
    Eq.trans
      (bernoulli_eq_bernoulli'_of_ne_one htwo_ne_one)
      bernoulli'_two
  have hcast := congrArg (fun q : ℚ => (q : ℝ)) hbernoulli_two
  have hone_cast : ((1 : ℚ) : ℝ) = (1 : ℝ) :=
    Rat.cast_one
  have hsix_cast : ((6 : ℚ) : ℝ) = (6 : ℝ) :=
    Rat.cast_ofNat 6
  have hdivision :
      (((1 : ℚ) / 6 : ℚ) : ℝ) = (1 : ℝ) / 6 := by
    calc
      (((1 : ℚ) / 6 : ℚ) : ℝ) =
          ((1 : ℚ) : ℝ) / ((6 : ℚ) : ℝ) :=
        Rat.cast_div 1 6
      _ = (1 : ℝ) / ((6 : ℚ) : ℝ) :=
        congrArg (fun r : ℝ => r / ((6 : ℚ) : ℝ)) hone_cast
      _ = (1 : ℝ) / 6 :=
        congrArg (fun r : ℝ => (1 : ℝ) / r) hsix_cast
  exact Eq.trans hcast hdivision

/-- Dividing the second Bernoulli value by two gives the centered constant
`1/12`. -/
theorem bernoulli_two_half_value :
    (bernoulliFun 2 0) / 2 = (1 : ℝ) / 12 := by
  have hvalue : bernoulliFun 2 0 = (1 : ℝ) / 6 :=
    Eq.trans (bernoulliFun_eval_zero 2) bernoulli_two_cast_real
  have hsix_mul_two : (6 : ℝ) * 2 = 12 := by
    have hnat : (6 : ℕ) * 2 = 12 := by
      rfl
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hnat
    have hcast_mul : (((6 : ℕ) * 2 : ℕ) : ℝ) = (6 : ℝ) * 2 :=
      Nat.cast_mul 6 2
    exact Eq.trans hcast_mul.symm hcast
  calc
    (bernoulliFun 2 0) / 2 = ((1 : ℝ) / 6) / 2 :=
      congrArg (fun r : ℝ => r / 2) hvalue
    _ = (1 : ℝ) / (6 * 2) := div_div 1 6 2
    _ = (1 : ℝ) / 12 :=
      congrArg (fun r : ℝ => (1 : ℝ) / r) hsix_mul_two

/-- Mathlib's `B₂/2` is exactly the centered quadratic primitive used by
the Fourier owner. -/
theorem bernoulliFun_two_div_two_eq_centeredQuadraticPrimitive (x : ℝ) :
    bernoulliFun 2 x / 2 =
      eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive x := by
  let mathlibPrimitive : ℝ → ℝ := fun y => bernoulliFun 2 y / 2
  have hmathlib_derivative :
      ∀ y : ℝ, HasDerivAt mathlibPrimitive (y - 1 / 2) y := by
    intro y
    have hraw := antideriv_bernoulliFun 1 y
    have hone_value : bernoulliFun 1 y = y - 1 / 2 :=
      bernoulliFun_one_eq_affine y
    have hfunction :
        (fun z : ℝ => bernoulliFun (1 + 1) z / (((1 : ℕ) : ℝ) + 1)) =
          mathlibPrimitive := by
      funext z
      have hone_add_one : (1 : ℕ) + 1 = 2 :=
        one_add_one_eq_two
      have hnumerator : bernoulliFun (1 + 1) z = bernoulliFun 2 z :=
        congrArg (fun k : ℕ => bernoulliFun k z) hone_add_one
      have hone_cast : (((1 : ℕ) : ℝ)) = (1 : ℝ) :=
        Nat.cast_one
      have hdenominator : (((1 : ℕ) : ℝ) + 1) = (2 : ℝ) :=
        Eq.trans
          (congrArg (fun r : ℝ => r + 1) hone_cast)
          one_add_one_eq_two
      exact congrArg₂ Div.div hnumerator hdenominator
    have htransported :
        HasDerivAt mathlibPrimitive (bernoulliFun 1 y) y :=
      Eq.subst
        (motive := fun f : ℝ → ℝ => HasDerivAt f (bernoulliFun 1 y) y)
        hfunction
        hraw
    exact htransported.congr_deriv hone_value
  have hcentered_derivative :
      ∀ y : ℝ,
        HasDerivAt
          eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive
          (y - 1 / 2)
          y :=
    hasDerivAt_eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive
  have hmathlib_differentiable : Differentiable ℝ mathlibPrimitive :=
    fun y => (hmathlib_derivative y).differentiableAt
  have hcentered_differentiable :
      Differentiable ℝ
        eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive :=
    fun y => (hcentered_derivative y).differentiableAt
  have hfderiv :
      ∀ y : ℝ,
        fderiv ℝ mathlibPrimitive y =
          fderiv ℝ
            eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive y := by
    intro y
    exact Eq.trans
      (hmathlib_derivative y).hasFDerivAt.fderiv
      (hcentered_derivative y).hasFDerivAt.fderiv.symm
  have hcentered_zero :
      eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive 0 =
        (1 : ℝ) / 12 := by
    calc
      eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive 0 =
          eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive 0 + 1 / 12 :=
        rfl
      _ = 0 + 1 / 12 :=
        congrArg (fun r : ℝ => r + 1 / 12)
          eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive_zero
      _ = 1 / 12 := zero_add (1 / 12)
  have hvalue : mathlibPrimitive 0 =
      eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive 0 :=
    Eq.trans bernoulli_two_half_value hcentered_zero.symm
  have hfunctions :
      mathlibPrimitive =
        eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive :=
    eq_of_fderiv_eq
      hmathlib_differentiable
      hcentered_differentiable
      hfderiv
      0
      hvalue
  exact congrFun hfunctions x

end
end LFunctions
end Boundary
