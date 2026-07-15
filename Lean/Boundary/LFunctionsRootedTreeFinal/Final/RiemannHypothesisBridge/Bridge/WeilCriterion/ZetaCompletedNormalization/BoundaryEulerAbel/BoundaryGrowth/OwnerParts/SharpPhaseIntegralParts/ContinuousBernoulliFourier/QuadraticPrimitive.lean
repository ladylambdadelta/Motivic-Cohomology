import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.PhaseSeparation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.BernoulliCore

/-!
# Quadratic primitive for the first periodic Bernoulli function

The first periodic Bernoulli function is discontinuous at the integers.  Its
integration-by-parts primitive is therefore owned first on a unit coordinate;
matching endpoint values permit the blockwise identities to telescope.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The normalized quadratic primitive of `u - 1/2` on a unit interval. -/
noncomputable def eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive
    (u : ℝ) : ℝ :=
  (u * u) / 2 - u / 2

/-- The centered quadratic primitive.  This is the normalization identified
with `B₂/2`; its constant term is the Bernoulli moment `1/12`. -/
noncomputable def eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive
    (u : ℝ) : ℝ :=
  eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive u + 1 / 12

/-- The zero-endpoint quadratic primitive vanishes at the left endpoint. -/
theorem eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive_zero :
    eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive 0 = 0 := by
  have hzero_mul : (0 : ℝ) * 0 = 0 :=
    zero_mul 0
  have hzero_div : (0 : ℝ) / 2 = 0 :=
    zero_div 2
  calc
    eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive 0 =
        ((0 : ℝ) * 0) / 2 - 0 / 2 := rfl
    _ = (0 : ℝ) / 2 - 0 / 2 :=
      congrArg (fun r : ℝ => r / 2 - 0 / 2) hzero_mul
    _ = 0 - 0 :=
      congrArg₂ Sub.sub hzero_div hzero_div
    _ = 0 := sub_zero 0

/-- The zero-endpoint quadratic primitive vanishes at the right endpoint. -/
theorem eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive_one :
    eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive 1 = 0 := by
  have hone_mul : (1 : ℝ) * 1 = 1 :=
    mul_one 1
  have hone_sub : (1 : ℝ) / 2 - 1 / 2 = 0 :=
    sub_self (1 / 2)
  calc
    eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive 1 =
        ((1 : ℝ) * 1) / 2 - 1 / 2 := rfl
    _ = (1 : ℝ) / 2 - 1 / 2 :=
      congrArg (fun r : ℝ => r / 2 - 1 / 2) hone_mul
    _ = 0 := hone_sub

/-- The quadratic primitive has matching values at the endpoints of a unit
interval. -/
theorem eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive_endpoints :
    eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive 1 =
      eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive 0 := by
  exact Eq.trans
    eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive_one
    eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive_zero.symm

/-- The derivative coefficient produced by the product rule reduces to the
first Bernoulli affine coordinate. -/
theorem eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive_derivativeCoefficient
    (u : ℝ) :
    (u * 1 + 1 * u) / 2 - 1 / 2 = u - 1 / 2 := by
  have hsum : u * 1 + 1 * u = 2 * u := by
    calc
      u * 1 + 1 * u = u + u :=
        congrArg₂ Add.add (mul_one u) (one_mul u)
      _ = 2 * u := (two_mul u).symm
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    two_ne_zero
  have hquotient : (2 * u) / 2 = u := by
    exact (div_eq_iff htwo_ne).mpr (mul_comm (2 : ℝ) u)
  calc
    (u * 1 + 1 * u) / 2 - 1 / 2 = (2 * u) / 2 - 1 / 2 :=
      congrArg (fun r : ℝ => r / 2 - 1 / 2) hsum
    _ = u - 1 / 2 :=
      congrArg (fun r : ℝ => r - 1 / 2) hquotient

/-- On a unit coordinate, the quadratic primitive differentiates to the
project's normalized first Bernoulli affine factor. -/
theorem hasDerivAt_eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive
    (u : ℝ) :
    HasDerivAt
      eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive
      (u - 1 / 2)
      u := by
  have hid : HasDerivAt (fun x : ℝ => x) 1 u :=
    hasDerivAt_id u
  have hproductRaw :
      HasDerivAt (fun x : ℝ => x * x) (1 * u + u * 1) u :=
    hid.mul hid
  have hproductCoefficient :
      (1 : ℝ) * u + u * 1 = u * 1 + 1 * u :=
    add_comm (1 * u) (u * 1)
  have hproduct : HasDerivAt (fun x : ℝ => x * x) (u * 1 + 1 * u) u :=
    hproductRaw.congr_deriv hproductCoefficient
  have hproduct_div :
      HasDerivAt (fun x : ℝ => (x * x) / 2) ((u * 1 + 1 * u) / 2) u :=
    hproduct.div_const 2
  have hid_div : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) u :=
    hid.div_const 2
  have hsub :
      HasDerivAt
        (fun x : ℝ => (x * x) / 2 - x / 2)
        ((u * 1 + 1 * u) / 2 - 1 / 2)
        u :=
    hproduct_div.sub hid_div
  have hcoefficient :
      (u * 1 + 1 * u) / 2 - 1 / 2 = u - 1 / 2 :=
    eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive_derivativeCoefficient u
  exact hsub.congr_deriv hcoefficient

/-- Centering by `1/12` does not change the derivative of the quadratic
primitive. -/
theorem hasDerivAt_eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive
    (u : ℝ) :
    HasDerivAt
      eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive
      (u - 1 / 2)
      u := by
  have hprimitive :=
    hasDerivAt_eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive u
  have hconstant : HasDerivAt (fun _x : ℝ => (1 : ℝ) / 12) 0 u :=
    hasDerivAt_const u ((1 : ℝ) / 12)
  have hadd :
      HasDerivAt
        (fun x : ℝ =>
          eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive x + 1 / 12)
        ((u - 1 / 2) + 0)
        u :=
    hprimitive.add hconstant
  have hcoefficient : (u - 1 / 2) + 0 = u - 1 / 2 :=
    add_zero (u - 1 / 2)
  exact hadd.congr_deriv hcoefficient

/-- The centered primitive differs from the zero-endpoint primitive by the
exact Bernoulli moment. -/
theorem eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive_sub_quadraticPrimitive
    (u : ℝ) :
    eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u -
        eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive u =
      1 / 12 := by
  exact add_sub_cancel_left
    (eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive u)
    (1 / 12)

/-- The centered quadratic primitive also has matching unit-interval
endpoints. -/
theorem eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive_endpoints :
    eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive 1 =
      eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive 0 := by
  have hquadratic :=
    eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive_endpoints
  exact congrArg (fun r : ℝ => r + 1 / 12) hquadratic

/-- On the half-open unit interval, translating by a natural number turns the
periodic Bernoulli sawtooth into its affine unit-coordinate formula. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_natAdd_eq_affine
    (n : ℕ)
    {u : ℝ}
    (hu_nonneg : 0 ≤ u)
    (hu_lt_one : u < 1) :
    eulerMaclaurinFirstPeriodicBernoulli ((n : ℝ) + u) = u - 1 / 2 := by
  have hfract_translate :
      Int.fract ((n : ℝ) + u) = Int.fract u :=
    Int.fract_nat_add n u
  have hfract_coordinate : Int.fract u = u :=
    Int.fract_eq_self.mpr (And.intro hu_nonneg hu_lt_one)
  calc
    eulerMaclaurinFirstPeriodicBernoulli ((n : ℝ) + u) =
        Int.fract ((n : ℝ) + u) - 1 / 2 := rfl
    _ = Int.fract u - 1 / 2 :=
      congrArg (fun r : ℝ => r - 1 / 2) hfract_translate
    _ = u - 1 / 2 :=
      congrArg (fun r : ℝ => r - 1 / 2) hfract_coordinate

/-- The unit-coordinate quadratic primitive differentiates to the translated
project Bernoulli factor at every nonterminal point of the unit interval. -/
theorem hasDerivAt_eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive_eq_natAdd
    (n : ℕ)
    {u : ℝ}
    (hu_nonneg : 0 ≤ u)
    (hu_lt_one : u < 1) :
    HasDerivAt
      eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive
      (eulerMaclaurinFirstPeriodicBernoulli ((n : ℝ) + u))
      u := by
  have hderivative :=
    hasDerivAt_eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive u
  have hcoefficient :
      u - 1 / 2 =
        eulerMaclaurinFirstPeriodicBernoulli ((n : ℝ) + u) :=
    (eulerMaclaurinFirstPeriodicBernoulli_natAdd_eq_affine
      n hu_nonneg hu_lt_one).symm
  exact hderivative.congr_deriv hcoefficient

end
end LFunctions
end Boundary
