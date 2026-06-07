import Boundary.Cycles.FiniteSum

/-!
# Divisor data on cycle-support atoms

This file packages the geometric input for principal divisors:
an integral support atom together with a rational function in its function field.
The quotient by rational equivalence is still downstream.

This is the classical principal-divisor input used in Chow theory; cf.
Hartshorne, *Algebraic Geometry*, Ch. I, §6, and Fulton,
*Intersection Theory*, §1.1–§1.4.
-/

universe u

open AlgebraicGeometry

namespace Boundary
namespace Cycles

noncomputable section

/-- A rational function on a cycle-support atom. -/
abbrev RationalFunctionOn {X : Scheme.{u}} (Z : CycleSupportAtom X) : Type (u + 1) :=
  Z.functionField

/-- Principal-divisor generator data on a scheme:
an integral support atom together with a rational function on it. -/
structure PrincipalDivisorGenerator (X : Scheme.{u}) where
  support : CycleSupportAtom X
  function : RationalFunctionOn support

namespace PrincipalDivisorGenerator

/-- Forget the function and keep the underlying support atom. -/
def toSupport {X : Scheme.{u}} (D : PrincipalDivisorGenerator X) : CycleSupportAtom X :=
  D.support

/-- The underlying support as an algebraic cycle. -/
def toCycle {X : Scheme.{u}} (D : PrincipalDivisorGenerator X) : AlgCycle X :=
  AlgCycle.ofSubscheme D.support.toIntClosedSubscheme

end PrincipalDivisorGenerator

end

end Cycles
end Boundary
