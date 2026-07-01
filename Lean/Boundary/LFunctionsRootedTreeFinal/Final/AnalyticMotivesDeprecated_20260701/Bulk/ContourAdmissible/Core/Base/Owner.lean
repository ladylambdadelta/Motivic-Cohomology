import Mathlib.AlgebraicGeometry.Scheme

/-!
# Arithmetic base for analytic bulks

This file owns the base layer for analytic bulk objects.  It records the
arithmetic ground over which analytic carriers are interpreted.  Carrier,
mapping, product, boundary, and contour data are downstream.

Foundational source: mathlib's `AlgebraicGeometry.Scheme` API supplies the
algebraic shadow for comparison with objects over `ℚ`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The algebraic shadow carried by an analytic bulk object. -/
abbrev ArithmeticBase : Type _ :=
  AlgebraicGeometry.Scheme

end AnalyticMotives
end LFunctions
end Boundary
