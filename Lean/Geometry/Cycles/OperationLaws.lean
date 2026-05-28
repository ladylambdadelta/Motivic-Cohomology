import Geometry.Cycles.Basic

/-!
# Cycle Operation Laws

This file records currently available coefficient laws that follow directly from
the `Finsupp` presentation of `AlgCycle`.

Boundary of the current implementation (not yet formalized here):

* `finiteMapImageMultiplicity`
* `finitePushforwardIntegralSubscheme`
* `finitePushforwardCycle`
* `finitePushforwardCycle_coeff_eq_genericLength`

These require real algebraic-geometry input:

* general scheme-theoretic image (or adequate affine/local reduction);
* generic-point or generic-rank/length API;
* local length/rank theorem for finite morphisms;
* proof that finite pushforward has finite support.
-/

universe u

open AlgebraicGeometry

namespace AlgCycle

variable {X : Scheme.{u}}

@[simp] theorem ofSubscheme_apply_self (Z : IntClosedSubscheme X) :
    (AlgCycle.ofSubscheme Z) Z = 1 := by
  classical
  simp [AlgCycle.ofSubscheme]

@[simp] theorem ofSubscheme_apply_of_ne
    (Z W : IntClosedSubscheme X) (h : W ≠ Z) :
    (AlgCycle.ofSubscheme Z) W = 0 := by
  classical
  simp [AlgCycle.ofSubscheme, Finsupp.single_apply, h.symm]

end AlgCycle
