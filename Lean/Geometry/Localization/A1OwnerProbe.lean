import Mathlib.AlgebraicGeometry.AffineSpace
import Geometry.Schemes.Basic

/-!
Temporary owner-layer probe for the affine line over `k`.

This file exists only to test whether the existing mathlib affine-space API
already provides the instance package needed to build `A1_k` as an object of
`Sm/k`.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Geometry

variable (k : Type u) [Field k] [PerfectField k]

abbrev a1SchemeProbe : Scheme.{u} :=
  AlgebraicGeometry.AffineSpace (Fin 1) (Spec (CommRingCat.of k))

abbrev a1StructMapProbe : a1SchemeProbe k ⟶ Spec (CommRingCat.of k) :=
  (AlgebraicGeometry.AffineSpace.over (n := Fin 1) (S := Spec (CommRingCat.of k))).hom

example : IsSeparated (a1StructMapProbe k) := by
  infer_instance

example : LocallyOfFiniteType (a1StructMapProbe k) := by
  infer_instance

example : QuasiCompact (a1StructMapProbe k) := by
  infer_instance

example : IsSmooth (a1StructMapProbe k) := by
  infer_instance

end Geometry
