import Mathlib.AlgebraicGeometry.AffineSpace
import Lean.Geometry.Schemes.Basic

/-!
This file is the owner-layer probe for the honest affine line over `k`.

The current task is to determine whether mathlib already exposes enough
structure to package `A¹_k` as an object of `Sm/k`, or whether a genuine
owner-layer theorem is still missing. The examples below are a reversible
instance probe for the map `A¹_k → Spec k`.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Geometry

variable (k : Type u) [Field k] [PerfectField k]

/-- Probe notation for the affine line over `Spec k`. -/
abbrev a1Scheme : Scheme.{u} :=
  AlgebraicGeometry.AffineSpace (Fin 1) (Spec (CommRingCat.of k))

/-- Probe notation for the structural map `A¹_k → Spec k`. -/
abbrev a1StructMap : a1Scheme k ⟶ Spec (CommRingCat.of k) :=
  (AlgebraicGeometry.AffineSpace.over (n := Fin 1) (S := Spec (CommRingCat.of k))).hom

example : IsSeparated (a1StructMap k) := by
  infer_instance

example : LocallyOfFiniteType (a1StructMap k) := by
  infer_instance

example : QuasiCompact (a1StructMap k) := by
  infer_instance

example : IsSmooth (a1StructMap k) := by
  infer_instance

end Geometry
