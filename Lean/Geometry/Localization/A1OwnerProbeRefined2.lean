import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.RingTheory.FiniteType
import Geometry.Schemes.Basic

/-!
Refined temporary owner-layer probe for the affine line over `k`.

This isolates the remaining owner-layer obligations after separating off the
instance facts that do already follow from the current mathlib API.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Geometry

noncomputable section

variable (k : Type u) [Field k] [PerfectField k]

abbrev a1SchemeProbe : Scheme.{u} :=
  AlgebraicGeometry.AffineSpace (Fin 1) (Spec (CommRingCat.of k))

abbrev a1StructMapProbe : a1SchemeProbe k ⟶ Spec (CommRingCat.of k) :=
  (AlgebraicGeometry.AffineSpace.over (n := Fin 1) (S := Spec (CommRingCat.of k))).hom

example : IsSeparated (a1StructMapProbe k) := by
  infer_instance

example : QuasiCompact (a1StructMapProbe k) := by
  infer_instance

example : RingHom.FiniteType (MvPolynomial.C : k →+* MvPolynomial (Fin 1) k) :=
  FiniteType.mvPolynomial k (Fin 1)

example : RingHom.IsStandardSmooth (MvPolynomial.C : k →+* MvPolynomial (Fin 1) k) := by
  infer_instance

end

end Geometry
