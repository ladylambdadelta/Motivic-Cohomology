import Boundary.Realization.DeRhamAffine.Maps

universe u

noncomputable section

open scoped TensorProduct
open scoped ModuleCat

attribute [local instance] IsScalarTower.of_compHom SMulCommClass.of_commMonoid

namespace Boundary
namespace Realization

variable (R : Type u)
variable [CommRing R]

section Map

variable {A B : Type u}
variable [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The Kähler first-piece map carries the universal differential of `x`
to the universal differential of its image. -/
theorem affineFirstDeRhamPieceMap_apply_D
    (f : A →ₐ[R] B) (x : A) :
    affineFirstDeRhamPieceMap (R := R) f (affineDeRhamD R A x) =
      affineDeRhamD R B (f x) :=
  affineFirstDeRhamPieceMap_D (R := R) f x

/-- The degree-zero de Rham differential is natural for `R`-algebra maps,
as an equality of `R`-linear maps into Kähler one-forms. -/
theorem affineDeRhamD_naturality
    (f : A →ₐ[R] B) :
    letI : Algebra A B := f.toAlgebra
    ((KaehlerDifferential.map R R A B).restrictScalars R).comp
      ((affineDeRhamD R A).toLinearMap.restrictScalars R) =
    ((affineDeRhamD R B).toLinearMap.restrictScalars R).comp
      f.toLinearMap := by
  letI : Algebra A B := f.toAlgebra
  apply LinearMap.ext
  intro x
  exact KaehlerDifferential.map_D R R A B x

end Map

end Realization
end Boundary
