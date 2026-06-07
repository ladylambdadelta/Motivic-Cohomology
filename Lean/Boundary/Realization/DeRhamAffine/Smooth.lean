import Boundary.Realization.DeRhamAffine.Naturality

universe u

noncomputable section

open scoped TensorProduct
open scoped ModuleCat

namespace Boundary
namespace Realization

variable (R S : Type u)
variable [CommRing R] [CommRing S] [Algebra R S]

section Smooth

variable [Algebra.Smooth R S]

/-- For a smooth affine algebra, the first de Rham piece is projective. -/
theorem affineFirstDeRhamPiece_projective :
    Module.Projective S (affineFirstDeRhamPiece R S) :=
  inferInstance

/-- For a smooth affine algebra, the first de Rham piece is finite. -/
theorem affineFirstDeRhamPiece_finite :
    Module.Finite S (affineFirstDeRhamPiece R S) :=
  inferInstance

end Smooth

end Realization
end Boundary
