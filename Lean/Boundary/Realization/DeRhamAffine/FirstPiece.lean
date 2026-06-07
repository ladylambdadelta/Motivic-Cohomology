import Boundary.Realization.DeRhamAffine.Basic
import Mathlib.RingTheory.Kaehler.Basic

universe u

noncomputable section

namespace Boundary
namespace Realization

variable (R S : Type u)
variable [CommRing R] [CommRing S] [Algebra R S]

section Map

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- The induced map on the first de Rham piece. -/
noncomputable def affineFirstDeRhamPieceMap (f : A →ₐ[R] B) :
    letI : Module A (affineFirstDeRhamPiece R B) :=
      Module.compHom (affineFirstDeRhamPiece R B) f.toRingHom
    affineFirstDeRhamPiece R A →ₗ[A] affineFirstDeRhamPiece R B := by
  letI : Algebra A B := f.toAlgebra
  letI : Module A (affineFirstDeRhamPiece R B) :=
    Module.compHom (affineFirstDeRhamPiece R B) f.toRingHom
  exact KaehlerDifferential.map R R A B

theorem affineFirstDeRhamPieceMap_D (f : A →ₐ[R] B) (x : A) :
    affineFirstDeRhamPieceMap (R := R) f (affineDeRhamD R A x) =
      affineDeRhamD R B (f x) := by
  letI : Algebra A B := f.toAlgebra
  letI : Module A (affineFirstDeRhamPiece R B) :=
    Module.compHom (affineFirstDeRhamPiece R B) f.toRingHom
  change KaehlerDifferential.map R R A B (KaehlerDifferential.D R A x) =
    KaehlerDifferential.D R B (f x)
  exact KaehlerDifferential.map_D R R A B x

end Map

end Realization
end Boundary
