import Boundary.Realization.DeRhamAffine.D1Quotient

universe u

noncomputable section

open scoped TensorProduct
open scoped ModuleCat

namespace Boundary
namespace Realization

variable (R S : Type u)
variable [CommRing R] [CommRing S] [Algebra R S]

section Map

variable {A : Type u}
variable [CommRing A] [Algebra R A]

theorem affineD1_comp_affineDeRhamD0ToOneForms :
    (affineD1 (R := R) (A := A)).comp
      ((affineDeRhamD R A).toLinearMap.restrictScalars R) = 0 := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  exact affineD1_D (R := R) (A := A) x

end Map

end Realization
end Boundary
