import Boundary.PrimeSupport
import Boundary.PrimeSupportCompositionHelpers

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

namespace PrimeFiniteCorrespondenceSupport

def compositionFiberProductAssocIso {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionFiberProduct P Q R ≅
      rightAssociatedCompositionFiberProduct P Q R := by
  refine
    { hom := PrimeFiniteCorrespondenceSupport.compositionFiberProductAssocIsoHom P Q R
      inv := PrimeFiniteCorrespondenceSupport.compositionFiberProductAssocIsoInv P Q R
      hom_inv_id := PrimeFiniteCorrespondenceSupport.compositionFiberProductAssocIsoHomInvId P Q R
      inv_hom_id := PrimeFiniteCorrespondenceSupport.compositionFiberProductAssocIsoInvHomId P Q R }

@[simp] theorem compositionFiberProductAssocIso_hom_comp_rightAssociatedCompositionToAmbientProduct
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
  (compositionFiberProductAssocIso P Q R).hom ≫
      rightAssociatedCompositionToAmbientProduct P Q R =
      leftAssociatedCompositionToAmbientProduct P Q R := by
  apply pullback.hom_ext
  · exact compositionFiber_condition P Q
  · exact compositionFiber_condition Q R

end PrimeFiniteCorrespondenceSupport

end -- noncomputable section

end Boundary
