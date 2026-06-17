import Boundary.PrimeSupport

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

namespace PrimeFiniteCorrespondenceSupport

private abbrev leftFst {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct P Q :=
  pullback.fst (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource

private abbrev leftSnd {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionFiberProduct P Q R ⟶ R.support :=
  pullback.snd (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource

private abbrev rightFst {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    rightAssociatedCompositionFiberProduct P Q R ⟶ P.support :=
  pullback.fst P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)

private abbrev rightSnd {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    rightAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct Q R :=
  pullback.snd P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)

private abbrev leftToQR {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct Q R :=
  pullback.lift (leftFst P Q R ≫ compositionFiberSnd P Q) (leftSnd P Q R) (by
    exact congrArg (fun f => f ≫ R.toAmbientSource) (compositionFiber_condition P Q))

private abbrev rightToPQ {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    rightAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct P Q :=
  pullback.lift (rightFst P Q R) (rightSnd P Q R ≫ compositionFiberFst Q R) (by
    exact congrArg (fun f => f ≫ Q.toAmbientSource) (compositionFiber_condition Q R))

private def hom {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionFiberProduct P Q R ⟶
      rightAssociatedCompositionFiberProduct P Q R :=
  pullback.lift (leftFst P Q R ≫ compositionFiberFst P Q) (leftToQR P Q R) (by
    calc
      leftFst P Q R ≫ compositionFiberFst P Q ≫ P.toTargetScheme =
          leftFst P Q R ≫ compositionFiberSnd P Q ≫ Q.toAmbientSource := by
            exact congrArg (fun f => leftFst P Q R ≫ f) (compositionFiber_condition P Q)
      _ = leftToQR P Q R ≫ compositionFiberFst Q R ≫ Q.toAmbientSource := by
            exact congrArg (fun f => f ≫ Q.toAmbientSource)
              (pullback.lift_fst (leftFst P Q R ≫ compositionFiberSnd P Q)
                (leftSnd P Q R)
                (congrArg (fun f => f ≫ R.toAmbientSource) (compositionFiber_condition P Q))).symm)

private def inv {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    rightAssociatedCompositionFiberProduct P Q R ⟶
      leftAssociatedCompositionFiberProduct P Q R :=
  pullback.lift (rightToPQ P Q R) (rightSnd P Q R ≫ compositionFiberSnd Q R) (by
    calc
      rightToPQ P Q R ≫ compositionFiberSnd P Q ≫ Q.toTargetScheme =
          rightSnd P Q R ≫ compositionFiberFst Q R ≫ Q.toTargetScheme := by
            exact congrArg (fun f => f ≫ Q.toTargetScheme)
              (pullback.lift_snd (rightFst P Q R) (rightSnd P Q R ≫ compositionFiberFst Q R)
                (congrArg (fun f => f ≫ Q.toAmbientSource) (compositionFiber_condition Q R)))
      _ = rightSnd P Q R ≫ compositionFiberSnd Q R ≫ R.toAmbientSource := by
            exact congrArg (fun f => rightSnd P Q R ≫ f) (compositionFiber_condition Q R))

def compositionFiberProductAssocIsoHom {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionFiberProduct P Q R ⟶
      rightAssociatedCompositionFiberProduct P Q R :=
  hom P Q R

def compositionFiberProductAssocIsoInv {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    rightAssociatedCompositionFiberProduct P Q R ⟶
      leftAssociatedCompositionFiberProduct P Q R :=
  inv P Q R

theorem compositionFiberProductAssocIsoHomInvId {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    compositionFiberProductAssocIsoHom P Q R ≫ compositionFiberProductAssocIsoInv P Q R =
      𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact compositionFiber_condition P Q
    · exact pullback.lift_snd _ _ _
  · exact pullback.lift_snd _ _ _

theorem compositionFiberProductAssocIsoInvHomId {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    compositionFiberProductAssocIsoInv P Q R ≫ compositionFiberProductAssocIsoHom P Q R =
      𝟙 _ := by
  apply pullback.hom_ext
  · exact pullback.lift_fst _ _ _
  · apply pullback.hom_ext
    · exact pullback.lift_snd _ _ _
    · exact compositionFiber_condition Q R

end PrimeFiniteCorrespondenceSupport

end -- noncomputable section

end Boundary
