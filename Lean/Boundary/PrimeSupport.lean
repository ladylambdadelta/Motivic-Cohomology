import Boundary.Basic
import Boundary.SmOver
import Boundary.ComponentGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

/-- Prime finite correspondence support data from `X` to `Y` over a chosen
source irreducible component of `X`.

Classically, a prime finite correspondence is integral and finite surjective
over an irreducible component of the source. We therefore package the chosen
source component explicitly before recording the closed immersion into the fiber
product with the target.

The structure itself uses ordinary Lean equality. The passage to geometric
prime supports modulo the isomorphism-over-product relation is handled in
`Boundary.SupportEquivalence`. -/
structure PrimeFiniteCorrespondenceSupport
    (X Y : Geometry.SmSchemeOver k) where
  sourceComponent : SourceIrreducibleComponent X
  support : Scheme
  isIntegral : IsIntegral support
  finiteOverSourceComponent : support ⟶ sourceComponent.carrier.scheme
  finite_toSourceComponent : IsFinite finiteOverSourceComponent
  surjective_toSourceComponent : Function.Surjective finiteOverSourceComponent.base
  toTarget : support ⟶ Y.scheme
  inclusion : support ⟶ overBaseProduct sourceComponent.carrier Y
  inclusion_fst : inclusion ≫ overBaseProduct.fst sourceComponent.carrier Y =
    finiteOverSourceComponent
  inclusion_snd : inclusion ≫ overBaseProduct.snd sourceComponent.carrier Y =
    toTarget
  isClosedImmersion : IsClosedImmersion inclusion

/-- Represented prime support data before quotienting by geometric
equivalence. -/
abbrev RepresentedPrimeSupport (X Y : Geometry.SmSchemeOver k) : Type (u + 1) :=
  PrimeFiniteCorrespondenceSupport X Y

namespace PrimeFiniteCorrespondenceSupport

/-- The source projection of a prime finite correspondence. -/
abbrev toSourceComponent {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport X Y) :
    Z.support ⟶ Z.sourceComponent.carrier.scheme :=
  Z.finiteOverSourceComponent

/-- The target projection of a prime finite correspondence. -/
abbrev toTargetScheme {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport X Y) : Z.support ⟶ Y.scheme :=
  Z.toTarget

/-- The source projection of a prime finite correspondence, viewed in the full
ambient source scheme. -/
abbrev toAmbientSource {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport X Y) : Z.support ⟶ X.scheme :=
  Z.finiteOverSourceComponent ≫ Z.sourceComponent.toAmbient

/-- The support-level fiber product `P.support ×_Y Q.support` used in geometric
composition. -/
abbrev compositionFiberProduct {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) : Scheme :=
  pullback P.toTargetScheme Q.toAmbientSource

/-- Projection from the composition fiber product to the left support. -/
abbrev compositionFiberFst {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionFiberProduct P Q ⟶ P.support :=
  pullback.fst P.toTargetScheme Q.toAmbientSource

/-- Projection from the composition fiber product to the right support. -/
abbrev compositionFiberSnd {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionFiberProduct P Q ⟶ Q.support :=
  pullback.snd P.toTargetScheme Q.toAmbientSource

@[simp] theorem compositionFiber_condition {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionFiberFst P Q ≫ P.toTargetScheme =
      compositionFiberSnd P Q ≫ Q.toAmbientSource := by
  simpa [compositionFiberProduct, compositionFiberFst, compositionFiberSnd] using
    pullback.condition (f := P.toTargetScheme) (g := Q.toAmbientSource)

@[simp] theorem toSourceComponent_overBase {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport X Y) :
    Z.toSourceComponent ≫ Z.sourceComponent.carrier.structMap =
      Z.toTargetScheme ≫ Y.structMap := by
  have hfst := congrArg
    (fun f => f ≫ Z.sourceComponent.carrier.structMap) Z.inclusion_fst
  have hsnd := congrArg (fun f => f ≫ Y.structMap) Z.inclusion_snd
  calc
    Z.toSourceComponent ≫ Z.sourceComponent.carrier.structMap
        = Z.inclusion ≫ overBaseProduct.fst Z.sourceComponent.carrier Y ≫
            Z.sourceComponent.carrier.structMap := by
              simpa [PrimeFiniteCorrespondenceSupport.toSourceComponent,
                Category.assoc] using hfst.symm
    _ = Z.inclusion ≫ overBaseProduct.snd Z.sourceComponent.carrier Y ≫ Y.structMap := by
          simp [overBaseProduct, Category.assoc, pullback.condition]
    _ = Z.toTargetScheme ≫ Y.structMap := by
          simpa [PrimeFiniteCorrespondenceSupport.toTargetScheme, Category.assoc] using hsnd

@[simp] theorem toAmbientSource_overBase {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport X Y) :
    Z.toAmbientSource ≫ X.structMap = Z.toTargetScheme ≫ Y.structMap := by
  simp [PrimeFiniteCorrespondenceSupport.toAmbientSource, Category.assoc,
    Z.toSourceComponent_overBase, Z.sourceComponent.toAmbient_overBase]

/-- The canonical map from the support fiber product `P.support ×_Y Q.support`
to `sourceComponent(P) ×_k Z`. -/
abbrev compositionToAmbientProduct {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionFiberProduct P Q ⟶ overBaseProduct P.sourceComponent.carrier Z :=
  pullback.lift
    (compositionFiberFst P Q ≫ P.toSourceComponent)
    (compositionFiberSnd P Q ≫ Q.toTargetScheme)
    (by
      have hP := congrArg
        (fun f => compositionFiberFst P Q ≫ f) P.toSourceComponent_overBase
      have hPQ' :
          compositionFiberFst P Q ≫ P.toTargetScheme ≫ Y.structMap =
            compositionFiberSnd P Q ≫ Q.toAmbientSource ≫ Y.structMap :=
        congrArg (fun f => f ≫ Y.structMap) (compositionFiber_condition P Q)
      have hQ := congrArg
        (fun f => compositionFiberSnd P Q ≫ f) Q.toAmbientSource_overBase
      calc
        compositionFiberFst P Q ≫ P.toSourceComponent ≫ P.sourceComponent.carrier.structMap
            = compositionFiberFst P Q ≫ P.toTargetScheme ≫ Y.structMap := by
                simpa [Category.assoc] using hP
        _ = compositionFiberSnd P Q ≫ Q.toAmbientSource ≫ Y.structMap := by
              exact hPQ'
        _ = compositionFiberSnd P Q ≫ Q.toTargetScheme ≫ Z.structMap := by
              simpa [Category.assoc] using hQ)

@[simp] theorem compositionToAmbientProduct_fst {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionToAmbientProduct P Q ≫ overBaseProduct.fst P.sourceComponent.carrier Z =
      compositionFiberFst P Q ≫ P.toSourceComponent := by
  simp [compositionToAmbientProduct]

@[simp] theorem compositionToAmbientProduct_snd {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionToAmbientProduct P Q ≫ overBaseProduct.snd P.sourceComponent.carrier Z =
      compositionFiberSnd P Q ≫ Q.toTargetScheme := by
  simp [compositionToAmbientProduct]

/-- The left-associated triple support fiber product
`(P.support ×_Y Q.support) ×_Z R.support`. -/
abbrev leftAssociatedCompositionFiberProduct {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) : Scheme :=
  pullback (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource

/-- The right-associated triple support fiber product
`P.support ×_X (Q.support ×_Y R.support)`. -/
abbrev rightAssociatedCompositionFiberProduct {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) : Scheme :=
  pullback P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)

/-- The canonical map from the left-associated triple support fiber product
`(P.support ×_X Q.support) ×_Y R.support` to `sourceComponent(P) ×_k Z`. -/
abbrev leftAssociatedCompositionToAmbientProduct {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionFiberProduct P Q R ⟶ overBaseProduct P.sourceComponent.carrier Z := by
  let leftFst : leftAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct P Q :=
    pullback.fst (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource
  let leftSnd : leftAssociatedCompositionFiberProduct P Q R ⟶ R.support :=
    pullback.snd (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource
  exact pullback.lift
    (leftFst ≫ compositionFiberFst P Q ≫ P.toSourceComponent)
    (leftSnd ≫ R.toTargetScheme)
    (by
      have hP := congrArg
        (fun f => leftFst ≫ compositionFiberFst P Q ≫ f) P.toSourceComponent_overBase
      have hPQ :
          leftFst ≫ compositionFiberFst P Q ≫ P.toTargetScheme ≫ X.structMap =
            leftFst ≫ compositionFiberSnd P Q ≫ Q.toAmbientSource ≫ X.structMap := by
        exact congrArg (fun f => f ≫ X.structMap)
          (congrArg (fun f => leftFst ≫ f) (compositionFiber_condition P Q))
      have hQ := congrArg
        (fun f => leftFst ≫ compositionFiberSnd P Q ≫ f) Q.toAmbientSource_overBase
      have hleft :
          leftFst ≫ compositionFiberSnd P Q ≫ Q.toTargetScheme ≫ Y.structMap =
            leftSnd ≫ R.toAmbientSource ≫ Y.structMap := by
        simpa [leftFst, leftSnd, Category.assoc] using
          congrArg (fun f => f ≫ Y.structMap)
            (pullback.condition (f := compositionFiberSnd P Q ≫ Q.toTargetScheme)
              (g := R.toAmbientSource))
      have hR := congrArg (fun f => leftSnd ≫ f) R.toAmbientSource_overBase
      calc
        leftFst ≫ compositionFiberFst P Q ≫ P.toSourceComponent ≫
            P.sourceComponent.carrier.structMap
            = leftFst ≫ compositionFiberFst P Q ≫ P.toTargetScheme ≫ X.structMap := by
                simpa [Category.assoc] using hP
        _ = leftFst ≫ compositionFiberSnd P Q ≫ Q.toAmbientSource ≫ X.structMap := by
              simpa [Category.assoc] using hPQ
        _ = leftFst ≫ compositionFiberSnd P Q ≫ Q.toTargetScheme ≫ Y.structMap := by
              simpa [Category.assoc] using hQ
        _ = leftSnd ≫ R.toAmbientSource ≫ Y.structMap := by
              simpa [Category.assoc] using hleft
        _ = leftSnd ≫ R.toTargetScheme ≫ Z.structMap := by
              simpa [Category.assoc] using hR)

@[simp] theorem leftAssociatedCompositionToAmbientProduct_fst
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionToAmbientProduct P Q R ≫
        overBaseProduct.fst P.sourceComponent.carrier Z =
      pullback.fst (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource ≫
        compositionFiberFst P Q ≫ P.toSourceComponent := by
  simp [leftAssociatedCompositionToAmbientProduct]

@[simp] theorem leftAssociatedCompositionToAmbientProduct_snd
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionToAmbientProduct P Q R ≫
        overBaseProduct.snd P.sourceComponent.carrier Z =
      pullback.snd (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource ≫
        R.toTargetScheme := by
  simp [leftAssociatedCompositionToAmbientProduct]

/-- The canonical map from the right-associated triple support fiber product
`P.support ×_X (Q.support ×_Y R.support)` to `sourceComponent(P) ×_k Z`. -/
abbrev rightAssociatedCompositionToAmbientProduct {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    rightAssociatedCompositionFiberProduct P Q R ⟶ overBaseProduct P.sourceComponent.carrier Z := by
  let rightFst : rightAssociatedCompositionFiberProduct P Q R ⟶ P.support :=
    pullback.fst P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)
  let rightSnd : rightAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct Q R :=
    pullback.snd P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)
  exact pullback.lift
    (rightFst ≫ P.toSourceComponent)
    (rightSnd ≫ compositionFiberSnd Q R ≫ R.toTargetScheme)
    (by
      have hP := congrArg (fun f => rightFst ≫ f) P.toSourceComponent_overBase
      have hright :
          rightFst ≫ P.toTargetScheme ≫ X.structMap =
            rightSnd ≫ compositionFiberFst Q R ≫ Q.toAmbientSource ≫ X.structMap := by
        simpa [rightFst, rightSnd, Category.assoc] using
          congrArg (fun f => f ≫ X.structMap)
            (pullback.condition (f := P.toTargetScheme)
              (g := compositionFiberFst Q R ≫ Q.toAmbientSource))
      have hQ := congrArg
        (fun f => rightSnd ≫ compositionFiberFst Q R ≫ f) Q.toAmbientSource_overBase
      have hQR :
          rightSnd ≫ compositionFiberFst Q R ≫ Q.toTargetScheme ≫ Y.structMap =
            rightSnd ≫ compositionFiberSnd Q R ≫ R.toAmbientSource ≫ Y.structMap := by
        exact congrArg (fun f => f ≫ Y.structMap)
          (congrArg (fun f => rightSnd ≫ f) (compositionFiber_condition Q R))
      have hR := congrArg
        (fun f => rightSnd ≫ compositionFiberSnd Q R ≫ f) R.toAmbientSource_overBase
      calc
        rightFst ≫ P.toSourceComponent ≫ P.sourceComponent.carrier.structMap
            = rightFst ≫ P.toTargetScheme ≫ X.structMap := by
                simpa [Category.assoc] using hP
        _ = rightSnd ≫ compositionFiberFst Q R ≫ Q.toAmbientSource ≫ X.structMap := by
              simpa [Category.assoc] using hright
        _ = rightSnd ≫ compositionFiberFst Q R ≫ Q.toTargetScheme ≫ Y.structMap := by
              simpa [Category.assoc] using hQ
        _ = rightSnd ≫ compositionFiberSnd Q R ≫ R.toAmbientSource ≫ Y.structMap := by
              simpa [Category.assoc] using hQR
        _ = rightSnd ≫ compositionFiberSnd Q R ≫ R.toTargetScheme ≫ Z.structMap := by
              simpa [Category.assoc] using hR)

@[simp] theorem rightAssociatedCompositionToAmbientProduct_fst
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    rightAssociatedCompositionToAmbientProduct P Q R ≫
        overBaseProduct.fst P.sourceComponent.carrier Z =
      pullback.fst P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource) ≫
        P.toSourceComponent := by
  simp [rightAssociatedCompositionToAmbientProduct]

@[simp] theorem rightAssociatedCompositionToAmbientProduct_snd
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    rightAssociatedCompositionToAmbientProduct P Q R ≫
        overBaseProduct.snd P.sourceComponent.carrier Z =
      pullback.snd P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource) ≫
        compositionFiberSnd Q R ≫ R.toTargetScheme := by
  simp [rightAssociatedCompositionToAmbientProduct]

/-- Canonical associativity isomorphism for iterated support fiber products. -/
def compositionFiberProductAssocIso {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionFiberProduct P Q R ≅
      rightAssociatedCompositionFiberProduct P Q R := by
  classical
  let leftFst : leftAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct P Q :=
    pullback.fst (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource
  let leftSnd : leftAssociatedCompositionFiberProduct P Q R ⟶ R.support :=
    pullback.snd (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource
  let rightFst : rightAssociatedCompositionFiberProduct P Q R ⟶ P.support :=
    pullback.fst P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)
  let rightSnd : rightAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct Q R :=
    pullback.snd P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)
  let leftToQR : leftAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct Q R :=
    pullback.lift (leftFst ≫ compositionFiberSnd P Q) leftSnd (by
      simpa [leftFst, leftSnd, Category.assoc] using
        pullback.condition (f := compositionFiberSnd P Q ≫ Q.toTargetScheme)
          (g := R.toAmbientSource))
  let hom : leftAssociatedCompositionFiberProduct P Q R ⟶
      rightAssociatedCompositionFiberProduct P Q R :=
    pullback.lift (leftFst ≫ compositionFiberFst P Q) leftToQR (by
      calc
        leftFst ≫ compositionFiberFst P Q ≫ P.toTargetScheme
            = leftFst ≫ compositionFiberSnd P Q ≫ Q.toAmbientSource := by
                simpa [Category.assoc] using
                  congrArg (fun f => leftFst ≫ f) (compositionFiber_condition P Q)
        _ = leftToQR ≫ compositionFiberFst Q R ≫ Q.toAmbientSource := by
              simp [leftToQR, Category.assoc])
  let rightToPQ : rightAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct P Q :=
    pullback.lift rightFst (rightSnd ≫ compositionFiberFst Q R) (by
      simpa [rightFst, rightSnd, Category.assoc] using
        pullback.condition (f := P.toTargetScheme)
          (g := compositionFiberFst Q R ≫ Q.toAmbientSource))
  let inv : rightAssociatedCompositionFiberProduct P Q R ⟶
      leftAssociatedCompositionFiberProduct P Q R :=
    pullback.lift rightToPQ (rightSnd ≫ compositionFiberSnd Q R) (by
      calc
        rightToPQ ≫ compositionFiberSnd P Q ≫ Q.toTargetScheme
            = rightSnd ≫ compositionFiberFst Q R ≫ Q.toTargetScheme := by
                simp [rightToPQ, Category.assoc]
        _ = rightSnd ≫ compositionFiberSnd Q R ≫ R.toAmbientSource := by
              simpa [Category.assoc] using
                congrArg (fun f => rightSnd ≫ f) (compositionFiber_condition Q R)
      )
  refine
    { hom := hom
      inv := inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [hom, inv, leftFst, rightFst, rightToPQ, Category.assoc]
      · simp [hom, inv, leftFst, rightSnd, rightToPQ, leftToQR, Category.assoc]
    · simp [hom, inv, leftSnd, rightSnd, leftToQR, Category.assoc]
  · apply pullback.hom_ext
    · simp [hom, inv, leftFst, rightFst, rightToPQ, Category.assoc]
    · apply pullback.hom_ext
      · simp [hom, inv, leftFst, leftSnd, rightSnd, rightToPQ, leftToQR, Category.assoc]
      · simp [hom, inv, leftSnd, rightSnd, leftToQR, Category.assoc]

    @[simp] theorem compositionFiberProductAssocIso_hom_comp_rightAssociatedCompositionToAmbientProduct
      {W X Y Z : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
      (R : RepresentedPrimeSupport Y Z) :
      (compositionFiberProductAssocIso P Q R).hom ≫
        rightAssociatedCompositionToAmbientProduct P Q R =
        leftAssociatedCompositionToAmbientProduct P Q R := by
      apply pullback.hom_ext
      · simp [compositionFiberProductAssocIso, leftAssociatedCompositionToAmbientProduct,
        rightAssociatedCompositionToAmbientProduct, Category.assoc]
      · simp [compositionFiberProductAssocIso, leftAssociatedCompositionToAmbientProduct,
        rightAssociatedCompositionToAmbientProduct, Category.assoc]

/-- The induced closed immersion into `sourceComponent ×_k Y`. -/
abbrev inducedMap {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport X Y) :
  Z.support ⟶ overBaseProduct Z.sourceComponent.carrier Y :=
  Z.inclusion

end PrimeFiniteCorrespondenceSupport

end -- noncomputable section

end Boundary
