import Boundary.Diagonal
import Boundary.NisnevichDescent
import Geometry.Correspondences.Composition
import Geometry.Correspondences.Graph

/-!
# Graph-Based Transfer Maps for Pulled-Back Nisnevich Squares

This file provides the graph-correspondence constructors for the four transfer
maps of a base-changed Nisnevich distinguished square.

## Strategy

Given a Nisnevich square `sq` and a base-change morphism `f : SmOverHom Y sq.base`,
the transfer maps for the pulled-back square are constructed as graph correspondences
of the scheme-level projection morphisms, using
`Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition`.

The geometric base-change data are taken from
`Boundary.NisnevichDescent.NisnevichDistinguishedSquareDataQ.baseChange_*`.
The only extra inputs here are the finite irreducible-component decompositions
needed to turn the structural morphisms of the pulled-back square into graph
correspondences.

## Exact remaining blocker for `NisnevichDistinguishedSquareDataQ.pullback`

Once the four transfer maps defined here are in hand, the hard remaining
obligation is the commutativity condition
`overlap_to_base_transfer_commutes` for the pulled-back square. That proof is
routed only through the canonical rational graph theorem
`Geometry.ordinaryMorphismGraph_comp_canonical_Q`, not through any abstract
`SmCorQ` graph-functoriality hypothesis.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory
open Boundary.RepresentedPrimeFiniteCorrespondenceComposition

namespace Boundary

noncomputable section

abbrev CanonicalCompositionData :=
  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData
    (k := k)

abbrev canonicalCategory
    (composition : CanonicalCompositionData (k := k)) :
    SmCorQ (k := k) :=
  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData.canonicalSmCorQ
    composition

abbrev ConcreteLiftedPackages :=
  {X Y Z : Geometry.SmSchemeOver k} →
  Boundary.PrimeFiniteCorrespondenceGeom X Y →
  Boundary.PrimeFiniteCorrespondenceGeom Y Z →
  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage (k := k)

abbrev ConcreteLiftedIdentityPackages :=
  {X Y : Geometry.SmSchemeOver k} →
  Boundary.PrimeFiniteCorrespondenceGeom X Y →
  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage (k := k)

abbrev concreteCanonicalComposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → Boundary.FiniteIrreducibleComponentDecomposition X)
    (packages : ConcreteLiftedPackages (k := k))
    (leftIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (leftIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y)
        (component : Boundary.SourceIrreducibleComponent X)
        (toComponent : P.sourceImage.carrier.scheme ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.sourceImage.toAmbient),
          packages (Boundary.SourceIrreducibleComponent.diagonalPrimeGeom component)
              (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) =
            leftIdentityPackage (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P))
    (rightIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (rightIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : Boundary.PrimeFiniteCorrespondenceGeom X Y)
        (diagClass : Boundary.PrimeFiniteCorrespondenceGeom Y Y),
          diagClass ∈ (diagonalDecomposition Y).diagonalPrimeClasses →
            packages prime diagClass = rightIdentityPackage prime)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y),
          SupportFiberProductImageCompositionPackageFamily.decomposition
              (fun {X} {Y} {Z} x y =>
                SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))
              P
              (Boundary.SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            Boundary.RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (toFiniteCorrespondenceCompositionData
              (SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                        (packages (X := X) (Y := Y) (Z := Z) x y))
                  P Q)))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              Boundary.FiniteCorrespondencePresentation.toGeom (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (toFiniteCorrespondenceCompositionData
              (SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                        (packages (X := X) (Y := Y) (Z := Z) x y))
                  Q R))) =
              Boundary.FiniteCorrespondencePresentation.toGeom (rightPresentation P Q R)) :
    CanonicalCompositionData (k := k) :=
  CanonicalCompositionPackageData.ofConcreteLiftedDecompositionFamily
      diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
      rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
      leftPresentation rightPresentation hpresentation hleft hright

abbrev concreteCanonicalCategory
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → Boundary.FiniteIrreducibleComponentDecomposition X)
    (packages : ConcreteLiftedPackages (k := k))
    (leftIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (leftIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y)
        (component : Boundary.SourceIrreducibleComponent X)
        (toComponent : P.sourceImage.carrier.scheme ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.sourceImage.toAmbient),
          packages (Boundary.SourceIrreducibleComponent.diagonalPrimeGeom component)
              (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) =
            leftIdentityPackage (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P))
    (rightIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (rightIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : Boundary.PrimeFiniteCorrespondenceGeom X Y)
        (diagClass : Boundary.PrimeFiniteCorrespondenceGeom Y Y),
          diagClass ∈ (diagonalDecomposition Y).diagonalPrimeClasses →
            packages prime diagClass = rightIdentityPackage prime)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y),
          SupportFiberProductImageCompositionPackageFamily.decomposition
              (fun {X} {Y} {Z} x y =>
                SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))
              P
              (Boundary.SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            Boundary.RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (toFiniteCorrespondenceCompositionData
              (SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                        (packages (X := X) (Y := Y) (Z := Z) x y))
                  P Q)))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              Boundary.FiniteCorrespondencePresentation.toGeom (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (toFiniteCorrespondenceCompositionData
              (SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                        (packages (X := X) (Y := Y) (Z := Z) x y))
                  Q R))) =
              Boundary.FiniteCorrespondencePresentation.toGeom (rightPresentation P Q R)) :
    SmCorQ (k := k) :=
  canonicalCategory
    (concreteCanonicalComposition
      diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
      rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
      leftPresentation rightPresentation hpresentation hleft hright)

namespace SmCorQ

/-- The graph-correspondence transfer map of an ordinary `Sm/k` morphism,
given a certified finite irreducible-component decomposition of the source.

This is a named alias for
`Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition`
placed in the `SmCorQ` namespace for use in Nisnevich-square constructions. -/
def graphTransfer
    (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (f : SmOverHom X Y)
    (decomp : FiniteIrreducibleComponentDecomposition X) :
    SmCorQ.Hom category X Y :=
  Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category f decomp

/-- `graphTransfer` does not depend on the choice of finite irreducible-component
decomposition of the source. -/
theorem graphTransfer_independent
    (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (f : SmOverHom X Y)
    (D₁ D₂ : FiniteIrreducibleComponentDecomposition X) :
    SmCorQ.graphTransfer category f D₁ = SmCorQ.graphTransfer category f D₂ :=
  Geometry.ordinaryMorphismGraph_rationalCorrespondence_independent category f D₁ D₂

/-- The componentwise graph support of the identity morphism is equivalent to
the diagonal represented prime support on the same source component. -/
theorem graphPrimeSupportEquivalent_id
    {X : Geometry.SmSchemeOver k}
    (component : Boundary.SourceIrreducibleComponent X) :
    Boundary.PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent
      (Geometry.ordinaryMorphismGraphPrimeSupport component (Boundary.SmOverHom.id X))
      (Boundary.SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component) := by
  let P :=
    Geometry.ordinaryMorphismGraphPrimeSupport component (Boundary.SmOverHom.id X)
  have hfinite : IsIso P.finiteOverSourceComponent := by
    change IsIso
      (Geometry.ordinaryMorphismGraphMap
          (Geometry.ordinaryMorphismOnSourceComponent component (Boundary.SmOverHom.id X)) ≫
        Boundary.sourceOverBaseProduct.fst (k := k)
          { scheme := component.carrier.scheme
            structMap := component.carrier.structMap } X)
    rw [Geometry.ordinaryMorphismGraphMap_sourceOverBaseProduct_fst]
    infer_instance
  letI := hfinite
  have htarget : P.toTarget = P.toAmbientSource := by
    change component.toAmbient ≫ (𝟙 X.scheme) =
      P.finiteOverSourceComponent ≫ component.toAmbient
    rw [Category.comp_id]
    change component.toAmbient =
      (Geometry.ordinaryMorphismGraphMap
          (Geometry.ordinaryMorphismOnSourceComponent component (Boundary.SmOverHom.id X)) ≫
        Boundary.sourceOverBaseProduct.fst (k := k)
          { scheme := component.carrier.scheme
            structMap := component.carrier.structMap } X) ≫
        component.toAmbient
    rw [Geometry.ordinaryMorphismGraphMap_sourceOverBaseProduct_fst]
    rw [Category.id_comp]
  exact
    Boundary.SourceImageSubscheme.primeSupportEquivalent_diagonal_of_isIso_toSourceImage_of_target_eq
      P htarget

/-- The componentwise graph singleton of the identity morphism is exactly the
diagonal singleton correspondence on the same source component. -/
theorem graphComponentCorrespondence_id
    {X : Geometry.SmSchemeOver k}
    (component : Boundary.SourceIrreducibleComponent X) :
    Geometry.ordinaryMorphismGraph_componentCorrespondence component (Boundary.SmOverHom.id X) =
      Boundary.SourceIrreducibleComponent.diagonalFiniteCorrespondence component := by
  rw [Geometry.ordinaryMorphismGraph_componentCorrespondence]
  exact Boundary.SourceIrreducibleComponent.single_eq_diagonal_of_primeSupportEquivalent
    (component := component)
    (graphPrimeSupportEquivalent_id (k := k) component)

/-- The graph transfer of the identity morphism recovers the rationalized
component-sum identity correspondence attached to the chosen decomposition. -/
theorem graphTransfer_id_eq_toRational_identity
    (category : SmCorQ (k := k))
    {X : Geometry.SmSchemeOver k}
  (D : Boundary.FiniteIrreducibleComponentDecomposition X) :
    SmCorQ.graphTransfer category (Boundary.SmOverHom.id X) D =
      Boundary.FiniteCorrespondence.toRational (D.identityFiniteCorrespondence) := by
  unfold SmCorQ.graphTransfer
  unfold Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition
  apply congrArg Boundary.FiniteCorrespondence.toRational
  rw [Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition]
  rw [Boundary.FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_eq_sum_components]
  refine Finset.sum_congr (β := Boundary.FiniteCorrespondence X X) rfl ?_
  intro component hcomponent
  exact graphComponentCorrespondence_id (k := k) component

/-- At the canonical diagonal decomposition, the graph transfer of the
identity morphism is the categorical identity in `SmCorQ`. -/
theorem graphTransfer_id
    (category : SmCorQ (k := k))
    {X : Geometry.SmSchemeOver k} :
    SmCorQ.graphTransfer category (Boundary.SmOverHom.id X)
      (category.integral.composition.diagonalDecomposition X) = category.id X := by
  rw [SmCorQ.id, Boundary.FiniteCorrespondenceCompositionData.idQ,
    Boundary.FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondenceQ]
  exact graphTransfer_id_eq_toRational_identity (category := category)
    (D := category.integral.composition.diagonalDecomposition X)

/-- The representable transfer map attached to a graph correspondence acts by
precomposition with that graph correspondence. -/
@[simp] theorem QtrMap_graphTransfer_app
    (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (D : Boundary.FiniteIrreducibleComponentDecomposition X)
    (W : Geometry.SmSchemeOver k)
    (corr : SmCorQ.Hom category W X) :
    letI := SmCorQCat category
    (QtrMap (category := category)
      (SmCorQ.graphTransfer category f D)).app (Opposite.op W) corr =
        category.comp corr (SmCorQ.graphTransfer category f D) :=
  rfl

/-- The representable transfer map attached to the graph of the identity
ordinary morphism is the identity natural transformation. -/
theorem QtrMap_graph_id
    (category : SmCorQ (k := k))
    {X : Geometry.SmSchemeOver k} :
    QtrMap (category := category)
      (SmCorQ.graphTransfer category (Boundary.SmOverHom.id X)
        (category.integral.composition.diagonalDecomposition X)) =
      𝟙 (Qtr (category := category) X) := by
  letI := SmCorQCat category
  rw [SmCorQ.graphTransfer_id]
  ext W corr
  exact category.comp_id corr

/-- Canonical-composition specialization of `graphTransfer_id`, stated with the
repository's `CanonicalCompositionData` surface so downstream files can use it
without referring to the raw `SmCorQ` owner theorem name. -/
theorem canonicalComposition_graphTransfer_id
    (composition : Boundary.CanonicalCompositionData (k := k))
    {X : Geometry.SmSchemeOver k} :
    SmCorQ.graphTransfer (Boundary.canonicalCategory composition)
      (Boundary.SmOverHom.id X)
      (composition.diagonalDecomposition X) =
        (Boundary.canonicalCategory composition).id X := by
  change
    SmCorQ.graphTransfer (Boundary.canonicalCategory composition)
      (Boundary.SmOverHom.id X)
      ((Boundary.canonicalCategory composition).integral.composition.diagonalDecomposition X) =
        (Boundary.canonicalCategory composition).id X
  exact graphTransfer_id
    (category := Boundary.canonicalCategory composition) (X := X)

/-- In the canonical rational correspondence category, graph correspondences of
ordinary morphisms compose by the existing diagonal/composition package.  The
proof unfolds `graphTransfer` to
`Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition` and
then applies Voevodsky's graph-composition construction through the canonical
package-family theorem `Geometry.ordinaryMorphismGraph_comp_canonical_Q`. -/
theorem canonicalComposition_graphTransfer_comp
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (g : Boundary.SmOverHom Y Z) :
    (Boundary.canonicalCategory composition).comp
      (SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        f
        (composition.diagonalDecomposition X))
      (SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        g
        (composition.diagonalDecomposition Y)) =
      SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        (Boundary.SmOverHom.comp f g)
        (composition.diagonalDecomposition X) := by
  change
    (Boundary.canonicalCategory composition).comp
      (Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition
          (Boundary.canonicalCategory composition) f
          (composition.diagonalDecomposition X))
      (Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition
          (Boundary.canonicalCategory composition) g
          (composition.diagonalDecomposition Y)) =
      Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition
        (Boundary.canonicalCategory composition) (Boundary.SmOverHom.comp f g)
        (composition.diagonalDecomposition X)
  exact Geometry.ordinaryMorphismGraph_comp_canonical_Q_ofCompatibilityObligation
    composition
    hgraph
    f
    g
    (composition.diagonalDecomposition X)
    (composition.diagonalDecomposition Y)

/-- The representable transfer map attached to the graph of a composite
ordinary morphism is the composite of the representable graph-transfer maps. -/
theorem QtrMap_graph_comp
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (g : Boundary.SmOverHom Y Z) :
    QtrMap (category := Boundary.canonicalCategory composition)
      (SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        (Boundary.SmOverHom.comp f g)
        (composition.diagonalDecomposition X)) =
      QtrMap (category := Boundary.canonicalCategory composition)
        (SmCorQ.graphTransfer
          (Boundary.canonicalCategory composition)
          f
          (composition.diagonalDecomposition X)) ≫
        QtrMap (category := Boundary.canonicalCategory composition)
          (SmCorQ.graphTransfer
            (Boundary.canonicalCategory composition)
            g
            (composition.diagonalDecomposition Y)) := by
  letI := SmCorQCat (Boundary.canonicalCategory composition)
  ext W corr
  change (Boundary.canonicalCategory composition).comp corr
      (SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        (Boundary.SmOverHom.comp f g)
        (composition.diagonalDecomposition X)) =
    (Boundary.canonicalCategory composition).comp
      ((Boundary.canonicalCategory composition).comp corr
        (SmCorQ.graphTransfer
          (Boundary.canonicalCategory composition)
          f
          (composition.diagonalDecomposition X)))
      (SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        g
        (composition.diagonalDecomposition Y))
  rw [(Boundary.canonicalCategory composition).assoc]
  rw [canonicalComposition_graphTransfer_comp
    (composition := composition) hgraph (f := f) (g := g)]

end SmCorQ

/-- Boundary-namespace wrapper around the canonical-composition specialization
of `SmCorQ.graphTransfer_id`, avoiding downstream references through the
`SmCorQ` namespace. -/
theorem canonicalCategory_graphTransfer_id
    (composition : Boundary.CanonicalCompositionData (k := k))
    {X : Geometry.SmSchemeOver k} :
    SmCorQ.graphTransfer (Boundary.canonicalCategory composition)
      (Boundary.SmOverHom.id X)
      (composition.diagonalDecomposition X) =
        (Boundary.canonicalCategory composition).id X := by
  open SmCorQ in
    exact
      (canonicalComposition_graphTransfer_id (composition := composition) (X := X))

/-- Boundary-namespace wrapper around the canonical graph-composition theorem,
stated directly for `canonicalCategory`. -/
theorem canonicalCategory_graphTransfer_comp
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (g : Boundary.SmOverHom Y Z) :
    (Boundary.canonicalCategory composition).comp
      (SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        f
        (composition.diagonalDecomposition X))
      (SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        g
        (composition.diagonalDecomposition Y)) =
      SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        (Boundary.SmOverHom.comp f g)
        (composition.diagonalDecomposition X) := by
  open SmCorQ in
    exact
      (canonicalComposition_graphTransfer_comp
        (composition := composition) hgraph (f := f) (g := g))

namespace NisnevichDistinguishedSquareDataQ

/-- The finite decompositions needed to realize the four structural maps of a
base-changed Nisnevich square as graph correspondences. -/
structure BaseChangeDecompositions {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) where
  openDecomp :
    Boundary.FiniteIrreducibleComponentDecomposition
      (NisnevichDistinguishedSquareDataQ.baseChange_open sq f)
  patchDecomp :
    Boundary.FiniteIrreducibleComponentDecomposition
      (NisnevichDistinguishedSquareDataQ.baseChange_patch sq f)
  overlapDecomp :
    Boundary.FiniteIrreducibleComponentDecomposition
      (NisnevichDistinguishedSquareDataQ.baseChange_overlap sq f)

/-- Graph transfer for the pulled-back open-to-base morphism. -/
def baseChange_openToBaseTransfer {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base)
    (decomp : Boundary.FiniteIrreducibleComponentDecomposition
      (NisnevichDistinguishedSquareDataQ.baseChange_open sq f)) :
    SmCorQ.Hom category
      (NisnevichDistinguishedSquareDataQ.baseChange_open sq f) Y :=
  SmCorQ.graphTransfer category
    (NisnevichDistinguishedSquareDataQ.baseChange_open_to_base sq f) decomp

/-- Graph transfer for the pulled-back patch-to-base morphism. -/
def baseChange_patchToBaseTransfer {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base)
    (decomp : Boundary.FiniteIrreducibleComponentDecomposition
      (NisnevichDistinguishedSquareDataQ.baseChange_patch sq f)) :
    SmCorQ.Hom category
      (NisnevichDistinguishedSquareDataQ.baseChange_patch sq f) Y :=
  SmCorQ.graphTransfer category
    (NisnevichDistinguishedSquareDataQ.baseChange_patch_to_base sq f) decomp

/-- Graph transfer for the pulled-back overlap-to-open morphism. -/
def baseChange_overlapToOpenTransfer {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base)
    (decomp : Boundary.FiniteIrreducibleComponentDecomposition
      (NisnevichDistinguishedSquareDataQ.baseChange_overlap sq f)) :
    SmCorQ.Hom category
      (NisnevichDistinguishedSquareDataQ.baseChange_overlap sq f)
      (NisnevichDistinguishedSquareDataQ.baseChange_open sq f) :=
  SmCorQ.graphTransfer category
    (NisnevichDistinguishedSquareDataQ.baseChange_overlap_to_open sq f) decomp

/-- Graph transfer for the pulled-back overlap-to-patch morphism. -/
def baseChange_overlapToPatchTransfer {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base)
    (decomp : Boundary.FiniteIrreducibleComponentDecomposition
      (NisnevichDistinguishedSquareDataQ.baseChange_overlap sq f)) :
    SmCorQ.Hom category
      (NisnevichDistinguishedSquareDataQ.baseChange_overlap sq f)
      (NisnevichDistinguishedSquareDataQ.baseChange_patch sq f) :=
  SmCorQ.graphTransfer category
    (NisnevichDistinguishedSquareDataQ.baseChange_overlap_to_patch sq f) decomp

/-- Canonical decompositions of the base-changed pieces from the canonical
composition data. -/
def canonicalBaseChangeDecompositions
    (composition : Boundary.CanonicalCompositionData (k := k))
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition))
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    BaseChangeDecompositions sq f where
  openDecomp := composition.diagonalDecomposition
    (NisnevichDistinguishedSquareDataQ.baseChange_open sq f)
  patchDecomp := composition.diagonalDecomposition
    (NisnevichDistinguishedSquareDataQ.baseChange_patch sq f)
  overlapDecomp := composition.diagonalDecomposition
    (NisnevichDistinguishedSquareDataQ.baseChange_overlap sq f)

/-- In the canonical rational correspondence category, the transfer maps of a
base-changed Nisnevich square commute because each side is the graph transfer
of the same composite ordinary morphism, and graph transfers compose by the
canonical owner theorem `canonicalCategory_graphTransfer_comp`. -/
theorem canonicalBaseChange_transfer_commutes
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition))
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    let decomps := canonicalBaseChangeDecompositions composition sq f
    (Boundary.canonicalCategory composition).comp
      (baseChange_overlapToOpenTransfer sq f decomps.overlapDecomp)
      (baseChange_openToBaseTransfer sq f decomps.openDecomp)
      = (Boundary.canonicalCategory composition).comp
          (baseChange_overlapToPatchTransfer sq f decomps.overlapDecomp)
          (baseChange_patchToBaseTransfer sq f decomps.patchDecomp) := by
  let decomps := canonicalBaseChangeDecompositions composition sq f
  let category := Boundary.canonicalCategory composition
  let overlapToOpen := baseChange_overlap_to_open sq f
  let openToBase := baseChange_open_to_base sq f
  let overlapToPatch := baseChange_overlap_to_patch sq f
  let patchToBase := baseChange_patch_to_base sq f
  letI := SmCorQCat category
  calc
    category.comp
        (baseChange_overlapToOpenTransfer sq f decomps.overlapDecomp)
        (baseChange_openToBaseTransfer sq f decomps.openDecomp)
      = SmCorQ.graphTransfer category
          (Boundary.SmOverHom.comp overlapToOpen openToBase)
          decomps.overlapDecomp := by
            change
              (Boundary.canonicalCategory composition).comp
                (SmCorQ.graphTransfer (Boundary.canonicalCategory composition)
                  overlapToOpen decomps.overlapDecomp)
                (SmCorQ.graphTransfer (Boundary.canonicalCategory composition)
                  openToBase decomps.openDecomp) =
              SmCorQ.graphTransfer (Boundary.canonicalCategory composition)
                (Boundary.SmOverHom.comp overlapToOpen openToBase)
                decomps.overlapDecomp
            exact Boundary.canonicalCategory_graphTransfer_comp
              (composition := composition)
              hgraph
              overlapToOpen
              openToBase
    _ = SmCorQ.graphTransfer category
          (Boundary.SmOverHom.comp overlapToPatch patchToBase)
          decomps.overlapDecomp := by
            have hoverlap :
                Boundary.SmOverHom.comp overlapToOpen openToBase =
                  Boundary.SmOverHom.comp overlapToPatch patchToBase :=
              baseChange_overlap_comp_eq sq f
            exact congrArg
              (fun morphism =>
                SmCorQ.graphTransfer category morphism decomps.overlapDecomp)
              hoverlap
    _ = category.comp
          (baseChange_overlapToPatchTransfer sq f decomps.overlapDecomp)
          (baseChange_patchToBaseTransfer sq f decomps.patchDecomp) := by
            symm
            change
              (Boundary.canonicalCategory composition).comp
                (SmCorQ.graphTransfer (Boundary.canonicalCategory composition)
                  overlapToPatch decomps.overlapDecomp)
                (SmCorQ.graphTransfer (Boundary.canonicalCategory composition)
                  patchToBase decomps.patchDecomp) =
              SmCorQ.graphTransfer (Boundary.canonicalCategory composition)
                (Boundary.SmOverHom.comp overlapToPatch patchToBase)
                decomps.overlapDecomp
            exact Boundary.canonicalCategory_graphTransfer_comp
              (composition := composition)
              hgraph
              overlapToPatch
              patchToBase

/-- The pulled-back distinguished square in the canonical rational
correspondence category, obtained directly from the existing base-change
construction and the canonical graph-transfer composition theorem. -/
def canonicalPullback
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition))
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    NisnevichDistinguishedSquareDataQ
      (Boundary.canonicalCategory composition) := by
  let decomps := canonicalBaseChangeDecompositions composition sq f
  exact
    { base := Y
      openPiece := baseChange_open sq f
      patchPiece := baseChange_patch sq f
      overlap := baseChange_overlap sq f
      openToBase := baseChange_open_to_base sq f
      patchToBase := baseChange_patch_to_base sq f
      overlapToOpen := baseChange_overlap_to_open sq f
      overlapToPatch := baseChange_overlap_to_patch sq f
      openToBaseTransfer := baseChange_openToBaseTransfer sq f decomps.openDecomp
      patchToBaseTransfer := baseChange_patchToBaseTransfer sq f decomps.patchDecomp
      overlapToOpenTransfer := baseChange_overlapToOpenTransfer sq f decomps.overlapDecomp
      overlapToPatchTransfer := baseChange_overlapToPatchTransfer sq f decomps.overlapDecomp
      overlap_to_base_transfer_commutes :=
        canonicalBaseChange_transfer_commutes composition hgraph sq f
      openToBase_isOpenImmersion :=
        baseChange_open_to_base_isOpenImmersion sq f
      patchToBase_isEtale :=
        baseChange_patch_to_base_isEtale sq f
      overlap_isPullback :=
        baseChange_overlap_isPullback sq f }

/-- Right product of a Nisnevich distinguished square with a smooth scheme:
pull back along the projection `base ×_k Y ⟶ base`. -/
def nisnevichSquare_product_right
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition))
    (Y : Geometry.SmSchemeOver k) :
    NisnevichDistinguishedSquareDataQ
      (Boundary.canonicalCategory composition) :=
  canonicalPullback composition hgraph sq (Boundary.overBaseProductFst sq.base Y)

/-- Left product of a Nisnevich distinguished square with a smooth scheme:
pull back along the projection `X ×_k base ⟶ base`. -/
def nisnevichSquare_product_left
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (X : Geometry.SmSchemeOver k)
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)) :
    NisnevichDistinguishedSquareDataQ
      (Boundary.canonicalCategory composition) :=
  canonicalPullback composition hgraph sq (Boundary.overBaseProductSnd X sq.base)

/-- The transfer maps for the base-changed Nisnevich square commute after
canonical rational graph composition. -/
theorem baseChange_transfer_commutes
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → Boundary.FiniteIrreducibleComponentDecomposition X)
    (packages : ConcreteLiftedPackages (k := k))
    (leftIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (leftIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y)
        (component : Boundary.SourceIrreducibleComponent X)
        (toComponent : P.sourceImage.carrier.scheme ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.sourceImage.toAmbient),
          packages (Boundary.SourceIrreducibleComponent.diagonalPrimeGeom component)
              (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) =
            leftIdentityPackage (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P))
    (rightIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (rightIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : Boundary.PrimeFiniteCorrespondenceGeom X Y)
        (diagClass : Boundary.PrimeFiniteCorrespondenceGeom Y Y),
          diagClass ∈ (diagonalDecomposition Y).diagonalPrimeClasses →
            packages prime diagClass = rightIdentityPackage prime)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y),
          SupportFiberProductImageCompositionPackageFamily.decomposition
              (fun {X} {Y} {Z} x y =>
                SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))
              P
              (Boundary.SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            Boundary.RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (toFiniteCorrespondenceCompositionData
              (SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                        (packages (X := X) (Y := Y) (Z := Z) x y))
                  P Q)))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              Boundary.FiniteCorrespondencePresentation.toGeom (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (toFiniteCorrespondenceCompositionData
              (SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                        (packages (X := X) (Y := Y) (Z := Z) x y))
                  Q R))) =
              Boundary.FiniteCorrespondencePresentation.toGeom (rightPresentation P Q R))
    (graphPair_yes :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (C : Boundary.SourceIrreducibleComponent X)
        (f : Boundary.SmOverHom X Y)
        (D : Boundary.SourceIrreducibleComponent Y)
        (g : Boundary.SmOverHom Y Z)
        (h : C.carrier.scheme ⟶ D.carrier.scheme)
        (hh : h ≫ D.toAmbient = C.toAmbient ≫ f.hom),
          ((packages
            (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented
              (Geometry.ordinaryMorphismGraphPrimeSupport C f))
            (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented
              (Geometry.ordinaryMorphismGraphPrimeSupport D g))).liftedDecomposition
              (Geometry.ordinaryMorphismGraphPrimeSupport C f)
              (Geometry.ordinaryMorphismGraphPrimeSupport D g)).toSupportFiberProductImageDecomposition =
            Geometry.graphPrimeSupportFiberProductImageDecomposition C f D g h hh)
    (graphPair_no :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (C : Boundary.SourceIrreducibleComponent X)
        (f : Boundary.SmOverHom X Y)
        (D : Boundary.SourceIrreducibleComponent Y)
        (g : Boundary.SmOverHom Y Z),
          (¬ Nonempty { h : C.carrier.scheme ⟶ D.carrier.scheme //
              h ≫ D.toAmbient = C.toAmbient ≫ f.hom }) →
            IsEmpty (((packages
              (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented
                (Geometry.ordinaryMorphismGraphPrimeSupport C f))
              (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented
                (Geometry.ordinaryMorphismGraphPrimeSupport D g))).liftedDecomposition
                (Geometry.ordinaryMorphismGraphPrimeSupport C f)
                (Geometry.ordinaryMorphismGraphPrimeSupport D g)).toSupportFiberProductImageDecomposition.index)
    )
    (sq : NisnevichDistinguishedSquareDataQ
      (concreteCanonicalCategory
        diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
        rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
        leftPresentation rightPresentation hpresentation hleft hright))
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base)
    (decomps : BaseChangeDecompositions sq f) :
    (concreteCanonicalCategory
      diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
      rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
      leftPresentation rightPresentation hpresentation hleft hright).comp
      (baseChange_overlapToOpenTransfer sq f decomps.overlapDecomp)
      (baseChange_openToBaseTransfer sq f decomps.openDecomp)
      = (concreteCanonicalCategory
          diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
          rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
          leftPresentation rightPresentation hpresentation hleft hright).comp
          (baseChange_overlapToPatchTransfer sq f decomps.overlapDecomp)
          (baseChange_patchToBaseTransfer sq f decomps.patchDecomp) := by
  let category := concreteCanonicalCategory
    diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
    rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
    leftPresentation rightPresentation hpresentation hleft hright
  let overlapToOpen := baseChange_overlap_to_open sq f
  let openToBase := baseChange_open_to_base sq f
  let overlapToPatch := baseChange_overlap_to_patch sq f
  let patchToBase := baseChange_patch_to_base sq f
  letI := SmCorQCat category
  calc
    category.comp
        (baseChange_overlapToOpenTransfer sq f decomps.overlapDecomp)
        (baseChange_openToBaseTransfer sq f decomps.openDecomp)
      = Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category
              (Boundary.SmOverHom.comp overlapToOpen openToBase)
          decomps.overlapDecomp := by
            change
              category.comp
                (Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category
                  overlapToOpen decomps.overlapDecomp)
                (Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category
                  openToBase decomps.openDecomp) =
              Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category
                (Boundary.SmOverHom.comp overlapToOpen openToBase)
                decomps.overlapDecomp
            exact Geometry.ordinaryMorphismGraph_comp_canonical_Q
              diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
              rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
              leftPresentation rightPresentation hpresentation hleft hright
              graphPair_yes graphPair_no
              overlapToOpen
              openToBase
              decomps.overlapDecomp decomps.openDecomp
    _ = Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category
              (Boundary.SmOverHom.comp overlapToPatch patchToBase)
          decomps.overlapDecomp := by
            have hoverlap :
                Boundary.SmOverHom.comp overlapToOpen openToBase =
                  Boundary.SmOverHom.comp overlapToPatch patchToBase :=
              baseChange_overlap_comp_eq sq f
            exact congrArg
              (fun morphism =>
                Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition
                  category morphism decomps.overlapDecomp)
              hoverlap
    _ = category.comp
          (baseChange_overlapToPatchTransfer sq f decomps.overlapDecomp)
          (baseChange_patchToBaseTransfer sq f decomps.patchDecomp) := by
            symm
            change
              category.comp
                (Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category
                  overlapToPatch decomps.overlapDecomp)
                (Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category
                  patchToBase decomps.patchDecomp) =
              Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category
                (Boundary.SmOverHom.comp overlapToPatch patchToBase)
                decomps.overlapDecomp
            exact Geometry.ordinaryMorphismGraph_comp_canonical_Q
              diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
              rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
              leftPresentation rightPresentation hpresentation hleft hright
              graphPair_yes graphPair_no
              overlapToPatch
              patchToBase
              decomps.overlapDecomp decomps.patchDecomp

/-- The pulled-back distinguished square in the canonical rational correspondence
category, with graph transfers routed through the validated canonical graph
composition theorem. -/
def pullback
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → Boundary.FiniteIrreducibleComponentDecomposition X)
    (packages : ConcreteLiftedPackages (k := k))
    (leftIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (leftIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y)
        (component : Boundary.SourceIrreducibleComponent X)
        (toComponent : P.sourceImage.carrier.scheme ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.sourceImage.toAmbient),
          packages (Boundary.SourceIrreducibleComponent.diagonalPrimeGeom component)
              (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) =
            leftIdentityPackage (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P))
    (rightIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (rightIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : Boundary.PrimeFiniteCorrespondenceGeom X Y)
        (diagClass : Boundary.PrimeFiniteCorrespondenceGeom Y Y),
          diagClass ∈ (diagonalDecomposition Y).diagonalPrimeClasses →
            packages prime diagClass = rightIdentityPackage prime)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y),
          SupportFiberProductImageCompositionPackageFamily.decomposition
              (fun {X} {Y} {Z} x y =>
                SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))
              P
              (Boundary.SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            Boundary.RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (toFiniteCorrespondenceCompositionData
              (SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                        (packages (X := X) (Y := Y) (Z := Z) x y))
                  P Q)))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              Boundary.FiniteCorrespondencePresentation.toGeom (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (toFiniteCorrespondenceCompositionData
              (SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                        (packages (X := X) (Y := Y) (Z := Z) x y))
                  Q R))) =
              Boundary.FiniteCorrespondencePresentation.toGeom (rightPresentation P Q R))
    (graphPair_yes :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (C : Boundary.SourceIrreducibleComponent X)
        (f : Boundary.SmOverHom X Y)
        (D : Boundary.SourceIrreducibleComponent Y)
        (g : Boundary.SmOverHom Y Z)
        (h : C.carrier.scheme ⟶ D.carrier.scheme)
        (hh : h ≫ D.toAmbient = C.toAmbient ≫ f.hom),
          ((packages
            (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented
              (Geometry.ordinaryMorphismGraphPrimeSupport C f))
            (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented
              (Geometry.ordinaryMorphismGraphPrimeSupport D g))).liftedDecomposition
              (Geometry.ordinaryMorphismGraphPrimeSupport C f)
              (Geometry.ordinaryMorphismGraphPrimeSupport D g)).toSupportFiberProductImageDecomposition =
            Geometry.graphPrimeSupportFiberProductImageDecomposition C f D g h hh)
    (graphPair_no :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (C : Boundary.SourceIrreducibleComponent X)
        (f : Boundary.SmOverHom X Y)
        (D : Boundary.SourceIrreducibleComponent Y)
        (g : Boundary.SmOverHom Y Z),
          (¬ Nonempty { h : C.carrier.scheme ⟶ D.carrier.scheme //
              h ≫ D.toAmbient = C.toAmbient ≫ f.hom }) →
            IsEmpty (((packages
              (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented
                (Geometry.ordinaryMorphismGraphPrimeSupport C f))
              (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented
                (Geometry.ordinaryMorphismGraphPrimeSupport D g))).liftedDecomposition
                (Geometry.ordinaryMorphismGraphPrimeSupport C f)
                (Geometry.ordinaryMorphismGraphPrimeSupport D g)).toSupportFiberProductImageDecomposition.index)
    )
    (sq : NisnevichDistinguishedSquareDataQ
      (concreteCanonicalCategory
        diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
        rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
        leftPresentation rightPresentation hpresentation hleft hright))
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base)
    (decomps : BaseChangeDecompositions sq f) :
    NisnevichDistinguishedSquareDataQ
      (concreteCanonicalCategory
        diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
        rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
        leftPresentation rightPresentation hpresentation hleft hright) where
  base := Y
  openPiece := baseChange_open sq f
  patchPiece := baseChange_patch sq f
  overlap := baseChange_overlap sq f
  openToBase := baseChange_open_to_base sq f
  patchToBase := baseChange_patch_to_base sq f
  overlapToOpen := baseChange_overlap_to_open sq f
  overlapToPatch := baseChange_overlap_to_patch sq f
  openToBaseTransfer := baseChange_openToBaseTransfer sq f decomps.openDecomp
  patchToBaseTransfer := baseChange_patchToBaseTransfer sq f decomps.patchDecomp
  overlapToOpenTransfer := baseChange_overlapToOpenTransfer sq f decomps.overlapDecomp
  overlapToPatchTransfer := baseChange_overlapToPatchTransfer sq f decomps.overlapDecomp
  overlap_to_base_transfer_commutes :=
    baseChange_transfer_commutes
      diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
      rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
      leftPresentation rightPresentation hpresentation hleft hright
      graphPair_yes graphPair_no
      sq f decomps
  openToBase_isOpenImmersion :=
    baseChange_open_to_base_isOpenImmersion sq f
  patchToBase_isEtale :=
    baseChange_patch_to_base_isEtale sq f
  overlap_isPullback :=
    baseChange_overlap_isPullback sq f

end NisnevichDistinguishedSquareDataQ

end -- noncomputable section

end Boundary
