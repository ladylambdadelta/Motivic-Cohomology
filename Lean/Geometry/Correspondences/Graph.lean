import Boundary.CorrespondenceSums
import Boundary.ComponentGeometry
import Boundary.PrimeSupport
import Boundary.RationalCompositionCategory
import Boundary.SmOver
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Graph Correspondence Obligation

This file records the exact remaining theorem needed to turn an ordinary
`Sm/k` morphism into a finite-correspondence graph.

The canonical graph map itself is already constructible. The current blocker is
the missing proof that this map is a closed immersion in the relevant ambient
fiber product.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace Geometry

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]

/-- The canonical graph map of an ordinary `Sm/k` morphism into the fiber
product `X ×_k Y`. -/
def ordinaryMorphismGraphMap {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) : X.scheme ⟶ Boundary.overBaseProduct X Y :=
  pullback.lift (𝟙 X.scheme) f.hom (by simpa using f.over.symm)

@[simp] theorem ordinaryMorphismGraphMap_fst {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    ordinaryMorphismGraphMap f ≫ Boundary.overBaseProduct.fst X Y = 𝟙 X.scheme := by
  simp [ordinaryMorphismGraphMap]

@[simp] theorem ordinaryMorphismGraphMap_snd {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    ordinaryMorphismGraphMap f ≫ Boundary.overBaseProduct.snd X Y = f.hom := by
  simp [ordinaryMorphismGraphMap]

@[simp, reassoc] theorem ordinaryMorphismGraphMap_overBaseProductMap_id_right_fst_fst
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    ordinaryMorphismGraphMap (Boundary.overBaseProductMap f (𝟙 Z)) ≫
        Boundary.overBaseProduct.fst
          (Boundary.overBaseProductObject X Z) (Boundary.overBaseProductObject Y Z) ≫
      Boundary.overBaseProduct.fst X Z =
      Boundary.overBaseProduct.fst X Z := by
  simp [ordinaryMorphismGraphMap, Boundary.overBaseProductMap, Category.assoc]

@[simp, reassoc] theorem ordinaryMorphismGraphMap_overBaseProductMap_id_right_fst_snd
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    ordinaryMorphismGraphMap (Boundary.overBaseProductMap f (𝟙 Z)) ≫
        Boundary.overBaseProduct.fst
          (Boundary.overBaseProductObject X Z) (Boundary.overBaseProductObject Y Z) ≫
      Boundary.overBaseProduct.snd X Z =
      Boundary.overBaseProduct.snd X Z := by
  simp [ordinaryMorphismGraphMap, Boundary.overBaseProductMap, Category.assoc]

@[simp, reassoc] theorem ordinaryMorphismGraphMap_overBaseProductMap_id_right_snd_fst
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    ordinaryMorphismGraphMap (Boundary.overBaseProductMap f (𝟙 Z)) ≫
        Boundary.overBaseProduct.snd
          (Boundary.overBaseProductObject X Z) (Boundary.overBaseProductObject Y Z) ≫
          Boundary.overBaseProduct.fst Y Z =
      Boundary.overBaseProduct.fst X Z ≫ f.hom := by
  simp [ordinaryMorphismGraphMap, Boundary.overBaseProductMap, Category.assoc]

@[simp, reassoc] theorem ordinaryMorphismGraphMap_overBaseProductMap_id_right_snd_snd
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    ordinaryMorphismGraphMap (Boundary.overBaseProductMap f (𝟙 Z)) ≫
        Boundary.overBaseProduct.snd
          (Boundary.overBaseProductObject X Z) (Boundary.overBaseProductObject Y Z) ≫
          Boundary.overBaseProduct.snd Y Z =
      Boundary.overBaseProduct.snd X Z := by
  simp [ordinaryMorphismGraphMap, Boundary.overBaseProductMap, Category.assoc]

@[simp, reassoc] theorem ordinaryMorphismGraphMap_overBaseProductMap_id_left_fst_fst
    {X Y Z : Geometry.SmSchemeOver k}
    (g : Boundary.SmOverHom Y Z) :
    ordinaryMorphismGraphMap (Boundary.overBaseProductMap (𝟙 X) g) ≫
        Boundary.overBaseProduct.fst
          (Boundary.overBaseProductObject X Y) (Boundary.overBaseProductObject X Z) ≫
      Boundary.overBaseProduct.fst X Y =
      Boundary.overBaseProduct.fst X Y := by
  simp [ordinaryMorphismGraphMap, Boundary.overBaseProductMap, Category.assoc]

@[simp, reassoc] theorem ordinaryMorphismGraphMap_overBaseProductMap_id_left_fst_snd
    {X Y Z : Geometry.SmSchemeOver k}
    (g : Boundary.SmOverHom Y Z) :
    ordinaryMorphismGraphMap (Boundary.overBaseProductMap (𝟙 X) g) ≫
        Boundary.overBaseProduct.fst
          (Boundary.overBaseProductObject X Y) (Boundary.overBaseProductObject X Z) ≫
      Boundary.overBaseProduct.snd X Y =
      Boundary.overBaseProduct.snd X Y := by
  simp [ordinaryMorphismGraphMap, Boundary.overBaseProductMap, Category.assoc]

@[simp, reassoc] theorem ordinaryMorphismGraphMap_overBaseProductMap_id_left_snd_fst
    {X Y Z : Geometry.SmSchemeOver k}
    (g : Boundary.SmOverHom Y Z) :
    ordinaryMorphismGraphMap (Boundary.overBaseProductMap (𝟙 X) g) ≫
        Boundary.overBaseProduct.snd
          (Boundary.overBaseProductObject X Y) (Boundary.overBaseProductObject X Z) ≫
          Boundary.overBaseProduct.fst X Z =
      Boundary.overBaseProduct.fst X Y := by
  simp [ordinaryMorphismGraphMap, Boundary.overBaseProductMap, Category.assoc]

@[simp, reassoc] theorem ordinaryMorphismGraphMap_overBaseProductMap_id_left_snd_snd
    {X Y Z : Geometry.SmSchemeOver k}
    (g : Boundary.SmOverHom Y Z) :
    ordinaryMorphismGraphMap (Boundary.overBaseProductMap (𝟙 X) g) ≫
        Boundary.overBaseProduct.snd
          (Boundary.overBaseProductObject X Y) (Boundary.overBaseProductObject X Z) ≫
          Boundary.overBaseProduct.snd X Z =
      Boundary.overBaseProduct.snd X Y ≫ g.hom := by
  simp [ordinaryMorphismGraphMap, Boundary.overBaseProductMap, Category.assoc]

@[simp] theorem ordinaryMorphismGraphMap_sourceOverBaseProduct_fst
    {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    ordinaryMorphismGraphMap f ≫
        Boundary.sourceOverBaseProduct.fst (k := k)
          { scheme := X.scheme, structMap := X.structMap } Y =
      𝟙 X.scheme := by
  simp [ordinaryMorphismGraphMap, Boundary.sourceOverBaseProduct]

@[simp] theorem ordinaryMorphismGraphMap_sourceOverBaseProduct_snd
    {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    ordinaryMorphismGraphMap f ≫
        Boundary.sourceOverBaseProduct.snd (k := k)
          { scheme := X.scheme, structMap := X.structMap } Y =
      f.hom := by
  simp [ordinaryMorphismGraphMap, Boundary.sourceOverBaseProduct]

/-- The graph projection `Γ_f ⟶ X` is an isomorphism. -/
theorem ordinaryMorphismGraphProjectionIso {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    IsIso (ordinaryMorphismGraphMap f ≫ Boundary.overBaseProduct.fst X Y) := by
  rw [ordinaryMorphismGraphMap_fst]
  infer_instance

/-- The graph projection `Γ_f ⟶ X` is finite because it is an isomorphism. -/
theorem ordinaryMorphismGraphProjectionFinite {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    IsFinite (ordinaryMorphismGraphMap f ≫ Boundary.overBaseProduct.fst X Y) := by
  letI : IsIso (ordinaryMorphismGraphMap f ≫ Boundary.overBaseProduct.fst X Y) :=
    ordinaryMorphismGraphProjectionIso f
  infer_instance

/-- Source-over-base version of graph-projection finiteness. -/
theorem ordinaryMorphismGraphProjectionFinite_sourceOverBaseProduct
    {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    IsFinite (ordinaryMorphismGraphMap f ≫
      Boundary.sourceOverBaseProduct.fst (k := k)
        { scheme := X.scheme, structMap := X.structMap } Y) := by
  simpa [Boundary.sourceOverBaseProduct, Boundary.overBaseProduct] using
    ordinaryMorphismGraphProjectionFinite f


/-- Restrict an ordinary `Sm/k` morphism to a chosen source irreducible
component. -/
def ordinaryMorphismOnSourceComponent {X Y : Geometry.SmSchemeOver k}
    (component : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y) : Boundary.SmOverHom component.carrier Y where
  hom := component.toAmbient ≫ f.hom
  over := by
    calc
      (component.toAmbient ≫ f.hom) ≫ Y.structMap
          = component.toAmbient ≫ (f.hom ≫ Y.structMap) := by simp [Category.assoc]
      _ = component.toAmbient ≫ X.structMap := by rw [f.over]
      _ = component.carrier.structMap := component.toAmbient_overBase

/-- The graph of an ordinary `Sm/k` morphism is a closed immersion into the
ambient fiber product. This is the local AG input needed before packaging the
graph as a finite correspondence. -/
theorem ordinaryMorphismGraphMap_isClosedImmersion {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    IsClosedImmersion (ordinaryMorphismGraphMap f) := by
  let graphIso :
      pullback (f.hom ≫ Y.structMap) Y.structMap ≅ Boundary.overBaseProduct X Y :=
    pullback.congrHom f.over rfl
  let graphMap : X.scheme ⟶ pullback (f.hom ≫ Y.structMap) Y.structMap :=
    pullback.lift (𝟙 X.scheme) f.hom (Category.id_comp (f.hom ≫ Y.structMap))
  let e : Arrow.mk (ordinaryMorphismGraphMap f) ≅ Arrow.mk graphMap :=
    Arrow.isoMk (Iso.refl _) graphIso.symm (by
      apply pullback.hom_ext
      · simp [ordinaryMorphismGraphMap, graphMap, graphIso, Boundary.overBaseProduct, f.over]
      · simp [ordinaryMorphismGraphMap, graphMap, graphIso, Boundary.overBaseProduct, f.over])
  letI : IsSeparated Y.structMap := Y.separated
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) e).2 inferInstance

/-- The componentwise graph of an ordinary `Sm/k` morphism defines a
represented prime support. -/
def ordinaryMorphismGraphPrimeSupport {X Y : Geometry.SmSchemeOver k}
    (component : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y) :
    Boundary.PrimeFiniteCorrespondenceSupport X Y := by
  let componentMorphism := ordinaryMorphismOnSourceComponent component f
  refine
    { sourceImage := component.toSourceImageSubscheme
      support := component.carrier.scheme
      isIntegral := component.isIntegral
      finiteOverSourceComponent :=
        ordinaryMorphismGraphMap componentMorphism ≫
          Boundary.sourceOverBaseProduct.fst (k := k) component.toSourceImageSubscheme.carrier Y
      finite_toSourceComponent := ?_
      surjective_toSourceComponent := ?_
      toTarget := component.toAmbient ≫ f.hom
      inclusion := ordinaryMorphismGraphMap componentMorphism
      inclusion_fst := rfl
      inclusion_snd := ?_
      isClosedImmersion := ?_ }
  · simpa [componentMorphism, ordinaryMorphismOnSourceComponent,
      Boundary.SourceIrreducibleComponent.toSourceImageSubscheme_carrier] using
      ordinaryMorphismGraphProjectionFinite_sourceOverBaseProduct componentMorphism
  · intro x
    have hfst :=
      ordinaryMorphismGraphMap_sourceOverBaseProduct_fst componentMorphism
    refine ⟨x, ?_⟩
    change (ordinaryMorphismGraphMap componentMorphism ≫
        Boundary.sourceOverBaseProduct.fst (k := k) component.toSourceImageSubscheme.carrier Y).base x = x
    simpa [componentMorphism, ordinaryMorphismOnSourceComponent,
      Boundary.SourceIrreducibleComponent.toSourceImageSubscheme_carrier] using
      congrArg (fun g => g.base x) hfst
  · simpa [componentMorphism, ordinaryMorphismOnSourceComponent,
      Boundary.SourceIrreducibleComponent.toSourceImageSubscheme_carrier] using
      ordinaryMorphismGraphMap_sourceOverBaseProduct_snd componentMorphism
  · exact ordinaryMorphismGraphMap_isClosedImmersion componentMorphism

@[simp] theorem ordinaryMorphismGraphPrimeSupport_sourceComponent
    {X Y : Geometry.SmSchemeOver k}
    (component : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y) :
    (ordinaryMorphismGraphPrimeSupport component f).sourceComponent =
      component.toSourceImageSubscheme := rfl

@[simp] theorem ordinaryMorphismGraphPrimeSupport_toSourceImage
    {X Y : Geometry.SmSchemeOver k}
    (component : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y) :
    (ordinaryMorphismGraphPrimeSupport component f).toSourceImage =
      𝟙 component.carrier.scheme := by
  change ordinaryMorphismGraphMap (ordinaryMorphismOnSourceComponent component f) ≫
      Boundary.sourceOverBaseProduct.fst (k := k)
        component.toSourceImageSubscheme.carrier Y =
    𝟙 component.carrier.scheme
  simpa [Boundary.SourceIrreducibleComponent.toSourceImageSubscheme_carrier] using
    ordinaryMorphismGraphMap_sourceOverBaseProduct_fst
      (ordinaryMorphismOnSourceComponent component f)

@[simp] theorem ordinaryMorphismGraphPrimeSupport_toSourceComponent
    {X Y : Geometry.SmSchemeOver k}
    (component : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y) :
    (ordinaryMorphismGraphPrimeSupport component f).toSourceComponent =
      𝟙 component.carrier.scheme :=
  ordinaryMorphismGraphPrimeSupport_toSourceImage component f

@[simp] theorem ordinaryMorphismGraphPrimeSupport_toAmbientSource
    {X Y : Geometry.SmSchemeOver k}
    (component : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y) :
    (ordinaryMorphismGraphPrimeSupport component f).toAmbientSource =
      component.toAmbient := by
  simp [Boundary.PrimeFiniteCorrespondenceSupport.toAmbientSource]
  exact Category.id_comp component.toAmbient

@[simp] theorem ordinaryMorphismGraphPrimeSupport_toTargetScheme
    {X Y : Geometry.SmSchemeOver k}
    (component : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y) :
    (ordinaryMorphismGraphPrimeSupport component f).toTargetScheme =
      component.toAmbient ≫ f.hom := rfl

@[simp] theorem ordinaryMorphismGraphPrimeSupport_inclusion_fst
    {X Y : Geometry.SmSchemeOver k}
    (component : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y) :
    (ordinaryMorphismGraphPrimeSupport component f).inclusion ≫
        Boundary.sourceOverBaseProduct.fst (k := k)
          component.toSourceImageSubscheme.carrier Y =
      𝟙 component.carrier.scheme := by
  exact (ordinaryMorphismGraphPrimeSupport component f).inclusion_fst.trans
    (ordinaryMorphismGraphPrimeSupport_toSourceImage component f)

@[simp] theorem ordinaryMorphismGraphPrimeSupport_inclusion_snd
    {X Y : Geometry.SmSchemeOver k}
    (component : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y) :
    (ordinaryMorphismGraphPrimeSupport component f).inclusion ≫
        Boundary.sourceOverBaseProduct.snd (k := k)
          component.toSourceImageSubscheme.carrier Y =
      component.toAmbient ≫ f.hom := by
  exact (ordinaryMorphismGraphPrimeSupport component f).inclusion_snd

/-- The quotient geometric class of the componentwise graph of an ordinary
`Sm/k` morphism. -/
def ordinaryMorphismGraphPrimeGeom {X Y : Geometry.SmSchemeOver k}
    (component : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y) :
    Boundary.PrimeFiniteCorrespondenceGeom X Y :=
  Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented
    (ordinaryMorphismGraphPrimeSupport component f)

/-- Componentwise graph prime supports for source components that are
isomorphic over the ambient source define equivalent represented supports. -/
theorem ordinaryMorphismGraphPrimeSupportEquivalent_of_isoOverAmbient
    {X Y : Geometry.SmSchemeOver k}
    {C D : Boundary.SourceIrreducibleComponent X}
    (f : Boundary.SmOverHom X Y)
    (h : Boundary.SourceIrreducibleComponent.IsoOverAmbient C D) :
    Boundary.PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent
      (ordinaryMorphismGraphPrimeSupport C f)
      (ordinaryMorphismGraphPrimeSupport D f) := by
  let sourceIso : Boundary.SourceImageSubscheme.IsoOverAmbient
      C.toSourceImageSubscheme D.toSourceImageSubscheme :=
    { iso := h.iso
      hom_toAmbient := h.hom_toAmbient }
  let compat :=
    Boundary.SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient
      (Y := Y) sourceIso
  refine ⟨compat, h.iso, ?_⟩
  change (ordinaryMorphismGraphPrimeSupport C f).inclusion ≫ compat.iso.hom =
    h.iso.hom ≫ (ordinaryMorphismGraphPrimeSupport D f).inclusion
  apply Limits.pullback.hom_ext
  · calc
      (ordinaryMorphismGraphPrimeSupport C f).inclusion ≫ compat.iso.hom ≫
          Boundary.sourceOverBaseProduct.fst (k := k) D.toSourceImageSubscheme.carrier Y
          = (ordinaryMorphismGraphPrimeSupport C f).inclusion ≫
              Boundary.sourceOverBaseProduct.fst (k := k) C.toSourceImageSubscheme.carrier Y ≫
                h.iso.hom := by
                simpa [compat,
                  Boundary.SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient,
                  Category.assoc] using
                  congrArg (fun g => (ordinaryMorphismGraphPrimeSupport C f).inclusion ≫ g)
                    (Boundary.SourceImageSubscheme.IsoOverAmbient.overBaseProductIso_hom_fst
                      (Y := Y) sourceIso)
      _ = (ordinaryMorphismGraphPrimeSupport C f).finiteOverSourceComponent ≫ h.iso.hom := by
            simpa [Category.assoc] using
              congrArg (fun g => g ≫ h.iso.hom)
                (ordinaryMorphismGraphPrimeSupport C f).inclusion_fst
      _ = h.iso.hom := by
            change ((ordinaryMorphismGraphMap
              (ordinaryMorphismOnSourceComponent C f) ≫
                Boundary.sourceOverBaseProduct.fst (k := k) C.toSourceImageSubscheme.carrier Y) ≫
                  h.iso.hom = h.iso.hom)
            simpa [Category.assoc] using
              congrArg (fun g => g ≫ h.iso.hom)
                (ordinaryMorphismGraphMap_sourceOverBaseProduct_fst
                  (ordinaryMorphismOnSourceComponent C f))
      _ = h.iso.hom ≫ (ordinaryMorphismGraphPrimeSupport D f).finiteOverSourceComponent := by
            change h.iso.hom = h.iso.hom ≫
              (ordinaryMorphismGraphMap (ordinaryMorphismOnSourceComponent D f) ≫
                Boundary.sourceOverBaseProduct.fst (k := k) D.toSourceImageSubscheme.carrier Y)
            simpa [Category.assoc] using
              congrArg (fun g => h.iso.hom ≫ g)
                (ordinaryMorphismGraphMap_sourceOverBaseProduct_fst
                  (ordinaryMorphismOnSourceComponent D f)).symm
      _ = h.iso.hom ≫ (ordinaryMorphismGraphPrimeSupport D f).inclusion ≫
            Boundary.sourceOverBaseProduct.fst (k := k) D.toSourceImageSubscheme.carrier Y := by
            simpa [Category.assoc] using
              congrArg (fun g => h.iso.hom ≫ g)
                (ordinaryMorphismGraphPrimeSupport D f).inclusion_fst.symm
  · calc
      (ordinaryMorphismGraphPrimeSupport C f).inclusion ≫ compat.iso.hom ≫
          Boundary.sourceOverBaseProduct.snd (k := k) D.toSourceImageSubscheme.carrier Y
          = (ordinaryMorphismGraphPrimeSupport C f).inclusion ≫
              Boundary.sourceOverBaseProduct.snd (k := k) C.toSourceImageSubscheme.carrier Y := by
                simpa [compat,
                  Boundary.SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient,
                  Category.assoc] using
                  congrArg (fun g => (ordinaryMorphismGraphPrimeSupport C f).inclusion ≫ g)
                    (Boundary.SourceImageSubscheme.IsoOverAmbient.overBaseProductIso_hom_snd
                      (Y := Y) sourceIso)
      _ = (ordinaryMorphismGraphPrimeSupport C f).toTarget := by
            exact (ordinaryMorphismGraphPrimeSupport C f).inclusion_snd
      _ = C.toAmbient ≫ f.hom := by
            rfl
      _ = (h.iso.hom ≫ D.toAmbient) ≫ f.hom := by
            rw [← h.hom_toAmbient]
      _ = h.iso.hom ≫ D.toAmbient ≫ f.hom := by
            simp [Category.assoc]
      _ = h.iso.hom ≫ (ordinaryMorphismGraphPrimeSupport D f).toTarget := by
            rfl
      _ = h.iso.hom ≫ (ordinaryMorphismGraphPrimeSupport D f).inclusion ≫
        Boundary.sourceOverBaseProduct.snd (k := k) D.toSourceImageSubscheme.carrier Y := by
            simpa [Category.assoc] using
              congrArg (fun g => h.iso.hom ≫ g)
                (ordinaryMorphismGraphPrimeSupport D f).inclusion_snd.symm

/-- The graph geometric class depends only on the source-component class over
the ambient source. -/
theorem ordinaryMorphismGraphPrimeGeom_eq_of_isoOverAmbient
    {X Y : Geometry.SmSchemeOver k}
    {C D : Boundary.SourceIrreducibleComponent X}
    (f : Boundary.SmOverHom X Y)
    (h : Boundary.SourceIrreducibleComponent.IsoOverAmbient C D) :
    ordinaryMorphismGraphPrimeGeom C f = ordinaryMorphismGraphPrimeGeom D f := by
  exact Boundary.PrimeFiniteCorrespondenceGeom.eq_of_primeSupportEquivalent
    (ordinaryMorphismGraphPrimeSupportEquivalent_of_isoOverAmbient f h)

/-- Equivalent componentwise graph prime supports already remember the source
component isomorphism over the ambient source. -/
def isoOverAmbient_of_ordinaryMorphismGraphPrimeSupportEquivalent
    {X Y : Geometry.SmSchemeOver k}
    {C D : Boundary.SourceIrreducibleComponent X}
    (f : Boundary.SmOverHom X Y)
    (h : Boundary.PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent
      (ordinaryMorphismGraphPrimeSupport C f)
      (ordinaryMorphismGraphPrimeSupport D f)) :
    Boundary.SourceIrreducibleComponent.IsoOverAmbient C D := by
  have h' :
      ∃ (compatibleSourceComponent :
          Boundary.SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso
            (Y := Y) C.toSourceImageSubscheme D.toSourceImageSubscheme)
        (_iso : C.carrier.scheme ≅ D.carrier.scheme),
        (ordinaryMorphismGraphPrimeSupport C f).inclusion ≫ compatibleSourceComponent.iso.hom =
          _iso.hom ≫ (ordinaryMorphismGraphPrimeSupport D f).inclusion := by
    simpa [Boundary.PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent,
      Boundary.PrimeFiniteCorrespondenceSupport.SupportIsoOverProduct] using h
  exact
    { iso := (Classical.choose h').sourceIso.iso
      hom_toAmbient := (Classical.choose h').sourceIso.hom_toAmbient }

/-- Equality of componentwise graph geometric classes forces the corresponding
source components to be isomorphic over the ambient source. -/
def isoOverAmbient_of_ordinaryMorphismGraphPrimeGeom_eq
    {X Y : Geometry.SmSchemeOver k}
    {C D : Boundary.SourceIrreducibleComponent X}
    (f : Boundary.SmOverHom X Y)
    (h : ordinaryMorphismGraphPrimeGeom C f = ordinaryMorphismGraphPrimeGeom D f) :
    Boundary.SourceIrreducibleComponent.IsoOverAmbient C D := by
  exact isoOverAmbient_of_ordinaryMorphismGraphPrimeSupportEquivalent f (Quotient.exact h)

/-- The singleton finite correspondence attached to the componentwise graph of
an ordinary `Sm/k` morphism. -/
def ordinaryMorphismGraph_componentCorrespondence {X Y : Geometry.SmSchemeOver k}
    (component : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y) :
    Boundary.FiniteCorrespondence X Y :=
  Boundary.FiniteCorrespondence.ofPrimeSupport (ordinaryMorphismGraphPrimeSupport component f)

/-- The componentwise singleton finite correspondence depends only on the
source-component class over the ambient source. -/
theorem ordinaryMorphismGraph_componentCorrespondence_eq_of_isoOverAmbient
    {X Y : Geometry.SmSchemeOver k}
    {C D : Boundary.SourceIrreducibleComponent X}
    (f : Boundary.SmOverHom X Y)
    (h : Boundary.SourceIrreducibleComponent.IsoOverAmbient C D) :
    ordinaryMorphismGraph_componentCorrespondence C f =
      ordinaryMorphismGraph_componentCorrespondence D f := by
  change Finsupp.single (ordinaryMorphismGraphPrimeGeom C f) (1 : ℤ) =
    Finsupp.single (ordinaryMorphismGraphPrimeGeom D f) (1 : ℤ)
  rw [ordinaryMorphismGraphPrimeGeom_eq_of_isoOverAmbient f h]

/-- The set of geometric graph classes contributed by a certified finite
irreducible-component decomposition of the source of an ordinary `Sm/k`
morphism. -/
def ordinaryMorphismGraph_graphPrimeClassesOfDecomposition {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (decomp : Boundary.FiniteIrreducibleComponentDecomposition X) :
    Finset (Boundary.PrimeFiniteCorrespondenceGeom X Y) := by
  classical
  exact decomp.components.image (fun component => ordinaryMorphismGraphPrimeGeom component f)

/-- The finite correspondence obtained by summing the componentwise singleton
graph correspondences over a chosen finite irreducible-component decomposition
of the source of an ordinary `Sm/k` morphism. -/
def ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition
    {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (decomp : Boundary.FiniteIrreducibleComponentDecomposition X) :
    Boundary.FiniteCorrespondence X Y :=
  ∑ component in decomp.components, ordinaryMorphismGraph_componentCorrespondence component f

/-- The decomposition-sum graph correspondence can be rewritten as a sum over
the induced geometric graph classes. -/
theorem ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition_eq_sum_graphPrimeGeoms
    {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (decomp : Boundary.FiniteIrreducibleComponentDecomposition X) :
    ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition f decomp =
      ∑ graphClass in ordinaryMorphismGraph_graphPrimeClassesOfDecomposition f decomp,
        Finsupp.single graphClass 1 := by
  classical
  rw [ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition,
    ordinaryMorphismGraph_graphPrimeClassesOfDecomposition]
  symm
  refine Finset.sum_image ?_
  intro C hC D hD hEq
  have hiso : Boundary.SourceIrreducibleComponent.IsoOverAmbient C D :=
    isoOverAmbient_of_ordinaryMorphismGraphPrimeGeom_eq f hEq
  exact decomp.no_equivalent_duplicates hC hD hiso

/-- Any two certified decompositions of the source of an ordinary `Sm/k`
morphism determine the same set of componentwise graph geometric classes. -/
theorem ordinaryMorphismGraph_graphPrimeClasses_eq
    {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (D₁ D₂ : Boundary.FiniteIrreducibleComponentDecomposition X) :
    ordinaryMorphismGraph_graphPrimeClassesOfDecomposition f D₁ =
      ordinaryMorphismGraph_graphPrimeClassesOfDecomposition f D₂ := by
  classical
  rw [ordinaryMorphismGraph_graphPrimeClassesOfDecomposition,
    ordinaryMorphismGraph_graphPrimeClassesOfDecomposition]
  apply Finset.ext
  intro graphClass
  constructor
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨component, hcomponent, hgraph⟩
    rcases D₂.exhaustive component with ⟨listed, hiso⟩
    exact Finset.mem_image.mpr ⟨listed.1, listed.2, by
      rw [← ordinaryMorphismGraphPrimeGeom_eq_of_isoOverAmbient f hiso]
      exact hgraph⟩
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨component, hcomponent, hgraph⟩
    rcases D₁.exhaustive component with ⟨listed, hiso⟩
    exact Finset.mem_image.mpr ⟨listed.1, listed.2, by
      rw [← ordinaryMorphismGraphPrimeGeom_eq_of_isoOverAmbient f hiso]
      exact hgraph⟩

/-- The decomposition-sum graph correspondence of an ordinary `Sm/k` morphism
is independent of the chosen finite irreducible-component decomposition of the
source. -/
theorem ordinaryMorphismGraph_finiteCorrespondence_independent
    {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (D₁ D₂ : Boundary.FiniteIrreducibleComponentDecomposition X) :
    ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition f D₁ =
      ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition f D₂ := by
  classical
  rw [ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition_eq_sum_graphPrimeGeoms,
    ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition_eq_sum_graphPrimeGeoms,
    ordinaryMorphismGraph_graphPrimeClasses_eq f D₁ D₂]

/-- The rationalized decomposition-sum graph correspondence of an ordinary
`Sm/k` morphism. -/
def ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition
    {X Y : Geometry.SmSchemeOver k}
    (category : Boundary.SmCorQ (k := k))
    (f : Boundary.SmOverHom X Y)
    (decomp : Boundary.FiniteIrreducibleComponentDecomposition X) :
    Boundary.SmCorQ.Hom category X Y :=
  Boundary.FiniteCorrespondence.toRational
    (ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition f decomp)

/-- The rationalized decomposition-sum graph correspondence of an ordinary
`Sm/k` morphism is independent of the chosen finite irreducible-component
decomposition of the source. -/
theorem ordinaryMorphismGraph_rationalCorrespondence_independent
    {X Y : Geometry.SmSchemeOver k}
    (category : Boundary.SmCorQ (k := k))
    (f : Boundary.SmOverHom X Y)
    (D₁ D₂ : Boundary.FiniteIrreducibleComponentDecomposition X) :
    ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category f D₁ =
      ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category f D₂ := by
  simpa [ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition] using
    congrArg Boundary.FiniteCorrespondence.toRational
      (ordinaryMorphismGraph_finiteCorrespondence_independent f D₁ D₂)

/-- Exact remaining blocker for the graph-to-transfer constructor attached to an
ordinary `Sm/k` morphism. Once this closed-immersion theorem is supplied, the
represented-graph correspondence package can be built without introducing fake
transfer data. -/
structure MorphismGraphTransferObligationQ {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) where
  graphClosedImmersion : IsClosedImmersion (ordinaryMorphismGraphMap f)

/-- Packaged graph-closed-immersion data for an ordinary `Sm/k` morphism. -/
def morphismGraphTransferObligation {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    MorphismGraphTransferObligationQ f where
  graphClosedImmersion := ordinaryMorphismGraphMap_isClosedImmersion f

end

end Geometry
