import Boundary.A1NisWeakEquivalences
/-!
This file was split out of `Boundary.A1Geometry`; declarations remain in
namespace `Boundary` under their mathematical owner layer.
-/

universe u

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Polynomial
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Geometry

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]
structure BoundaryAdditiveCategoryStructure
    (C : Type*) [Category C] where
  preadditive : Preadditive C
  hasZeroObject : CategoryTheory.Limits.HasZeroObject C
  hasZeroMorphisms : CategoryTheory.Limits.HasZeroMorphisms C
  hasFiniteBiproducts : CategoryTheory.Limits.HasFiniteBiproducts C

/-- Boundary-owned weak-equivalence package for the canonical A1/Nis
localization. -/
structure CanonicalA1NisWeakEquivalencePackage
    (composition : Boundary.CanonicalCompositionData (k := k)) where
  property : MorphismProperty (LinearPST (Boundary.canonicalCategory composition))
  property_eq :
    property = canonicalA1NisLocalEquivalencesProperty composition
  generatedProperty :
    MorphismProperty (LinearPST (Boundary.canonicalCategory composition))
  generatedProperty_eq :
    generatedProperty = canonicalA1NisWeakEquivalencesProperty composition
  bousfieldGeneratedProperty :
    MorphismProperty (LinearPST (Boundary.canonicalCategory composition))
  bousfieldGeneratedProperty_eq :
    bousfieldGeneratedProperty =
      canonicalA1NisGeneratedWeakEquivalencesProperty composition

/-- The canonical weak-equivalence package really does package the full closure
theorems for the generator-built Bousfield class.

This is exactly the canonical theorem chain in C. Weibel, *An Introduction to
Homological Algebra*, Chapter 9.4, now expressed at owner level via the
generated-class closure API established in `Boundary.A1NisWeakEquivalences`. -/
theorem canonicalA1NisWeakEquivalencePackage_generatedClosure
    (composition : Boundary.CanonicalCompositionData (k := k))
    (weakEquiv : CanonicalA1NisWeakEquivalencePackage composition) :
    CanonicalA1NisWeakEquivalenceClosure composition
      (CanonicalA1NisWeakEquivalencePackage.generatedProperty weakEquiv) := by
  simpa [weakEquiv.generatedProperty_eq] using
    (canonicalA1NisGeneratedWeakEquivalences_closure composition)

/-- The generated-property side of the canonical package has 2-out-of-3 and
retract stability in the canonical setting. -/
theorem canonicalA1NisWeakEquivalencePackage_generatedTwoOutOfThree
    (composition : Boundary.CanonicalCompositionData (k := k))
    (weakEquiv : CanonicalA1NisWeakEquivalencePackage composition)
    {X Y Z : LinearPST (Boundary.canonicalCategory composition)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (weakEquiv.generatedProperty g →
      weakEquiv.generatedProperty (f ≫ g) →
        weakEquiv.generatedProperty f) ∧
    (weakEquiv.generatedProperty f →
      weakEquiv.generatedProperty (f ≫ g) →
        weakEquiv.generatedProperty g) := by
  refine
    ⟨?_, ?_⟩
  · simpa [weakEquiv.generatedProperty_eq] using
      (canonicalA1NisGeneratedWeakEquivalences_closure composition
        |>.two_out_of_three_left (f := f) (g := g))
  · simpa [weakEquiv.generatedProperty_eq] using
      (canonicalA1NisGeneratedWeakEquivalences_closure composition
        |>.two_out_of_three_right (f := f) (g := g))

structure CanonicalA1NisReflectorPackage
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Preadditive (LinearPST (Boundary.canonicalCategory composition))] where
  reflector :
    LinearPST (Boundary.canonicalCategory composition) ⥤
      LinearA1NisLocalPST (Boundary.canonicalCategory composition)
  adjunction :
    reflector ⊣
      LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition)
  preservesFiniteLimits : CategoryTheory.Limits.PreservesFiniteLimits reflector
  additive : reflector.Additive
  counit_isIso :
    ∀ L : LinearA1NisLocalPST (Boundary.canonicalCategory composition),
      IsIso (adjunction.counit.app L)
  unit_mem :
    ∀ X : LinearPST (Boundary.canonicalCategory composition),
      canonicalA1NisLocalEquivalences composition (adjunction.unit.app X)
  reflects_localEquivalences :
    ∀ {X Y : LinearPST (Boundary.canonicalCategory composition)}
      (φ : X ⟶ Y),
      canonicalA1NisLocalEquivalences composition φ ↔
        IsIso (reflector.map φ)

/-- The canonical reflector package is itself a localization of
`canonicalA1NisLocalEquivalencesProperty`.  This is the standard adjunction
argument in Gabriel–Zisman, §2.1. -/
theorem canonicalA1NisReflectorPackage_isLocalization
    (composition : Boundary.CanonicalCompositionData (k := k))
    (reflector : CanonicalA1NisReflectorPackage composition) :
    reflector.reflector.IsLocalization
      (canonicalA1NisLocalEquivalencesProperty composition) := by
  simpa [canonicalA1NisLocalEquivalencesProperty] using
    (Localization.LeftBousfield.isLocalization reflector.adjunction :
      reflector.reflector.IsLocalization
        (Localization.LeftBousfield.W
          (· ∈ Set.range
            (LinearA1NisLocalPST.inclusion
              (Boundary.canonicalCategory composition)).obj)))

/-- Construct the canonical A1/Nis reflector package from an actual
sheafification adjunction and its left-exactness. -/
noncomputable def canonicalA1NisReflectorPackage_of_adj
    (composition : Boundary.CanonicalCompositionData (k := k))
    (sheafification :
      LinearPST (Boundary.canonicalCategory composition) ⥤
        LinearA1NisLocalPST (Boundary.canonicalCategory composition))
    (adj :
      sheafification ⊣
        LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition))
    [CategoryTheory.Limits.PreservesFiniteLimits sheafification] :
    CanonicalA1NisReflectorPackage composition := by
  letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
    Boundary.linearPSTPreadditive
      (category := Boundary.canonicalCategory composition)
  letI : Preadditive (LinearA1NisLocalPST (Boundary.canonicalCategory composition)) :=
    LinearA1NisLocalPST.preadditive
      (category := Boundary.canonicalCategory composition)
  letI : CategoryTheory.Limits.HasFiniteLimits
      (LinearPST (Boundary.canonicalCategory composition)) :=
    LinearPST.hasFiniteLimits
      (category := Boundary.canonicalCategory composition)
  letI : CategoryTheory.Limits.HasBinaryProducts
      (LinearPST (Boundary.canonicalCategory composition)) := by
    infer_instance
  letI : sheafification.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  letI : sheafification.PreservesZeroMorphisms := by
    infer_instance
  letI : CategoryTheory.Limits.PreservesLimitsOfShape
      (Discrete CategoryTheory.Limits.WalkingPair) sheafification := by
    infer_instance
  refine
    { reflector := sheafification
      adjunction := adj
      preservesFiniteLimits := by infer_instance
      additive :=
        Functor.additive_of_preserves_binary_products sheafification
      counit_isIso := ?_
      unit_mem := ?_
      reflects_localEquivalences := ?_ }
  · intro L
    exact canonicalA1NisSheafification_counit_isIso
      composition sheafification adj L
  · intro X
    exact canonicalA1NisSheafification_unit_mem_localEquivalences
      composition sheafification adj X
  · intro X Y φ
    exact canonicalA1NisLocalEquivalence_iff_sheafification_map_isIso
      composition sheafification adj φ

/-- Boundary-owned calculus-of-fractions package for the canonical A1/Nis
localization class. -/
structure CanonicalA1NisLeftCalculusPackage
    (composition : Boundary.CanonicalCompositionData (k := k)) where
  weakEquivalences : CanonicalA1NisWeakEquivalencePackage composition
  hasLeftCalculus :
    (canonicalA1NisLocalEquivalencesProperty
      composition).HasLeftCalculusOfFractions

def canonicalA1NisLocalEquivalences_respectsIso
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (canonicalA1NisLocalEquivalencesProperty composition).RespectsIso := by
  let inclusion :=
    LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition)
  let P : LinearPST (Boundary.canonicalCategory composition) → Prop :=
    (· ∈ Set.range inclusion.obj)
  let W : MorphismProperty (LinearPST (Boundary.canonicalCategory composition)) :=
    Localization.LeftBousfield.W P
  change W.RespectsIso
  apply MorphismProperty.RespectsIso.mk W
  · intro X Y Z e f hf
    exact W.comp_mem e.hom f
      (Localization.LeftBousfield.W_of_isIso P e.hom) hf
  · intro X Y Z e f hf
    exact W.comp_mem f e.hom hf
      (Localization.LeftBousfield.W_of_isIso P e.hom)

/-- Componentwise canonical local equivalences induce a canonical local
equivalence on finite biproducts. -/
theorem canonicalA1NisLocalEquivalences_biproduct_map
    (composition : Boundary.CanonicalCompositionData (k := k))
    {J : Type*} [Fintype J]
    {X Y : J → LinearPST (Boundary.canonicalCategory composition)}
    (f : ∀ j, X j ⟶ Y j)
    (hf : ∀ j, canonicalA1NisLocalEquivalences composition (f j)) :
    canonicalA1NisLocalEquivalences composition
      (CategoryTheory.Limits.biproduct.map f) := by
  letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
    Boundary.linearPSTPreadditive
      (category := Boundary.canonicalCategory composition)
  letI : CategoryTheory.Limits.HasFiniteBiproducts
      (LinearPST (Boundary.canonicalCategory composition)) :=
    LinearPST.hasFiniteBiproducts
      (category := Boundary.canonicalCategory composition)
  intro Z hZ
  constructor
  · intro g h hgh
    apply CategoryTheory.Limits.biproduct.hom_ext'
    intro j
    apply (hf j Z hZ).1
    have hcomponent :
        CategoryTheory.Limits.biproduct.ι X j ≫
            CategoryTheory.Limits.biproduct.map f ≫ g =
          CategoryTheory.Limits.biproduct.ι X j ≫
            CategoryTheory.Limits.biproduct.map f ≫ h := by
      simpa [Category.assoc] using
        congrArg (fun q => CategoryTheory.Limits.biproduct.ι X j ≫ q) hgh
    simpa [Category.assoc] using hcomponent
  · intro g
    classical
    choose desc hdesc using
      fun j => (hf j Z hZ).2
        (CategoryTheory.Limits.biproduct.ι X j ≫ g)
    refine ⟨CategoryTheory.Limits.biproduct.desc desc, ?_⟩
    apply CategoryTheory.Limits.biproduct.hom_ext'
    intro j
    simpa [Category.assoc] using hdesc j

/-- The canonical A1/Nis local-equivalence class is stable under finite
products, by finite-product/biproduct comparison in the preadditive source. -/
def canonicalA1NisLocalEquivalences_isStableUnderFiniteProducts
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (canonicalA1NisLocalEquivalencesProperty
      composition).IsStableUnderFiniteProducts := by
  letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
    Boundary.linearPSTPreadditive
      (category := Boundary.canonicalCategory composition)
  letI : CategoryTheory.Limits.HasFiniteBiproducts
      (LinearPST (Boundary.canonicalCategory composition)) :=
    LinearPST.hasFiniteBiproducts
      (category := Boundary.canonicalCategory composition)
  letI : CategoryTheory.Limits.HasFiniteProducts
      (LinearPST (Boundary.canonicalCategory composition)) :=
    LinearPST.hasFiniteProducts
      (category := Boundary.canonicalCategory composition)
  let W := canonicalA1NisLocalEquivalencesProperty composition
  letI : W.RespectsIso :=
    canonicalA1NisLocalEquivalences_respectsIso composition
  letI : W.IsStableUnderComposition := by
    change
      (Localization.LeftBousfield.W
        (· ∈ Set.range
          (LinearA1NisLocalPST.inclusion
            (Boundary.canonicalCategory composition)).obj)).IsStableUnderComposition
    infer_instance
  refine
    { isStableUnderProductsOfShape := fun J _ => ?_ }
  classical
  cases nonempty_fintype J
  apply MorphismProperty.IsStableUnderProductsOfShape.mk
  intro X Y f hf
  have hf' :
      ∀ j, canonicalA1NisLocalEquivalences composition (f j) := by
    intro j
    exact hf j
  have hb :
      W (CategoryTheory.Limits.biproduct.map f) := by
    change canonicalA1NisLocalEquivalences composition
      (CategoryTheory.Limits.biproduct.map f)
    exact canonicalA1NisLocalEquivalences_biproduct_map
      (J := J) (X := X) (Y := Y) composition f hf'
  have hPi :
      CategoryTheory.Limits.Pi.map f =
        (CategoryTheory.Limits.biproduct.isoProduct X).inv ≫
          CategoryTheory.Limits.biproduct.map f ≫
          (CategoryTheory.Limits.biproduct.isoProduct Y).hom := by
    apply CategoryTheory.Limits.Pi.hom_ext
    intro j
    simp [Category.assoc,
      CategoryTheory.Limits.biproduct.isoProduct_hom,
      CategoryTheory.Limits.biproduct.isoProduct_inv]
  rw [hPi]
  exact W.comp_mem
    ((CategoryTheory.Limits.biproduct.isoProduct X).inv ≫
      CategoryTheory.Limits.biproduct.map f)
    (CategoryTheory.Limits.biproduct.isoProduct Y).hom
    (W.comp_mem (CategoryTheory.Limits.biproduct.isoProduct X).inv
      (CategoryTheory.Limits.biproduct.map f)
      (Localization.LeftBousfield.W_of_isIso
        (· ∈ Set.range
          (LinearA1NisLocalPST.inclusion
            (Boundary.canonicalCategory composition)).obj)
        (CategoryTheory.Limits.biproduct.isoProduct X).inv)
      hb)
    (Localization.LeftBousfield.W_of_isIso
      (· ∈ Set.range
        (LinearA1NisLocalPST.inclusion
          (Boundary.canonicalCategory composition)).obj)
      (CategoryTheory.Limits.biproduct.isoProduct Y).hom)

/-- The canonical local inclusion is full. -/
theorem canonicalA1NisLocalInclusion_full
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (LinearA1NisLocalPST.inclusion
      (Boundary.canonicalCategory composition)).Full :=
  LinearA1NisLocalPST.inclusion_full

/-- The canonical local inclusion is faithful. -/
theorem canonicalA1NisLocalInclusion_faithful
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (LinearA1NisLocalPST.inclusion
      (Boundary.canonicalCategory composition)).Faithful :=
  LinearA1NisLocalPST.inclusion_faithful

/-- The canonical local inclusion is fully faithful. -/
noncomputable def canonicalA1NisLocalInclusion_fullyFaithful
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (LinearA1NisLocalPST.inclusion
      (Boundary.canonicalCategory composition)).FullyFaithful := by
  letI : (LinearA1NisLocalPST.inclusion
      (Boundary.canonicalCategory composition)).Full :=
    canonicalA1NisLocalInclusion_full composition
  letI : (LinearA1NisLocalPST.inclusion
      (Boundary.canonicalCategory composition)).Faithful :=
    canonicalA1NisLocalInclusion_faithful composition
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- If `sheafification ⊣ localInclusion`, then the counit on local objects is
an isomorphism because the inclusion is fully faithful. -/
theorem canonicalA1NisSheafification_counit_isIso
    (composition : Boundary.CanonicalCompositionData (k := k))
    (sheafification :
      LinearPST (Boundary.canonicalCategory composition) ⥤
        LinearA1NisLocalPST (Boundary.canonicalCategory composition))
    (adj :
      sheafification ⊣
        LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition))
    (L : LinearA1NisLocalPST (Boundary.canonicalCategory composition)) :
    IsIso (adj.counit.app L) := by
  letI : (LinearA1NisLocalPST.inclusion
      (Boundary.canonicalCategory composition)).Full :=
    canonicalA1NisLocalInclusion_full composition
  letI : (LinearA1NisLocalPST.inclusion
      (Boundary.canonicalCategory composition)).Faithful :=
    canonicalA1NisLocalInclusion_faithful composition
  exact (inferInstance : IsIso (adj.counit.app L))

/-- The reflector unit belongs to the canonical A1/Nis local-equivalence class. -/
theorem canonicalA1NisSheafification_unit_mem_localEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k))
    (sheafification :
      LinearPST (Boundary.canonicalCategory composition) ⥤
        LinearA1NisLocalPST (Boundary.canonicalCategory composition))
    (adj :
      sheafification ⊣
        LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition))
    (X : LinearPST (Boundary.canonicalCategory composition)) :
    canonicalA1NisLocalEquivalences composition (adj.unit.app X) := by
  exact Localization.LeftBousfield.W_adj_unit_app adj X

/-- A morphism is a canonical local equivalence iff its image under the
reflector is an isomorphism. -/
theorem canonicalA1NisLocalEquivalence_iff_sheafification_map_isIso
    (composition : Boundary.CanonicalCompositionData (k := k))
    (sheafification :
      LinearPST (Boundary.canonicalCategory composition) ⥤
        LinearA1NisLocalPST (Boundary.canonicalCategory composition))
    (adj :
      sheafification ⊣
        LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition))
    {X Y : LinearPST (Boundary.canonicalCategory composition)}
    (φ : X ⟶ Y) :
    canonicalA1NisLocalEquivalences composition φ ↔
      IsIso (sheafification.map φ) := by
  letI : (LinearA1NisLocalPST.inclusion
      (Boundary.canonicalCategory composition)).Full :=
    canonicalA1NisLocalInclusion_full composition
  letI : (LinearA1NisLocalPST.inclusion
      (Boundary.canonicalCategory composition)).Faithful :=
    canonicalA1NisLocalInclusion_faithful composition
  exact Localization.LeftBousfield.W_iff_isIso_map adj φ

/-- The reflector inverts every canonical A1/Nis local equivalence. -/
theorem canonicalA1NisSheafification_reflector_inverts_localEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k))
    (sheafification :
      LinearPST (Boundary.canonicalCategory composition) ⥤
        LinearA1NisLocalPST (Boundary.canonicalCategory composition))
    (adj :
      sheafification ⊣
        LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition))
    {X Y : LinearPST (Boundary.canonicalCategory composition)}
    (φ : X ⟶ Y)
    (hφ : canonicalA1NisLocalEquivalences composition φ) :
    IsIso (sheafification.map φ) :=
  (canonicalA1NisLocalEquivalence_iff_sheafification_map_isIso
    composition sheafification adj φ).mp hφ

/-- A reflector onto the bundled `A1`+Nisnevich-local linear presheaves gives
the canonical local-equivalence class a left calculus of fractions.

This is the Ore argument for the left Bousfield class: for a right fraction
`X ← X' → Y`, the unit `Y ⟶ i L Y` is the new denominator, and the required
map out of `X` is obtained from the defining bijection against the local object
`i L Y`. The extension axiom is proved by the same injectivity condition. -/
theorem canonicalA1NisLocalEquivalences_hasLeftCalculusOfFractions_of_adj
    (composition : Boundary.CanonicalCompositionData (k := k))
    (sheafification :
      LinearPST (Boundary.canonicalCategory composition) ⥤
        LinearA1NisLocalPST (Boundary.canonicalCategory composition))
    (adj :
      sheafification ⊣
        LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition)) :
    (canonicalA1NisLocalEquivalencesProperty
      composition).HasLeftCalculusOfFractions := by
  let inclusion :=
    LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition)
  let W : MorphismProperty (LinearPST (Boundary.canonicalCategory composition)) :=
    Localization.LeftBousfield.W (· ∈ Set.range inclusion.obj)
  change W.HasLeftCalculusOfFractions
  refine
    { exists_leftFraction := ?_
      ext := ?_ }
  · intro X Y φ
    let localY := inclusion.obj (sheafification.obj Y)
    have hlocalY : localY ∈ Set.range inclusion.obj :=
      ⟨sheafification.obj Y, rfl⟩
    have hunit : W (adj.unit.app Y) :=
      canonicalA1NisSheafification_unit_mem_localEquivalences
        composition sheafification adj Y
    rcases (φ.hs localY hlocalY).2 (φ.f ≫ adj.unit.app Y) with
      ⟨lift, hlift⟩
    refine ⟨MorphismProperty.LeftFraction.mk lift (adj.unit.app Y) hunit, ?_⟩
    exact hlift.symm
  · intro X' X Y f₁ f₂ s hs h
    let localY := inclusion.obj (sheafification.obj Y)
    have hlocalY : localY ∈ Set.range inclusion.obj :=
      ⟨sheafification.obj Y, rfl⟩
    have hunit : W (adj.unit.app Y) :=
      canonicalA1NisSheafification_unit_mem_localEquivalences
        composition sheafification adj Y
    refine ⟨localY, adj.unit.app Y, hunit, ?_⟩
    apply (hs localY hlocalY).1

/-- The canonical A1/Nis localization category carries the quotient
preadditive structure produced by the localization calculus of fractions from
a reflector adjunction. -/
noncomputable def canonicalA1NisLocalization_preadditive_of_adj
    (composition : Boundary.CanonicalCompositionData (k := k))
    (sheafification :
      LinearPST (Boundary.canonicalCategory composition) ⥤
        LinearA1NisLocalPST (Boundary.canonicalCategory composition))
    (adj :
      sheafification ⊣
        LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition)) :
    Preadditive (canonicalA1NisLocalization composition) := by
  let W := canonicalA1NisLocalEquivalencesProperty composition
  change Preadditive W.Localization
  letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
    Boundary.linearPSTPreadditive
      (category := Boundary.canonicalCategory composition)
  letI : W.HasLeftCalculusOfFractions :=
    canonicalA1NisLocalEquivalences_hasLeftCalculusOfFractions_of_adj
      composition sheafification adj
  exact Localization.preadditive W.Q W

/-- The canonical A1/Nis localization category carries the quotient
preadditive structure produced by a left calculus of fractions. -/
noncomputable def canonicalA1NisLocalization_preadditive_of_leftCalculus
    (composition : Boundary.CanonicalCompositionData (k := k))
    (leftCalculus : CanonicalA1NisLeftCalculusPackage composition) :
    Preadditive (canonicalA1NisLocalization composition) := by
  let W := canonicalA1NisLocalEquivalencesProperty composition
  change Preadditive W.Localization
  letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
    Boundary.linearPSTPreadditive
      (category := Boundary.canonicalCategory composition)
  letI : W.HasLeftCalculusOfFractions := leftCalculus.hasLeftCalculus
  exact Localization.preadditive W.Q W

theorem canonicalA1NisLocalizationFunctor_additive_from_sheafification
    (composition : Boundary.CanonicalCompositionData (k := k))
    (sheafification :
      LinearPST (Boundary.canonicalCategory composition) ⥤
        LinearA1NisLocalPST (Boundary.canonicalCategory composition))
    (adj :
      sheafification ⊣
        LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition)) :
    letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
      Boundary.linearPSTPreadditive
        (category := Boundary.canonicalCategory composition)
    letI : Preadditive (canonicalA1NisLocalization composition) :=
      canonicalA1NisLocalization_preadditive_of_adj
        composition sheafification adj
    (canonicalA1NisLocalizationFunctor composition).Additive := by
  letI : Preadditive (canonicalA1NisLocalization composition) :=
    canonicalA1NisLocalization_preadditive_of_adj
      composition sheafification adj
  let W := canonicalA1NisLocalEquivalencesProperty composition
  change W.Q.Additive
  letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
    Boundary.linearPSTPreadditive
      (category := Boundary.canonicalCategory composition)
  letI : W.HasLeftCalculusOfFractions :=
    canonicalA1NisLocalEquivalences_hasLeftCalculusOfFractions_of_adj
      composition sheafification adj
  exact Localization.functor_additive W.Q W

/-- The canonical A1/Nis localization functor is additive for the quotient
preadditive structure produced by the left calculus of fractions. -/
theorem canonicalA1NisLocalizationFunctor_additive_of_leftCalculus
    (composition : Boundary.CanonicalCompositionData (k := k))
    (leftCalculus : CanonicalA1NisLeftCalculusPackage composition) :
    letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
      Boundary.linearPSTPreadditive
        (category := Boundary.canonicalCategory composition)
    letI : Preadditive (canonicalA1NisLocalization composition) :=
      canonicalA1NisLocalization_preadditive_of_leftCalculus
        composition leftCalculus
    (canonicalA1NisLocalizationFunctor composition).Additive := by
  letI : Preadditive (canonicalA1NisLocalization composition) :=
    canonicalA1NisLocalization_preadditive_of_leftCalculus
      composition leftCalculus
  let W := canonicalA1NisLocalEquivalencesProperty composition
  change W.Q.Additive
  letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
    Boundary.linearPSTPreadditive
      (category := Boundary.canonicalCategory composition)
  letI : W.HasLeftCalculusOfFractions := leftCalculus.hasLeftCalculus
  exact Localization.functor_additive W.Q W

/-- The canonical A1/Nis localization has a zero object transported by the
additive localization functor from the source zero object. -/
noncomputable def canonicalA1NisLocalization_hasZeroObject_of_leftCalculus
    (composition : Boundary.CanonicalCompositionData (k := k))
    (leftCalculus : CanonicalA1NisLeftCalculusPackage composition) :
    CategoryTheory.Limits.HasZeroObject
      (canonicalA1NisLocalization composition) := by
  let W := canonicalA1NisLocalEquivalencesProperty composition
  change CategoryTheory.Limits.HasZeroObject W.Localization
  letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
    Boundary.linearPSTPreadditive
      (category := Boundary.canonicalCategory composition)
  letI : W.HasLeftCalculusOfFractions := leftCalculus.hasLeftCalculus
  letI : CategoryTheory.Limits.HasZeroObject
      (LinearPST (Boundary.canonicalCategory composition)) :=
    LinearPST.hasZeroObject
      (category := Boundary.canonicalCategory composition)
  exact W.Q.hasZeroObject_of_additive

/-- Zero morphisms in the canonical A1/Nis localization are part of the
preadditive quotient structure. -/
noncomputable def canonicalA1NisLocalization_hasZeroMorphisms_of_leftCalculus
    (composition : Boundary.CanonicalCompositionData (k := k))
    (leftCalculus : CanonicalA1NisLeftCalculusPackage composition) :
    CategoryTheory.Limits.HasZeroMorphisms
      (canonicalA1NisLocalization composition) := by
  letI : Preadditive (canonicalA1NisLocalization composition) :=
    canonicalA1NisLocalization_preadditive_of_leftCalculus
      composition leftCalculus
  infer_instance

/-- The canonical source category of linear presheaves with transfers has a
terminal object, because it has the constructed zero object. -/
def canonicalLinearPST_hasTerminal
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    CategoryTheory.Limits.HasTerminal
      (LinearPST (Boundary.canonicalCategory composition)) := by
  letI : CategoryTheory.Limits.HasZeroObject
      (LinearPST (Boundary.canonicalCategory composition)) :=
    LinearPST.hasZeroObject
      (category := Boundary.canonicalCategory composition)
  infer_instance

/-- The canonical A1/Nis localization has a terminal object, because it has
the constructed zero object. -/
noncomputable def canonicalA1NisLocalization_hasTerminal_of_leftCalculus
    (composition : Boundary.CanonicalCompositionData (k := k))
    (leftCalculus : CanonicalA1NisLeftCalculusPackage composition) :
    CategoryTheory.Limits.HasTerminal
      (canonicalA1NisLocalization composition) := by
  letI : CategoryTheory.Limits.HasZeroObject
      (canonicalA1NisLocalization composition) :=
    canonicalA1NisLocalization_hasZeroObject_of_leftCalculus
      composition leftCalculus
  infer_instance

/-- The canonical A1/Nis localization has finite products because its
local-equivalence class is stable under finite products. -/
noncomputable def canonicalA1NisLocalization_hasFiniteProducts_of_leftCalculus
    (composition : Boundary.CanonicalCompositionData (k := k))
    (_leftCalculus : CanonicalA1NisLeftCalculusPackage composition) :
    CategoryTheory.Limits.HasFiniteProducts
      (canonicalA1NisLocalization composition) := by
  let W := canonicalA1NisLocalEquivalencesProperty composition
  change CategoryTheory.Limits.HasFiniteProducts W.Localization
  letI : CategoryTheory.Limits.HasFiniteProducts
      (LinearPST (Boundary.canonicalCategory composition)) :=
    LinearPST.hasFiniteProducts
      (category := Boundary.canonicalCategory composition)
  letI : W.ContainsIdentities := by
    change
      (Localization.LeftBousfield.W
        (· ∈ Set.range
          (LinearA1NisLocalPST.inclusion
            (Boundary.canonicalCategory composition)).obj)).ContainsIdentities
    infer_instance
  letI : W.IsStableUnderFiniteProducts :=
    canonicalA1NisLocalEquivalences_isStableUnderFiniteProducts composition
  exact Localization.hasFiniteProducts W.Q W

/-- The canonical A1/Nis localization has finite biproducts, obtained from
finite products in its quotient preadditive structure. -/
noncomputable def canonicalA1NisLocalization_hasFiniteBiproducts_of_leftCalculus
    (composition : Boundary.CanonicalCompositionData (k := k))
    (leftCalculus : CanonicalA1NisLeftCalculusPackage composition) :
    letI : CategoryTheory.Limits.HasZeroMorphisms
      (canonicalA1NisLocalization composition) :=
        canonicalA1NisLocalization_hasZeroMorphisms_of_leftCalculus
          composition leftCalculus
    CategoryTheory.Limits.HasFiniteBiproducts
      (canonicalA1NisLocalization composition) := by
  letI : Preadditive (canonicalA1NisLocalization composition) :=
    canonicalA1NisLocalization_preadditive_of_leftCalculus
      composition leftCalculus
  letI : CategoryTheory.Limits.HasZeroMorphisms
      (canonicalA1NisLocalization composition) :=
    canonicalA1NisLocalization_hasZeroMorphisms_of_leftCalculus
      composition leftCalculus
  letI : CategoryTheory.Limits.HasFiniteProducts
      (canonicalA1NisLocalization composition) :=
    canonicalA1NisLocalization_hasFiniteProducts_of_leftCalculus
      composition leftCalculus
  exact CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- The canonical A1/Nis localization has finite coproducts because it has
finite biproducts. -/
noncomputable def canonicalA1NisLocalization_hasFiniteCoproducts_of_leftCalculus
    (composition : Boundary.CanonicalCompositionData (k := k))
    (leftCalculus : CanonicalA1NisLeftCalculusPackage composition) :
    letI : CategoryTheory.Limits.HasZeroMorphisms
      (canonicalA1NisLocalization composition) :=
        canonicalA1NisLocalization_hasZeroMorphisms_of_leftCalculus
          composition leftCalculus
    CategoryTheory.Limits.HasFiniteCoproducts
      (canonicalA1NisLocalization composition) := by
  letI : CategoryTheory.Limits.HasZeroMorphisms
      (canonicalA1NisLocalization composition) :=
    canonicalA1NisLocalization_hasZeroMorphisms_of_leftCalculus
      composition leftCalculus
  letI : CategoryTheory.Limits.HasFiniteBiproducts
      (canonicalA1NisLocalization composition) :=
    canonicalA1NisLocalization_hasFiniteBiproducts_of_leftCalculus
      composition leftCalculus
  infer_instance

/-- The canonical A1/Nis localization has pullbacks once the canonical
reflector model is supplied.

The proof transfers pullbacks from the full subcategory of local linear
presheaves across the equivalence between Mathlib's abstract localization and
the reflector model. The pullbacks in the local subcategory are constructed
as ambient pullbacks in `LinearPST`, using
`LinearA1NisLocalPST.isLinearA1NisLocal_pullback`. -/
noncomputable def canonicalA1NisLocalization_hasPullbacks_of_reflector
    (composition : Boundary.CanonicalCompositionData (k := k))
    (reflector : CanonicalA1NisReflectorPackage composition) :
    CategoryTheory.Limits.HasPullbacks
      (canonicalA1NisLocalization composition) := by
  let W := canonicalA1NisLocalEquivalencesProperty composition
  let L := reflector.reflector
  haveI : L.IsLocalization W := by
    change L.IsLocalization
      (Localization.LeftBousfield.W
        (· ∈ Set.range
          (LinearA1NisLocalPST.inclusion
            (Boundary.canonicalCategory composition)).obj))
    exact Localization.LeftBousfield.isLocalization reflector.adjunction
  letI : CategoryTheory.Limits.HasPullbacks
      (LinearPST (Boundary.canonicalCategory composition)) := by
    letI : CategoryTheory.Limits.HasFiniteLimits
        (LinearPST (Boundary.canonicalCategory composition)) :=
      LinearPST.hasFiniteLimits
        (category := Boundary.canonicalCategory composition)
    infer_instance
  letI : CategoryTheory.Limits.HasPullbacks
      (LinearA1NisLocalPST (Boundary.canonicalCategory composition)) :=
    LinearA1NisLocalPST.hasPullbacks
      (category := Boundary.canonicalCategory composition)
  let e := Localization.equivalenceFromModel L W
  exact CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence e.functor

/-- The canonical A1/Nis localization has finite limits from its constructed
terminal object and the pullbacks transported from the reflector model. -/
noncomputable def canonicalA1NisLocalization_hasFiniteLimits_of_leftCalculus
    (composition : Boundary.CanonicalCompositionData (k := k))
    (leftCalculus : CanonicalA1NisLeftCalculusPackage composition)
    (reflector : CanonicalA1NisReflectorPackage composition) :
    CategoryTheory.Limits.HasFiniteLimits
      (canonicalA1NisLocalization composition) := by
  letI : CategoryTheory.Limits.HasTerminal
      (canonicalA1NisLocalization composition) :=
    canonicalA1NisLocalization_hasTerminal_of_leftCalculus
      composition leftCalculus
  letI : CategoryTheory.Limits.HasPullbacks
      (canonicalA1NisLocalization composition) :=
    canonicalA1NisLocalization_hasPullbacks_of_reflector
      composition reflector
  exact CategoryTheory.Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The canonical A1/Nis localization functor preserves zero morphisms because
it is additive for the quotient preadditive structure. -/
noncomputable def
    canonicalA1NisLocalizationFunctor_preservesZeroMorphisms_of_leftCalculus
    (composition : Boundary.CanonicalCompositionData (k := k))
    (leftCalculus : CanonicalA1NisLeftCalculusPackage composition) :
    letI : CategoryTheory.Limits.HasZeroMorphisms
      (LinearPST (Boundary.canonicalCategory composition)) := by
        letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
          Boundary.linearPSTPreadditive
            (category := Boundary.canonicalCategory composition)
        infer_instance
    letI : CategoryTheory.Limits.HasZeroMorphisms
      (canonicalA1NisLocalization composition) :=
        canonicalA1NisLocalization_hasZeroMorphisms_of_leftCalculus
          composition leftCalculus
    (canonicalA1NisLocalizationFunctor composition).PreservesZeroMorphisms := by
  letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
    Boundary.linearPSTPreadditive
      (category := Boundary.canonicalCategory composition)
  letI : Preadditive (canonicalA1NisLocalization composition) :=
    canonicalA1NisLocalization_preadditive_of_leftCalculus
      composition leftCalculus
  letI : (canonicalA1NisLocalizationFunctor composition).Additive :=
    canonicalA1NisLocalizationFunctor_additive_of_leftCalculus
      composition leftCalculus
  infer_instance

/-- The canonical A1/Nis localization functor preserves terminal objects
because it preserves zero morphisms between categories with zero objects. -/
noncomputable def
    canonicalA1NisLocalizationFunctor_preservesTerminal_of_leftCalculus
    (composition : Boundary.CanonicalCompositionData (k := k))
    (leftCalculus : CanonicalA1NisLeftCalculusPackage composition) :
    CategoryTheory.Limits.PreservesLimit
      (Functor.empty.{0}
        (LinearPST (Boundary.canonicalCategory composition)))
      (canonicalA1NisLocalizationFunctor composition) := by
  letI : CategoryTheory.Limits.HasZeroObject
      (LinearPST (Boundary.canonicalCategory composition)) :=
    LinearPST.hasZeroObject
      (category := Boundary.canonicalCategory composition)
  letI : CategoryTheory.Limits.HasZeroObject
      (canonicalA1NisLocalization composition) :=
    canonicalA1NisLocalization_hasZeroObject_of_leftCalculus
      composition leftCalculus
  letI : CategoryTheory.Limits.HasZeroMorphisms
      (LinearPST (Boundary.canonicalCategory composition)) := by
    letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
      Boundary.linearPSTPreadditive
        (category := Boundary.canonicalCategory composition)
    infer_instance
  letI : CategoryTheory.Limits.HasZeroMorphisms
      (canonicalA1NisLocalization composition) :=
    canonicalA1NisLocalization_hasZeroMorphisms_of_leftCalculus
      composition leftCalculus
  letI : (canonicalA1NisLocalizationFunctor composition).PreservesZeroMorphisms :=
    canonicalA1NisLocalizationFunctor_preservesZeroMorphisms_of_leftCalculus
      composition leftCalculus
  exact CategoryTheory.preservesTerminalObject_of_preservesZeroMorphisms
    (canonicalA1NisLocalizationFunctor composition)

/-- The canonical A1/Nis localization functor preserves finite products by the
finite-product localization theorem. -/
noncomputable def
    canonicalA1NisLocalizationFunctor_preservesFiniteProducts_of_leftCalculus
    (composition : Boundary.CanonicalCompositionData (k := k))
    (_leftCalculus : CanonicalA1NisLeftCalculusPackage composition) :
    CategoryTheory.Limits.PreservesFiniteProducts
      (canonicalA1NisLocalizationFunctor composition) := by
  let W := canonicalA1NisLocalEquivalencesProperty composition
  change CategoryTheory.Limits.PreservesFiniteProducts W.Q
  letI : CategoryTheory.Limits.HasFiniteProducts
      (LinearPST (Boundary.canonicalCategory composition)) :=
    LinearPST.hasFiniteProducts
      (category := Boundary.canonicalCategory composition)
  letI : W.ContainsIdentities := by
    change
      (Localization.LeftBousfield.W
        (· ∈ Set.range
          (LinearA1NisLocalPST.inclusion
            (Boundary.canonicalCategory composition)).obj)).ContainsIdentities
    infer_instance
  letI : W.IsStableUnderFiniteProducts :=
    canonicalA1NisLocalEquivalences_isStableUnderFiniteProducts composition
  exact Localization.preservesFiniteProducts W.Q W

instance canonicalA1NisLocalizationFunctor_isLocalization
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (canonicalA1NisLocalizationFunctor composition).IsLocalization
      (canonicalA1NisLocalEquivalencesProperty composition) := by
  dsimp [canonicalA1NisLocalizationFunctor, canonicalA1NisLocalization]
  infer_instance

/-- The abstract canonical A1/Nis localization is equivalent to the reflector
model of local objects.

Proof chain: the reflector adjunction identifies local objects with the
left-Bousfield localization model; Mathlib's `equivalenceFromModel` then
compares that model with the abstract localization category. -/
noncomputable def canonicalA1NisLocalization_equivalenceFromReflector
    (composition : Boundary.CanonicalCompositionData (k := k))
    (reflector : CanonicalA1NisReflectorPackage composition) :
    canonicalA1NisLocalization composition ≌
      LinearA1NisLocalPST (Boundary.canonicalCategory composition) := by
  let W := canonicalA1NisLocalEquivalencesProperty composition
  let L := reflector.reflector
  haveI : L.IsLocalization W := by
    change L.IsLocalization
      (Localization.LeftBousfield.W
        (· ∈ Set.range
          (LinearA1NisLocalPST.inclusion
            (Boundary.canonicalCategory composition)).obj))
    exact Localization.LeftBousfield.isLocalization reflector.adjunction
  exact Localization.equivalenceFromModel L W

/-- Under the reflector-model equivalence, the abstract localization functor is
the canonical A1/Nis reflector. -/
noncomputable def
    canonicalA1NisLocalizationFunctor_comp_equivalenceFromReflector_functor
    (composition : Boundary.CanonicalCompositionData (k := k))
    (reflector : CanonicalA1NisReflectorPackage composition) :
    canonicalA1NisLocalizationFunctor composition ⋙
        (canonicalA1NisLocalization_equivalenceFromReflector
          composition reflector).functor ≅
      reflector.reflector := by
  let W := canonicalA1NisLocalEquivalencesProperty composition
  let L := reflector.reflector
  haveI : L.IsLocalization W := by
    change L.IsLocalization
      (Localization.LeftBousfield.W
        (· ∈ Set.range
          (LinearA1NisLocalPST.inclusion
            (Boundary.canonicalCategory composition)).obj))
    exact Localization.LeftBousfield.isLocalization reflector.adjunction
  exact Localization.qCompEquivalenceFromModelFunctorIso L W

/-- Composing the reflector with the inverse reflector-model equivalence gives
the abstract localization functor. -/
noncomputable def
    canonicalA1NisReflector_comp_equivalenceFromReflector_inverse
    (composition : Boundary.CanonicalCompositionData (k := k))
    (reflector : CanonicalA1NisReflectorPackage composition) :
    reflector.reflector ⋙
        (canonicalA1NisLocalization_equivalenceFromReflector
          composition reflector).inverse ≅
      canonicalA1NisLocalizationFunctor composition := by
  let W := canonicalA1NisLocalEquivalencesProperty composition
  let L := reflector.reflector
  haveI : L.IsLocalization W := by
    change L.IsLocalization
      (Localization.LeftBousfield.W
        (· ∈ Set.range
          (LinearA1NisLocalPST.inclusion
            (Boundary.canonicalCategory composition)).obj))
    exact Localization.LeftBousfield.isLocalization reflector.adjunction
  exact Localization.compEquivalenceFromModelInverseIso L W

/-- Finite-limit preservation of the canonical A1/Nis localization functor,
proved by comparing it with the left-exact canonical reflector. -/
noncomputable def
    canonicalA1NisLocalizationFunctor_preservesFiniteLimits_of_reflector
    (composition : Boundary.CanonicalCompositionData (k := k))
    (reflector : CanonicalA1NisReflectorPackage composition) :
    CategoryTheory.Limits.PreservesFiniteLimits
      (canonicalA1NisLocalizationFunctor composition) := by
  let e := canonicalA1NisLocalization_equivalenceFromReflector
    composition reflector
  letI : CategoryTheory.Limits.PreservesFiniteLimits reflector.reflector :=
    reflector.preservesFiniteLimits
  letI : CategoryTheory.Limits.PreservesFiniteLimits e.inverse := by
    infer_instance
  letI : CategoryTheory.Limits.PreservesFiniteLimits
      (reflector.reflector ⋙ e.inverse) :=
    CategoryTheory.Limits.comp_preservesFiniteLimits reflector.reflector e.inverse
  exact CategoryTheory.Limits.preservesFiniteLimits_of_natIso
    (canonicalA1NisReflector_comp_equivalenceFromReflector_inverse
      composition reflector)

/-- Finite-colimit preservation of the canonical A1/Nis localization functor,
proved by comparing it with the reflector. The reflector preserves colimits as
a left adjoint, and the inverse equivalence preserves colimits. -/
noncomputable def
    canonicalA1NisLocalizationFunctor_preservesFiniteColimits_of_reflector
    (composition : Boundary.CanonicalCompositionData (k := k))
    (reflector : CanonicalA1NisReflectorPackage composition) :
    CategoryTheory.Limits.PreservesFiniteColimits
      (canonicalA1NisLocalizationFunctor composition) := by
  let e := canonicalA1NisLocalization_equivalenceFromReflector
    composition reflector
  letI : CategoryTheory.Limits.PreservesColimits reflector.reflector :=
    reflector.adjunction.leftAdjoint_preservesColimits
  letI : CategoryTheory.Limits.PreservesFiniteColimits reflector.reflector := by
    infer_instance
  letI : CategoryTheory.Limits.PreservesFiniteColimits e.inverse := by
    infer_instance
  letI : CategoryTheory.Limits.PreservesFiniteColimits
      (reflector.reflector ⋙ e.inverse) :=
    CategoryTheory.Limits.comp_preservesFiniteColimits reflector.reflector e.inverse
  exact CategoryTheory.Limits.preservesFiniteColimits_of_natIso

/-- A sheafification functor left adjoint to the inclusion of A1/Nis-local
linear presheaves is a localization at the corresponding Bousfield class. -/
theorem a1NisLocalization_of_adj
    {category : SmCorQ (k := k)}
    (L : LinearPST category ⥤ LinearA1NisLocalPST category)
    (adj : L ⊣ LinearA1NisLocalPST.inclusion category) :
    L.IsLocalization
      (Localization.LeftBousfield.W
        (· ∈ Set.range (LinearA1NisLocalPST.inclusion category).obj)) :=
  Localization.LeftBousfield.isLocalization adj

end Boundary
