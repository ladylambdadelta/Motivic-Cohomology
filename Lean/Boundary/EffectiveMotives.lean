import Boundary.A1Geometry
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Canonical effective motives ambient layer

This file starts the effective-motives layer over `canonicalSmCorQ` without
introducing `DMgm`, Tate stabilization, or mixed motives.

The honest ambient categorical substrate available in mathlib is:

* cochain complexes of `LinearPST (canonicalSmCorQ)`;
* the homotopy category of those complexes;
* the derived category, once `LinearPST (canonicalSmCorQ)` is equipped with an
  abelian structure.

This file now constructs the honest effective-motives quotient by producing
canonical motivic acyclics from the homological kernel of the derived
canonical `A1`/Nis localization followed by degree-zero homology.
-/

universe u

open CategoryTheory

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]

/-- Once `LinearPST` is abelian, Mathlib supplies the standard derived
category localization. This separates the real obligation, abelianity of
linear presheaves with transfers, from the derived-category packaging. -/
def canonicalLinearPST_hasDerivedCategory_standard
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))] :
    HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition)) :=
  HasDerivedCategory.standard _

/-- Once the canonical `A1`/Nis localization is abelian, Mathlib supplies the
standard derived category localization for it as well. -/
def canonicalA1NisLocalization_hasDerivedCategory_standard
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (canonicalA1NisLocalization composition)] :
    HasDerivedCategory (canonicalA1NisLocalization composition) :=
  HasDerivedCategory.standard _

/-- The ambient cochain-complex category underlying the effective layer over
`canonicalSmCorQ`. -/
abbrev canonicalEffectiveCochainComplexes
  (composition : Boundary.CanonicalCompositionData (k := k))
  [Limits.HasZeroMorphisms (LinearPST (Boundary.canonicalCategory composition))]
  [Preadditive (LinearPST (Boundary.canonicalCategory composition))] :=
  CochainComplex (LinearPST (Boundary.canonicalCategory composition)) Int

/-- The ambient homotopy category of cochain complexes over
`LinearPST (canonicalSmCorQ)`. -/
abbrev canonicalEffectiveHomotopyCategory
  (composition : Boundary.CanonicalCompositionData (k := k))
  [Limits.HasZeroMorphisms (LinearPST (Boundary.canonicalCategory composition))]
  [Preadditive (LinearPST (Boundary.canonicalCategory composition))] :=
  HomotopyCategory (LinearPST (Boundary.canonicalCategory composition)) (ComplexShape.up Int)

/-- The quasi-isomorphism class on the ambient effective cochain-complex
category. -/
abbrev canonicalEffectiveQuasiIsomorphisms
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Limits.HasZeroMorphisms (LinearPST (Boundary.canonicalCategory composition))]
    [Preadditive (LinearPST (Boundary.canonicalCategory composition))]
    [CategoryWithHomology (LinearPST (Boundary.canonicalCategory composition))] :
    MorphismProperty (canonicalEffectiveCochainComplexes composition) :=
  HomologicalComplex.quasiIso
    (LinearPST (Boundary.canonicalCategory composition)) (ComplexShape.up Int)

/-- The ambient derived category of linear presheaves with transfers over
`canonicalSmCorQ`, before the extra `A1`/Nisnevich Verdier quotient is imposed. -/
abbrev canonicalEffectiveAmbientDerivedCategory
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))] :=
  DerivedCategory (LinearPST (Boundary.canonicalCategory composition))

/-- The localization functor from cochain complexes of linear presheaves with
transfers to their ambient derived category. -/
def canonicalEffectiveAmbientDerivedLocalizationFunctor
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))] :
    canonicalEffectiveCochainComplexes composition ⥤
      canonicalEffectiveAmbientDerivedCategory composition :=
  DerivedCategory.Q

instance canonicalEffectiveAmbientDerivedLocalizationFunctor_isLocalization
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))] :
    (canonicalEffectiveAmbientDerivedLocalizationFunctor composition).IsLocalization
      (canonicalEffectiveQuasiIsomorphisms composition) := by
  dsimp [canonicalEffectiveAmbientDerivedLocalizationFunctor,
    canonicalEffectiveAmbientDerivedCategory, canonicalEffectiveQuasiIsomorphisms]
  infer_instance

/-- Universal property of the ambient derived category: functors out of the
ambient derived category are equivalent to functors on cochain complexes that
invert quasi-isomorphisms. -/
def canonicalEffectiveAmbientDerived_universalProperty
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (D : Type*) [Category D] :
    (canonicalEffectiveAmbientDerivedCategory composition ⥤ D) ≌
      (canonicalEffectiveQuasiIsomorphisms composition).FunctorsInverting D :=
  Localization.functorEquivalence
    (canonicalEffectiveAmbientDerivedLocalizationFunctor composition)
    (canonicalEffectiveQuasiIsomorphisms composition)
    D

/-- The derived target of the canonical `A1`/Nis localization functor, under
the additional hypothesis that the abelian localization category itself admits a
derived category. -/
abbrev canonicalA1NisLocalizedDerivedCategory
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)] :=
  DerivedCategory (canonicalA1NisLocalization composition)

/-- The canonical `A1`/Nis localization functor sends every canonical local
equivalence to an isomorphism. -/
lemma canonicalA1NisLocalizationFunctor_map_isIso_of_localEquivalence
    (composition : Boundary.CanonicalCompositionData (k := k))
    {X Y : LinearPST (Boundary.canonicalCategory composition)}
    (φ : X ⟶ Y)
    (hφ : canonicalA1NisLocalEquivalences composition φ) :
    IsIso ((canonicalA1NisLocalizationFunctor composition).map φ) := by
  let W : MorphismProperty (LinearPST (Boundary.canonicalCategory composition)) :=
    fun _ _ ψ => canonicalA1NisLocalEquivalences composition ψ
  letI : (canonicalA1NisLocalizationFunctor composition).IsLocalization W := by
    simpa [W] using canonicalA1NisLocalizationFunctor_isLocalization composition
  exact Localization.inverts (canonicalA1NisLocalizationFunctor composition) W φ hφ

/-- The canonical `A1`/Nis localization functor sends every Bousfield-generated
canonical weak equivalence to an isomorphism. -/
lemma canonicalA1NisLocalizationFunctor_map_isIso_of_generatedWeakEquivalence
    (composition : Boundary.CanonicalCompositionData (k := k))
    {X Y : LinearPST (Boundary.canonicalCategory composition)}
    (φ : X ⟶ Y)
    (hφ : canonicalA1NisGeneratedWeakEquivalences composition φ) :
    IsIso ((canonicalA1NisLocalizationFunctor composition).map φ) :=
  canonicalA1NisLocalizationFunctor_map_isIso_of_localEquivalence composition φ
    ((canonicalA1NisGeneratedWeakEquivalences_eq_localEquivalences composition φ).mp hφ)

/-- The derived functor induced by the canonical `A1`/Nis localization functor,
assuming the localization category is abelian and the localization functor is
exact in the sense required by mathlib's derived-category API. -/
def canonicalA1NisLocalization_mapDerivedCategory
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
  [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
  [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    canonicalEffectiveAmbientDerivedCategory composition ⥤
      canonicalA1NisLocalizedDerivedCategory composition :=
  (canonicalA1NisLocalizationFunctor composition).mapDerivedCategory

private noncomputable def canonicalA1NisLocalization_mapDerivedCategory_singleFunctorIso
    (composition : Boundary.CanonicalCompositionData (k := k))
    (n : ℤ)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    DerivedCategory.singleFunctor (LinearPST (Boundary.canonicalCategory composition)) n ⋙
        canonicalA1NisLocalization_mapDerivedCategory composition ≅
      canonicalA1NisLocalizationFunctor composition ⋙
        DerivedCategory.singleFunctor (canonicalA1NisLocalization composition) n := by
  let source := LinearPST (Boundary.canonicalCategory composition)
  let target := canonicalA1NisLocalization composition
  let L := canonicalA1NisLocalizationFunctor composition
  let eSource :=
    (SingleFunctors.evaluation source (DerivedCategory source) n).mapIso
      (DerivedCategory.singleFunctorsPostcompQIso source)
  let eTarget :=
    (SingleFunctors.evaluation target (DerivedCategory target) n).mapIso
      (DerivedCategory.singleFunctorsPostcompQIso target)
  exact
    isoWhiskerRight eSource
      (canonicalA1NisLocalization_mapDerivedCategory composition) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ L.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight
        (HomologicalComplex.singleMapHomologicalComplex L (ComplexShape.up ℤ) n)
        (DerivedCategory.Q (C := target)) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft L eTarget.symm

private lemma canonicalA1NisLocalization_mapDerivedCategory_singleFunctor_map_isIso
    (composition : Boundary.CanonicalCompositionData (k := k))
    (n : ℤ)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    {X Y : LinearPST (Boundary.canonicalCategory composition)}
    (φ : X ⟶ Y)
    [hφ : IsIso ((canonicalA1NisLocalizationFunctor composition).map φ)] :
    IsIso
      ((canonicalA1NisLocalization_mapDerivedCategory composition).map
        ((DerivedCategory.singleFunctor
            (LinearPST (Boundary.canonicalCategory composition)) n).map φ)) := by
  let source := LinearPST (Boundary.canonicalCategory composition)
  let target := canonicalA1NisLocalization composition
  let L := canonicalA1NisLocalizationFunctor composition
  let e := canonicalA1NisLocalization_mapDerivedCategory_singleFunctorIso composition n
  have hright : IsIso (((DerivedCategory.singleFunctor target n).map (L.map φ))) := by
    infer_instance
  have hEq :
      (canonicalA1NisLocalization_mapDerivedCategory composition).map
          ((DerivedCategory.singleFunctor source n).map φ) =
        (e.hom.app X) ≫ ((DerivedCategory.singleFunctor target n).map (L.map φ)) ≫
          (e.inv.app Y) := by
    calc
      (canonicalA1NisLocalization_mapDerivedCategory composition).map
          ((DerivedCategory.singleFunctor source n).map φ)
        = ((canonicalA1NisLocalization_mapDerivedCategory composition).map
            ((DerivedCategory.singleFunctor source n).map φ)) ≫ e.hom.app Y ≫ e.inv.app Y := by
              simp [Category.assoc]
      _ = e.hom.app X ≫ ((L ⋙ DerivedCategory.singleFunctor target n).map φ) ≫ e.inv.app Y := by
            simpa [Category.assoc] using
              congrArg (fun f => f ≫ e.inv.app Y) (e.hom.naturality φ)
      _ = (e.hom.app X) ≫ ((DerivedCategory.singleFunctor target n).map (L.map φ)) ≫
            (e.inv.app Y) := by
            simp [Functor.comp_map, Category.assoc]
  rw [hEq]
  infer_instance

/-- Abelian-valued homological functor obtained by taking degree-zero homology
after applying the derived canonical `A1`/Nis localization functor. -/
def canonicalA1NisDerivedHomologyFunctor
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    canonicalEffectiveAmbientDerivedCategory composition ⥤
      canonicalA1NisLocalization composition :=
  canonicalA1NisLocalization_mapDerivedCategory composition ⋙
    DerivedCategory.homologyFunctor (canonicalA1NisLocalization composition) 0

instance canonicalA1NisDerivedHomologyFunctor_isHomological
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    (canonicalA1NisDerivedHomologyFunctor composition).IsHomological := by
  change
    ((canonicalA1NisLocalizationFunctor composition).mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor (canonicalA1NisLocalization composition) 0).IsHomological
  infer_instance

noncomputable instance canonicalA1NisDerivedHomologyFunctor_shiftSequence
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    (canonicalA1NisDerivedHomologyFunctor composition).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

/-- Proof-relevant degree-zero kill data needed to extract canonical motivic
acyclics from a homological functor on the ambient derived category. -/
structure CanonicalDegreeZeroKillData
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    {A : Type*} [Category A] [Abelian A]
    (F : canonicalEffectiveAmbientDerivedCategory composition ⥤ A)
    [F.IsHomological] [F.ShiftSequence ℤ] where
  killsDegreeZeroImages :
    ∀ {X Y : LinearPST (Boundary.canonicalCategory composition)} (φ : X ⟶ Y),
      canonicalA1NisGeneratedWeakEquivalences composition φ →
        F.homologicalKernel.W
          ((DerivedCategory.singleFunctor
              (LinearPST (Boundary.canonicalCategory composition)) 0).map φ)

/-- Specialized degree-zero kill datum for the derived canonical `A1`/Nis
localization followed by degree-zero homology. -/
abbrev canonicalA1NisDerivedHomologyDegreeZeroKillData
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :=
  CanonicalDegreeZeroKillData composition
    (canonicalA1NisDerivedHomologyFunctor composition)

private lemma canonicalA1NisDerivedHomologyFunctor_singleFunctor_map_isIso
    (composition : Boundary.CanonicalCompositionData (k := k))
    (n : ℤ)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    {X Y : LinearPST (Boundary.canonicalCategory composition)}
    (φ : X ⟶ Y)
    [hφ : IsIso ((canonicalA1NisLocalizationFunctor composition).map φ)] :
    IsIso
      ((canonicalA1NisDerivedHomologyFunctor composition).map
        ((DerivedCategory.singleFunctor
            (LinearPST (Boundary.canonicalCategory composition)) n).map φ)) := by
  letI := canonicalA1NisLocalization_mapDerivedCategory_singleFunctor_map_isIso
    composition n φ
  change IsIso
    ((DerivedCategory.homologyFunctor (canonicalA1NisLocalization composition) 0).map
      ((canonicalA1NisLocalization_mapDerivedCategory composition).map
        ((DerivedCategory.singleFunctor
            (LinearPST (Boundary.canonicalCategory composition)) n).map φ)))
  infer_instance

/-- The candidate derived canonical `A1`/Nis homology functor carries explicit
degree-zero kill data for all Bousfield-generated canonical weak equivalences. -/
def canonicalA1NisDerivedHomologyDegreeZeroKill
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    canonicalA1NisDerivedHomologyDegreeZeroKillData composition := by
  refine ⟨?_⟩
  let source := LinearPST (Boundary.canonicalCategory composition)
  let F := canonicalA1NisDerivedHomologyFunctor composition
  intro X Y φ hφ
  letI : IsIso ((canonicalA1NisLocalizationFunctor composition).map φ) :=
    canonicalA1NisLocalizationFunctor_map_isIso_of_generatedWeakEquivalence composition φ hφ
  refine ((F.mem_homologicalKernel_W_iff
    ((DerivedCategory.singleFunctor source 0).map φ)).2 ?_)
  intro n
  change IsIso (F.map ((((DerivedCategory.singleFunctor source 0).map φ)⟦n⟧')))
  let s := (DerivedCategory.singleFunctors source).shiftIso n (-n) 0 (by
    rw [add_right_neg])
  have hs :
      (((DerivedCategory.singleFunctor source 0).map φ)⟦n⟧') ≫ s.hom.app Y =
        s.hom.app X ≫ ((DerivedCategory.singleFunctor source (-n)).map φ) := by
    exact s.hom.naturality φ
  have hsF :
      F.map ((((DerivedCategory.singleFunctor source 0).map φ)⟦n⟧')) ≫ F.map (s.hom.app Y) =
        F.map (s.hom.app X) ≫ F.map ((DerivedCategory.singleFunctor source (-n)).map φ) := by
    simpa [Functor.map_comp, Category.assoc] using congrArg (fun f => F.map f) hs
  letI := canonicalA1NisDerivedHomologyFunctor_singleFunctor_map_isIso composition (-n) φ
  have hmap :
      F.map ((((DerivedCategory.singleFunctor source 0).map φ)⟦n⟧')) =
        F.map (s.hom.app X) ≫ F.map ((DerivedCategory.singleFunctor source (-n)).map φ) ≫
          F.map (s.inv.app Y) := by
    have hcomp :
        ((((DerivedCategory.singleFunctor source 0).map φ)⟦n⟧') ≫ s.hom.app Y) ≫ s.inv.app Y =
          (((DerivedCategory.singleFunctor source 0).map φ)⟦n⟧') := by
      simpa [Category.assoc] using
        congrArg
          (fun f => (((DerivedCategory.singleFunctor source 0).map φ)⟦n⟧') ≫ f)
          (Iso.hom_inv_id_app s Y)
    have hfirst :
        F.map ((((DerivedCategory.singleFunctor source 0).map φ)⟦n⟧')) =
          F.map ((((DerivedCategory.singleFunctor source 0).map φ)⟦n⟧') ≫ s.hom.app Y) ≫
            F.map (s.inv.app Y) := by
      let shiftedMap := (((DerivedCategory.singleFunctor source 0).map φ)⟦n⟧')
      have hfirst' :
          F.map shiftedMap = F.map ((shiftedMap ≫ s.hom.app Y) ≫ s.inv.app Y) := by
        exact congrArg (fun f => F.map f) hcomp.symm
      have hmid :
          F.map ((shiftedMap ≫ s.hom.app Y) ≫ s.inv.app Y) =
            F.map (shiftedMap ≫ s.hom.app Y) ≫ F.map (s.inv.app Y) := by
        rw [Functor.map_comp]
      have hpre :
          F.map shiftedMap ≫ F.map (s.hom.app Y) = F.map (shiftedMap ≫ s.hom.app Y) := by
        exact (Functor.map_comp F shiftedMap (s.hom.app Y)).symm
      have hpost :
          F.map shiftedMap ≫ F.map (s.hom.app Y) ≫ F.map (s.inv.app Y) =
            F.map (shiftedMap ≫ s.hom.app Y) ≫ F.map (s.inv.app Y) := by
        simpa [Category.assoc] using congrArg (fun f => f ≫ F.map (s.inv.app Y)) hpre
      have hpost' :
          F.map shiftedMap ≫ F.map (s.hom.app Y) ≫ F.map (s.inv.app Y) =
            F.map
                ((shiftFunctor (canonicalEffectiveAmbientDerivedCategory composition) n).map
                    ((DerivedCategory.singleFunctor source 0).map φ) ≫
                  s.hom.app Y) ≫
              F.map (s.inv.app Y) := by
        simpa [shiftedMap] using hpost
      calc
        F.map shiftedMap = F.map ((shiftedMap ≫ s.hom.app Y) ≫ s.inv.app Y) := hfirst'
        _ = F.map (shiftedMap ≫ s.hom.app Y) ≫ F.map (s.inv.app Y) := hmid
        _ = F.map shiftedMap ≫ F.map (s.hom.app Y) ≫ F.map (s.inv.app Y) := hpost.symm
        _ = F.map
          ((shiftFunctor (canonicalEffectiveAmbientDerivedCategory composition) n).map
              ((DerivedCategory.singleFunctor source 0).map φ) ≫
            s.hom.app Y) ≫
              F.map (s.inv.app Y) := hpost'
    have hsecond :
        F.map ((((DerivedCategory.singleFunctor source 0).map φ)⟦n⟧') ≫ s.hom.app Y) ≫
            F.map (s.inv.app Y) =
          F.map (s.hom.app X) ≫ F.map ((DerivedCategory.singleFunctor source (-n)).map φ) ≫
            F.map (s.inv.app Y) := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (fun f => f ≫ F.map (s.inv.app Y)) hsF
    calc
    F.map ((((DerivedCategory.singleFunctor source 0).map φ)⟦n⟧'))
      = F.map ((((DerivedCategory.singleFunctor source 0).map φ)⟦n⟧') ≫ s.hom.app Y) ≫
          F.map (s.inv.app Y) := hfirst
    _ = F.map (s.hom.app X) ≫ F.map ((DerivedCategory.singleFunctor source (-n)).map φ) ≫
          F.map (s.inv.app Y) := hsecond
  have hIso :
      IsIso
        (F.map (s.hom.app X) ≫ F.map ((DerivedCategory.singleFunctor source (-n)).map φ) ≫
          F.map (s.inv.app Y)) := by
    infer_instance
  rw [← hmap] at hIso
  exact hIso

/-- The canonical `A1`/Nis Verdier subcategory of the ambient effective
derived category: the homological kernel of derived canonical `A1`/Nis
localization followed by degree-zero homology. -/
abbrev canonicalA1NisVerdierLocalizingSubcategory
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    Triangulated.Subcategory (canonicalEffectiveAmbientDerivedCategory composition) :=
  (canonicalA1NisDerivedHomologyFunctor composition).homologicalKernel

/-- The Verdier morphism class attached to the canonical `A1`/Nis subcategory. -/
abbrev canonicalA1NisVerdierLocalizingMorphisms
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    MorphismProperty (canonicalEffectiveAmbientDerivedCategory composition) :=
  (canonicalA1NisVerdierLocalizingSubcategory composition).W

/-- The canonical `A1`/Nis Verdier subcategory contains the degree-zero image
of every Bousfield-generated canonical `A1`/Nis weak equivalence. -/
theorem canonicalA1NisVerdierLocalizingSubcategory_contains_degreeZeroA1Nis
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    {F G : LinearPST (Boundary.canonicalCategory composition)}
    (φ : F ⟶ G)
    (hφ : canonicalA1NisGeneratedWeakEquivalences composition φ) :
    canonicalA1NisVerdierLocalizingMorphisms composition
      ((DerivedCategory.singleFunctor
          (LinearPST (Boundary.canonicalCategory composition)) 0).map φ) :=
  (canonicalA1NisDerivedHomologyDegreeZeroKill composition).killsDegreeZeroImages φ hφ

/-- Under the degree-zero kill target, the derived canonical `A1`/Nis homology
candidate kills every raw generator-built weak equivalence on the linear
surface. -/
theorem canonicalA1NisDerivedHomology_kills_degreeZeroRawWeakEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (hkill : canonicalA1NisDerivedHomologyDegreeZeroKillData composition)
    {F G : LinearPST (Boundary.canonicalCategory composition)}
    (φ : F ⟶ G)
    (hφ : canonicalA1NisWeakEquivalences composition (F := F.toPST) (G := G.toPST) φ) :
    (canonicalA1NisDerivedHomologyFunctor composition).homologicalKernel.W
      ((DerivedCategory.singleFunctor
          (LinearPST (Boundary.canonicalCategory composition)) 0).map φ) :=
  hkill.killsDegreeZeroImages φ
    (canonicalA1NisWeakEquivalences_le_generatedWeakEquivalences composition φ hφ)

/-- Under the degree-zero kill target, the derived canonical `A1`/Nis homology
candidate kills each primitive canonical `A1`-projection generator in degree
zero. -/
theorem canonicalA1NisDerivedHomology_kills_degreeZeroA1Projection
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (hkill : canonicalA1NisDerivedHomologyDegreeZeroKillData composition)
    (X : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    (canonicalA1NisDerivedHomologyFunctor composition).homologicalKernel.W
      ((DerivedCategory.singleFunctor
          (LinearPST (Boundary.canonicalCategory composition)) 0).map
        (show QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X) ⟶
            QtrLinear (category := Boundary.canonicalCategory composition) X from
          projectionToBase_QtrMapOfDecomposition
            (Boundary.canonicalCategory composition) X D)) :=
  hkill.killsDegreeZeroImages _
    (canonicalA1NisLocalEquivalences_le_generatedWeakEquivalences composition _
      ((canonicalA1NisGenerators_areCanonicalLocalEquivalences composition).1 X D))

/-- Under the degree-zero kill target, the derived canonical `A1`/Nis homology
candidate kills each primitive Nisnevich descent generator in degree zero. -/
theorem canonicalA1NisDerivedHomology_kills_degreeZeroNisnevichDescent
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (hkill : canonicalA1NisDerivedHomologyDegreeZeroKillData composition)
    (square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)) :
    (canonicalA1NisDerivedHomologyFunctor composition).homologicalKernel.W
      ((DerivedCategory.singleFunctor
          (LinearPST (Boundary.canonicalCategory composition)) 0).map
        square.nisnevichDescentGeneratorMapLinear) :=
  hkill.killsDegreeZeroImages _
    (canonicalA1NisLocalEquivalences_le_generatedWeakEquivalences composition _
      ((canonicalA1NisGenerators_areCanonicalLocalEquivalences composition).2 square))

/-- The canonical acyclic presentation uses exactly the direct canonical
`A1`/Nis Verdier subcategory. -/
theorem canonicalMotivicAcyclicsOfCanonicalA1NisDerivedHomology_subcategory
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    canonicalA1NisVerdierLocalizingSubcategory composition =
      (canonicalA1NisDerivedHomologyFunctor composition).homologicalKernel :=
  rfl

/-- The Verdier-class morphism property determined by the canonical motivic
acyclic subcategory produced from derived canonical `A1`/Nis homology. -/
abbrev canonicalEffectiveMotivesMorphismProperty
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    MorphismProperty (canonicalEffectiveAmbientDerivedCategory composition) :=
  canonicalA1NisVerdierLocalizingMorphisms composition

/-- Honest canonical effective motives: the Verdier/localization quotient of
`D(LinearPST(canonicalSmCorQ))` by the canonical motivic acyclics coming from
the derived canonical `A1`/Nis homology kernel. -/
abbrev canonicalEffectiveMotives
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :=
  (canonicalA1NisVerdierLocalizingMorphisms composition).Localization

/-- Canonical effective motives with the A1/Nis localization implementation
installed explicitly.

This owner-file wrapper prevents downstream files from relying on fragile
global typeclass search for additivity and finite-limit/finite-colimit
preservation of the localization functor. The mathematical content is still
the same Verdier quotient `canonicalEffectiveMotives`; the dictionaries are
exported by `A1Geometry` from its calculus and reflector comparison
theorems. -/
abbrev canonicalEffectiveMotivesFromA1NisImplementation
    (composition : Boundary.CanonicalCompositionData (k := k))
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)] :=
  letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
    implementation.sourcePreadditive
  letI : Preadditive (canonicalA1NisLocalization composition) :=
    implementation.localizedPreadditive
  let hAdd : (canonicalA1NisLocalizationFunctor composition).Additive :=
    canonicalA1NisLocalizationFunctor_additive composition implementation
  let hFiniteLimits : Limits.PreservesFiniteLimits
      (canonicalA1NisLocalizationFunctor composition) :=
    canonicalA1NisLocalizationFunctor_preservesFiniteLimits
      composition implementation
  let hFiniteColimits : Limits.PreservesFiniteColimits
      (canonicalA1NisLocalizationFunctor composition) :=
    canonicalA1NisLocalizationFunctor_preservesFiniteColimits
      composition implementation
  @canonicalEffectiveMotives k _ _ composition _ _ _ _ hAdd
    hFiniteLimits hFiniteColimits

/-- The canonical Verdier-localization functor from the ambient derived
category to the honest effective-motives quotient. -/
def canonicalEffectiveMotivesLocalizationFunctor
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    canonicalEffectiveAmbientDerivedCategory composition ⥤
      canonicalEffectiveMotives composition :=
  (canonicalA1NisVerdierLocalizingMorphisms composition).Q

/-- The canonical localization functor into effective motives, with the
A1/Nis implementation dictionaries installed explicitly. -/
def canonicalEffectiveMotivesLocalizationFunctorFromA1NisImplementation
    (composition : Boundary.CanonicalCompositionData (k := k))
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)] :
    canonicalEffectiveAmbientDerivedCategory composition ⥤
      canonicalEffectiveMotivesFromA1NisImplementation
        composition implementation :=
  letI : Preadditive (LinearPST (Boundary.canonicalCategory composition)) :=
    implementation.sourcePreadditive
  letI : Preadditive (canonicalA1NisLocalization composition) :=
    implementation.localizedPreadditive
  let hAdd : (canonicalA1NisLocalizationFunctor composition).Additive :=
    canonicalA1NisLocalizationFunctor_additive composition implementation
  let hFiniteLimits : Limits.PreservesFiniteLimits
      (canonicalA1NisLocalizationFunctor composition) :=
    canonicalA1NisLocalizationFunctor_preservesFiniteLimits
      composition implementation
  let hFiniteColimits : Limits.PreservesFiniteColimits
      (canonicalA1NisLocalizationFunctor composition) :=
    canonicalA1NisLocalizationFunctor_preservesFiniteColimits
      composition implementation
  @canonicalEffectiveMotivesLocalizationFunctor k _ _ composition _ _ _ _
    hAdd hFiniteLimits hFiniteColimits

instance canonicalEffectiveMotivesLocalizationFunctor_isLocalization
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    (canonicalEffectiveMotivesLocalizationFunctor composition).IsLocalization
      (canonicalEffectiveMotivesMorphismProperty composition) := by
  dsimp [canonicalEffectiveMotivesLocalizationFunctor,
    canonicalEffectiveMotivesMorphismProperty, canonicalEffectiveMotives]
  infer_instance

/-- The honest effective-motives Verdier quotient inverts the degree-zero
derived image of every canonical `A¹`/Nis local equivalence.

Proof chain: a canonical local equivalence is the same as a Bousfield-generated
weak equivalence; the canonical motivic acyclic datum is constructed from the
derived `A¹`/Nis homology kernel and contains the degree-zero image of every
Bousfield-generated weak equivalence; `canonicalEffectiveMotives` is the localization at
that Verdier class, so its localization functor inverts the displayed
degree-zero map. -/
theorem canonicalEffectiveMotivesLocalizationFunctor_map_degreeZero_isIso_of_localEquivalence
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    {F G : LinearPST (Boundary.canonicalCategory composition)}
    (φ : F ⟶ G)
    (hφ : canonicalA1NisLocalEquivalences composition φ) :
    IsIso
      ((canonicalEffectiveMotivesLocalizationFunctor composition).map
        ((DerivedCategory.singleFunctor
          (LinearPST (Boundary.canonicalCategory composition)) 0).map φ)) := by
  let W : MorphismProperty (canonicalEffectiveAmbientDerivedCategory composition) :=
    canonicalEffectiveMotivesMorphismProperty composition
  have hW : W
      ((DerivedCategory.singleFunctor
        (LinearPST (Boundary.canonicalCategory composition)) 0).map φ) := by
    exact canonicalA1NisVerdierLocalizingSubcategory_contains_degreeZeroA1Nis composition φ
      ((canonicalA1NisGeneratedWeakEquivalences_eq_localEquivalences composition φ).mpr hφ)
  letI : (canonicalEffectiveMotivesLocalizationFunctor composition).IsLocalization W := by
    rw [W, canonicalEffectiveMotivesMorphismProperty]
      using canonicalEffectiveMotivesLocalizationFunctor_isLocalization composition
  exact Localization.inverts
    (canonicalEffectiveMotivesLocalizationFunctor composition) W
    ((DerivedCategory.singleFunctor
      (LinearPST (Boundary.canonicalCategory composition)) 0).map φ) hW

/-- Universal property of honest canonical effective motives: functors out of
the quotient are equivalent to functors on the ambient derived category that
invert the canonical motivic acyclic morphisms. -/
def canonicalEffectiveMotives_universalProperty
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (D : Type*) [Category D] :
    (canonicalEffectiveMotives composition ⥤ D) ≌
      (canonicalEffectiveMotivesMorphismProperty composition).FunctorsInverting D :=
  Localization.functorEquivalence
    (canonicalEffectiveMotivesLocalizationFunctor composition)
    (canonicalEffectiveMotivesMorphismProperty composition)
    D

end

end Boundary
