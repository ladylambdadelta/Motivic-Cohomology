import Boundary.Basic
import Boundary.SmOver
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Topology.Irreducible

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

/-- The fiber product `X ×_k Y` over the base field. -/
abbrev overBaseProduct (X Y : Geometry.SmSchemeOver k) : Scheme :=
  pullback X.structMap Y.structMap

/-- The projection `X ×_k Y → X`. -/
abbrev overBaseProduct.fst (X Y : Geometry.SmSchemeOver k) :
    overBaseProduct X Y ⟶ X.scheme :=
  pullback.fst X.structMap Y.structMap

/-- The projection `X ×_k Y → Y`. -/
abbrev overBaseProduct.snd (X Y : Geometry.SmSchemeOver k) :
    overBaseProduct X Y ⟶ Y.scheme :=
  pullback.snd X.structMap Y.structMap

/-- The fiber product `X ×_k Y` as an actual object of `Sm/k`. -/
def overBaseProductObject (X Y : Geometry.SmSchemeOver k) : Geometry.SmSchemeOver k where
  scheme := overBaseProduct X Y
  structMap := overBaseProduct.fst X Y ≫ X.structMap
  smooth := by
    letI : MorphismProperty.IsStableUnderBaseChange @IsSmooth :=
      AlgebraicGeometry.isSmooth_isStableUnderBaseChange
    letI : IsSmooth (overBaseProduct.fst X Y) :=
      MorphismProperty.pullback_fst X.structMap Y.structMap Y.smooth
    letI : IsSmooth X.structMap := X.smooth
    infer_instance
  separated := by
    letI : IsSeparated (overBaseProduct.fst X Y) :=
      MorphismProperty.pullback_fst X.structMap Y.structMap Y.separated
    letI : IsSeparated X.structMap := X.separated
    infer_instance
  finiteType := ⟨by
      letI : QuasiCompact (overBaseProduct.fst X Y) :=
        MorphismProperty.pullback_fst X.structMap Y.structMap Y.quasiCompact_structMap
      letI : QuasiCompact X.structMap := X.quasiCompact_structMap
      infer_instance,
    by
      letI : LocallyOfFiniteType (overBaseProduct.fst X Y) :=
        MorphismProperty.pullback_fst X.structMap Y.structMap Y.locallyOfFiniteType_structMap
      letI : LocallyOfFiniteType X.structMap := X.locallyOfFiniteType_structMap
      infer_instance⟩

/-- The unit object for products over `Spec k`. -/
def overBaseUnitObject : Geometry.SmSchemeOver k where
  scheme := Spec (CommRingCat.of k)
  structMap := 𝟙 _
  smooth := by infer_instance
  separated := by infer_instance
  finiteType := by constructor <;> infer_instance

/-- The first projection `X ×_k Y ⟶ X` in `Sm/k`. -/
def overBaseProductFst (X Y : Geometry.SmSchemeOver k) :
    SmOverHom (overBaseProductObject X Y) X where
  hom := overBaseProduct.fst X Y
  over := rfl

/-- The second projection `X ×_k Y ⟶ Y` in `Sm/k`. -/
def overBaseProductSnd (X Y : Geometry.SmSchemeOver k) :
    SmOverHom (overBaseProductObject X Y) Y where
  hom := overBaseProduct.snd X Y
  over := by
    change pullback.snd X.structMap Y.structMap ≫ Y.structMap =
      pullback.fst X.structMap Y.structMap ≫ X.structMap
    simpa [overBaseProduct] using (pullback.condition (f := X.structMap) (g := Y.structMap)).symm

/-- Functoriality of the base product over `Spec k` on ordinary morphisms. -/
def overBaseProductMap
    {X₁ X₂ Y₁ Y₂ : Geometry.SmSchemeOver k}
    (f : SmOverHom X₁ X₂)
    (g : SmOverHom Y₁ Y₂) :
    SmOverHom (overBaseProductObject X₁ Y₁) (overBaseProductObject X₂ Y₂) where
  hom :=
    pullback.map X₁.structMap Y₁.structMap X₂.structMap Y₂.structMap
      f.hom g.hom (𝟙 _)
      (by simpa [Category.assoc] using f.over.symm)
      (by simpa [Category.assoc] using g.over.symm)
  over := by
    simp [overBaseProductObject, Category.assoc, f.over]

@[simp] theorem overBaseProductMap_id
    (X Y : Geometry.SmSchemeOver k) :
    overBaseProductMap (𝟙 X) (𝟙 Y) =
      𝟙 (overBaseProductObject X Y) := by
  apply SmOverHom.ext
  apply pullback.hom_ext
  · convert Category.id_comp (pullback.fst X.structMap Y.structMap) <;>
      simp [overBaseProductMap]
  · convert Category.id_comp (pullback.snd X.structMap Y.structMap) <;>
      simp [overBaseProductMap]

@[simp] theorem overBaseProductMap_comp
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Geometry.SmSchemeOver k}
    (f₁₂ : SmOverHom X₁ X₂) (f₂₃ : SmOverHom X₂ X₃)
    (g₁₂ : SmOverHom Y₁ Y₂) (g₂₃ : SmOverHom Y₂ Y₃) :
    overBaseProductMap (SmOverHom.comp f₁₂ f₂₃) (SmOverHom.comp g₁₂ g₂₃) =
      SmOverHom.comp (overBaseProductMap f₁₂ g₁₂) (overBaseProductMap f₂₃ g₂₃) := by
  apply SmOverHom.ext
  apply pullback.hom_ext <;>
    simp [overBaseProductMap, SmOverHom.comp, Category.assoc, Category.comp_id, Category.id_comp]

/-- Left unitor for the fiber product over `Spec k`. -/
noncomputable def overBaseProductLeftUnitor
    (X : Geometry.SmSchemeOver k) :
    overBaseProductObject (overBaseUnitObject (k := k)) X ≅ X where
  hom := overBaseProductSnd (overBaseUnitObject (k := k)) X
  inv :=
    { hom :=
        pullback.lift X.structMap (𝟙 X.scheme) (by simp [overBaseUnitObject])
      over := by
        simp [overBaseProductObject, overBaseUnitObject, Category.assoc] }
  hom_inv_id := by
    apply SmOverHom.ext
    change overBaseProduct.snd (overBaseUnitObject (k := k)) X ≫
        pullback.lift X.structMap (𝟙 X.scheme) _ =
      𝟙 (overBaseProductObject (overBaseUnitObject (k := k)) X).scheme
    apply pullback.hom_ext
    · simpa [overBaseProductSnd, overBaseProductObject, overBaseUnitObject, Category.assoc]
        using (pullback.condition
          (f := (𝟙 (Spec (CommRingCat.of k))))
          (g := X.structMap)).symm
    · simp [overBaseProductSnd, overBaseProductObject, overBaseUnitObject, Category.assoc]
  inv_hom_id := by
    apply SmOverHom.ext
    change pullback.lift X.structMap (𝟙 X.scheme) _ ≫
        overBaseProduct.snd (overBaseUnitObject (k := k)) X =
      𝟙 X.scheme
    simp [overBaseProductSnd]

/-- Right unitor for the fiber product over `Spec k`. -/
noncomputable def overBaseProductRightUnitor
    (X : Geometry.SmSchemeOver k) :
    overBaseProductObject X (overBaseUnitObject (k := k)) ≅ X where
  hom := overBaseProductFst X (overBaseUnitObject (k := k))
  inv :=
    { hom :=
        pullback.lift (𝟙 X.scheme) X.structMap (by simp [overBaseUnitObject])
      over := by
        simp [overBaseProductObject, overBaseUnitObject, Category.assoc] }
  hom_inv_id := by
    apply SmOverHom.ext
    change overBaseProduct.fst X (overBaseUnitObject (k := k)) ≫
        pullback.lift (𝟙 X.scheme) X.structMap _ =
      𝟙 (overBaseProductObject X (overBaseUnitObject (k := k))).scheme
    apply pullback.hom_ext
    · simpa [overBaseProductFst, overBaseProductObject, overBaseUnitObject, Category.assoc]
        using (pullback.condition
          (f := X.structMap)
          (g := (𝟙 (Spec (CommRingCat.of k)))))
    · simpa [overBaseProductFst, overBaseProductObject, overBaseUnitObject, Category.assoc]
        using (pullback.condition
          (f := X.structMap)
          (g := (𝟙 (Spec (CommRingCat.of k)))))
  inv_hom_id := by
    apply SmOverHom.ext
    change pullback.lift (𝟙 X.scheme) X.structMap _ ≫
        overBaseProduct.fst X (overBaseUnitObject (k := k)) =
      𝟙 X.scheme
    simp [overBaseProductFst]

@[simp, reassoc] theorem overBaseProductLeftUnitor_hom
    (X : Geometry.SmSchemeOver k) :
    (overBaseProductLeftUnitor (k := k) X).hom.hom =
      overBaseProduct.snd (overBaseUnitObject (k := k)) X := by
  rfl

@[simp, reassoc] theorem overBaseProductLeftUnitor_inv_fst
    (X : Geometry.SmSchemeOver k) :
    (overBaseProductLeftUnitor (k := k) X).inv.hom ≫
        overBaseProduct.fst (overBaseUnitObject (k := k)) X =
      X.structMap := by
  simp [overBaseProductLeftUnitor, overBaseUnitObject]

@[simp, reassoc] theorem overBaseProductLeftUnitor_inv_snd
    (X : Geometry.SmSchemeOver k) :
    (overBaseProductLeftUnitor (k := k) X).inv.hom ≫
        overBaseProduct.snd (overBaseUnitObject (k := k)) X =
      𝟙 X.scheme := by
  simp [overBaseProductLeftUnitor, overBaseUnitObject]

@[simp, reassoc] theorem overBaseProductRightUnitor_hom
    (X : Geometry.SmSchemeOver k) :
    (overBaseProductRightUnitor (k := k) X).hom.hom =
      overBaseProduct.fst X (overBaseUnitObject (k := k)) := by
  rfl

@[simp, reassoc] theorem overBaseProductRightUnitor_inv_fst
    (X : Geometry.SmSchemeOver k) :
    (overBaseProductRightUnitor (k := k) X).inv.hom ≫
        overBaseProduct.fst X (overBaseUnitObject (k := k)) =
      𝟙 X.scheme := by
  simp [overBaseProductRightUnitor, overBaseUnitObject]

@[simp, reassoc] theorem overBaseProductRightUnitor_inv_snd
    (X : Geometry.SmSchemeOver k) :
    (overBaseProductRightUnitor (k := k) X).inv.hom ≫
        overBaseProduct.snd X (overBaseUnitObject (k := k)) =
      X.structMap := by
  simp [overBaseProductRightUnitor, overBaseUnitObject]

/-- Associativity isomorphism for iterated fiber products over `Spec k`,
written at the level of `Sm/k` objects. -/
noncomputable def overBaseProductAssoc
    (X Y Z : Geometry.SmSchemeOver k) :
    overBaseProductObject (overBaseProductObject X Y) Z ≅
      overBaseProductObject X (overBaseProductObject Y Z) := by
  refine
    { hom :=
        { hom :=
            pullback.lift
              (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.fst X Y)
              (pullback.lift
                (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.snd X Y)
                (overBaseProduct.snd (overBaseProductObject X Y) Z)
                (by
                  calc
                    (overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                          overBaseProduct.snd X Y) ≫ Y.structMap =
                        overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                          (overBaseProduct.snd X Y ≫ Y.structMap) := by
                          simp [Category.assoc]
                    _ = overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                          (overBaseProduct.fst X Y ≫ X.structMap) := by
                          rw [(pullback.condition (f := X.structMap) (g := Y.structMap)).symm]
                    _ = overBaseProduct.snd (overBaseProductObject X Y) Z ≫ Z.structMap := by
                          simpa [overBaseProductObject, Category.assoc] using
                            (pullback.condition
                              (f := (overBaseProductObject X Y).structMap)
                              (g := Z.structMap))))
              (by
                calc
                  (overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                        overBaseProduct.fst X Y) ≫ X.structMap =
                      overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                        (overBaseProduct.fst X Y ≫ X.structMap) := by
                        simp [Category.assoc]
                  _ = overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                        (overBaseProduct.snd X Y ≫ Y.structMap) := by
                        rw [pullback.condition (f := X.structMap) (g := Y.structMap)]
                  _ =
                      pullback.lift
                        (overBaseProduct.fst (overBaseProductObject X Y) Z ≫
                          overBaseProduct.snd X Y)
                        (overBaseProduct.snd (overBaseProductObject X Y) Z)
                        _ ≫ (overBaseProductObject Y Z).structMap := by
                        simp [overBaseProductObject, Category.assoc])
          over := by
            simp [overBaseProductObject, Category.assoc] }
      inv :=
        { hom :=
            pullback.lift
              (pullback.lift
                (overBaseProduct.fst X (overBaseProductObject Y Z))
                (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.fst Y Z)
                (by
                  calc
                    overBaseProduct.fst X (overBaseProductObject Y Z) ≫ X.structMap =
                        overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                          (overBaseProductObject Y Z).structMap := by
                          exact pullback.condition
                    _ = (overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                            overBaseProduct.fst Y Z) ≫ Y.structMap := by
                          simp [overBaseProductObject, Category.assoc]))
              (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.snd Y Z)
              (by
                calc
                  pullback.lift
                        (overBaseProduct.fst X (overBaseProductObject Y Z))
                        (overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                          overBaseProduct.fst Y Z)
                        _ ≫ (overBaseProductObject X Y).structMap =
                      overBaseProduct.fst X (overBaseProductObject Y Z) ≫ X.structMap := by
                        simp [overBaseProductObject, Category.assoc]
                  _ = overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                        (overBaseProductObject Y Z).structMap := by
                        exact pullback.condition
                  _ = overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                        (overBaseProduct.snd Y Z ≫ Z.structMap) := by
                        simp [overBaseProductObject, Category.assoc,
                          pullback.condition (f := Y.structMap) (g := Z.structMap)]
                  _ = (overBaseProduct.snd X (overBaseProductObject Y Z) ≫
                        overBaseProduct.snd Y Z) ≫ Z.structMap := by
                        simp [Category.assoc])
          over := by
            simp [overBaseProductObject, Category.assoc] }
      hom_inv_id := by
        apply SmOverHom.ext
        change (pullback.lift
            (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.fst X Y)
            (pullback.lift
              (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.snd X Y)
              (overBaseProduct.snd (overBaseProductObject X Y) Z) _)
            _ ≫
          pullback.lift
            (pullback.lift
              (overBaseProduct.fst X (overBaseProductObject Y Z))
              (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.fst Y Z) _)
            (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.snd Y Z) _) =
          𝟙 (overBaseProductObject (overBaseProductObject X Y) Z).scheme
        apply pullback.hom_ext
        · apply pullback.hom_ext <;>
            simp [overBaseProduct, overBaseProduct.fst, overBaseProduct.snd,
              overBaseProductObject, Category.assoc,
              Category.id_comp, Category.comp_id]
        · simp [overBaseProduct, overBaseProduct.fst, overBaseProduct.snd,
            overBaseProductObject, Category.assoc,
            Category.id_comp, Category.comp_id]
      inv_hom_id := by
        apply SmOverHom.ext
        change (pullback.lift
            (pullback.lift
              (overBaseProduct.fst X (overBaseProductObject Y Z))
              (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.fst Y Z) _)
            (overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.snd Y Z) _ ≫
          pullback.lift
            (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.fst X Y)
            (pullback.lift
              (overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.snd X Y)
              (overBaseProduct.snd (overBaseProductObject X Y) Z) _)
            _) =
          𝟙 (overBaseProductObject X (overBaseProductObject Y Z)).scheme
        apply pullback.hom_ext
        · simp [overBaseProduct, overBaseProduct.fst, overBaseProduct.snd,
            overBaseProductObject, Category.assoc,
            Category.id_comp, Category.comp_id]
        · apply pullback.hom_ext <;>
            simp [overBaseProduct, overBaseProduct.fst, overBaseProduct.snd,
              overBaseProductObject, Category.assoc,
              Category.id_comp, Category.comp_id] }

/-- Symmetry isomorphism for the fiber product over `Spec k`,
written at the level of `Sm/k` objects. -/
noncomputable def overBaseProductSymm
    (X Y : Geometry.SmSchemeOver k) :
    overBaseProductObject X Y ≅ overBaseProductObject Y X := by
  let e := pullbackSymmetry X.structMap Y.structMap
  refine
    { hom :=
        { hom := e.hom
          over := by
            simpa [e, overBaseProductObject, Category.assoc] using
              (pullback.condition (f := X.structMap) (g := Y.structMap)).symm }
      inv :=
        { hom := e.inv
          over := by
            simpa [e, overBaseProductObject, Category.assoc] using
              (pullback.condition (f := Y.structMap) (g := X.structMap)).symm }
      hom_inv_id := by
        apply SmOverHom.ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply SmOverHom.ext
        exact e.inv_hom_id }

@[simp, reassoc] theorem overBaseProductAssoc_hom_fst
    (X Y Z : Geometry.SmSchemeOver k) :
    (overBaseProductAssoc X Y Z).hom.hom ≫ overBaseProduct.fst X (overBaseProductObject Y Z) =
      overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.fst X Y := by
  simp [overBaseProductAssoc, overBaseProductObject, Category.assoc]

@[simp, reassoc] theorem overBaseProductAssoc_hom_snd_fst
    (X Y Z : Geometry.SmSchemeOver k) :
    (overBaseProductAssoc X Y Z).hom.hom ≫ overBaseProduct.snd X (overBaseProductObject Y Z) ≫
        overBaseProduct.fst Y Z =
      overBaseProduct.fst (overBaseProductObject X Y) Z ≫ overBaseProduct.snd X Y := by
  simp [overBaseProductAssoc, overBaseProductObject, Category.assoc]

@[simp, reassoc] theorem overBaseProductAssoc_hom_snd_snd
    (X Y Z : Geometry.SmSchemeOver k) :
    (overBaseProductAssoc X Y Z).hom.hom ≫ overBaseProduct.snd X (overBaseProductObject Y Z) ≫
        overBaseProduct.snd Y Z =
      overBaseProduct.snd (overBaseProductObject X Y) Z := by
  simp [overBaseProductAssoc, overBaseProductObject, Category.assoc]

@[simp, reassoc] theorem overBaseProductAssoc_inv_fst_fst
    (X Y Z : Geometry.SmSchemeOver k) :
    (overBaseProductAssoc X Y Z).inv.hom ≫ overBaseProduct.fst (overBaseProductObject X Y) Z ≫
        overBaseProduct.fst X Y =
      overBaseProduct.fst X (overBaseProductObject Y Z) := by
  simp [overBaseProductAssoc, overBaseProductObject, Category.assoc]

@[simp, reassoc] theorem overBaseProductAssoc_inv_fst_snd
    (X Y Z : Geometry.SmSchemeOver k) :
    (overBaseProductAssoc X Y Z).inv.hom ≫ overBaseProduct.fst (overBaseProductObject X Y) Z ≫
        overBaseProduct.snd X Y =
      overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.fst Y Z := by
  simp [overBaseProductAssoc, overBaseProductObject, Category.assoc]

@[simp, reassoc] theorem overBaseProductAssoc_inv_snd
    (X Y Z : Geometry.SmSchemeOver k) :
    (overBaseProductAssoc X Y Z).inv.hom ≫ overBaseProduct.snd (overBaseProductObject X Y) Z =
      overBaseProduct.snd X (overBaseProductObject Y Z) ≫ overBaseProduct.snd Y Z := by
  simp [overBaseProductAssoc, overBaseProductObject, Category.assoc]

@[simp, reassoc] theorem overBaseProductSymm_hom_fst
    (X Y : Geometry.SmSchemeOver k) :
    (overBaseProductSymm X Y).hom.hom ≫ overBaseProduct.fst Y X =
      overBaseProduct.snd X Y := by
  simp [overBaseProductSymm, overBaseProductObject, Category.assoc]

@[simp, reassoc] theorem overBaseProductSymm_hom_snd
    (X Y : Geometry.SmSchemeOver k) :
    (overBaseProductSymm X Y).hom.hom ≫ overBaseProduct.snd Y X =
      overBaseProduct.fst X Y := by
  simp [overBaseProductSymm, overBaseProductObject, Category.assoc]

/-- An integral open-and-closed source subscheme of `X`. -/
structure IntegralClopenSourceSubscheme (X : Geometry.SmSchemeOver k) where
  carrier : Geometry.SmSchemeOver k
  immersion : carrier.scheme ⟶ X.scheme
  overBase : immersion ≫ X.structMap = carrier.structMap
  isOpenImmersion : IsOpenImmersion immersion
  isClosedImmersion : IsClosedImmersion immersion
  isIntegral : IsIntegral carrier.scheme

namespace IntegralClopenSourceSubscheme

abbrev toAmbient {X : Geometry.SmSchemeOver k}
    (sourceSubscheme : IntegralClopenSourceSubscheme X) :
    sourceSubscheme.carrier.scheme ⟶ X.scheme :=
  sourceSubscheme.immersion

/-- Package an open-and-closed smooth subscheme as an
`IntegralClopenSourceSubscheme`. -/
def ofOpen (X : Geometry.SmSchemeOver k) (U : X.scheme.Opens)
    [IsClosedImmersion U.ι] (hIntegral : IsIntegral U.toScheme) :
    IntegralClopenSourceSubscheme X where
  carrier := Geometry.SmSchemeOver.ofOpen X U
  immersion := U.ι
  overBase := rfl
  isOpenImmersion := inferInstance
  isClosedImmersion := inferInstance
  isIntegral := hIntegral

/-- Package a clopen integral smooth subscheme as an
`IntegralClopenSourceSubscheme`. -/
def ofClopen (X : Geometry.SmSchemeOver k) (U : X.scheme.Opens)
    (hU : IsClosed (U : Set X.scheme)) (hIntegral : IsIntegral U.toScheme) :
    IntegralClopenSourceSubscheme X := by
  letI : IsClosedImmersion U.ι := Geometry.SmSchemeOver.isClosedImmersion_ι_of_isClosed X U hU
  exact ofOpen X U hIntegral

end IntegralClopenSourceSubscheme

/-- A final-form source irreducible component of `X`.
This extends the integral clopen source subscheme layer with a genuine
componenthood field on the underlying topological space: the image must be an
irreducible component of `X.scheme`. -/
structure SourceIrreducibleComponent (X : Geometry.SmSchemeOver k)
    extends IntegralClopenSourceSubscheme X where
  range_mem_irreducibleComponents :
    Set.range immersion.base ∈ irreducibleComponents X.scheme

namespace SourceIrreducibleComponent

@[ext] theorem ext
    {X : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X)
    (hBase : C.toIntegralClopenSourceSubscheme = D.toIntegralClopenSourceSubscheme) :
    C = D := by
  cases C
  cases D
  cases hBase
  rfl

theorem extensionality
    {X : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X)
    (hBase : C.toIntegralClopenSourceSubscheme = D.toIntegralClopenSourceSubscheme) :
    C = D :=
  ext C D hBase

abbrev toAmbient {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    component.carrier.scheme ⟶ X.scheme :=
  component.immersion

theorem range_eq_of_subset_range
    {X : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X)
    (hCD : Set.range C.toAmbient.base ⊆ Set.range D.toAmbient.base) :
    Set.range C.toAmbient.base = Set.range D.toAmbient.base := by
  exact Set.Subset.antisymm hCD <|
    by
      exact C.range_mem_irreducibleComponents.2
        D.range_mem_irreducibleComponents.1 hCD

/-- Package an open-and-closed integral subscheme whose image is a topological
irreducible component as a `SourceIrreducibleComponent`. -/
def ofOpen (X : Geometry.SmSchemeOver k) (U : X.scheme.Opens)
    [IsClosedImmersion U.ι] (hIntegral : IsIntegral U.toScheme)
    (hComponent : (U : Set X.scheme) ∈ irreducibleComponents X.scheme) :
    SourceIrreducibleComponent X where
  toIntegralClopenSourceSubscheme :=
    IntegralClopenSourceSubscheme.ofOpen X U hIntegral
  range_mem_irreducibleComponents := by
    convert hComponent using 1
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩

/-- Package a clopen integral smooth subscheme whose underlying set is an
irreducible component as a `SourceIrreducibleComponent`. -/
def ofClopen (X : Geometry.SmSchemeOver k) (U : X.scheme.Opens)
    (hU : IsClosed (U : Set X.scheme)) (hIntegral : IsIntegral U.toScheme)
    (hComponent : (U : Set X.scheme) ∈ irreducibleComponents X.scheme) :
    SourceIrreducibleComponent X := by
  letI : IsClosedImmersion U.ι := Geometry.SmSchemeOver.isClosedImmersion_ι_of_isClosed X U hU
  exact ofOpen X U hIntegral hComponent

/-- Package one topological irreducible component of a smooth scheme as a
source component, once that topological component has been identified as open,
closed, and integral as an open subscheme. -/
def ofTopologicalComponent (X : Geometry.SmSchemeOver k)
    (C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme })
    (hOpen : IsOpen C.1) (hClosed : IsClosed C.1)
    (hIntegral : IsIntegral (Scheme.Opens.toScheme (⟨C.1, hOpen⟩ : X.scheme.Opens))) :
    SourceIrreducibleComponent X :=
  ofClopen X (⟨C.1, hOpen⟩ : X.scheme.Opens) hClosed hIntegral C.2

@[simp] theorem range_ofTopologicalComponent
    (X : Geometry.SmSchemeOver k)
    (C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme })
    (hOpen : IsOpen C.1) (hClosed : IsClosed C.1)
    (hIntegral : IsIntegral (Scheme.Opens.toScheme (⟨C.1, hOpen⟩ : X.scheme.Opens))) :
    Set.range (ofTopologicalComponent X C hOpen hClosed hIntegral).toAmbient.base = C.1 := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact u.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem toAmbient_overBase {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    component.toAmbient ≫ X.structMap = component.carrier.structMap :=
  component.overBase

structure IsoOverAmbient {X : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X) where
  iso : C.carrier.scheme ≅ D.carrier.scheme
  hom_toAmbient : iso.hom ≫ D.toAmbient = C.toAmbient

noncomputable def isoOverAmbient_of_range_eq
    {X : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X)
    (hCD : Set.range C.toAmbient.base = Set.range D.toAmbient.base) :
    IsoOverAmbient C D where
  iso := by
    letI : IsOpenImmersion C.toAmbient := C.isOpenImmersion
    letI : IsOpenImmersion D.toAmbient := D.isOpenImmersion
    exact IsOpenImmersion.isoOfRangeEq C.toAmbient D.toAmbient hCD
  hom_toAmbient := by
    letI : IsOpenImmersion C.toAmbient := C.isOpenImmersion
    letI : IsOpenImmersion D.toAmbient := D.isOpenImmersion
    simpa using IsOpenImmersion.isoOfRangeEq_hom_fac C.toAmbient D.toAmbient hCD

noncomputable def isoOverAmbient_of_subset_range
    {X : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X)
    (hCD : Set.range C.toAmbient.base ⊆ Set.range D.toAmbient.base) :
    IsoOverAmbient C D :=
  isoOverAmbient_of_range_eq C D (range_eq_of_subset_range C D hCD)

namespace IsoOverAmbient

def refl {X : Geometry.SmSchemeOver k}
    (C : SourceIrreducibleComponent X) : IsoOverAmbient C C where
  iso := Iso.refl _
  hom_toAmbient := by simp

def symm {X : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X} (h : IsoOverAmbient C D) :
    IsoOverAmbient D C where
  iso := h.iso.symm
  hom_toAmbient := by
    calc
      h.iso.inv ≫ C.toAmbient = h.iso.inv ≫ (h.iso.hom ≫ D.toAmbient) := by
        rw [h.hom_toAmbient]
      _ = D.toAmbient := by simp [Category.assoc]

def trans {X : Geometry.SmSchemeOver k}
    {C D E : SourceIrreducibleComponent X}
    (hCD : IsoOverAmbient C D) (hDE : IsoOverAmbient D E) :
    IsoOverAmbient C E where
  iso := hCD.iso ≪≫ hDE.iso
  hom_toAmbient := by
    calc
      (hCD.iso ≪≫ hDE.iso).hom ≫ E.toAmbient = hCD.iso.hom ≫ (hDE.iso.hom ≫ E.toAmbient) := by
        simp [Category.assoc]
      _ = hCD.iso.hom ≫ D.toAmbient := by rw [hDE.hom_toAmbient]
      _ = C.toAmbient := by rw [hCD.hom_toAmbient]

theorem hom_structMap {X : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X} (h : IsoOverAmbient C D) :
    h.iso.hom ≫ D.carrier.structMap = C.carrier.structMap := by
  calc
    h.iso.hom ≫ D.carrier.structMap = h.iso.hom ≫ (D.toAmbient ≫ X.structMap) := by
      rw [D.toAmbient_overBase]
    _ = (h.iso.hom ≫ D.toAmbient) ≫ X.structMap := by simp [Category.assoc]
    _ = C.toAmbient ≫ X.structMap := by rw [h.hom_toAmbient]
    _ = C.carrier.structMap := C.toAmbient_overBase

noncomputable def overBaseProductIso {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X} (h : IsoOverAmbient C D) :
    pullback C.carrier.structMap Y.structMap ≅ pullback D.carrier.structMap Y.structMap := by
  refine asIso <|
    pullback.map C.carrier.structMap Y.structMap D.carrier.structMap Y.structMap
      h.iso.hom (𝟙 Y.scheme) (𝟙 (Spec (CommRingCat.of k))) ?_ ?_
  · simpa using h.hom_structMap.symm
  · simp

@[simp] theorem overBaseProductIso_hom_fst {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k} {C D : SourceIrreducibleComponent X}
    (h : IsoOverAmbient C D) :
    (h.overBaseProductIso (Y := Y)).hom ≫ pullback.fst D.carrier.structMap Y.structMap =
      pullback.fst C.carrier.structMap Y.structMap ≫ h.iso.hom := by
  simp [IsoOverAmbient.overBaseProductIso, Category.assoc]

@[simp] theorem overBaseProductIso_hom_snd {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k} {C D : SourceIrreducibleComponent X}
    (h : IsoOverAmbient C D) :
    (h.overBaseProductIso (Y := Y)).hom ≫ pullback.snd D.carrier.structMap Y.structMap =
      pullback.snd C.carrier.structMap Y.structMap := by
  simp [IsoOverAmbient.overBaseProductIso, Category.assoc]

/-- Explicit compatibility between represented source components and the
induced fiber products with a target. -/
structure CompatibleOverBaseProductIso {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k}
    (C D : SourceIrreducibleComponent X) where
  sourceIso : IsoOverAmbient C D
  iso : overBaseProduct C.carrier Y ≅ overBaseProduct D.carrier Y
  hom_fst :
    iso.hom ≫ overBaseProduct.fst D.carrier Y =
      overBaseProduct.fst C.carrier Y ≫ sourceIso.iso.hom
  hom_snd :
    iso.hom ≫ overBaseProduct.snd D.carrier Y =
      overBaseProduct.snd C.carrier Y

namespace CompatibleOverBaseProductIso

/-- Reflexive compatibility of source components and their fiber products. -/
def refl {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    (C : SourceIrreducibleComponent X) : CompatibleOverBaseProductIso (Y := Y) C C where
  sourceIso := IsoOverAmbient.refl C
  iso := Iso.refl _
  hom_fst := by simp [IsoOverAmbient.refl, Category.assoc]
  hom_snd := by simp

/-- Symmetry of compatibility of source components and their fiber products. -/
def symm {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X}
    (h : CompatibleOverBaseProductIso (Y := Y) C D) :
    CompatibleOverBaseProductIso (Y := Y) D C where
  sourceIso := h.sourceIso.symm
  iso := h.iso.symm
  hom_fst := by
    have hleft :
        h.iso.inv ≫ overBaseProduct.fst C.carrier Y ≫ h.sourceIso.iso.hom =
          overBaseProduct.fst D.carrier Y := by
      simpa [Category.assoc] using
        (congrArg (fun f => h.iso.inv ≫ f) h.hom_fst).symm
    have hright :
        h.iso.inv ≫ overBaseProduct.fst C.carrier Y =
          overBaseProduct.fst D.carrier Y ≫ h.sourceIso.iso.inv := by
      simpa [Category.assoc] using
        congrArg (fun f => f ≫ h.sourceIso.iso.inv) hleft
    simpa [Category.assoc] using hright
  hom_snd := by
    simpa [Category.assoc] using
      (congrArg (fun f => h.iso.inv ≫ f) h.hom_snd).symm

/-- Transitivity of compatibility of source components and their fiber products. -/
def trans {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D E : SourceIrreducibleComponent X}
    (hCD : CompatibleOverBaseProductIso (Y := Y) C D)
    (hDE : CompatibleOverBaseProductIso (Y := Y) D E) :
    CompatibleOverBaseProductIso (Y := Y) C E where
  sourceIso := hCD.sourceIso.trans hDE.sourceIso
  iso := hCD.iso ≪≫ hDE.iso
  hom_fst := by
    calc
      (hCD.iso ≪≫ hDE.iso).hom ≫ overBaseProduct.fst E.carrier Y
          = hCD.iso.hom ≫ (hDE.iso.hom ≫ overBaseProduct.fst E.carrier Y) := by
            simp [Category.assoc]
      _ = hCD.iso.hom ≫
          (overBaseProduct.fst D.carrier Y ≫ hDE.sourceIso.iso.hom) := by
            rw [hDE.hom_fst]
      _ = (hCD.iso.hom ≫ overBaseProduct.fst D.carrier Y) ≫ hDE.sourceIso.iso.hom := by
            simp [Category.assoc]
      _ = (overBaseProduct.fst C.carrier Y ≫ hCD.sourceIso.iso.hom) ≫
          hDE.sourceIso.iso.hom := by
            rw [hCD.hom_fst]
      _ = overBaseProduct.fst C.carrier Y ≫
          (hCD.sourceIso.iso ≪≫ hDE.sourceIso.iso).hom := by
            simp [Category.assoc]
  hom_snd := by
    calc
      (hCD.iso ≪≫ hDE.iso).hom ≫ overBaseProduct.snd E.carrier Y
          = hCD.iso.hom ≫ (hDE.iso.hom ≫ overBaseProduct.snd E.carrier Y) := by
            simp [Category.assoc]
      _ = hCD.iso.hom ≫ overBaseProduct.snd D.carrier Y := by rw [hDE.hom_snd]
      _ = overBaseProduct.snd C.carrier Y := by rw [hCD.hom_snd]

/-- The canonical fiber-product compatibility induced by a source-component
isomorphism over the ambient source. -/
def ofIsoOverAmbient {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceIrreducibleComponent X} (h : IsoOverAmbient C D) :
    CompatibleOverBaseProductIso (Y := Y) C D where
  sourceIso := h
  iso := h.overBaseProductIso (Y := Y)
  hom_fst := by simpa using h.overBaseProductIso_hom_fst (Y := Y)
  hom_snd := by simpa using h.overBaseProductIso_hom_snd (Y := Y)

end CompatibleOverBaseProductIso

end IsoOverAmbient

end SourceIrreducibleComponent

/-- Product of two integral clopen source subschemes over `Spec k`. -/
def productIntegralClopenSourceSubscheme
    {X Y : Geometry.SmSchemeOver k}
    (C : IntegralClopenSourceSubscheme X)
    (D : IntegralClopenSourceSubscheme Y)
    (hIntegral : IsIntegral (overBaseProduct C.carrier D.carrier)) :
    IntegralClopenSourceSubscheme (overBaseProductObject X Y) where
  carrier := overBaseProductObject C.carrier D.carrier
  immersion :=
    (overBaseProductMap
      { hom := C.toAmbient
        over := C.overBase }
      { hom := D.toAmbient
        over := D.overBase }).hom
  overBase := by
    simp [overBaseProductObject, overBaseProductMap, Category.assoc, C.overBase]
  isOpenImmersion := by
    letI : MorphismProperty.IsStableUnderBaseChange @IsOpenImmersion :=
      AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange
    letI : MorphismProperty.IsStableUnderComposition @IsOpenImmersion := inferInstance
    dsimp [overBaseProductMap]
    exact MorphismProperty.pullback_map
      (P := @IsOpenImmersion)
      C.isOpenImmersion D.isOpenImmersion C.overBase.symm D.overBase.symm
  isClosedImmersion := by
    letI : MorphismProperty.IsStableUnderBaseChange @IsClosedImmersion :=
      IsClosedImmersion.isStableUnderBaseChange
    letI : MorphismProperty.IsStableUnderComposition @IsClosedImmersion := inferInstance
    dsimp [overBaseProductMap]
    exact MorphismProperty.pullback_map
      (P := @IsClosedImmersion)
      C.isClosedImmersion D.isClosedImmersion C.overBase.symm D.overBase.symm
  isIntegral := hIntegral

@[simp] theorem productIntegralClopenSourceSubscheme_toAmbient
    {X Y : Geometry.SmSchemeOver k}
    (C : IntegralClopenSourceSubscheme X)
    (D : IntegralClopenSourceSubscheme Y)
    (hIntegral : IsIntegral (overBaseProduct C.carrier D.carrier)) :
    (productIntegralClopenSourceSubscheme C D hIntegral).toAmbient =
      (overBaseProductMap
        { hom := C.toAmbient
          over := C.overBase }
        { hom := D.toAmbient
          over := D.overBase }).hom := by
  rfl

@[simp, reassoc] theorem productIntegralClopenSourceSubscheme_fst
    {X Y : Geometry.SmSchemeOver k}
    (C : IntegralClopenSourceSubscheme X)
    (D : IntegralClopenSourceSubscheme Y)
    (hIntegral : IsIntegral (overBaseProduct C.carrier D.carrier)) :
    (productIntegralClopenSourceSubscheme C D hIntegral).toAmbient ≫
        overBaseProduct.fst X Y =
      overBaseProduct.fst C.carrier D.carrier ≫ C.toAmbient := by
  change
    (overBaseProductMap
      { hom := C.toAmbient
        over := C.overBase }
      { hom := D.toAmbient
        over := D.overBase }).hom ≫ overBaseProduct.fst X Y =
      overBaseProduct.fst C.carrier D.carrier ≫ C.toAmbient
  simp [overBaseProductMap, Category.assoc]

@[simp, reassoc] theorem productIntegralClopenSourceSubscheme_snd
    {X Y : Geometry.SmSchemeOver k}
    (C : IntegralClopenSourceSubscheme X)
    (D : IntegralClopenSourceSubscheme Y)
    (hIntegral : IsIntegral (overBaseProduct C.carrier D.carrier)) :
    (productIntegralClopenSourceSubscheme C D hIntegral).toAmbient ≫
        overBaseProduct.snd X Y =
      overBaseProduct.snd C.carrier D.carrier ≫ D.toAmbient := by
  simp [overBaseProductMap, Category.assoc]

/-- A restricted owner hypothesis asserting that a source irreducible component
remains integral after product with any source irreducible component. This is
the exact extra data needed for the current product-source-component route,
without asserting any false global product-integrality theorem. -/
structure ProductStableSourceComponent (X : Geometry.SmSchemeOver k) where
  component : SourceIrreducibleComponent X
  product_isIntegral :
    ∀ {Y : Geometry.SmSchemeOver k} (other : SourceIrreducibleComponent Y),
      IsIntegral (overBaseProduct component.carrier other.carrier)

theorem productStableSourceComponent_product
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    IsIntegral (overBaseProduct C.component.carrier D.carrier) :=
  C.product_isIntegral D

private theorem isIrreducibleComponent_of_clopen_irreducible
    {T : Type u} [TopologicalSpace T]
    {s : Set T}
    (hsClosed : IsClosed s)
    (hsOpen : IsOpen s)
    (hsIrred : IsIrreducible s) :
    s ∈ irreducibleComponents T := by
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨hsClosed, hsIrred⟩, ?_⟩
  intro t ht hst
  have hsNonempty : s.Nonempty := hsIrred.nonempty
  rcases hsNonempty with ⟨x, hx⟩
  have hxt : x ∈ t := hst hx
  have htSubsetClosure :
      t ⊆ closure (t ∩ s) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen
      ht.2.isPreirreducible hsOpen ⟨x, hxt, hx⟩
  have htsEq : t ∩ s = s := by
    ext y
    constructor
    · exact fun hy => hy.2
    · exact fun hy => ⟨hst hy, hy⟩
  have hclosure : closure (t ∩ s) = s := by
    rw [htsEq]
    exact hsClosed.closure_eq
  simpa [hclosure] using htSubsetClosure

/-- Product source component constructed from a product-stable source component
and an arbitrary source irreducible component in the second factor. -/
def productSourceIrreducibleComponent_of_geometricallyIntegral
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    SourceIrreducibleComponent (overBaseProductObject X Y) where
  toIntegralClopenSourceSubscheme :=
    productIntegralClopenSourceSubscheme
      C.component.toIntegralClopenSourceSubscheme
      D.toIntegralClopenSourceSubscheme
      (C.product_isIntegral D)
  range_mem_irreducibleComponents := by
    let S :=
      productIntegralClopenSourceSubscheme
        C.component.toIntegralClopenSourceSubscheme
        D.toIntegralClopenSourceSubscheme
        (C.product_isIntegral D)
    refine isIrreducibleComponent_of_clopen_irreducible ?_ ?_ ?_
    · letI : IsClosedImmersion S.immersion := S.isClosedImmersion
      simpa using (IsClosedImmersion.base_closed (f := S.immersion)).2
    · letI : IsOpenImmersion S.immersion := S.isOpenImmersion
      simpa using IsOpenImmersion.isOpen_range S.immersion
    · letI : IsIntegral S.carrier.scheme := S.isIntegral
      have hcarrier : IsIrreducible (Set.univ : Set S.carrier.scheme) :=
        (irreducibleSpace_def S.carrier.scheme.carrier).1
          (inferInstance : IrreducibleSpace S.carrier.scheme.carrier)
      simpa [Set.image_univ] using
        hcarrier.image S.immersion.base S.immersion.base.continuous.continuousOn

/-- Product source component constructed from a product-stable left factor. -/
abbrev productSourceIrreducibleComponent
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    SourceIrreducibleComponent (overBaseProductObject X Y) :=
  productSourceIrreducibleComponent_of_geometricallyIntegral C D

@[simp] theorem productSourceIrreducibleComponent_fst_image
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    (productSourceIrreducibleComponent C D).toAmbient ≫ overBaseProduct.fst X Y =
      overBaseProduct.fst C.component.carrier D.carrier ≫ C.component.toAmbient := by
  simpa [productSourceIrreducibleComponent,
    productSourceIrreducibleComponent_of_geometricallyIntegral]
    using productIntegralClopenSourceSubscheme_fst
      C.component.toIntegralClopenSourceSubscheme
      D.toIntegralClopenSourceSubscheme
      (C.product_isIntegral D)

@[simp] theorem productSourceIrreducibleComponent_snd_image
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    (productSourceIrreducibleComponent C D).toAmbient ≫ overBaseProduct.snd X Y =
      overBaseProduct.snd C.component.carrier D.carrier ≫ D.toAmbient := by
  simpa [productSourceIrreducibleComponent,
    productSourceIrreducibleComponent_of_geometricallyIntegral]
    using productIntegralClopenSourceSubscheme_snd
      C.component.toIntegralClopenSourceSubscheme
      D.toIntegralClopenSourceSubscheme
      (C.product_isIntegral D)

lemma productSourceIrreducibleComponent_toAmbient_fst_apply
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (w : (productSourceIrreducibleComponent C D).carrier.scheme.carrier) :
    C.component.toAmbient.base ((overBaseProduct.fst C.component.carrier D.carrier).base w) =
      (overBaseProduct.fst X Y).base
        ((productSourceIrreducibleComponent C D).toAmbient.base w) := by
  change
    (overBaseProduct.fst C.component.carrier D.carrier ≫ C.component.toAmbient).base w =
      ((productSourceIrreducibleComponent C D).toAmbient ≫ overBaseProduct.fst X Y).base w
  rw [productSourceIrreducibleComponent_fst_image]
  rfl

lemma productSourceIrreducibleComponent_toAmbient_snd_apply
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (w : (productSourceIrreducibleComponent C D).carrier.scheme.carrier) :
    D.toAmbient.base ((overBaseProduct.snd C.component.carrier D.carrier).base w) =
      (overBaseProduct.snd X Y).base
        ((productSourceIrreducibleComponent C D).toAmbient.base w) := by
  change
    (overBaseProduct.snd C.component.carrier D.carrier ≫ D.toAmbient).base w =
      ((productSourceIrreducibleComponent C D).toAmbient ≫ overBaseProduct.snd X Y).base w
  rw [productSourceIrreducibleComponent_snd_image]
  rfl

@[simp] theorem productSourceIrreducibleComponent_support_eq
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    (productSourceIrreducibleComponent C D).carrier =
      overBaseProductObject C.component.carrier D.carrier := by
  rfl

theorem productSourceIrreducibleComponent_proj_mem_of_mem_range
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    {x : (overBaseProductObject X Y).scheme.carrier}
    (hx : x ∈ Set.range (productSourceIrreducibleComponent C D).toAmbient.base) :
    (overBaseProduct.fst X Y).base x ∈ Set.range C.component.toAmbient.base ∧
      (overBaseProduct.snd X Y).base x ∈ Set.range D.toAmbient.base := by
  rcases hx with ⟨z, rfl⟩
  constructor
  · refine ⟨(overBaseProduct.fst C.component.carrier D.carrier).base z, ?_⟩
    simpa using productSourceIrreducibleComponent_toAmbient_fst_apply (C := C) (D := D) z
  · refine ⟨(overBaseProduct.snd C.component.carrier D.carrier).base z, ?_⟩
    simpa using productSourceIrreducibleComponent_toAmbient_snd_apply (C := C) (D := D) z

theorem productSourceIrreducibleComponent_mem_range_of_proj_mem
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    {x : (overBaseProductObject X Y).scheme.carrier}
    (hfst : (overBaseProduct.fst X Y).base x ∈ Set.range C.component.toAmbient.base)
    (hsnd : (overBaseProduct.snd X Y).base x ∈ Set.range D.toAmbient.base) :
    x ∈ Set.range (productSourceIrreducibleComponent C D).toAmbient.base := by
  have hRange :
      Set.range (productSourceIrreducibleComponent C D).toAmbient.base =
        (overBaseProduct.fst X Y).base ⁻¹' Set.range C.component.toAmbient.base ∩
          (overBaseProduct.snd X Y).base ⁻¹' Set.range D.toAmbient.base := by
    change
      Set.range
          (pullback.map C.component.carrier.structMap D.carrier.structMap
            X.structMap Y.structMap C.component.toAmbient D.toAmbient (𝟙 _)
            (by simpa [Category.assoc] using C.component.overBase.symm)
            (by simpa [Category.assoc] using D.overBase.symm)).base =
        (pullback.fst X.structMap Y.structMap).base ⁻¹'
            Set.range C.component.toAmbient.base ∩
          (pullback.snd X.structMap Y.structMap).base ⁻¹'
            Set.range D.toAmbient.base
    simpa [overBaseProduct, overBaseProductObject] using
      (AlgebraicGeometry.Scheme.Pullback.range_map
        C.component.carrier.structMap D.carrier.structMap
        X.structMap Y.structMap C.component.toAmbient D.toAmbient (𝟙 _)
        (by simpa [Category.assoc] using C.component.overBase.symm)
        (by simpa [Category.assoc] using D.overBase.symm))
  rw [hRange]
  exact ⟨hfst, hsnd⟩

theorem productSourceIrreducibleComponent_mem_range_iff
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    {x : (overBaseProductObject X Y).scheme.carrier} :
    x ∈ Set.range (productSourceIrreducibleComponent C D).toAmbient.base ↔
      (overBaseProduct.fst X Y).base x ∈ Set.range C.component.toAmbient.base ∧
        (overBaseProduct.snd X Y).base x ∈ Set.range D.toAmbient.base := by
  constructor
  · exact productSourceIrreducibleComponent_proj_mem_of_mem_range C D
  · intro hx
    exact productSourceIrreducibleComponent_mem_range_of_proj_mem C D hx.1 hx.2

private theorem exists_product_component_point
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (xC : C.component.carrier.scheme.carrier)
    (yD : D.carrier.scheme.carrier)
    (hbase : C.component.carrier.structMap.base xC =
      D.carrier.structMap.base yD) :
    ∃ z : (productSourceIrreducibleComponent C D).carrier.scheme.carrier,
      (overBaseProduct.fst C.component.carrier D.carrier).base z = xC ∧
      (overBaseProduct.snd C.component.carrier D.carrier).base z = yD := by
  rcases AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (f := C.component.carrier.structMap)
      (g := D.carrier.structMap) xC yD hbase with ⟨z, hzfst, hzsnd⟩
  exact ⟨z, hzfst, hzsnd⟩

theorem productSourceIrreducibleComponent_range_image_fst
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    Set.image (overBaseProduct.fst X Y).base
        (Set.range (productSourceIrreducibleComponent C D).toAmbient.base) =
      Set.range C.component.toAmbient.base := by
  ext x
  constructor
  · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
    refine ⟨(overBaseProduct.fst C.component.carrier D.carrier).base w, ?_⟩
    simpa using productSourceIrreducibleComponent_toAmbient_fst_apply (C := C) (D := D) w
  · intro hx
    rcases D.range_mem_irreducibleComponents.1.nonempty with ⟨y, hy⟩
    rcases hy with ⟨yD, hyD⟩
    rcases hx with ⟨xC, rfl⟩
    have hbase :
        C.component.carrier.structMap.base xC =
          D.carrier.structMap.base yD := by
      exact Subsingleton.elim _ _
    rcases exists_product_component_point C D xC yD hbase with ⟨z, hzfst, _⟩
    refine ⟨(productSourceIrreducibleComponent C D).toAmbient.base z, ?_, ?_⟩
    · exact ⟨z, rfl⟩
    · calc
        (overBaseProduct.fst X Y).base ((productSourceIrreducibleComponent C D).toAmbient.base z)
            = C.component.toAmbient.base
                ((overBaseProduct.fst C.component.carrier D.carrier).base z) := by
                  simpa using (productSourceIrreducibleComponent_toAmbient_fst_apply
                    (C := C) (D := D) z).symm
        _ = C.component.toAmbient.base xC := by simpa [hzfst]

theorem productSourceIrreducibleComponent_range_image_snd
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    Set.image (overBaseProduct.snd X Y).base
        (Set.range (productSourceIrreducibleComponent C D).toAmbient.base) =
      Set.range D.toAmbient.base := by
  ext y
  constructor
  · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
    refine ⟨(overBaseProduct.snd C.component.carrier D.carrier).base w, ?_⟩
    simpa using productSourceIrreducibleComponent_toAmbient_snd_apply (C := C) (D := D) w
  · intro hy
    rcases C.component.range_mem_irreducibleComponents.1.nonempty with ⟨x, hx⟩
    rcases hx with ⟨xC, hxC⟩
    rcases hy with ⟨yD, rfl⟩
    have hbase :
        C.component.carrier.structMap.base xC =
          D.carrier.structMap.base yD := by
      exact Subsingleton.elim _ _
    rcases exists_product_component_point C D xC yD hbase with ⟨z, _, hzsnd⟩
    refine ⟨(productSourceIrreducibleComponent C D).toAmbient.base z, ?_, ?_⟩
    · exact ⟨z, rfl⟩
    · calc
        (overBaseProduct.snd X Y).base ((productSourceIrreducibleComponent C D).toAmbient.base z)
            = D.toAmbient.base
                ((overBaseProduct.snd C.component.carrier D.carrier).base z) := by
                  simpa using (productSourceIrreducibleComponent_toAmbient_snd_apply
                    (C := C) (D := D) z).symm
        _ = D.toAmbient.base yD := by simpa [hzsnd]

private theorem subset_of_irreducible_inter_clopen_nonempty
    {T : Type u} [TopologicalSpace T]
    {s t : Set T}
    (hs : IsIrreducible s)
    (htOpen : IsOpen t)
    (htClosed : IsClosed t)
    (hst : (s ∩ t).Nonempty) :
    s ⊆ t := by
  have hsPre : IsPreirreducible s := hs.isPreirreducible
  have hsUnion : s ⊆ t ∪ tᶜ := by
    intro x hx
    by_cases hxt : x ∈ t
    · exact Set.mem_union_left _ hxt
    · exact Set.mem_union_right _ hxt
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hsPre)
      t tᶜ htClosed htOpen.isClosed_compl hsUnion with hsT | hsTc
  · exact hsT
  · exfalso
    rcases hst with ⟨x, hxS, hxT⟩
    exact hsTc hxS hxT

/-- A certified finite irreducible-component decomposition of `X`.
This is the first abstraction strong enough to state the component-sum identity
canonically enough for downstream use: the chosen finite family must represent
every source irreducible component up to isomorphism over `X`, and it must not
contain duplicate representatives up to that same equivalence. The record also
stores the honest topological content of the decomposition: the listed
component images cover `X`, and distinct listed components have disjoint
images. -/
structure FiniteIrreducibleComponentDecomposition (X : Geometry.SmSchemeOver k) where
  components : Finset (SourceIrreducibleComponent X)
  covers :
    ∀ x : X.scheme.carrier,
      ∃ component ∈ components, x ∈ Set.range component.toAmbient.base
  pairwise_disjoint :
    ∀ {C D : SourceIrreducibleComponent X},
      C ∈ components →
      D ∈ components →
      C ≠ D →
        Disjoint (Set.range C.toAmbient.base) (Set.range D.toAmbient.base)
  exhaustive :
    (component : SourceIrreducibleComponent X) →
      Σ listed : { listed : SourceIrreducibleComponent X // listed ∈ components },
        SourceIrreducibleComponent.IsoOverAmbient component listed.1
  no_equivalent_duplicates :
    ∀ {C D : SourceIrreducibleComponent X},
      C ∈ components →
      D ∈ components →
      SourceIrreducibleComponent.IsoOverAmbient C D →
        C = D

namespace FiniteIrreducibleComponentDecomposition

variable {X : Geometry.SmSchemeOver k}

/-- Choose the listed representative supplied by exhaustivity for any source
component. -/
def listedRepresentative (D : FiniteIrreducibleComponentDecomposition X)
    (component : SourceIrreducibleComponent X) :
    { listed : SourceIrreducibleComponent X // listed ∈ D.components } :=
  (D.exhaustive component).1

/-- The ambient-compatible isomorphism from a source component to its chosen
listed representative. -/
def listedRepresentativeIso (D : FiniteIrreducibleComponentDecomposition X)
    (component : SourceIrreducibleComponent X) :
    SourceIrreducibleComponent.IsoOverAmbient component (D.listedRepresentative component).1 :=
  (D.exhaustive component).2

@[simp] theorem listedRepresentative_mem
    (D : FiniteIrreducibleComponentDecomposition X)
    (component : SourceIrreducibleComponent X) :
    (D.listedRepresentative component).1 ∈ D.components :=
  (D.listedRepresentative component).2

theorem listedRepresentative_eq_of_iso
    (D : FiniteIrreducibleComponentDecomposition X)
    {component listed : SourceIrreducibleComponent X}
    (hlisted : listed ∈ D.components)
    (hiso : SourceIrreducibleComponent.IsoOverAmbient component listed) :
    (D.listedRepresentative component).1 = listed := by
  exact D.no_equivalent_duplicates
    (D.listedRepresentative_mem component) hlisted
    ((D.listedRepresentativeIso component).symm.trans hiso)

theorem listedRepresentative_eq_self_of_mem
    (D : FiniteIrreducibleComponentDecomposition X)
    {component : SourceIrreducibleComponent X}
    (hcomponent : component ∈ D.components) :
    (D.listedRepresentative component).1 = component :=
  D.listedRepresentative_eq_of_iso hcomponent
    (SourceIrreducibleComponent.IsoOverAmbient.refl component)

theorem disjoint_of_mem_ne
    (D : FiniteIrreducibleComponentDecomposition X)
    {C D' : SourceIrreducibleComponent X}
    (hC : C ∈ D.components) (hD' : D' ∈ D.components) (hneq : C ≠ D') :
    Disjoint (Set.range C.toAmbient.base) (Set.range D'.toAmbient.base) :=
  D.pairwise_disjoint hC hD' hneq

/-- Construct a finite source-component decomposition directly from the
topological irreducible components of `X`.  The hypotheses are exactly the
geometric content needed to turn those topological components into clopen
integral source subschemes; the finiteness, cover, disjointness, exhaustivity,
and uniqueness clauses are then consequences of irreducible-component
maximality. -/
noncomputable def ofTopologicalComponents
    (X : Geometry.SmSchemeOver k)
    (hFinite : (irreducibleComponents X.scheme).Finite)
    (hOpen :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsOpen C.1)
    (hClosed :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsClosed C.1)
    (hIntegral :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsIntegral (Scheme.Opens.toScheme (⟨C.1, hOpen C⟩ : X.scheme.Opens))) :
    FiniteIrreducibleComponentDecomposition X := by
  classical
  let Index := { C : Set X.scheme // C ∈ irreducibleComponents X.scheme }
  letI : Fintype Index := hFinite.fintype
  letI : DecidableEq Index := Classical.decEq Index
  let source : Index → SourceIrreducibleComponent X :=
    fun C => SourceIrreducibleComponent.ofTopologicalComponent
      X C (hOpen C) (hClosed C) (hIntegral C)
  let components : Finset (SourceIrreducibleComponent X) :=
    Finset.univ.image source
  have hsource_range :
      ∀ C : Index, Set.range (source C).toAmbient.base = C.1 := by
    intro C
    exact SourceIrreducibleComponent.range_ofTopologicalComponent
      X C (hOpen C) (hClosed C) (hIntegral C)
  refine
    { components := components
      covers := ?_
      pairwise_disjoint := ?_
      exhaustive := ?_
      no_equivalent_duplicates := ?_ }
  · intro x
    let C : Index :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    refine ⟨source C, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨C, Finset.mem_univ C, rfl⟩
    · rw [hsource_range C]
      exact mem_irreducibleComponent
  · intro C D hC hD hneq
    rw [Set.disjoint_left]
    intro x hxC hxD
    rcases Finset.mem_image.mp hC with ⟨Ctop, _hCtop, hCeq⟩
    rcases Finset.mem_image.mp hD with ⟨Dtop, _hDtop, hDeq⟩
    subst C
    subst D
    have hsubset :
        Ctop.1 ⊆ Dtop.1 := by
      apply subset_of_irreducible_inter_clopen_nonempty Ctop.2.1
      · exact hOpen Dtop
      · exact hClosed Dtop
      · refine ⟨x, ?_, ?_⟩
        · simpa [hsource_range Ctop] using hxC
        · simpa [hsource_range Dtop] using hxD
    have hsets_eq : Ctop.1 = Dtop.1 :=
      Set.Subset.antisymm hsubset (Ctop.2.2 Dtop.2.1 hsubset)
    have htops_eq : Ctop = Dtop := by
      exact Subtype.ext hsets_eq
    exact hneq (by simpa [htops_eq])
  · intro component
    let C : Index :=
      ⟨Set.range component.toAmbient.base, component.range_mem_irreducibleComponents⟩
    refine ⟨⟨source C, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨C, Finset.mem_univ C, rfl⟩
    · exact SourceIrreducibleComponent.isoOverAmbient_of_range_eq component (source C)
        (by
          simpa [hsource_range C])
  · intro C D hC hD hiso
    rcases Finset.mem_image.mp hC with ⟨Ctop, _hCtop, hCeq⟩
    rcases Finset.mem_image.mp hD with ⟨Dtop, _hDtop, hDeq⟩
    subst C
    subst D
    have hsubset :
        Ctop.1 ⊆ Dtop.1 := by
      intro x hx
      rw [← hsource_range Ctop] at hx
      rcases hx with ⟨z, rfl⟩
      rw [← hsource_range Dtop]
      exact ⟨hiso.iso.hom.base z,
        by
          change ((hiso.iso.hom ≫ (source Dtop).toAmbient).base z) =
            (source Ctop).toAmbient.base z
          simpa [SourceIrreducibleComponent.IsoOverAmbient.hom_toAmbient] using
            congrArg (fun f => f.base z) hiso.hom_toAmbient⟩
    have hsets_eq : Ctop.1 = Dtop.1 :=
      Set.Subset.antisymm hsubset (Ctop.2.2 Dtop.2.1 hsubset)
    have htops_eq : Ctop = Dtop := by
      exact Subtype.ext hsets_eq
    simpa [htops_eq]

end FiniteIrreducibleComponentDecomposition

lemma stableDX_component_eq
    {X : Geometry.SmSchemeOver k}
    {DX : FiniteIrreducibleComponentDecomposition X}
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (listedX : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) :
    (stableDX listedX).component = listedX.1 := by
  simpa using hstableDX listedX

lemma stableDX_component_range_eq
    {X : Geometry.SmSchemeOver k}
    {DX : FiniteIrreducibleComponentDecomposition X}
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (listedX : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) :
    Set.range (stableDX listedX).component.toAmbient.base =
      Set.range listedX.1.toAmbient.base := by
  rw [stableDX_component_eq stableDX hstableDX listedX]

lemma isoOverAmbient_hom_toAmbient_base_apply
    {X : Geometry.SmSchemeOver k}
    {P Q : SourceIrreducibleComponent X}
    (hiso : SourceIrreducibleComponent.IsoOverAmbient P Q)
    (z : P.carrier.scheme.carrier) :
    Q.toAmbient.base (hiso.iso.hom.base z) = P.toAmbient.base z := by
  change ((hiso.iso.hom ≫ Q.toAmbient).base z) = P.toAmbient.base z
  simpa [SourceIrreducibleComponent.IsoOverAmbient.hom_toAmbient] using
    congrArg (fun f => f.base z) hiso.hom_toAmbient

/- Exhaustivity of listed product source components: any source irreducible
component of the product ambient is isomorphic over the ambient product to one
of the listed products of the chosen factor decompositions. -/
noncomputable def productSourceIrreducibleComponent_exhaustive
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (component : SourceIrreducibleComponent (overBaseProductObject X Y)) :
    Σ listedX : { listed : SourceIrreducibleComponent X // listed ∈ DX.components },
      Σ listedY : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components },
        SourceIrreducibleComponent.IsoOverAmbient component
          (productSourceIrreducibleComponent (stableDX listedX) listedY.1) := by
  classical
  have h :
      Nonempty (Σ listedX : { listed : SourceIrreducibleComponent X // listed ∈ DX.components },
        Σ listedY : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components },
          SourceIrreducibleComponent.IsoOverAmbient component
            (productSourceIrreducibleComponent (stableDX listedX) listedY.1)) := by
    rcases component.range_mem_irreducibleComponents.1.nonempty with ⟨x, hxComponent⟩
    rcases DX.covers ((overBaseProduct.fst X Y).base x) with ⟨CX, hCXmem, hxCX⟩
    rcases DY.covers ((overBaseProduct.snd X Y).base x) with ⟨DY', hDYmem, hxDY⟩
    let listedX : { listed : SourceIrreducibleComponent X // listed ∈ DX.components } := ⟨CX, hCXmem⟩
    let listedY : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components } := ⟨DY', hDYmem⟩
    let productListed :
        SourceIrreducibleComponent (overBaseProductObject X Y) :=
      productSourceIrreducibleComponent (stableDX listedX) listedY.1
    have hxProduct :
        x ∈ Set.range productListed.toAmbient.base := by
      have hx :
          (overBaseProduct.fst X Y).base x ∈ Set.range (stableDX listedX).component.toAmbient.base ∧
            (overBaseProduct.snd X Y).base x ∈ Set.range listedY.1.toAmbient.base := by
        constructor
        · have hxCX' :
              (overBaseProduct.fst X Y).base x ∈ Set.range listedX.1.toAmbient.base := hxCX
          simpa only [← stableDX_component_range_eq stableDX hstableDX listedX] using hxCX'
        · simpa [listedY] using hxDY
      simpa [productListed] using
        (productSourceIrreducibleComponent_mem_range_iff
          (C := stableDX listedX) (D := listedY.1) (x := x)).2 hx
    have hsubset :
        Set.range component.toAmbient.base ⊆ Set.range productListed.toAmbient.base := by
      apply subset_of_irreducible_inter_clopen_nonempty
        component.range_mem_irreducibleComponents.1
      · simpa [productListed] using productListed.isOpenImmersion.isOpen_range
      · simpa [productListed] using
          (AlgebraicGeometry.IsClosedImmersion.iff_isPreimmersion.mp
            productListed.isClosedImmersion).2
      · exact ⟨x, hxComponent, hxProduct⟩
    exact ⟨⟨listedX, listedY,
      SourceIrreducibleComponent.isoOverAmbient_of_subset_range component productListed hsubset⟩⟩
  rcases Classical.choice h with ⟨listedX, listedY, hIso⟩
  exact ⟨listedX, listedY, hIso⟩

theorem product_range_eq_left_of_product_range_eq
    {X Y : Geometry.SmSchemeOver k}
    {DX : FiniteIrreducibleComponentDecomposition X}
    {DY : FiniteIrreducibleComponentDecomposition Y}
    {listedX₁ listedX₂ : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }}
    {listedY₁ listedY₂ : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components }}
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (hRange :
      Set.range (productSourceIrreducibleComponent (stableDX listedX₁) listedY₁.1).toAmbient.base =
      Set.range (productSourceIrreducibleComponent (stableDX listedX₂) listedY₂.1).toAmbient.base) :
    Set.range listedX₁.1.toAmbient.base = Set.range listedX₂.1.toAmbient.base := by
  calc
    Set.range listedX₁.1.toAmbient.base
      = Set.image (overBaseProduct.fst X Y).base
          (Set.range (productSourceIrreducibleComponent (stableDX listedX₁) listedY₁.1).toAmbient.base) := by
          simpa only [← stableDX_component_range_eq stableDX hstableDX listedX₁] using
            (productSourceIrreducibleComponent_range_image_fst
              (C := stableDX listedX₁) (D := listedY₁.1)).symm
    _ = Set.image (overBaseProduct.fst X Y).base
          (Set.range (productSourceIrreducibleComponent (stableDX listedX₂) listedY₂.1).toAmbient.base) := by
          rw [hRange]
    _ = Set.range listedX₂.1.toAmbient.base := by
          simpa only [← stableDX_component_range_eq stableDX hstableDX listedX₂] using
            (productSourceIrreducibleComponent_range_image_fst
              (C := stableDX listedX₂) (D := listedY₂.1))

theorem product_range_eq_right_of_product_range_eq
    {X Y : Geometry.SmSchemeOver k}
    {DX : FiniteIrreducibleComponentDecomposition X}
    {DY : FiniteIrreducibleComponentDecomposition Y}
    {listedX₁ listedX₂ : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }}
    {listedY₁ listedY₂ : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components }}
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hRange :
      Set.range (productSourceIrreducibleComponent (stableDX listedX₁) listedY₁.1).toAmbient.base =
      Set.range (productSourceIrreducibleComponent (stableDX listedX₂) listedY₂.1).toAmbient.base) :
    Set.range listedY₁.1.toAmbient.base = Set.range listedY₂.1.toAmbient.base := by
  calc
    Set.range listedY₁.1.toAmbient.base
      = Set.image (overBaseProduct.snd X Y).base
          (Set.range (productSourceIrreducibleComponent (stableDX listedX₁) listedY₁.1).toAmbient.base) := by
          symm
          exact productSourceIrreducibleComponent_range_image_snd
            (C := stableDX listedX₁) (D := listedY₁.1)
    _ = Set.image (overBaseProduct.snd X Y).base
          (Set.range (productSourceIrreducibleComponent (stableDX listedX₂) listedY₂.1).toAmbient.base) := by
          rw [hRange]
    _ = Set.range listedY₂.1.toAmbient.base := by
          exact productSourceIrreducibleComponent_range_image_snd
            (C := stableDX listedX₂) (D := listedY₂.1)

/-- Uniqueness of listed product source components: if two listed products are
isomorphic over the ambient product, then the listed factors agree. -/
theorem productSourceIrreducibleComponent_unique
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    {listedX₁ listedX₂ : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }}
    {listedY₁ listedY₂ : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components }}
    (hiso :
      SourceIrreducibleComponent.IsoOverAmbient
        (productSourceIrreducibleComponent (stableDX listedX₁) listedY₁.1)
        (productSourceIrreducibleComponent (stableDX listedX₂) listedY₂.1)) :
    listedX₁ = listedX₂ ∧ listedY₁ = listedY₂ := by
  let P₁ := productSourceIrreducibleComponent (stableDX listedX₁) listedY₁.1
  let P₂ := productSourceIrreducibleComponent (stableDX listedX₂) listedY₂.1
  have hsubset :
      Set.range P₁.toAmbient.base ⊆ Set.range P₂.toAmbient.base := by
    rintro x ⟨z, rfl⟩
    exact ⟨hiso.iso.hom.base z, by
      simpa [P₁, P₂] using isoOverAmbient_hom_toAmbient_base_apply hiso z⟩
  have hRange :
      Set.range P₁.toAmbient.base = Set.range P₂.toAmbient.base :=
    SourceIrreducibleComponent.range_eq_of_subset_range P₁ P₂ hsubset
  have hLeft :
      Set.range listedX₁.1.toAmbient.base = Set.range listedX₂.1.toAmbient.base :=
    product_range_eq_left_of_product_range_eq (DX := DX) (DY := DY) stableDX hstableDX hRange
  have hRight :
      Set.range listedY₁.1.toAmbient.base = Set.range listedY₂.1.toAmbient.base :=
    product_range_eq_right_of_product_range_eq (DX := DX) (DY := DY) stableDX hRange
  have hXeq := DX.no_equivalent_duplicates listedX₁.2 listedX₂.2
    (SourceIrreducibleComponent.isoOverAmbient_of_range_eq listedX₁.1 listedX₂.1 hLeft)
  have hYeq := DY.no_equivalent_duplicates listedY₁.2 listedY₂.2
    (SourceIrreducibleComponent.isoOverAmbient_of_range_eq listedY₁.1 listedY₂.1 hRight)
  exact ⟨Subtype.ext hXeq, Subtype.ext hYeq⟩

noncomputable def productSourceIrreducibleComponent_exhaustive_packaged
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (components :
      Finset (SourceIrreducibleComponent (overBaseProductObject X Y)))
    (hcomponents :
      components = @Finset.image _ _ (Classical.decEq _)
        (fun (p :
            { listed : SourceIrreducibleComponent X // listed ∈ DX.components } ×
              { listed : SourceIrreducibleComponent Y // listed ∈ DY.components }) =>
        productSourceIrreducibleComponent (stableDX p.1) p.2.1)
        (DX.components.attach.product DY.components.attach))
    (component : SourceIrreducibleComponent (overBaseProductObject X Y)) :
    Σ listed : { listed : SourceIrreducibleComponent (overBaseProductObject X Y) // listed ∈ components },
      SourceIrreducibleComponent.IsoOverAmbient component listed.1 := by
  classical
  letI : DecidableEq (SourceIrreducibleComponent (overBaseProductObject X Y)) := Classical.decEq _
  rcases productSourceIrreducibleComponent_exhaustive DX DY stableDX hstableDX component with
    ⟨listedX, listedY, hIso⟩
  refine ⟨⟨productSourceIrreducibleComponent (stableDX listedX) listedY.1, ?_⟩, ?_⟩
  · rw [hcomponents]
    refine Finset.mem_image.mpr ?_
    refine ⟨(listedX, listedY), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩
  · simpa using hIso

/-- The finite irreducible-component decomposition of `X ×_k Y` obtained by
forming the listed products of a finite decomposition of `X` with a finite
decomposition of `Y`, under the explicit product-stability data carried by the
listed left components. -/
noncomputable def finiteProductSourceIrreducibleComponentDecomposition
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y) := by
  classical
  letI : DecidableEq (SourceIrreducibleComponent (overBaseProductObject X Y)) := Classical.decEq _
  let listedPairs :=
    DX.components.attach.product DY.components.attach
  let components :
      Finset (SourceIrreducibleComponent (overBaseProductObject X Y)) :=
    @Finset.image _ _ (Classical.decEq _) (fun (p :
        { listed : SourceIrreducibleComponent X // listed ∈ DX.components } ×
          { listed : SourceIrreducibleComponent Y // listed ∈ DY.components }) =>
      productSourceIrreducibleComponent (stableDX p.1) p.2.1) listedPairs
  refine
    { components := components
      covers := ?_
      pairwise_disjoint := ?_
      exhaustive := ?_
      no_equivalent_duplicates := ?_ }
  · intro x
    rcases DX.covers ((overBaseProduct.fst X Y).base x) with ⟨CX, hCXmem, hxCX⟩
    rcases DY.covers ((overBaseProduct.snd X Y).base x) with ⟨CY, hCYmem, hxCY⟩
    let listedX : { listed : SourceIrreducibleComponent X // listed ∈ DX.components } :=
      ⟨CX, hCXmem⟩
    let listedY : { listed : SourceIrreducibleComponent Y // listed ∈ DY.components } :=
      ⟨CY, hCYmem⟩
    refine ⟨productSourceIrreducibleComponent (stableDX listedX) listedY.1, ?_, ?_⟩
    · refine Finset.mem_image.mpr ?_
      refine ⟨(listedX, listedY), ?_, rfl⟩
      change (listedX, listedY) ∈ listedPairs
      exact Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩
    · have hxCX' :
          (overBaseProduct.fst X Y).base x ∈ Set.range (stableDX listedX).component.toAmbient.base := by
          have hxCX'' :
              (overBaseProduct.fst X Y).base x ∈ Set.range listedX.1.toAmbient.base := hxCX
          simpa only [← stableDX_component_range_eq stableDX hstableDX listedX] using hxCX''
      simpa [listedX, listedY] using
        (productSourceIrreducibleComponent_mem_range_iff
          (C := stableDX listedX) (D := listedY.1) (x := x)).2
          ⟨hxCX', hxCY⟩
  · intro C D hC hD hneq
    rcases Finset.mem_image.mp hC with ⟨p, hpMem, rfl⟩
    rcases Finset.mem_image.mp hD with ⟨q, hqMem, hqEq⟩
    subst D
    by_cases hpqX : p.1 = q.1
    · have hpqY : p.2 ≠ q.2 := by
        intro hpqY
        apply hneq
        simpa [hpqX, hpqY]
      rw [Set.disjoint_left]
      intro x hxP hxQ
      have hprojP :=
        productSourceIrreducibleComponent_proj_mem_of_mem_range
          (C := stableDX p.1) (D := p.2.1) hxP
      have hprojQ :=
        productSourceIrreducibleComponent_proj_mem_of_mem_range
          (C := stableDX q.1) (D := q.2.1) hxQ
      have hdisj :=
        DY.disjoint_of_mem_ne p.2.2 q.2.2 (by
          intro hEq
          exact hpqY (Subtype.ext hEq))
      exact hdisj.le_bot ⟨hprojP.2, hprojQ.2⟩
    · rw [Set.disjoint_left]
      intro x hxP hxQ
      have hprojP :=
        productSourceIrreducibleComponent_proj_mem_of_mem_range
          (C := stableDX p.1) (D := p.2.1) hxP
      have hprojQ :=
        productSourceIrreducibleComponent_proj_mem_of_mem_range
          (C := stableDX q.1) (D := q.2.1) hxQ
      have hdisj :=
        DX.disjoint_of_mem_ne p.1.2 q.1.2 (by
          intro hEq
          exact hpqX (Subtype.ext hEq))
      exact hdisj.le_bot
        ⟨by
            rw [← stableDX_component_range_eq stableDX hstableDX p.1]
            exact hprojP.1,
          by
            rw [← stableDX_component_range_eq stableDX hstableDX q.1]
            exact hprojQ.1⟩
  · intro component
    exact productSourceIrreducibleComponent_exhaustive_packaged
      DX DY stableDX hstableDX components rfl component
  · intro C D hC hD hiso
    rcases Finset.mem_image.mp hC with ⟨p, hpMem, hpEq⟩
    rcases Finset.mem_image.mp hD with ⟨q, hqMem, hqEq⟩
    subst C
    have hiso' :
        SourceIrreducibleComponent.IsoOverAmbient
          (productSourceIrreducibleComponent (stableDX p.1) p.2.1)
          (productSourceIrreducibleComponent (stableDX q.1) q.2.1) := by
      simpa [hqEq] using hiso
    rcases productSourceIrreducibleComponent_unique DX DY stableDX hstableDX hiso' with
      ⟨hpqX, hpqY⟩
    have hpq : p = q := Prod.ext hpqX hpqY
    subst q
    exact hqEq

/-- Smooth schemes of finite type over a field have finitely many topological
irreducible components. This supplies the finite-index part of a canonical
`FiniteIrreducibleComponentDecomposition`; the geometric packaging of each
component as a clopen integral smooth subscheme is the separate constructor
needed for that decomposition. -/
theorem finite_irreducibleComponents (X : Geometry.SmSchemeOver k) :
    (irreducibleComponents X.scheme).Finite :=
  AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian

/-- The finite source-component decomposition obtained by listing the actual
topological irreducible components of a smooth finite-type scheme, once those
components have been realized as open, closed, integral source subschemes. -/
noncomputable def finiteSourceIrreducibleComponentDecompositionOfTopologicalComponents
    (X : Geometry.SmSchemeOver k)
    (hOpen :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsOpen C.1)
    (hClosed :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsClosed C.1)
    (hIntegral :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsIntegral (Scheme.Opens.toScheme (⟨C.1, hOpen C⟩ : X.scheme.Opens))) :
    FiniteIrreducibleComponentDecomposition X :=
  FiniteIrreducibleComponentDecomposition.ofTopologicalComponents
    X (finite_irreducibleComponents X) hOpen hClosed hIntegral

/-- The finite source-component decomposition obtained from the actual
irreducible components once those components are known to be clopen.  The
remaining hypothesis is the genuine scheme-theoretic integrality of the
corresponding open component schemes. -/
noncomputable def finiteSourceIrreducibleComponentDecompositionOfClopenComponents
    (X : Geometry.SmSchemeOver k)
    (hClopen :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsClopen C.1)
    (hIntegral :
      ∀ C : { C : Set X.scheme // C ∈ irreducibleComponents X.scheme },
        IsIntegral
          (Scheme.Opens.toScheme (⟨C.1, (hClopen C).right⟩ : X.scheme.Opens))) :
    FiniteIrreducibleComponentDecomposition X :=
  finiteSourceIrreducibleComponentDecompositionOfTopologicalComponents X
    (fun C => (hClopen C).right)
    (fun C => (hClopen C).left)
    hIntegral

end -- noncomputable section

end Boundary
