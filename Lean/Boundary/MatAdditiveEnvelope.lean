import Mathlib.CategoryTheory.Preadditive.Mat

/-!
# Boundary API for `Mat_`

Project-local helper lemmas for the additive envelope `Mat_`.  These are kept
outside the vendored mathlib checkout.
-/

open CategoryTheory CategoryTheory.Preadditive Limits

open scoped Classical

noncomputable section

namespace CategoryTheory

universe v₁ u₁

namespace Mat_

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]

@[reassoc (attr := simp)]
lemma embedding_isoBiproductEmbedding_hom_π (X : C) :
    ((embedding C).obj X).isoBiproductEmbedding.hom ≫
        biproduct.π (fun i => (embedding C).obj (((embedding C).obj X).X i)) PUnit.unit =
      𝟙 ((embedding C).obj X) := by
  rw [isoBiproductEmbedding_hom, biproduct.lift_π]
  ext ⟨⟩ ⟨⟩
  simp [embedding]

@[reassoc (attr := simp)]
lemma embedding_ι_isoBiproductEmbedding_inv (X : C) :
    biproduct.ι (fun i => (embedding C).obj (((embedding C).obj X).X i)) PUnit.unit ≫
        ((embedding C).obj X).isoBiproductEmbedding.inv =
      𝟙 ((embedding C).obj X) := by
  rw [isoBiproductEmbedding_inv, biproduct.ι_desc]
  ext ⟨⟩ ⟨⟩
  simp [embedding]

variable {D : Type u₁} [Category.{v₁} D] [Preadditive D] [HasFiniteBiproducts D]

/-- A natural transformation of additive functors induces a natural transformation
between their extensions to the additive envelope. -/
def liftMap {F G : C ⥤ D} [Functor.Additive F] [Functor.Additive G] (η : F ⟶ G) :
    lift F ⟶ lift G where
  app M := biproduct.map fun i => η.app (M.X i)
  naturality M N f := by
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, lift_map, biproduct.matrix_π, biproduct.map_π]
    apply biproduct.hom_ext'
    intro i
    simpa [biproduct.components] using η.naturality (f i j)

@[reassoc (attr := simp)]
lemma liftMap_π {F G : C ⥤ D} [Functor.Additive F] [Functor.Additive G]
    (η : F ⟶ G) (M : Mat_ C) (i : M.ι) :
    (liftMap η).app M ≫ biproduct.π (fun i => G.obj (M.X i)) i =
      biproduct.π (fun i => F.obj (M.X i)) i ≫ η.app (M.X i) := by
  simp [liftMap]

@[simp]
lemma liftMap_id (F : C ⥤ D) [Functor.Additive F] :
    liftMap (𝟙 F) = 𝟙 (lift F) := by
  apply NatTrans.ext
  funext M
  apply biproduct.hom_ext
  intro i
  simp [liftMap]

@[simp]
lemma liftMap_comp {F G H : C ⥤ D} [Functor.Additive F] [Functor.Additive G]
    [Functor.Additive H] (η : F ⟶ G) (θ : G ⟶ H) :
    liftMap (η ≫ θ) = liftMap η ≫ liftMap θ := by
  apply NatTrans.ext
  funext M
  apply biproduct.hom_ext
  intro i
  simp [liftMap, Category.assoc]

@[reassoc (attr := simp)]
lemma embeddingLiftIso_hom_naturality {F G : C ⥤ D} [Functor.Additive F]
    [Functor.Additive G] (η : F ⟶ G) :
    (embeddingLiftIso F).hom ≫ η =
      whiskerLeft (embedding C) (liftMap η) ≫ (embeddingLiftIso G).hom := by
  apply NatTrans.ext
  funext X
  apply biproduct.hom_ext'
  rintro ⟨⟩
  simp [embeddingLiftIso, liftMap, Category.assoc]

@[reassoc (attr := simp)]
lemma embeddingLiftIso_inv_naturality {F G : C ⥤ D} [Functor.Additive F]
    [Functor.Additive G] (η : F ⟶ G) :
    η ≫ (embeddingLiftIso G).inv =
      (embeddingLiftIso F).inv ≫ whiskerLeft (embedding C) (liftMap η) := by
  apply NatTrans.ext
  funext X
  apply biproduct.hom_ext
  rintro ⟨⟩
  simp [embeddingLiftIso, liftMap, Category.assoc]

@[reassoc (attr := simp)]
lemma additiveObjIsoBiproduct_hom_naturality {F G : Mat_ C ⥤ D} [Functor.Additive F]
    [Functor.Additive G] (η : F ⟶ G) (M : Mat_ C) :
    η.app M ≫ (additiveObjIsoBiproduct G M).hom =
      (additiveObjIsoBiproduct F M).hom ≫
        biproduct.map fun i => η.app ((embedding C).obj (M.X i)) := by
  ext i : 1
  simp only [Category.assoc, additiveObjIsoBiproduct_hom_π, biproduct.map_π]
  simpa [Category.assoc] using (η.naturality _).symm

@[reassoc (attr := simp)]
lemma additiveObjIsoBiproduct_inv_naturality {F G : Mat_ C ⥤ D} [Functor.Additive F]
    [Functor.Additive G] (η : F ⟶ G) (M : Mat_ C) :
    biproduct.map (fun i => η.app ((embedding C).obj (M.X i))) ≫
        (additiveObjIsoBiproduct G M).inv =
      (additiveObjIsoBiproduct F M).inv ≫ η.app M := by
  rw [← cancel_mono (additiveObjIsoBiproduct G M).hom]
  simp [Category.assoc]

theorem natTrans_ext {F G : Mat_ C ⥤ D} [Functor.Additive F] [Functor.Additive G]
    {η θ : F ⟶ G} (h : ∀ X, η.app ((embedding C).obj X) = θ.app ((embedding C).obj X)) :
    η = θ := by
  apply NatTrans.ext
  funext M
  rw [← cancel_mono (additiveObjIsoBiproduct G M).hom]
  rw [additiveObjIsoBiproduct_hom_naturality,
    additiveObjIsoBiproduct_hom_naturality]
  congr 1
  apply biproduct.hom_ext
  intro i
  simp [h]

end Mat_

end CategoryTheory
