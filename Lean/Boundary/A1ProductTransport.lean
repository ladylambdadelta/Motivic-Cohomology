import Boundary.A1AffineBasic
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
/-- Reassociate the affine-line factor to the right:

`(X ×_k Y) ×_k A¹ ≅ (X ×_k A¹) ×_k Y`.
-/
private noncomputable def productWithA1_product_right_iso_hom_scheme
    (X Y : Geometry.SmSchemeOver k) :
    (productWithA1 (overBaseProductObject X Y)).scheme ⟶
      (overBaseProductObject (productWithA1 X) Y).scheme :=
  ((pullbackRightPullbackFstIso X.structMap (A1_k (k := k)).structMap
      (overBaseProduct.fst X Y)).symm ≪≫
    asIso
      (Limits.pullback.map
        (overBaseProduct.fst X Y)
        (overBaseProduct.fst X (A1_k (k := k)))
        (overBaseProduct.snd Y X)
        (overBaseProduct.fst X (A1_k (k := k)))
        (pullbackSymmetry X.structMap Y.structMap).hom
        (𝟙 _)
        (𝟙 _)
        (by
          simpa [overBaseProduct] using
            (pullbackSymmetry_hom_comp_snd
              (f := X.structMap) (g := Y.structMap)))
        (by simp)) ≪≫
    pullbackLeftPullbackSndIso Y.structMap X.structMap
      (overBaseProduct.fst X (A1_k (k := k))) ≪≫
    pullbackSymmetry Y.structMap
      ((productWithA1 X).structMap)).hom

private noncomputable def productWithA1_product_right_iso_inv_scheme
    (X Y : Geometry.SmSchemeOver k) :
    (overBaseProductObject (productWithA1 X) Y).scheme ⟶
      (productWithA1 (overBaseProductObject X Y)).scheme :=
  ((pullbackRightPullbackFstIso X.structMap (A1_k (k := k)).structMap
      (overBaseProduct.fst X Y)).symm ≪≫
    asIso
      (Limits.pullback.map
        (overBaseProduct.fst X Y)
        (overBaseProduct.fst X (A1_k (k := k)))
        (overBaseProduct.snd Y X)
        (overBaseProduct.fst X (A1_k (k := k)))
        (pullbackSymmetry X.structMap Y.structMap).hom
        (𝟙 _)
        (𝟙 _)
        (by
          simpa [overBaseProduct] using
            (pullbackSymmetry_hom_comp_snd
              (f := X.structMap) (g := Y.structMap)))
        (by simp)) ≪≫
    pullbackLeftPullbackSndIso Y.structMap X.structMap
      (overBaseProduct.fst X (A1_k (k := k))) ≪≫
    pullbackSymmetry Y.structMap
      ((productWithA1 X).structMap)).inv

@[simp, reassoc] private theorem productWithA1_product_right_iso_hom_scheme_fst
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.fst X (A1_k (k := k)) =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y := by
  simp [productWithA1_product_right_iso_hom_scheme, productWithA1, overBaseProductObject,
    overBaseProduct, Category.assoc]

@[simp, reassoc] private theorem productWithA1_product_right_iso_hom_scheme_snd
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.snd (productWithA1 X) Y =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y := by
  simp [productWithA1_product_right_iso_hom_scheme, productWithA1, overBaseProductObject,
    overBaseProduct, Category.assoc]

@[simp, reassoc] private theorem productWithA1_product_right_iso_hom_scheme_snd_a1
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.fst (productWithA1 X) Y ≫ overBaseProduct.snd X (A1_k (k := k)) =
      overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) := by
  simp [productWithA1_product_right_iso_hom_scheme, productWithA1, overBaseProductObject,
    overBaseProduct, Category.assoc]

@[simp, reassoc] private theorem productWithA1_product_right_iso_inv_scheme_fst
    (X Y : Geometry.SmSchemeOver k) :
    (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        (pullbackLeftPullbackSndIso Y.structMap X.structMap
          (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
          Limits.pullback.map
            (overBaseProduct.snd Y X)
            (overBaseProduct.fst X (A1_k (k := k)))
            (overBaseProduct.fst X Y)
            (overBaseProduct.fst X (A1_k (k := k)))
            (pullbackSymmetry X.structMap Y.structMap).inv
            (𝟙 _)
            (𝟙 _)
            (by simpa [overBaseProduct] using
              (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
            (by simp) ≫
              (pullbackRightPullbackFstIso X.structMap (A1_k (k := k)).structMap
                (overBaseProduct.fst X Y)).hom ≫
                overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
                overBaseProduct.fst X Y =
      overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.fst X (A1_k (k := k)) := by
  calc
    (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        (pullbackLeftPullbackSndIso Y.structMap X.structMap
          (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
          Limits.pullback.map
            (overBaseProduct.snd Y X)
            (overBaseProduct.fst X (A1_k (k := k)))
            (overBaseProduct.fst X Y)
            (overBaseProduct.fst X (A1_k (k := k)))
            (pullbackSymmetry X.structMap Y.structMap).inv
            (𝟙 _)
            (𝟙 _)
            (by simpa [overBaseProduct] using
              (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
            (by simp) ≫
              (pullbackRightPullbackFstIso X.structMap (A1_k (k := k)).structMap
                (overBaseProduct.fst X Y)).hom ≫
                overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
                overBaseProduct.fst X Y
      =
    (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        (pullbackLeftPullbackSndIso Y.structMap X.structMap
          (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
        Limits.pullback.map
          (overBaseProduct.snd Y X)
          (overBaseProduct.fst X (A1_k (k := k)))
          (overBaseProduct.fst X Y)
          (overBaseProduct.fst X (A1_k (k := k)))
          (pullbackSymmetry X.structMap Y.structMap).inv
          (𝟙 _)
          (𝟙 _)
          (by simpa [overBaseProduct] using
            (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
          (by simp) ≫
        CategoryTheory.Limits.pullback.fst
          (overBaseProduct.fst X Y)
          (overBaseProduct.fst X (A1_k (k := k))) ≫
        overBaseProduct.fst X Y := by
          simpa only [Category.assoc] using congrArg
            (fun z =>
              (pullbackSymmetry Y.structMap
                  (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
                (pullbackLeftPullbackSndIso Y.structMap X.structMap
                  (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
                Limits.pullback.map
                  (overBaseProduct.snd Y X)
                  (overBaseProduct.fst X (A1_k (k := k)))
                  (overBaseProduct.fst X Y)
                  (overBaseProduct.fst X (A1_k (k := k)))
                  (pullbackSymmetry X.structMap Y.structMap).inv
                  (𝟙 _)
                  (𝟙 _)
                  (by simpa [overBaseProduct] using
                    (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
                  (by simp) ≫ z)
            (pullbackRightPullbackFstIso_hom_fst_assoc
              (f := X.structMap) (g := (A1_k (k := k)).structMap)
              (f' := overBaseProduct.fst X Y)
              (overBaseProduct.fst X Y))
    _ =
      (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        (pullbackLeftPullbackSndIso Y.structMap X.structMap
          (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
        CategoryTheory.Limits.pullback.fst
          (overBaseProduct.snd Y X)
          (overBaseProduct.fst X (A1_k (k := k))) ≫
        overBaseProduct.snd Y X := by
          have hstep :=
            congrArg
              (fun z =>
                (pullbackSymmetry Y.structMap
                    (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
                  (pullbackLeftPullbackSndIso Y.structMap X.structMap
                    (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
                  CategoryTheory.Limits.pullback.fst
                    (overBaseProduct.snd Y X)
                    (overBaseProduct.fst X (A1_k (k := k))) ≫ z)
              (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap))
          simpa only [Limits.pullback.map, Category.assoc, Limits.pullback.lift_fst_assoc] using hstep
    _ =
      (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        overBaseProduct.snd Y (productWithA1 X) ≫
        overBaseProduct.fst X (A1_k (k := k)) := by
          have hstep :=
            congrArg
              (fun z =>
                (pullbackSymmetry Y.structMap
                    (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫ z)
              (pullbackLeftPullbackSndIso_inv_fst_snd
                (f := Y.structMap) (g := X.structMap)
                (g' := overBaseProduct.fst X (A1_k (k := k))))
          simpa only [Category.assoc] using hstep
    _ = overBaseProduct.fst (productWithA1 X) Y ≫
          overBaseProduct.fst X (A1_k (k := k)) := by
          have hstep :=
            congrArg
              (fun z => z ≫ overBaseProduct.fst X (A1_k (k := k)))
              (pullbackSymmetry_inv_comp_snd
                (f := Y.structMap)
                (g := overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap))
          simpa only [Category.assoc] using hstep

@[simp, reassoc] private theorem productWithA1_product_right_iso_inv_scheme_fst_eq
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y =
      overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.fst X (A1_k (k := k)) := by
  let mHom :=
    Limits.pullback.map
      (overBaseProduct.fst X Y)
      (overBaseProduct.fst X (A1_k (k := k)))
      (overBaseProduct.snd Y X)
      (overBaseProduct.fst X (A1_k (k := k)))
      (pullbackSymmetry X.structMap Y.structMap).hom
      (𝟙 _)
      (𝟙 _)
      (by
        simpa [overBaseProduct] using
          (pullbackSymmetry_hom_comp_snd (f := X.structMap) (g := Y.structMap)))
      (by simp)
  let mInv :=
    Limits.pullback.map
      (overBaseProduct.snd Y X)
      (overBaseProduct.fst X (A1_k (k := k)))
      (overBaseProduct.fst X Y)
      (overBaseProduct.fst X (A1_k (k := k)))
      (pullbackSymmetry X.structMap Y.structMap).inv
      (𝟙 _)
      (𝟙 _)
      (by
        simpa [overBaseProduct] using
          (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
      (by simp)
  have hcomp : mHom ≫ mInv = 𝟙 _ := by
    dsimp [mHom, mInv]
    rw [Limits.pullback.map_comp]
    simp [Limits.pullback.map_id, Category.assoc, overBaseProduct]
  letI : IsIso mHom := by
    dsimp [mHom]
    infer_instance
  have hInv : inv mHom = mInv := by
    simpa using (IsIso.eq_inv_of_hom_inv_id hcomp).symm
  change (pullbackSymmetry Y.structMap (productWithA1 X).structMap).inv ≫
      (pullbackLeftPullbackSndIso Y.structMap X.structMap
        (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
      inv mHom ≫
      (pullbackRightPullbackFstIso X.structMap (A1_k (k := k)).structMap
        (overBaseProduct.fst X Y)).hom ≫
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
      overBaseProduct.fst X Y =
    overBaseProduct.fst (productWithA1 X) Y ≫
      overBaseProduct.fst X (A1_k (k := k))
  rw [hInv]
  exact productWithA1_product_right_iso_inv_scheme_fst (k := k) X Y

@[simp, reassoc] private theorem productWithA1_product_right_iso_inv_scheme_snd
    (X Y : Geometry.SmSchemeOver k) :
    (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        (pullbackLeftPullbackSndIso Y.structMap X.structMap
          (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
          Limits.pullback.map
            (overBaseProduct.snd Y X)
            (overBaseProduct.fst X (A1_k (k := k)))
            (overBaseProduct.fst X Y)
            (overBaseProduct.fst X (A1_k (k := k)))
            (pullbackSymmetry X.structMap Y.structMap).inv
            (𝟙 _)
            (𝟙 _)
            (by simpa [overBaseProduct] using
              (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
            (by simp) ≫
              (pullbackRightPullbackFstIso X.structMap (A1_k (k := k)).structMap
                (overBaseProduct.fst X Y)).hom ≫
                overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) =
      overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.snd X (A1_k (k := k)) := by
  calc
    (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        (pullbackLeftPullbackSndIso Y.structMap X.structMap
          (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
          Limits.pullback.map
            (overBaseProduct.snd Y X)
            (overBaseProduct.fst X (A1_k (k := k)))
            (overBaseProduct.fst X Y)
            (overBaseProduct.fst X (A1_k (k := k)))
            (pullbackSymmetry X.structMap Y.structMap).inv
            (𝟙 _)
            (𝟙 _)
            (by simpa [overBaseProduct] using
              (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
            (by simp) ≫
              (pullbackRightPullbackFstIso X.structMap (A1_k (k := k)).structMap
                (overBaseProduct.fst X Y)).hom ≫
                overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k))
      =
    (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        (pullbackLeftPullbackSndIso Y.structMap X.structMap
          (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
        Limits.pullback.map
          (overBaseProduct.snd Y X)
          (overBaseProduct.fst X (A1_k (k := k)))
          (overBaseProduct.fst X Y)
          (overBaseProduct.fst X (A1_k (k := k)))
          (pullbackSymmetry X.structMap Y.structMap).inv
          (𝟙 _)
          (𝟙 _)
          (by simpa [overBaseProduct] using
            (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
          (by simp) ≫
        CategoryTheory.Limits.pullback.snd
          (overBaseProduct.fst X Y)
          (overBaseProduct.fst X (A1_k (k := k))) ≫
        overBaseProduct.snd X (A1_k (k := k)) := by
          have hstep :=
            congrArg
              (fun z =>
                (pullbackSymmetry Y.structMap
                    (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
                  (pullbackLeftPullbackSndIso Y.structMap X.structMap
                    (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
                  Limits.pullback.map
                    (overBaseProduct.snd Y X)
                    (overBaseProduct.fst X (A1_k (k := k)))
                    (overBaseProduct.fst X Y)
                    (overBaseProduct.fst X (A1_k (k := k)))
                    (pullbackSymmetry X.structMap Y.structMap).inv
                    (𝟙 _)
                    (𝟙 _)
                    (by simpa [overBaseProduct] using
                      (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
                    (by simp) ≫ z)
              (pullbackRightPullbackFstIso_hom_snd
                (f := X.structMap) (g := (A1_k (k := k)).structMap)
                (f' := overBaseProduct.fst X Y))
          simpa only [Category.assoc] using hstep
    _ =
      (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        (pullbackLeftPullbackSndIso Y.structMap X.structMap
          (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
        CategoryTheory.Limits.pullback.snd
          (overBaseProduct.snd Y X)
          (overBaseProduct.fst X (A1_k (k := k))) ≫
        overBaseProduct.snd X (A1_k (k := k)) := by
          simp only [Limits.pullback.map, Category.assoc, Limits.pullback.lift_snd_assoc,
            pullbackSymmetry_inv_comp_snd_assoc, Category.id_comp]
    _ =
      (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        overBaseProduct.snd Y (productWithA1 X) ≫
        overBaseProduct.snd X (A1_k (k := k)) := by
          have hstep :=
            congrArg
              (fun z =>
                (pullbackSymmetry Y.structMap
                    (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
                  z ≫ overBaseProduct.snd X (A1_k (k := k)))
              (pullbackLeftPullbackSndIso_inv_snd_snd
                (f := Y.structMap) (g := X.structMap)
                (g' := overBaseProduct.fst X (A1_k (k := k))))
          simpa only [Category.assoc] using hstep
    _ = overBaseProduct.fst (productWithA1 X) Y ≫
          overBaseProduct.snd X (A1_k (k := k)) := by
          simpa only [Category.assoc] using
            (pullbackSymmetry_inv_comp_snd_assoc
              (f := Y.structMap)
              (g := overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)
              (overBaseProduct.snd X (A1_k (k := k))))

@[simp, reassoc] private theorem productWithA1_product_right_iso_inv_scheme_snd_eq
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) =
      overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.snd X (A1_k (k := k)) := by
  let mHom :=
    Limits.pullback.map
      (overBaseProduct.fst X Y)
      (overBaseProduct.fst X (A1_k (k := k)))
      (overBaseProduct.snd Y X)
      (overBaseProduct.fst X (A1_k (k := k)))
      (pullbackSymmetry X.structMap Y.structMap).hom
      (𝟙 _)
      (𝟙 _)
      (by
        simpa [overBaseProduct] using
          (pullbackSymmetry_hom_comp_snd (f := X.structMap) (g := Y.structMap)))
      (by simp)
  let mInv :=
    Limits.pullback.map
      (overBaseProduct.snd Y X)
      (overBaseProduct.fst X (A1_k (k := k)))
      (overBaseProduct.fst X Y)
      (overBaseProduct.fst X (A1_k (k := k)))
      (pullbackSymmetry X.structMap Y.structMap).inv
      (𝟙 _)
      (𝟙 _)
      (by
        simpa [overBaseProduct] using
          (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
      (by simp)
  have hcomp : mHom ≫ mInv = 𝟙 _ := by
    dsimp [mHom, mInv]
    rw [Limits.pullback.map_comp]
    simp [Limits.pullback.map_id, Category.assoc, overBaseProduct]
  letI : IsIso mHom := by
    dsimp [mHom]
    infer_instance
  have hInv : inv mHom = mInv := by
    simpa using (IsIso.eq_inv_of_hom_inv_id hcomp).symm
  change (pullbackSymmetry Y.structMap (productWithA1 X).structMap).inv ≫
      (pullbackLeftPullbackSndIso Y.structMap X.structMap
        (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
      inv mHom ≫
      (pullbackRightPullbackFstIso X.structMap (A1_k (k := k)).structMap
        (overBaseProduct.fst X Y)).hom ≫
      overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) =
    overBaseProduct.fst (productWithA1 X) Y ≫
      overBaseProduct.snd X (A1_k (k := k))
  rw [hInv]
  exact productWithA1_product_right_iso_inv_scheme_snd (k := k) X Y

set_option maxHeartbeats 20000000 in
@[simp, reassoc] private theorem productWithA1_product_right_iso_inv_scheme_base_snd_aux
    (X Y : Geometry.SmSchemeOver k) :
    (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        (pullbackLeftPullbackSndIso Y.structMap X.structMap
          (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
        Limits.pullback.map
          (overBaseProduct.snd Y X)
          (overBaseProduct.fst X (A1_k (k := k)))
          (overBaseProduct.fst X Y)
          (overBaseProduct.fst X (A1_k (k := k)))
          (pullbackSymmetry X.structMap Y.structMap).inv
          (𝟙 _)
          (𝟙 _)
          (by simpa [overBaseProduct] using
            (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
          (by simp) ≫
        (pullbackRightPullbackFstIso X.structMap (A1_k (k := k)).structMap
          (overBaseProduct.fst X Y)).hom ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y =
      overBaseProduct.snd (productWithA1 X) Y := by
  calc
    (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        (pullbackLeftPullbackSndIso Y.structMap X.structMap
          (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
        Limits.pullback.map
          (overBaseProduct.snd Y X)
          (overBaseProduct.fst X (A1_k (k := k)))
          (overBaseProduct.fst X Y)
          (overBaseProduct.fst X (A1_k (k := k)))
          (pullbackSymmetry X.structMap Y.structMap).inv
          (𝟙 _)
          (𝟙 _)
          (by simpa [overBaseProduct] using
            (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
          (by simp) ≫
        (pullbackRightPullbackFstIso X.structMap (A1_k (k := k)).structMap
          (overBaseProduct.fst X Y)).hom ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y
      =
    (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        (pullbackLeftPullbackSndIso Y.structMap X.structMap
          (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
        Limits.pullback.map
          (overBaseProduct.snd Y X)
          (overBaseProduct.fst X (A1_k (k := k)))
          (overBaseProduct.fst X Y)
          (overBaseProduct.fst X (A1_k (k := k)))
          (pullbackSymmetry X.structMap Y.structMap).inv
          (𝟙 _)
          (𝟙 _)
          (by simpa [overBaseProduct] using
            (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
          (by simp) ≫
        CategoryTheory.Limits.pullback.fst
          (overBaseProduct.fst X Y)
          (overBaseProduct.fst X (A1_k (k := k))) ≫
        overBaseProduct.snd X Y := by
          simpa only [Category.assoc] using congrArg
            (fun z =>
              (pullbackSymmetry Y.structMap
                  (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
                (pullbackLeftPullbackSndIso Y.structMap X.structMap
                  (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
                Limits.pullback.map
                  (overBaseProduct.snd Y X)
                  (overBaseProduct.fst X (A1_k (k := k)))
                  (overBaseProduct.fst X Y)
                  (overBaseProduct.fst X (A1_k (k := k)))
                  (pullbackSymmetry X.structMap Y.structMap).inv
                  (𝟙 _)
                  (𝟙 _)
                  (by simpa [overBaseProduct] using
                    (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
                  (by simp) ≫ z)
            (pullbackRightPullbackFstIso_hom_fst_assoc
              (f := X.structMap) (g := (A1_k (k := k)).structMap)
              (f' := overBaseProduct.fst X Y)
              (overBaseProduct.snd X Y))
    _ =
      (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        (pullbackLeftPullbackSndIso Y.structMap X.structMap
          (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
        CategoryTheory.Limits.pullback.fst
          (overBaseProduct.snd Y X)
          (overBaseProduct.fst X (A1_k (k := k))) ≫
        overBaseProduct.fst Y X := by
          have hstep :=
            congrArg
              (fun z =>
                (pullbackSymmetry Y.structMap
                    (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
                  (pullbackLeftPullbackSndIso Y.structMap X.structMap
                    (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
                  CategoryTheory.Limits.pullback.fst
                    (overBaseProduct.snd Y X)
                    (overBaseProduct.fst X (A1_k (k := k))) ≫ z)
              (pullbackSymmetry_inv_comp_snd (f := X.structMap) (g := Y.structMap))
          simpa only [Limits.pullback.map, Category.assoc, Limits.pullback.lift_fst_assoc] using hstep
    _ =
      (pullbackSymmetry Y.structMap (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
        overBaseProduct.fst Y (productWithA1 X) := by
          change
            (pullbackSymmetry Y.structMap
                (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
              ((pullbackLeftPullbackSndIso Y.structMap X.structMap
                  (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
                CategoryTheory.Limits.pullback.fst
                  (overBaseProduct.snd Y X)
                  (overBaseProduct.fst X (A1_k (k := k))) ≫
                CategoryTheory.Limits.pullback.snd Y.structMap
                  (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)) =
            (pullbackSymmetry Y.structMap
                (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫
              overBaseProduct.fst Y (productWithA1 X)
          have hstep :=
            congrArg
              (fun z =>
                (pullbackSymmetry Y.structMap
                    (overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap)).inv ≫ z)
              (pullbackLeftPullbackSndIso_inv_fst_snd
                (f := Y.structMap) (g := X.structMap)
                (g' := overBaseProduct.fst X (A1_k (k := k))))
          simpa only [Category.assoc] using hstep
    _ = overBaseProduct.snd (productWithA1 X) Y := by
          simpa only [Category.assoc] using
            (pullbackSymmetry_inv_comp_fst
              (f := Y.structMap)
              (g := overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap))

@[simp, reassoc] private theorem productWithA1_product_right_iso_inv_scheme_base_snd
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y =
      overBaseProduct.snd (productWithA1 X) Y := by
  let mHom :=
    Limits.pullback.map
      (overBaseProduct.fst X Y)
      (overBaseProduct.fst X (A1_k (k := k)))
      (overBaseProduct.snd Y X)
      (overBaseProduct.fst X (A1_k (k := k)))
      (pullbackSymmetry X.structMap Y.structMap).hom
      (𝟙 _)
      (𝟙 _)
      (by
        simpa [overBaseProduct] using
          (pullbackSymmetry_hom_comp_snd (f := X.structMap) (g := Y.structMap)))
      (by simp)
  let mInv :=
    Limits.pullback.map
      (overBaseProduct.snd Y X)
      (overBaseProduct.fst X (A1_k (k := k)))
      (overBaseProduct.fst X Y)
      (overBaseProduct.fst X (A1_k (k := k)))
      (pullbackSymmetry X.structMap Y.structMap).inv
      (𝟙 _)
      (𝟙 _)
      (by
        simpa [overBaseProduct] using
          (pullbackSymmetry_inv_comp_fst (f := X.structMap) (g := Y.structMap)))
      (by simp)
  have hcomp : mHom ≫ mInv = 𝟙 _ := by
    dsimp [mHom, mInv]
    rw [Limits.pullback.map_comp]
    simp [Limits.pullback.map_id, Category.assoc, overBaseProduct]
  letI : IsIso mHom := by
    dsimp [mHom]
    infer_instance
  have hInv : inv mHom = mInv := by
    simpa using (IsIso.eq_inv_of_hom_inv_id hcomp).symm
  change (pullbackSymmetry Y.structMap (productWithA1 X).structMap).inv ≫
      (pullbackLeftPullbackSndIso Y.structMap X.structMap
        (overBaseProduct.fst X (A1_k (k := k)))).inv ≫
      inv mHom ≫
      (pullbackRightPullbackFstIso X.structMap (A1_k (k := k)).structMap
        (overBaseProduct.fst X Y)).hom ≫
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
      overBaseProduct.snd X Y =
    overBaseProduct.snd (productWithA1 X) Y
  rw [hInv]
  exact productWithA1_product_right_iso_inv_scheme_base_snd_aux (k := k) X Y

@[simp, reassoc] private theorem productWithA1_product_right_iso_inv_scheme_base_snd_eq
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y =
      overBaseProduct.snd (productWithA1 X) Y := by
  unfold productWithA1_product_right_iso_inv_scheme
  simpa only [Category.assoc] using
    productWithA1_product_right_iso_inv_scheme_base_snd (k := k) X Y

@[simp, reassoc] private theorem productWithA1_product_right_iso_hom_inv_fst
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y := by
  calc
    productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y =
      productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        (productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
          overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
          overBaseProduct.fst X Y) := by simp [Category.assoc]
    _ = productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.fst X (A1_k (k := k)) := by
          simpa only [Category.assoc] using
            congrArg
              (fun z =>
                productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫ z)
              (productWithA1_product_right_iso_inv_scheme_fst_eq (k := k) X Y)
    _ = overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y := by
          rw [productWithA1_product_right_iso_hom_scheme_fst]

@[simp, reassoc] private theorem productWithA1_product_right_iso_hom_inv_snd
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) =
      overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) := by
  calc
    productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) =
      productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        (productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
          overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k))) := by
          simp [Category.assoc]
    _ = productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.snd X (A1_k (k := k)) := by
          simpa only [Category.assoc] using
            congrArg
              (fun z =>
                productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫ z)
              (productWithA1_product_right_iso_inv_scheme_snd_eq (k := k) X Y)
    _ = overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) := by
          rw [productWithA1_product_right_iso_hom_scheme_snd_a1]

@[simp, reassoc] private theorem productWithA1_product_right_iso_hom_inv_toBaseProduct
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) := by
  apply Limits.pullback.hom_ext
  · change productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y
    simpa only [Category.assoc] using
      productWithA1_product_right_iso_hom_inv_fst (k := k) X Y
  · change productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y
    calc
      productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
          productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
          overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
          overBaseProduct.snd X Y =
        productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
          (productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
            overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
            overBaseProduct.snd X Y) := by
              simp [Category.assoc]
      _ = productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
          overBaseProduct.snd (productWithA1 X) Y := by
            rw [productWithA1_product_right_iso_inv_scheme_base_snd_eq]
      _ = overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
          overBaseProduct.snd X Y := by
            rw [productWithA1_product_right_iso_hom_scheme_snd]

@[simp, reassoc] private theorem productWithA1_product_right_iso_inv_hom_fst
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.fst X (A1_k (k := k)) =
      overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.fst X (A1_k (k := k)) := by
  calc
    productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.fst X (A1_k (k := k)) =
      productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        (productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
          overBaseProduct.fst (productWithA1 X) Y ≫
          overBaseProduct.fst X (A1_k (k := k))) := by simp [Category.assoc]
    _ = productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y := by
          simpa only [Category.assoc] using
            congrArg
              (fun z =>
                productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫ z)
              (productWithA1_product_right_iso_hom_scheme_fst (k := k) X Y)
    _ = overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.fst X (A1_k (k := k)) := by
          rw [productWithA1_product_right_iso_inv_scheme_fst_eq]

@[simp, reassoc] private theorem productWithA1_product_right_iso_inv_hom_snd
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.snd (productWithA1 X) Y =
      overBaseProduct.snd (productWithA1 X) Y := by
  calc
    productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.snd (productWithA1 X) Y =
      productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        (productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
          overBaseProduct.snd (productWithA1 X) Y) := by simp [Category.assoc]
    _ = productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y := by
          simpa only [Category.assoc] using
            congrArg
              (fun z =>
                productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫ z)
              (productWithA1_product_right_iso_hom_scheme_snd (k := k) X Y)
    _ = overBaseProduct.snd (productWithA1 X) Y := by
          rw [productWithA1_product_right_iso_inv_scheme_base_snd_eq]

@[simp, reassoc] private theorem productWithA1_product_right_iso_inv_hom_a1
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.snd X (A1_k (k := k)) =
      overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.snd X (A1_k (k := k)) := by
  calc
    productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.snd X (A1_k (k := k)) =
      productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        (productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
          overBaseProduct.fst (productWithA1 X) Y ≫
          overBaseProduct.snd X (A1_k (k := k))) := by
            simp [Category.assoc]
    _ = productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) := by
          rw [productWithA1_product_right_iso_hom_scheme_snd_a1]
    _ = overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.snd X (A1_k (k := k)) := by
          rw [productWithA1_product_right_iso_inv_scheme_snd_eq]

@[simp, reassoc] private theorem productWithA1_product_right_iso_inv_hom_toProductSource
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
        productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.fst (productWithA1 X) Y =
      overBaseProduct.fst (productWithA1 X) Y := by
  apply Limits.pullback.hom_ext
  · simpa only [Category.assoc] using
      productWithA1_product_right_iso_inv_hom_fst (k := k) X Y
  · simpa only [Category.assoc] using
      productWithA1_product_right_iso_inv_hom_a1 (k := k) X Y

set_option maxHeartbeats 20000000 in
noncomputable def productWithA1_product_right_iso
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1 (overBaseProductObject X Y) ≅
      overBaseProductObject (productWithA1 X) Y where
  hom :=
    { hom :=
        productWithA1_product_right_iso_hom_scheme (k := k) X Y
      over := by
        simpa [productWithA1, overBaseProductObject, Category.assoc] using
          congrArg
            (fun z => z ≫ X.structMap)
            (productWithA1_product_right_iso_hom_scheme_fst (k := k) X Y) }
  inv :=
    { hom :=
        productWithA1_product_right_iso_inv_scheme (k := k) X Y
      over := by
        change productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
            overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
            overBaseProduct.fst X Y ≫ X.structMap =
          overBaseProduct.fst (productWithA1 X) Y ≫
            overBaseProduct.fst X (A1_k (k := k)) ≫ X.structMap
        simpa [productWithA1, overBaseProductObject, Category.assoc] using
          congrArg
            (fun z => z ≫ X.structMap)
            (productWithA1_product_right_iso_inv_scheme_fst_eq (k := k) X Y) }
  hom_inv_id := by
    apply Boundary.SmOverHom.ext
    apply Limits.pullback.hom_ext
    · change productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
          productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
          overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) =
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k))
      simpa only [Category.assoc] using
        productWithA1_product_right_iso_hom_inv_toBaseProduct (k := k) X Y
    · change productWithA1_product_right_iso_hom_scheme (k := k) X Y ≫
          productWithA1_product_right_iso_inv_scheme (k := k) X Y ≫
          overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) =
        overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k))
      simpa only [Category.assoc] using
        productWithA1_product_right_iso_hom_inv_snd (k := k) X Y
  inv_hom_id := by
    apply Boundary.SmOverHom.ext
    apply Limits.pullback.hom_ext
    · exact productWithA1_product_right_iso_inv_hom_toProductSource (k := k) X Y
    · exact productWithA1_product_right_iso_inv_hom_snd (k := k) X Y

set_option maxHeartbeats 20000000 in
@[reassoc] theorem productWithA1_product_right_iso_hom_fst
    (X Y : Geometry.SmSchemeOver k) :
    (productWithA1_product_right_iso (k := k) X Y).hom.hom ≫
        overBaseProduct.fst (productWithA1 X) Y ≫
        overBaseProduct.fst X (A1_k (k := k)) =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y := by
  simpa [productWithA1_product_right_iso] using
    productWithA1_product_right_iso_hom_scheme_fst (k := k) X Y

set_option maxHeartbeats 20000000 in
@[reassoc] theorem productWithA1_product_right_iso_hom_snd
    (X Y : Geometry.SmSchemeOver k) :
    (productWithA1_product_right_iso (k := k) X Y).hom.hom ≫
        overBaseProduct.snd (productWithA1 X) Y =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y := by
  simpa [productWithA1_product_right_iso] using
    productWithA1_product_right_iso_hom_scheme_snd (k := k) X Y

/-- Reassociate the affine-line factor to the left:

`(X ×_k Y) ×_k A¹ ≅ X ×_k (Y ×_k A¹)`.
-/
private noncomputable def productWithA1_product_left_iso_hom_scheme
    (X Y : Geometry.SmSchemeOver k) :
    (productWithA1 (overBaseProductObject X Y)).scheme ⟶
      (overBaseProductObject X (productWithA1 Y)).scheme :=
  ((pullback.congrHom
      (by
        simpa [overBaseProductObject, overBaseProduct] using
          (pullback.condition (f := X.structMap) (g := Y.structMap)))
      rfl) ≪≫
    (pullbackRightPullbackFstIso Y.structMap (A1_k (k := k)).structMap
      (overBaseProduct.snd X Y)).symm ≪≫
    pullbackLeftPullbackSndIso X.structMap Y.structMap
      (overBaseProduct.fst Y (A1_k (k := k)))).hom

private noncomputable def productWithA1_product_left_iso_inv_scheme
    (X Y : Geometry.SmSchemeOver k) :
    (overBaseProductObject X (productWithA1 Y)).scheme ⟶
      (productWithA1 (overBaseProductObject X Y)).scheme :=
  ((pullback.congrHom
      (by
        simpa [overBaseProductObject, overBaseProduct] using
          (pullback.condition (f := X.structMap) (g := Y.structMap)))
      rfl) ≪≫
    (pullbackRightPullbackFstIso Y.structMap (A1_k (k := k)).structMap
      (overBaseProduct.snd X Y)).symm ≪≫
    pullbackLeftPullbackSndIso X.structMap Y.structMap
      (overBaseProduct.fst Y (A1_k (k := k)))).inv

set_option maxHeartbeats 20000000 in
@[reassoc] theorem productWithA1_product_left_iso_hom_scheme_fst
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.fst X (productWithA1 Y) =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y := by
  unfold productWithA1_product_left_iso_hom_scheme
  simp [productWithA1, overBaseProductObject, overBaseProduct, Category.assoc]

set_option maxHeartbeats 20000000 in
@[reassoc] theorem productWithA1_product_left_iso_hom_scheme_snd
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.snd X (productWithA1 Y) ≫ overBaseProduct.fst Y (A1_k (k := k)) =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y := by
  unfold productWithA1_product_left_iso_hom_scheme
  simp [productWithA1, overBaseProductObject, overBaseProduct, Category.assoc]

set_option maxHeartbeats 20000000 in
@[reassoc] theorem productWithA1_product_left_iso_hom_scheme_snd_a1
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.snd X (productWithA1 Y) ≫ overBaseProduct.snd Y (A1_k (k := k)) =
      overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) := by
  unfold productWithA1_product_left_iso_hom_scheme
  simp [productWithA1, overBaseProductObject, overBaseProduct, Category.assoc]

@[simp, reassoc] private theorem productWithA1_product_left_iso_inv_scheme_fst
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y =
      overBaseProduct.fst X (productWithA1 Y) := by
  simp [productWithA1_product_left_iso_inv_scheme, productWithA1, overBaseProductObject,
    overBaseProduct, Category.assoc]

@[simp, reassoc] private theorem productWithA1_product_left_iso_inv_scheme_snd
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) =
      overBaseProduct.snd X (productWithA1 Y) ≫ overBaseProduct.snd Y (A1_k (k := k)) := by
  simp [productWithA1_product_left_iso_inv_scheme, productWithA1, overBaseProductObject,
    overBaseProduct, Category.assoc]

@[simp, reassoc] private theorem productWithA1_product_left_iso_inv_scheme_base_snd
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y =
      overBaseProduct.snd X (productWithA1 Y) ≫
        overBaseProduct.fst Y (A1_k (k := k)) := by
  simp [productWithA1_product_left_iso_inv_scheme, productWithA1, overBaseProductObject,
    overBaseProduct, Category.assoc]

@[simp, reassoc] private theorem productWithA1_product_left_iso_hom_inv_fst
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y := by
  calc
    productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y =
      productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        (productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
          overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
          overBaseProduct.fst X Y) := by simp [Category.assoc]
    _ = productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.fst X (productWithA1 Y) := by
          simpa only [Category.assoc] using
            congrArg
              (fun z =>
                productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫ z)
              (productWithA1_product_left_iso_inv_scheme_fst (k := k) X Y)
    _ = overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y := by
          rw [productWithA1_product_left_iso_hom_scheme_fst]

@[simp, reassoc] private theorem productWithA1_product_left_iso_hom_inv_snd
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) =
      overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) := by
  calc
    productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) =
      productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        (productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
          overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k))) := by
          simp [Category.assoc]
    _ = productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.snd X (productWithA1 Y) ≫
        overBaseProduct.snd Y (A1_k (k := k)) := by
          simpa only [Category.assoc] using
            congrArg
              (fun z =>
                productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫ z)
              (productWithA1_product_left_iso_inv_scheme_snd (k := k) X Y)
    _ = overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) := by
          rw [productWithA1_product_left_iso_hom_scheme_snd_a1]

@[simp, reassoc] private theorem productWithA1_product_left_iso_hom_inv_toBaseProduct
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) := by
  apply Limits.pullback.hom_ext
  · change productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y
    simpa only [Category.assoc] using
      productWithA1_product_left_iso_hom_inv_fst (k := k) X Y
  · change productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y
    calc
      productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
          productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
          overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
          overBaseProduct.snd X Y =
        productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
          (productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
            overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
            overBaseProduct.snd X Y) := by
              simp [Category.assoc]
      _ = productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
          overBaseProduct.snd X (productWithA1 Y) ≫
          overBaseProduct.fst Y (A1_k (k := k)) := by
            rw [productWithA1_product_left_iso_inv_scheme_base_snd]
      _ = overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
          overBaseProduct.snd X Y := by
            rw [productWithA1_product_left_iso_hom_scheme_snd]

@[simp, reassoc] private theorem productWithA1_product_left_iso_inv_hom_fst
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.fst X (productWithA1 Y) =
      overBaseProduct.fst X (productWithA1 Y) := by
  calc
    productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.fst X (productWithA1 Y) =
      productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        (productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
          overBaseProduct.fst X (productWithA1 Y)) := by simp [Category.assoc]
    _ = productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y := by
          simpa only [Category.assoc] using
            congrArg
              (fun z =>
                productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫ z)
              (productWithA1_product_left_iso_hom_scheme_fst (k := k) X Y)
    _ = overBaseProduct.fst X (productWithA1 Y) := by
          rw [productWithA1_product_left_iso_inv_scheme_fst]

@[simp, reassoc] private theorem productWithA1_product_left_iso_inv_hom_snd
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.snd X (productWithA1 Y) ≫
        overBaseProduct.fst Y (A1_k (k := k)) =
      overBaseProduct.snd X (productWithA1 Y) ≫
        overBaseProduct.fst Y (A1_k (k := k)) := by
  calc
    productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.snd X (productWithA1 Y) ≫
        overBaseProduct.fst Y (A1_k (k := k)) =
      productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        (productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
          overBaseProduct.snd X (productWithA1 Y) ≫
          overBaseProduct.fst Y (A1_k (k := k))) := by simp [Category.assoc]
    _ = productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y := by
          simpa only [Category.assoc] using
            congrArg
              (fun z =>
                productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫ z)
              (productWithA1_product_left_iso_hom_scheme_snd (k := k) X Y)
    _ = overBaseProduct.snd X (productWithA1 Y) ≫
        overBaseProduct.fst Y (A1_k (k := k)) := by
          rw [productWithA1_product_left_iso_inv_scheme_base_snd]

@[simp, reassoc] private theorem productWithA1_product_left_iso_inv_hom_a1
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.snd X (productWithA1 Y) ≫
        overBaseProduct.snd Y (A1_k (k := k)) =
      overBaseProduct.snd X (productWithA1 Y) ≫
        overBaseProduct.snd Y (A1_k (k := k)) := by
  calc
    productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.snd X (productWithA1 Y) ≫
        overBaseProduct.snd Y (A1_k (k := k)) =
      productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        (productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
          overBaseProduct.snd X (productWithA1 Y) ≫
          overBaseProduct.snd Y (A1_k (k := k))) := by
            simp [Category.assoc]
    _ = productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) := by
          rw [productWithA1_product_left_iso_hom_scheme_snd_a1]
    _ = overBaseProduct.snd X (productWithA1 Y) ≫
        overBaseProduct.snd Y (A1_k (k := k)) := by
          rw [productWithA1_product_left_iso_inv_scheme_snd]

@[simp, reassoc] private theorem productWithA1_product_left_iso_inv_hom_toProductSource
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
        productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
        overBaseProduct.snd X (productWithA1 Y) =
      overBaseProduct.snd X (productWithA1 Y) := by
  refine Limits.pullback.hom_ext ?_ ?_
  · exact productWithA1_product_left_iso_inv_hom_snd (k := k) X Y
  · exact productWithA1_product_left_iso_inv_hom_a1 (k := k) X Y

set_option maxHeartbeats 20000000 in
noncomputable def productWithA1_product_left_iso
    (X Y : Geometry.SmSchemeOver k) :
    productWithA1 (overBaseProductObject X Y) ≅
      overBaseProductObject X (productWithA1 Y) where
  hom :=
    { hom :=
        productWithA1_product_left_iso_hom_scheme (k := k) X Y
      over := by
        change productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
            overBaseProduct.fst X (productWithA1 Y) ≫ X.structMap =
          overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
            overBaseProduct.fst X Y ≫ X.structMap
        rw [productWithA1_product_left_iso_hom_scheme_fst]
        simp [productWithA1, overBaseProductObject, Category.assoc] }
  inv :=
    { hom :=
        productWithA1_product_left_iso_inv_scheme (k := k) X Y
      over := by
        change productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
            overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
            overBaseProduct.fst X Y ≫ X.structMap =
          overBaseProduct.fst X (productWithA1 Y) ≫ X.structMap
        rw [productWithA1_product_left_iso_inv_scheme_fst]
        simp [productWithA1, overBaseProductObject, Category.assoc] }
  hom_inv_id := by
    apply Boundary.SmOverHom.ext
    apply Limits.pullback.hom_ext
    · change productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
          productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
          overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) =
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k))
      simpa only [Category.assoc] using
        productWithA1_product_left_iso_hom_inv_toBaseProduct (k := k) X Y
    · change productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
          productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
          overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k)) =
        overBaseProduct.snd (overBaseProductObject X Y) (A1_k (k := k))
      simpa only [Category.assoc] using
        productWithA1_product_left_iso_hom_inv_snd (k := k) X Y
  inv_hom_id := by
    apply Boundary.SmOverHom.ext
    apply Limits.pullback.hom_ext
    · change productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
          productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
          overBaseProduct.fst X (productWithA1 Y) =
        overBaseProduct.fst X (productWithA1 Y)
      simpa only [Category.assoc] using
        productWithA1_product_left_iso_inv_hom_fst (k := k) X Y
    · change productWithA1_product_left_iso_inv_scheme (k := k) X Y ≫
          productWithA1_product_left_iso_hom_scheme (k := k) X Y ≫
          overBaseProduct.snd X (productWithA1 Y) =
        overBaseProduct.snd X (productWithA1 Y)
      simpa only [Category.assoc] using
        productWithA1_product_left_iso_inv_hom_toProductSource (k := k) X Y

set_option maxHeartbeats 20000000 in
@[reassoc] theorem productWithA1_product_left_iso_hom_fst
    (X Y : Geometry.SmSchemeOver k) :
    (productWithA1_product_left_iso (k := k) X Y).hom.hom ≫
        overBaseProduct.fst X (productWithA1 Y) =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.fst X Y := by
  simpa [productWithA1_product_left_iso] using
    productWithA1_product_left_iso_hom_scheme_fst (k := k) X Y

set_option maxHeartbeats 20000000 in
@[reassoc] theorem productWithA1_product_left_iso_hom_snd
    (X Y : Geometry.SmSchemeOver k) :
    (productWithA1_product_left_iso (k := k) X Y).hom.hom ≫
        overBaseProduct.snd X (productWithA1 Y) ≫
        overBaseProduct.fst Y (A1_k (k := k)) =
      overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) ≫
        overBaseProduct.snd X Y := by
  simpa [productWithA1_product_left_iso] using
    productWithA1_product_left_iso_hom_scheme_snd (k := k) X Y

/-- Under the right reassociation isomorphism, the ordinary projection
`(X × A¹) × Y → X × Y` transports to the usual `A¹` projection
`(X × Y) × A¹ → X × Y`. -/
theorem productWithA1_product_right_iso_hom_comp_projection
    (X Y : Geometry.SmSchemeOver k) :
    (productWithA1_product_right_iso (k := k) X Y).hom.hom ≫
      (overBaseProductMap (projectionToBase X) (𝟙 Y)).hom =
        (projectionToBase (overBaseProductObject X Y)).hom := by
  apply Limits.pullback.hom_ext
  · change ((productWithA1_product_right_iso (k := k) X Y).hom.hom ≫
        (overBaseProductMap (projectionToBase X) (𝟙 Y)).hom) ≫
        overBaseProduct.fst X Y =
      (projectionToBase (overBaseProductObject X Y)).hom ≫
        overBaseProduct.fst X Y
    simpa [projectionToBase, overBaseProductMap, Category.assoc] using
      productWithA1_product_right_iso_hom_fst (k := k) X Y
  · change ((productWithA1_product_right_iso (k := k) X Y).hom.hom ≫
        (overBaseProductMap (projectionToBase X) (𝟙 Y)).hom) ≫
        overBaseProduct.snd X Y =
      (projectionToBase (overBaseProductObject X Y)).hom ≫
        overBaseProduct.snd X Y
    simpa [projectionToBase, overBaseProductMap, Category.assoc] using
      productWithA1_product_right_iso_hom_snd (k := k) X Y

/-- Under the left reassociation isomorphism, the ordinary projection
`X × (Y × A¹) → X × Y` transports to the usual `A¹` projection
`(X × Y) × A¹ → X × Y`. -/
theorem productWithA1_product_left_iso_hom_comp_projection
    (X Y : Geometry.SmSchemeOver k) :
    (productWithA1_product_left_iso (k := k) X Y).hom.hom ≫
      (overBaseProductMap (𝟙 X) (projectionToBase Y)).hom =
        (projectionToBase (overBaseProductObject X Y)).hom := by
  apply Limits.pullback.hom_ext
  · change ((productWithA1_product_left_iso (k := k) X Y).hom.hom ≫
        (overBaseProductMap (𝟙 X) (projectionToBase Y)).hom) ≫
        overBaseProduct.fst X Y =
      (projectionToBase (overBaseProductObject X Y)).hom ≫
        overBaseProduct.fst X Y
    simpa [projectionToBase, overBaseProductMap, Category.assoc] using
      productWithA1_product_left_iso_hom_fst (k := k) X Y
  · change ((productWithA1_product_left_iso (k := k) X Y).hom.hom ≫
        (overBaseProductMap (𝟙 X) (projectionToBase Y)).hom) ≫
        overBaseProduct.snd X Y =
      (projectionToBase (overBaseProductObject X Y)).hom ≫
        overBaseProduct.snd X Y
    simpa [projectionToBase, overBaseProductMap, Category.assoc] using
      productWithA1_product_left_iso_hom_snd (k := k) X Y

/-- The right-product projection is exactly the transported `A¹` projection on
`X ×_k Y`. -/
theorem overBaseProductMap_projectionToBase_right_eq
    (X Y : Geometry.SmSchemeOver k) :
    overBaseProductMap (projectionToBase X) (𝟙 Y) =
      (productWithA1_product_right_iso (k := k) X Y).inv ≫
        projectionToBase (overBaseProductObject X Y) := by
  apply Boundary.SmOverHom.ext
  apply Limits.pullback.hom_ext
  · change (overBaseProductMap (projectionToBase X) (𝟙 Y)).hom ≫
        overBaseProduct.fst X Y =
      ((productWithA1_product_right_iso (k := k) X Y).inv ≫
          projectionToBase (overBaseProductObject X Y)).hom ≫
        overBaseProduct.fst X Y
    simpa [projectionToBase, overBaseProductMap, Category.assoc] using
      (productWithA1_product_right_iso_inv_scheme_fst_eq (k := k) X Y).symm
  · change (overBaseProductMap (projectionToBase X) (𝟙 Y)).hom ≫
        overBaseProduct.snd X Y =
      ((productWithA1_product_right_iso (k := k) X Y).inv ≫
          projectionToBase (overBaseProductObject X Y)).hom ≫
        overBaseProduct.snd X Y
    simpa [projectionToBase, overBaseProductMap, Category.assoc] using
      (productWithA1_product_right_iso_inv_scheme_base_snd_eq (k := k) X Y).symm

/-- The left-product projection is exactly the transported `A¹` projection on
`X ×_k Y`. -/
theorem overBaseProductMap_projectionToBase_left_eq
    (X Y : Geometry.SmSchemeOver k) :
    overBaseProductMap (𝟙 X) (projectionToBase Y) =
      (productWithA1_product_left_iso (k := k) X Y).inv ≫
        projectionToBase (overBaseProductObject X Y) := by
  apply Boundary.SmOverHom.ext
  apply Limits.pullback.hom_ext
  · change (overBaseProductMap (𝟙 X) (projectionToBase Y)).hom ≫
        overBaseProduct.fst X Y =
      ((productWithA1_product_left_iso (k := k) X Y).inv ≫
          projectionToBase (overBaseProductObject X Y)).hom ≫
        overBaseProduct.fst X Y
    simpa [projectionToBase, overBaseProductMap, Category.assoc] using
      (productWithA1_product_left_iso_inv_scheme_fst (k := k) X Y).symm
  · change (overBaseProductMap (𝟙 X) (projectionToBase Y)).hom ≫
        overBaseProduct.snd X Y =
      ((productWithA1_product_left_iso (k := k) X Y).inv ≫
          projectionToBase (overBaseProductObject X Y)).hom ≫
        overBaseProduct.snd X Y
    simpa [projectionToBase, overBaseProductMap, Category.assoc] using
      (productWithA1_product_left_iso_inv_scheme_base_snd (k := k) X Y).symm

/-- Right-associated transport of the `A1`-projection along
`((X × A1) × Y) ≅ ((X × Y) × A1)`. This is the geometric map whose graph is
the expected external product of the projection `X × A1 ⟶ X` with `id_Y`. -/
def a1ProjectionProductRightTransport
    (X Y : Geometry.SmSchemeOver k) :
    overBaseProductObject (productWithA1 X) Y ⟶ overBaseProductObject X Y :=
  (productWithA1_product_right_iso (k := k) X Y).inv ≫
    projectionToBase (overBaseProductObject X Y)

@[simp, reassoc] theorem a1ProjectionProductRightTransport_hom
    (X Y : Geometry.SmSchemeOver k) :
    (a1ProjectionProductRightTransport X Y).hom =
      (productWithA1_product_right_iso (k := k) X Y).inv.hom ≫
        overBaseProduct.fst (overBaseProductObject X Y) (A1_k (k := k)) := by
  rfl

/-- Left-associated transport of the `A1`-projection along
`((X × Y) × A1) ≅ (X × (Y × A1))`. -/
def a1ProjectionProductLeftTransport
    (X Y : Geometry.SmSchemeOver k) :
    overBaseProductObject X (productWithA1 Y) ⟶ overBaseProductObject X Y :=
  Boundary.overBaseProductMap (Boundary.SmOverHom.id X) (projectionToBase Y)

@[simp] theorem a1ProjectionProductLeftTransport_hom
    (X Y : Geometry.SmSchemeOver k) :
    (a1ProjectionProductLeftTransport X Y).hom =
      Limits.pullback.map X.structMap (productWithA1 Y).structMap
        X.structMap Y.structMap
        (𝟙 X.scheme) (projectionToBase Y).hom (𝟙 (Spec (CommRingCat.of k)))
        (by simp [Category.assoc])
        (by
          change (projectionToBase Y).hom ≫ Y.structMap = (productWithA1 Y).structMap
          rfl) := by
  rfl

end Boundary
