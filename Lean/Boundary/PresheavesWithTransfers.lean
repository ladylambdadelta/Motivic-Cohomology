import Boundary.RationalCompositionCategory
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Opposites
import Mathlib.LinearAlgebra.Prod

/-!
# Presheaves With Transfers

This file packages `ℚ`-linear presheaves with transfers on the rational
finite-correspondence category `SmCorQ(k)`.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

/-- Transparent alias for the target category of `ℚ`-vector spaces. -/
abbrev VectQ := ModuleCat.{u + 1} ℚ

/-- `ℚ`-linear presheaves with transfers on a chosen rational correspondence
category. -/
abbrev PresheafWithTransfers (category : SmCorQ (k := k)) := by
  letI := SmCorQCat category
  exact (Geometry.SmSchemeOver k)ᵒᵖ ⥤ ModuleCat.{u + 1} ℚ

/-- Short public name for presheaves with transfers. -/
abbrev PST (category : SmCorQ (k := k)) :=
  PresheafWithTransfers category

/-- A presheaf with transfers is `ℚ`-linear in the correspondence variable when
it preserves addition and rational scalar multiplication on transfer groups. -/
def IsTransferLinear {category : SmCorQ (k := k)} (F : PST category) : Prop := by
  letI := SmCorQCat category
  exact
    (∀ ⦃X Y : Geometry.SmSchemeOver k⦄
      (f g : SmCorQ.Hom category X Y),
        F.map (Quiver.Hom.op (f + g)) =
          F.map (Quiver.Hom.op f) + F.map (Quiver.Hom.op g)) ∧
    (∀ ⦃X Y : Geometry.SmSchemeOver k⦄
      (a : ℚ) (f : SmCorQ.Hom category X Y),
        F.map (Quiver.Hom.op (a • f)) = a • F.map (Quiver.Hom.op f))

section TransferLinearCokernel

variable [Category (Geometry.SmSchemeOver k)]

/-- Pointwise surjectivity of the cokernel projection in a presheaf category
with values in `ModuleCat ℚ`. -/
theorem PST_cokernel_app_surjective
    {F G : (Geometry.SmSchemeOver k)ᵒᵖ ⥤ ModuleCat.{u + 1} ℚ}
    (f : F ⟶ G)
    [Limits.HasCokernel f]
    (X : (Geometry.SmSchemeOver k)ᵒᵖ) :
    Function.Surjective ((Limits.cokernel.π f).app X) := by
  have hπ : Epi (Limits.cokernel.π f) := inferInstance
  have hπX : Epi ((Limits.cokernel.π f).app X) :=
    (NatTrans.epi_iff_epi_app (f := Limits.cokernel.π f)).1 hπ X
  exact (ModuleCat.epi_iff_surjective ((Limits.cokernel.π f).app X)).1 hπX

/-- Naturality of `cokernel.π`, evaluated at an element. -/
theorem PST_cokernel_map_π_apply
    {F G : (Geometry.SmSchemeOver k)ᵒᵖ ⥤ ModuleCat.{u + 1} ℚ}
    (f : F ⟶ G)
    [Limits.HasCokernel f]
    {X Y : (Geometry.SmSchemeOver k)ᵒᵖ}
    (α : X ⟶ Y)
    (y : G.obj X) :
    (Limits.cokernel f).map α ((Limits.cokernel.π f).app X y) =
      (Limits.cokernel.π f).app Y (G.map α y) := by
  have h := DFunLike.congr_fun ((Limits.cokernel.π f).naturality α) y
  exact h.symm

end TransferLinearCokernel

namespace IsTransferLinear

/-- Transfer-linearity is preserved by cokernels in `PST`. -/
theorem of_cokernel
    {category : SmCorQ (k := k)}
    {F G : PST category}
    (f : F ⟶ G)
    [Limits.HasCokernel f]
    (_hF : IsTransferLinear F)
    (hG : IsTransferLinear G) :
    IsTransferLinear (Limits.cokernel f) := by
  letI := SmCorQCat category
  constructor
  · intro X Y a b
    apply LinearMap.ext
    intro x
    rcases PST_cokernel_app_surjective (f := f) (X := Opposite.op Y) x with ⟨y, rfl⟩
    have hG_add_eval :
        G.map (Quiver.Hom.op (a + b)) y =
          (G.map (Quiver.Hom.op a) + G.map (Quiver.Hom.op b)) y :=
      congrArg (fun ψ => ψ y) (hG.1 a b)
    calc
      (Limits.cokernel f).map (Quiver.Hom.op (a + b))
          ((Limits.cokernel.π f).app (Opposite.op Y) y)
          = (Limits.cokernel.π f).app (Opposite.op X)
              (G.map (Quiver.Hom.op (a + b)) y) :=
              PST_cokernel_map_π_apply (f := f) (α := Quiver.Hom.op (a + b)) y
      _ = (Limits.cokernel.π f).app (Opposite.op X)
            ((G.map (Quiver.Hom.op a) + G.map (Quiver.Hom.op b)) y) := by
            exact congrArg ((Limits.cokernel.π f).app (Opposite.op X)) hG_add_eval
      _ = (Limits.cokernel.π f).app (Opposite.op X) (G.map (Quiver.Hom.op a) y) +
            (Limits.cokernel.π f).app (Opposite.op X) (G.map (Quiver.Hom.op b) y) := by
            change
              (Limits.cokernel.π f).app (Opposite.op X)
                (G.map (Quiver.Hom.op a) y + G.map (Quiver.Hom.op b) y) =
              (Limits.cokernel.π f).app (Opposite.op X) (G.map (Quiver.Hom.op a) y) +
                (Limits.cokernel.π f).app (Opposite.op X) (G.map (Quiver.Hom.op b) y)
            rw [LinearMap.map_add]
      _ = (Limits.cokernel f).map (Quiver.Hom.op a)
            ((Limits.cokernel.π f).app (Opposite.op Y) y) +
          (Limits.cokernel f).map (Quiver.Hom.op b)
            ((Limits.cokernel.π f).app (Opposite.op Y) y) := by
            rw [← PST_cokernel_map_π_apply (f := f) (α := Quiver.Hom.op a) y,
              ← PST_cokernel_map_π_apply (f := f) (α := Quiver.Hom.op b) y]
      _ =
          ((Limits.cokernel f).map (Quiver.Hom.op a) +
            (Limits.cokernel f).map (Quiver.Hom.op b))
            ((Limits.cokernel.π f).app (Opposite.op Y) y) := by
              rw [LinearMap.add_apply]
  · intro X Y coeff a
    apply LinearMap.ext
    intro x
    rcases PST_cokernel_app_surjective (f := f) (X := Opposite.op Y) x with ⟨y, rfl⟩
    have hG_smul_eval :
        G.map (Quiver.Hom.op (coeff • a)) y =
          (coeff • G.map (Quiver.Hom.op a)) y :=
      congrArg (fun ψ => ψ y) (hG.2 coeff a)
    calc
      (Limits.cokernel f).map (Quiver.Hom.op (coeff • a))
          ((Limits.cokernel.π f).app (Opposite.op Y) y)
          = (Limits.cokernel.π f).app (Opposite.op X)
              (G.map (Quiver.Hom.op (coeff • a)) y) :=
              PST_cokernel_map_π_apply (f := f) (α := Quiver.Hom.op (coeff • a)) y
      _ = (Limits.cokernel.π f).app (Opposite.op X)
            ((coeff • G.map (Quiver.Hom.op a)) y) := by
            exact congrArg ((Limits.cokernel.π f).app (Opposite.op X)) hG_smul_eval
      _ = coeff • (Limits.cokernel.π f).app (Opposite.op X)
            (G.map (Quiver.Hom.op a) y) := by
            change
              (Limits.cokernel.π f).app (Opposite.op X)
                (coeff • G.map (Quiver.Hom.op a) y) =
              coeff • (Limits.cokernel.π f).app (Opposite.op X) (G.map (Quiver.Hom.op a) y)
            rw [LinearMap.map_smul]
      _ = coeff • (Limits.cokernel f).map (Quiver.Hom.op a)
            ((Limits.cokernel.π f).app (Opposite.op Y) y) := by
            rw [PST_cokernel_map_π_apply (f := f) (α := Quiver.Hom.op a) y]
      _ = (coeff • (Limits.cokernel f).map (Quiver.Hom.op a))
            ((Limits.cokernel.π f).app (Opposite.op Y) y) := by
        rw [LinearMap.smul_apply]

end IsTransferLinear



/-- Bundled presheaves with transfers that are `ℚ`-linear in the correspondence
variable. -/
abbrev LinearPST (category : SmCorQ (k := k)) :=
  { F : PST category // IsTransferLinear F }

namespace LinearPST

/-- Forget the linearity proof and view a bundled linear presheaf with
transfers as an ordinary presheaf with transfers. -/
abbrev toPST {category : SmCorQ (k := k)}
    (F : LinearPST category) : PST category :=
  F.1

instance {category : SmCorQ (k := k)} : Category (LinearPST category) := by
  letI := SmCorQCat category
  exact InducedCategory.category LinearPST.toPST

/-- Morphisms in `LinearPST` are exactly ordinary `PST` morphisms between the
underlying presheaves. -/
@[simp] theorem Hom_def {category : SmCorQ (k := k)}
    (F G : LinearPST category) :
    (F ⟶ G) = (F.toPST ⟶ G.toPST) :=
  rfl

/-- The forgetful functor from bundled linear presheaves with transfers to
ordinary presheaves with transfers. -/
def forgetToPST {category : SmCorQ (k := k)} : LinearPST category ⥤ PST category := by
  letI := SmCorQCat category
  exact inducedFunctor LinearPST.toPST

@[simp] theorem forgetToPST_obj {category : SmCorQ (k := k)}
    (F : LinearPST category) :
    (forgetToPST (category := category)).obj F = F.toPST :=
  rfl

@[simp] theorem forgetToPST_map {category : SmCorQ (k := k)}
    {F G : LinearPST category} (f : F ⟶ G) :
    (forgetToPST (category := category)).map f = f :=
  rfl

instance forgetToPST_full {category : SmCorQ (k := k)} :
    (forgetToPST (category := category)).Full := by
  letI := SmCorQCat category
  change (inducedFunctor LinearPST.toPST).Full
  infer_instance

instance forgetToPST_faithful {category : SmCorQ (k := k)} :
    (forgetToPST (category := category)).Faithful := by
  letI := SmCorQCat category
  change (inducedFunctor LinearPST.toPST).Faithful
  infer_instance

end LinearPST

/-- The representable `ℚ`-linear presheaf with transfers attached to an object
of `SmCorQ(k)`. -/
def Qtr {category : SmCorQ (k := k)}
    (X : Geometry.SmSchemeOver k) : PST category := by
  letI := SmCorQCat category
  exact
    { obj := fun Y => ModuleCat.of ℚ (SmCorQ.Hom category Y.unop X)
      map := fun f =>
        { toFun := fun g => category.comp f.unop g
          map_add' := by
            intro g h
            exact category.comp_add f.unop g h
          map_smul' := by
            intro coeff g
            exact category.comp_smul coeff f.unop g }
      map_id := by
        intro Y
        apply LinearMap.ext
        intro g
        exact category.id_comp g
      map_comp := by
        intro Y Z W f g
        apply LinearMap.ext
        intro h
        exact category.assoc g.unop f.unop h }

/-- Representables are `ℚ`-linear in the correspondence variable. -/
theorem Qtr_isTransferLinear {category : SmCorQ (k := k)}
    (X : Geometry.SmSchemeOver k) :
    IsTransferLinear (Qtr (category := category) X) := by
  letI := SmCorQCat category
  constructor
  · intro Y Z f g
    apply LinearMap.ext
    intro h
    change category.comp (f + g) h = category.comp f h + category.comp g h
    exact category.add_comp f g h
  · intro Y Z a f
    apply LinearMap.ext
    intro h
    change category.comp (a • f) h = a • category.comp f h
    exact category.smul_comp a f h

/-- The representable presheaf with transfers, viewed as a bundled linear
presheaf. -/
def QtrLinear {category : SmCorQ (k := k)}
    (X : Geometry.SmSchemeOver k) : LinearPST category :=
  ⟨Qtr (category := category) X, Qtr_isTransferLinear (category := category) X⟩

/-- A correspondence induces a natural transformation between the associated
canonical representable transfer presheaves. -/
def QtrMap {category : SmCorQ (k := k)}
    {X Y : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category X Y) :
    Qtr (category := category) X ⟶ Qtr (category := category) Y := by
  letI := SmCorQCat category
  exact
    { app := fun Z =>
        { toFun := fun g => category.comp g f
          map_add' := by
            intro g h
            exact category.add_comp g h f
          map_smul' := by
            intro coeff g
            exact category.smul_comp coeff g f }
      naturality := by
        intro Z W g
        apply LinearMap.ext
        intro h
        exact category.assoc g.unop h f }

/-- Evaluation at the identity correspondence realizes the representable/Yoneda
bridge for bundled linear presheaves with transfers. The morphism space is
spelled in the underlying `PST` category because `LinearPST` currently carries
only its bundled proof data. -/
def QtrLinear_yoneda {category : SmCorQ (k := k)}
    (F : LinearPST category) (X : Geometry.SmSchemeOver k) :
    letI := SmCorQCat category
    ((QtrLinear (category := category) X).toPST ⟶ F.toPST) ≃
      ↥(F.toPST.obj (Opposite.op X)) := by
  letI := SmCorQCat category
  refine
    { toFun := fun η => η.app (Opposite.op X) (category.id X)
      invFun := fun x =>
        { app := fun Y =>
            { toFun := fun g => F.toPST.map (Quiver.Hom.op g) x
              map_add' := by
                intro g h
                exact congrArg (fun ψ => ψ x) (F.2.1 g h)
              map_smul' := by
                intro a g
                exact congrArg (fun ψ => ψ x) (F.2.2 a g) }
          naturality := by
            intro Y Z f
            apply LinearMap.ext
            intro g
            change (F.toPST.map ((Quiver.Hom.op g) ≫ f)) x =
              (F.toPST.map f) ((F.toPST.map (Quiver.Hom.op g)) x)
            rw [F.toPST.map_comp]
            rfl }
      left_inv := by
        intro η
        ext Y g
        change F.toPST.map (Quiver.Hom.op g) (η.app (Opposite.op X) (category.id X)) =
          η.app Y g
        have hη := congrArg (fun ψ => ψ (category.id X)) (η.naturality (Quiver.Hom.op g))
        have hη' :
            (η.app (Opposite.op X) ≫ F.toPST.map (Quiver.Hom.op g)) (category.id X) =
              (((QtrLinear (category := category) X).toPST.map (Quiver.Hom.op g)) ≫
                η.app Y) (category.id X) := by
          exact hη.symm
        calc
          F.toPST.map (Quiver.Hom.op g) (η.app (Opposite.op X) (category.id X))
            = (η.app (Opposite.op X) ≫ F.toPST.map (Quiver.Hom.op g)) (category.id X) := by
                rfl
          _ = (((QtrLinear (category := category) X).toPST.map (Quiver.Hom.op g)) ≫
                η.app Y) (category.id X) := hη'
          _ = η.app Y (((QtrLinear (category := category) X).toPST.map (Quiver.Hom.op g))
                (category.id X)) := by
                rfl
          _ = η.app Y (category.comp g (category.id X)) := by
                rfl
          _ = η.app Y g := by rw [category.comp_id]
      right_inv := by
        intro x
        change F.toPST.map (𝟙 (Opposite.op X)) x = x
        rw [F.toPST.map_id]
        rfl }

/-- Under the representable/Yoneda bridge, precomposition by `QtrMap α`
corresponds to the value map induced by `α`. -/
theorem QtrLinear_yoneda_naturality {category : SmCorQ (k := k)}
    (F : LinearPST category)
    {X Y : Geometry.SmSchemeOver k}
    (α : SmCorQ.Hom category X Y) :
    letI := SmCorQCat category
    ∀ (η : (QtrLinear (category := category) Y).toPST ⟶ F.toPST),
      QtrLinear_yoneda F X ((QtrMap (category := category) α) ≫ η) =
        F.toPST.map (Quiver.Hom.op α) (QtrLinear_yoneda F Y η) := by
  letI := SmCorQCat category
  intro η
  change
    η.app (Opposite.op X) (category.comp (category.id X) α) =
      F.toPST.map (Quiver.Hom.op α) (η.app (Opposite.op Y) (category.id Y))
  have hη := congrArg (fun ψ => ψ (category.id Y)) (η.naturality (Quiver.Hom.op α))
  have hη' :
      (((QtrLinear (category := category) Y).toPST.map (Quiver.Hom.op α)) ≫
        η.app (Opposite.op X)) (category.id Y) =
          (η.app (Opposite.op Y) ≫ F.toPST.map (Quiver.Hom.op α)) (category.id Y) := by
    exact hη
  calc
    η.app (Opposite.op X) (category.comp (category.id X) α)
      = η.app (Opposite.op X) α := by rw [category.id_comp]
    _ = η.app (Opposite.op X) (category.comp α (category.id Y)) := by
      exact congrArg (η.app (Opposite.op X)) (Eq.symm (category.comp_id α))
    _ = η.app (Opposite.op X)
          (((QtrLinear (category := category) Y).toPST.map (Quiver.Hom.op α))
            (category.id Y)) := by
          rfl
    _ = (((QtrLinear (category := category) Y).toPST.map (Quiver.Hom.op α)) ≫
          η.app (Opposite.op X)) (category.id Y) := by
          rfl
    _ = (η.app (Opposite.op Y) ≫ F.toPST.map (Quiver.Hom.op α)) (category.id Y) := hη'
    _ = F.toPST.map (Quiver.Hom.op α) (η.app (Opposite.op Y) (category.id Y)) := by
          rfl

/-- Pointwise binary direct sum of canonical presheaves with transfers. -/
def directSum {category : SmCorQ (k := k)}
    (F G : PST category) : PST category := by
  letI := SmCorQCat category
  exact
    { obj := fun X => ModuleCat.of ℚ (F.obj X × G.obj X)
      map := fun f =>
        { toFun := fun value => (F.map f value.1, G.map f value.2)
          map_add' := by
            rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
            apply Prod.ext
            · change F.map f (a₁ + b₁) = ((F.map f a₁, G.map f a₂) + (F.map f b₁, G.map f b₂)).1
              simpa using (F.map f).map_add a₁ b₁
            · change G.map f (a₂ + b₂) = ((F.map f a₁, G.map f a₂) + (F.map f b₁, G.map f b₂)).2
              simpa using (G.map f).map_add a₂ b₂
          map_smul' := by
            rintro coeff ⟨fst, snd⟩
            apply Prod.ext
            · change F.map f (coeff • fst) = (coeff • (F.map f fst, G.map f snd)).1
              simpa using (F.map f).map_smul coeff fst
            · change G.map f (coeff • snd) = (coeff • (F.map f fst, G.map f snd)).2
              simpa using (G.map f).map_smul coeff snd }
      map_id := by
        intro X
        apply LinearMap.ext
        rintro ⟨fst, snd⟩
        apply Prod.ext
        · change (F.map (𝟙 X)) fst = fst
          simpa using DFunLike.congr_fun (F.map_id X) fst
        · change (G.map (𝟙 X)) snd = snd
          simpa using DFunLike.congr_fun (G.map_id X) snd
      map_comp := by
        intro X Y Z f g
        apply LinearMap.ext
        rintro ⟨fst, snd⟩
        apply Prod.ext
        · change (F.map (f ≫ g)) fst = (F.map g) ((F.map f) fst)
          simpa using DFunLike.congr_fun (F.map_comp f g) fst
        · change (G.map (f ≫ g)) snd = (G.map g) ((G.map f) snd)
          simpa using DFunLike.congr_fun (G.map_comp f g) snd }

namespace IsTransferLinear

/-- Transfer-linearity is closed under the pointwise direct-sum construction. -/
theorem directSum
    {category : SmCorQ (k := k)}
    {F G : PST category}
    (hF : IsTransferLinear F)
    (hG : IsTransferLinear G) :
    IsTransferLinear (Boundary.directSum F G) := by
  constructor
  · intro X Y α β
    apply LinearMap.ext
    rintro ⟨fst, snd⟩
    apply Prod.ext
    · exact congrArg (fun ψ => ψ fst) (hF.1 α β)
    · exact congrArg (fun ψ => ψ snd) (hG.1 α β)
  · intro X Y coeff α
    apply LinearMap.ext
    rintro ⟨fst, snd⟩
    apply Prod.ext
    · exact congrArg (fun ψ => ψ fst) (hF.2 coeff α)
    · exact congrArg (fun ψ => ψ snd) (hG.2 coeff α)

end IsTransferLinear

end

end Boundary
