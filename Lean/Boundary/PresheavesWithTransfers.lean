import Boundary.RationalCompositionCategory
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.CategoryTheory.Preadditive.Opposite
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
def IsTransferLinear {category : SmCorQ (k := k)} (F : PST category) := by
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

/-- Pointwise injectivity of the kernel inclusion in a presheaf category with
values in `ModuleCat ℚ`. -/
theorem PST_kernel_app_injective
    {F G : (Geometry.SmSchemeOver k)ᵒᵖ ⥤ ModuleCat.{u + 1} ℚ}
    (f : F ⟶ G)
    [Limits.HasKernel f]
    (X : (Geometry.SmSchemeOver k)ᵒᵖ) :
    Function.Injective ((Limits.kernel.ι f).app X) := by
  have hι : Mono (Limits.kernel.ι f) := inferInstance
  have hιX : Mono ((Limits.kernel.ι f).app X) :=
    (NatTrans.mono_iff_mono_app (f := Limits.kernel.ι f)).1 hι X
  exact (ModuleCat.mono_iff_injective ((Limits.kernel.ι f).app X)).1 hιX

/-- Naturality of `kernel.ι`, evaluated at an element. -/
theorem PST_kernel_map_ι_apply
    {F G : (Geometry.SmSchemeOver k)ᵒᵖ ⥤ ModuleCat.{u + 1} ℚ}
    (f : F ⟶ G)
    [Limits.HasKernel f]
    {X Y : (Geometry.SmSchemeOver k)ᵒᵖ}
    (α : X ⟶ Y)
    (x : (Limits.kernel f).obj X) :
    (Limits.kernel.ι f).app Y ((Limits.kernel f).map α x) =
      F.map α ((Limits.kernel.ι f).app X x) := by
  have h := DFunLike.congr_fun ((Limits.kernel.ι f).naturality α) x
  exact h

end TransferLinearCokernel

namespace IsTransferLinear

/-- Explicit zero object of `PST`, avoiding reliance on zero notation for
functor categories. -/
def zeroPST {category : SmCorQ (k := k)} : PST category := by
  letI := SmCorQCat category
  exact
    { obj := fun _ => ModuleCat.of ℚ PUnit
      map := fun _ => 𝟙 _
      map_id := by
        intro X
        rfl
      map_comp := by
        intro W X Y f g
        rfl }

/-- Transfer-linearity is closed under the zero presheaf. -/
theorem zero
    {category : SmCorQ (k := k)} :
    IsTransferLinear (zeroPST (category := category)) := by
  constructor
  · intro X Y f g
    ext x
    cases x
    rfl
  · intro X Y coeff f
    ext x
    cases x
    rfl

/-- Transfer-linearity is preserved by kernels in `PST`. -/
theorem of_kernel
    {category : SmCorQ (k := k)}
    {F G : PST category}
    (f : F ⟶ G)
    [Limits.HasKernel f]
    (hF : IsTransferLinear F)
    (_hG : IsTransferLinear G) :
    IsTransferLinear (Limits.kernel f) := by
  letI := SmCorQCat category
  constructor
  · intro X Y a b
    apply LinearMap.ext
    intro x
    apply PST_kernel_app_injective (f := f) (X := Opposite.op X)
    calc
      (Limits.kernel.ι f).app (Opposite.op X)
          ((Limits.kernel f).map (Quiver.Hom.op (a + b)) x)
        = F.map (Quiver.Hom.op (a + b))
            ((Limits.kernel.ι f).app (Opposite.op Y) x) :=
            PST_kernel_map_ι_apply (f := f) (α := Quiver.Hom.op (a + b)) x
      _ = (F.map (Quiver.Hom.op a) + F.map (Quiver.Hom.op b))
            ((Limits.kernel.ι f).app (Opposite.op Y) x) := by
            exact congrArg (fun ψ => ψ ((Limits.kernel.ι f).app (Opposite.op Y) x))
              (hF.1 a b)
      _ = F.map (Quiver.Hom.op a) ((Limits.kernel.ι f).app (Opposite.op Y) x) +
            F.map (Quiver.Hom.op b) ((Limits.kernel.ι f).app (Opposite.op Y) x) := by
            rw [LinearMap.add_apply]
      _ = (Limits.kernel.ι f).app (Opposite.op X)
            ((Limits.kernel f).map (Quiver.Hom.op a) x) +
          (Limits.kernel.ι f).app (Opposite.op X)
            ((Limits.kernel f).map (Quiver.Hom.op b) x) := by
            rw [← PST_kernel_map_ι_apply (f := f) (α := Quiver.Hom.op a) x,
              ← PST_kernel_map_ι_apply (f := f) (α := Quiver.Hom.op b) x]
      _ = (Limits.kernel.ι f).app (Opposite.op X)
            (((Limits.kernel f).map (Quiver.Hom.op a) +
              (Limits.kernel f).map (Quiver.Hom.op b)) x) := by
            rw [LinearMap.add_apply]
            rw [LinearMap.map_add]
  · intro X Y coeff a
    apply LinearMap.ext
    intro x
    apply PST_kernel_app_injective (f := f) (X := Opposite.op X)
    calc
      (Limits.kernel.ι f).app (Opposite.op X)
          ((Limits.kernel f).map (Quiver.Hom.op (coeff • a)) x)
        = F.map (Quiver.Hom.op (coeff • a))
            ((Limits.kernel.ι f).app (Opposite.op Y) x) :=
            PST_kernel_map_ι_apply (f := f) (α := Quiver.Hom.op (coeff • a)) x
      _ = (coeff • F.map (Quiver.Hom.op a))
            ((Limits.kernel.ι f).app (Opposite.op Y) x) := by
            exact congrArg (fun ψ => ψ ((Limits.kernel.ι f).app (Opposite.op Y) x))
              (hF.2 coeff a)
      _ = coeff • F.map (Quiver.Hom.op a)
            ((Limits.kernel.ι f).app (Opposite.op Y) x) := by
            rw [LinearMap.smul_apply]
      _ = coeff • (Limits.kernel.ι f).app (Opposite.op X)
            ((Limits.kernel f).map (Quiver.Hom.op a) x) := by
            rw [← PST_kernel_map_ι_apply (f := f) (α := Quiver.Hom.op a) x]
      _ = (Limits.kernel.ι f).app (Opposite.op X)
            ((coeff • (Limits.kernel f).map (Quiver.Hom.op a)) x) := by
            rw [LinearMap.smul_apply]
            change coeff • (Limits.kernel.ι f).app (Opposite.op X)
                ((Limits.kernel f).map (Quiver.Hom.op a) x) =
              (Limits.kernel.ι f).app (Opposite.op X)
                (coeff • (Limits.kernel f).map (Quiver.Hom.op a) x)
            rw [LinearMap.map_smul]

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

/-- The zero presheaf with transfers, bundled as a linear presheaf. -/
def zero {category : SmCorQ (k := k)} : LinearPST category :=
  ⟨IsTransferLinear.zeroPST (category := category),
    IsTransferLinear.zero (category := category)⟩

/-- `LinearPST` inherits its preadditive structure from the underlying functor
category of presheaves with values in `ℚ`-vector spaces. -/
instance preadditive {category : SmCorQ (k := k)} :
    Preadditive (LinearPST category) := by
  letI := SmCorQCat category
  change Preadditive (InducedCategory (PST category) LinearPST.toPST)
  infer_instance

/-- Owner definition exposing the preadditive structure of `LinearPST`.

Downstream construction records consume this named definition rather than relying
on namespace field notation or broad typeclass search. -/
def preadditive_owner {category : SmCorQ (k := k)} :
    Preadditive (LinearPST category) := by
  infer_instance

/-- The forgetful functor from linear presheaves with transfers to ordinary
presheaves with transfers is additive. -/
instance forgetToPST_additive {category : SmCorQ (k := k)} :
    (forgetToPST (category := category)).Additive := by
  letI := SmCorQCat category
  change (inducedFunctor LinearPST.toPST).Additive
  infer_instance

/-- The bundled zero linear presheaf is a zero object of `LinearPST`. -/
theorem zero_isZero {category : SmCorQ (k := k)} :
    Limits.IsZero (zero (category := category)) := by
  letI := SmCorQCat category
  constructor
  · intro F
    refine ⟨{ default := 0, uniq := ?_ }⟩
    intro f
    apply NatTrans.ext
    apply funext
    intro X
    apply LinearMap.ext
    intro x
    cases x
    change (f.app X) 0 = 0
    exact (f.app X).map_zero
  · intro F
    refine ⟨{ default := 0, uniq := ?_ }⟩
    intro f
    apply NatTrans.ext
    apply funext
    intro X
    apply LinearMap.ext
    intro x
    cases f.app X x
    rfl

/-- `LinearPST` has a zero object, constructed by the actual zero presheaf. -/
instance hasZeroObject {category : SmCorQ (k := k)} :
    Limits.HasZeroObject (LinearPST category) :=
  ⟨⟨zero (category := category), zero_isZero (category := category)⟩⟩

end LinearPST

namespace IsTransferLinear

def additiveFunctor {category : SmCorQ (k := k)}
    {F : PST category} (hF : IsTransferLinear F) := by
  letI := SmCorQCat category
  letI := SmCorQCat_preadditive category
  exact
    { map_add := by
        intro X Y f g
        cases X
        cases Y
        exact hF.1 f.unop g.unop :
      F.Additive }

theorem of_additive {category : SmCorQ (k := k)}
    (F : PST category)
    (hF : by
      letI := SmCorQCat category
      letI := SmCorQCat_preadditive category
      exact F.Additive) :
    IsTransferLinear F := by
  letI := SmCorQCat category
  letI := SmCorQCat_preadditive category
  letI := SmCorQCat_linear category
  letI := Boundary.SmCorQCat_op_preadditive category
  letI := Boundary.SmCorQCat_op_linear category
  letI : F.Additive := hF
  letI : F.Linear ℚ := inferInstance
  constructor
  · intro X Y f g
    change
      F.map (Quiver.Hom.op f + Quiver.Hom.op g) =
        F.map (Quiver.Hom.op f) + F.map (Quiver.Hom.op g)
    exact
      (Functor.map_add (F := F)
        (f := Quiver.Hom.op f) (g := Quiver.Hom.op g))
  · intro X Y coeff f
    have hsmul :
        Quiver.Hom.op (coeff • f) =
          coeff • (Quiver.Hom.op f : Opposite.op Y ⟶ Opposite.op X) := by
      apply Quiver.Hom.unop_inj
      change coeff • f = coeff • f
      rfl
    rw [hsmul]
    exact F.map_smul coeff (Quiver.Hom.op f)

end IsTransferLinear

namespace LinearPST

/-- The standard additive-functor category presentation of linear presheaves
with transfers. Since both `SmCorQ` and `ModuleCat ℚ` are `ℚ`-linear,
Mathlib upgrades additive functors to `ℚ`-linear functors automatically. -/
abbrev correspondenceOpposite (category : SmCorQ (k := k)) :=
  (Geometry.SmSchemeOver k)ᵒᵖ

instance correspondenceOpposite_category (category : SmCorQ (k := k)) :
    Category (correspondenceOpposite (k := k) category) := by
  letI := SmCorQCat category
  infer_instance

/-- The additive structure on the opposite correspondence category. -/
instance correspondenceOpposite_preadditive (category : SmCorQ (k := k)) :
    Preadditive (correspondenceOpposite (category := category)) := by
  letI := SmCorQCat category
  exact SmCorQCat_op_preadditive category

/-- The `ℚ`-linear structure on the opposite correspondence category. -/
instance correspondenceOpposite_linear (category : SmCorQ (k := k)) :
    CategoryTheory.Linear ℚ (correspondenceOpposite (category := category)) := by
  letI := SmCorQCat category
  exact SmCorQCat_op_linear category

abbrev asLinearFunctorCategory (category : SmCorQ (k := k)) :=
  letI := SmCorQCat category
  letI := Boundary.SmCorQCat_preadditive category
  letI := Boundary.SmCorQCat_linear category
  letI := SmCorQCat_op_preadditive category
  letI := SmCorQCat_op_linear category
  correspondenceOpposite (category := category) ⥤+ ModuleCat.{u + 1} ℚ

noncomputable def toAsLinearFunctorCategory
    (category : SmCorQ (k := k)) :
    LinearPST category ⥤ asLinearFunctorCategory (category := category) where
  obj F := by
    letI := SmCorQCat category
    letI := SmCorQCat_preadditive category
    letI := SmCorQCat_linear category
    letI := SmCorQCat_op_preadditive category
    letI := SmCorQCat_op_linear category
    letI : F.toPST.Additive := IsTransferLinear.additiveFunctor F.2
    exact AdditiveFunctor.of (C := correspondenceOpposite (category := category))
      (D := ModuleCat.{u + 1} ℚ) F.toPST
  map {F G} f := f
  map_id := by intro F; rfl
  map_comp := by intro F G H f g; rfl

noncomputable def fromAsLinearFunctorCategory
    (category : SmCorQ (k := k)) :
    asLinearFunctorCategory (category := category) ⥤ LinearPST category where
  obj F := by
    letI := SmCorQCat category
    letI := SmCorQCat_preadditive category
    letI := SmCorQCat_linear category
    letI := SmCorQCat_op_preadditive category
    letI := SmCorQCat_op_linear category
    exact ⟨F.1, IsTransferLinear.of_additive F.1 F.2⟩
  map {F G} f := f
  map_id := by intro F; rfl
  map_comp := by intro F G H f g; rfl

@[simp] theorem to_asLinearFunctorCategory_obj
    (category : SmCorQ (k := k)) (F : LinearPST category) :
    ((toAsLinearFunctorCategory (category := category)).obj F).1 = F.toPST := by
  letI := SmCorQCat category
  letI := SmCorQCat_preadditive category
  letI := SmCorQCat_linear category
  letI := SmCorQCat_op_preadditive category
  letI := SmCorQCat_op_linear category
  letI : F.toPST.Additive := IsTransferLinear.additiveFunctor F.2
  rfl

@[simp] theorem from_asLinearFunctorCategory_obj
    (category : SmCorQ (k := k)) (F : asLinearFunctorCategory (category := category)) :
    ((fromAsLinearFunctorCategory (category := category)).obj F).1 = F.1 := by
  rfl

@[simp] theorem to_from_asLinearFunctorCategory_obj
    (category : SmCorQ (k := k)) (F : asLinearFunctorCategory (category := category)) :
    (fromAsLinearFunctorCategory (category := category) ⋙
        toAsLinearFunctorCategory (category := category)).obj F = F := by
  cases F
  rfl

@[simp] theorem from_to_asLinearFunctorCategory_obj
    (category : SmCorQ (k := k)) (F : LinearPST category) :
    (toAsLinearFunctorCategory (category := category) ⋙
        fromAsLinearFunctorCategory (category := category)).obj F = F := by
  cases F
  rfl

/-- Owner bridge from the bundled predicate presentation of `LinearPST` to the
standard additive/`ℚ`-linear functor category presentation. -/
noncomputable def equivAdditiveFunctorCategory
    (category : SmCorQ (k := k)) :
    LinearPST category ≌ asLinearFunctorCategory (category := category) := by
  letI := SmCorQCat category
  letI := Boundary.SmCorQCat_preadditive category
  letI := Boundary.SmCorQCat_linear category
  letI := SmCorQCat_op_preadditive category
  letI := SmCorQCat_op_linear category
  let Phi := toAsLinearFunctorCategory (category := category)
  let Psi := fromAsLinearFunctorCategory (category := category)
  refine
    { functor := Phi
      inverse := Psi
      unitIso := NatIso.ofComponents
        (fun F => eqToIso (LinearPST.from_to_asLinearFunctorCategory_obj (category := category) F).symm)
        (by
          intro F G f
          cases F
          cases G
          rfl)
      counitIso := NatIso.ofComponents
        (fun F => eqToIso (LinearPST.to_from_asLinearFunctorCategory_obj (category := category) F))
        (by
          intro F G f
          cases F
          cases G
          rfl)
      functor_unitIso_comp := by
        intro F
        simp }

end LinearPST

/-- Public owner name for the standard additive/`ℚ`-linear functor category
presentation of `LinearPST`. -/
abbrev LinearPST_as_linear_functor_category
    (category : SmCorQ (k := k)) :=
  LinearPST.asLinearFunctorCategory (category := category)

/-- Public owner equivalence between bundled linear presheaves with transfers
and additive, hence `ℚ`-linear, presheaves on `SmCorQᵒᵖ`. -/
noncomputable def LinearPST_equiv_AdditiveFunctorCategory
    (category : SmCorQ (k := k)) :
    LinearPST category ≌ LinearPST_as_linear_functor_category (category := category) :=
  LinearPST.equivAdditiveFunctorCategory (category := category)

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

@[simp] theorem QtrMap_id {category : SmCorQ (k := k)}
    (X : Geometry.SmSchemeOver k) :
    QtrMap (category := category) (category.id X) =
      𝟙 (Qtr (category := category) X) := by
  letI := SmCorQCat category
  ext Y f
  exact category.comp_id f

theorem QtrMap_comp {category : SmCorQ (k := k)}
    {X Y Z : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category X Y)
    (g : SmCorQ.Hom category Y Z) :
    QtrMap (category := category) (category.comp f g) =
      QtrMap (category := category) f ≫ QtrMap (category := category) g := by
  letI := SmCorQCat category
  ext W h
  exact category.assoc h f g

@[simp] theorem QtrMap_zero {category : SmCorQ (k := k)}
    {X Y : Geometry.SmSchemeOver k} :
    QtrMap (category := category) (0 : SmCorQ.Hom category X Y) = 0 := by
  letI := SmCorQCat category
  ext W h
  exact category.comp_zero h

theorem QtrMap_add {category : SmCorQ (k := k)}
    {X Y : Geometry.SmSchemeOver k}
    (f g : SmCorQ.Hom category X Y) :
    QtrMap (category := category) (f + g) =
      QtrMap (category := category) f + QtrMap (category := category) g := by
  letI := SmCorQCat category
  ext W h
  exact category.comp_add h f g

theorem QtrMap_smul {category : SmCorQ (k := k)}
    {X Y : Geometry.SmSchemeOver k}
    (a : ℚ) (f : SmCorQ.Hom category X Y) :
    QtrMap (category := category) (a • f) =
      a • QtrMap (category := category) f := by
  letI := SmCorQCat category
  ext W h
  exact category.comp_smul a h f

/-- Object-level representable external product: on smooth schemes it is the
representable presheaf of the fiber product over `Spec k`. -/
abbrev QtrExternalProductObj {category : SmCorQ (k := k)}
    [FiniteCorrespondence.CanonicalExternalProductFamily (k := k)]
    (X Y : Geometry.SmSchemeOver k) :
    LinearPST category :=
  QtrLinear (category := category) (overBaseProductObject X Y)

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

namespace LinearPST

/-- The pointwise direct sum of two bundled linear presheaves. -/
def directSum {category : SmCorQ (k := k)}
    (F G : LinearPST category) : LinearPST category :=
  ⟨Boundary.directSum F.toPST G.toPST, IsTransferLinear.directSum F.2 G.2⟩

/-- First projection from the pointwise direct sum of linear presheaves. -/
def directSum_fst {category : SmCorQ (k := k)}
    (F G : LinearPST category) : directSum F G ⟶ F := by
  letI := SmCorQCat category
  exact
    { app := fun X =>
        { toFun := fun value => value.1
          map_add' := by
            intro x y
            rfl
          map_smul' := by
            intro coeff x
            rfl }
      naturality := by
        intro X Y f
        apply LinearMap.ext
        intro x
        rfl }

/-- Second projection from the pointwise direct sum of linear presheaves. -/
def directSum_snd {category : SmCorQ (k := k)}
    (F G : LinearPST category) : directSum F G ⟶ G := by
  letI := SmCorQCat category
  exact
    { app := fun X =>
        { toFun := fun value => value.2
          map_add' := by
            intro x y
            rfl
          map_smul' := by
            intro coeff x
            rfl }
      naturality := by
        intro X Y f
        apply LinearMap.ext
        intro x
        rfl }

/-- Left inclusion into the pointwise direct sum of linear presheaves. -/
def directSum_inl {category : SmCorQ (k := k)}
    (F G : LinearPST category) : F ⟶ directSum F G := by
  letI := SmCorQCat category
  exact
    { app := fun X =>
        { toFun := fun value => (value, 0)
          map_add' := by
            intro x y
            apply Prod.ext
            · change x + y = x + y
              rfl
            · change (0 : G.toPST.obj X) = 0 + 0
              simp
          map_smul' := by
            intro coeff x
            apply Prod.ext
            · change coeff • x = coeff • x
              rfl
            · change (0 : G.toPST.obj X) = coeff • 0
              simp }
      naturality := by
        intro X Y f
        apply LinearMap.ext
        intro x
        apply Prod.ext
        · rfl
        · change (0 : G.toPST.obj Y) = G.toPST.map f 0
          rw [LinearMap.map_zero] }

/-- Right inclusion into the pointwise direct sum of linear presheaves. -/
def directSum_inr {category : SmCorQ (k := k)}
    (F G : LinearPST category) : G ⟶ directSum F G := by
  letI := SmCorQCat category
  exact
    { app := fun X =>
        { toFun := fun value => (0, value)
          map_add' := by
            intro x y
            apply Prod.ext
            · change (0 : F.toPST.obj X) = 0 + 0
              simp
            · change x + y = x + y
              rfl
          map_smul' := by
            intro coeff x
            apply Prod.ext
            · change (0 : F.toPST.obj X) = coeff • 0
              simp
            · change coeff • x = coeff • x
              rfl }
      naturality := by
        intro X Y f
        apply LinearMap.ext
        intro x
        apply Prod.ext
        · change (0 : F.toPST.obj Y) = F.toPST.map f 0
          rw [LinearMap.map_zero]
        · rfl }

@[simp] theorem directSum_inl_fst {category : SmCorQ (k := k)}
    (F G : LinearPST category) :
    directSum_inl F G ≫ directSum_fst F G = 𝟙 F := by
  letI := SmCorQCat category
  apply NatTrans.ext
  apply funext
  intro X
  apply LinearMap.ext
  intro x
  rfl

@[simp] theorem directSum_inl_snd {category : SmCorQ (k := k)}
    (F G : LinearPST category) :
    directSum_inl F G ≫ directSum_snd F G = 0 := by
  letI := SmCorQCat category
  apply NatTrans.ext
  apply funext
  intro X
  apply LinearMap.ext
  intro x
  rfl

@[simp] theorem directSum_inr_fst {category : SmCorQ (k := k)}
    (F G : LinearPST category) :
    directSum_inr F G ≫ directSum_fst F G = 0 := by
  letI := SmCorQCat category
  apply NatTrans.ext
  apply funext
  intro X
  apply LinearMap.ext
  intro x
  rfl

@[simp] theorem directSum_inr_snd {category : SmCorQ (k := k)}
    (F G : LinearPST category) :
    directSum_inr F G ≫ directSum_snd F G = 𝟙 G := by
  letI := SmCorQCat category
  apply NatTrans.ext
  apply funext
  intro X
  apply LinearMap.ext
  intro x
  rfl

/-- The map into a pointwise direct sum induced by two component maps. -/
def directSum_lift {category : SmCorQ (k := k)}
    (S F G : LinearPST category)
    (fst : S ⟶ F) (snd : S ⟶ G) :
    S ⟶ directSum F G := by
  letI := SmCorQCat category
  exact
    { app := fun X =>
        { toFun := fun value => (fst.app X value, snd.app X value)
          map_add' := by
            intro x y
            apply Prod.ext
            · change fst.app X (x + y) = fst.app X x + fst.app X y
              rw [LinearMap.map_add]
            · change snd.app X (x + y) = snd.app X x + snd.app X y
              rw [LinearMap.map_add]
          map_smul' := by
            intro coeff x
            apply Prod.ext
            · change fst.app X (coeff • x) = coeff • fst.app X x
              rw [LinearMap.map_smul]
            · change snd.app X (coeff • x) = coeff • snd.app X x
              rw [LinearMap.map_smul] }
      naturality := by
        intro X Y f
        apply LinearMap.ext
        intro x
        apply Prod.ext
        · exact congrArg (fun φ => φ x) (fst.naturality f)
        · exact congrArg (fun φ => φ x) (snd.naturality f) }

@[simp] theorem directSum_lift_fst {category : SmCorQ (k := k)}
    (S F G : LinearPST category)
    (fst : S ⟶ F) (snd : S ⟶ G) :
    directSum_lift S F G fst snd ≫ directSum_fst F G = fst := by
  letI := SmCorQCat category
  apply NatTrans.ext
  apply funext
  intro X
  apply LinearMap.ext
  intro x
  rfl

@[simp] theorem directSum_lift_snd {category : SmCorQ (k := k)}
    (S F G : LinearPST category)
    (fst : S ⟶ F) (snd : S ⟶ G) :
    directSum_lift S F G fst snd ≫ directSum_snd F G = snd := by
  letI := SmCorQCat category
  apply NatTrans.ext
  apply funext
  intro X
  apply LinearMap.ext
  intro x
  rfl

/-- The map out of a pointwise direct sum induced by two component maps. -/
def directSum_desc {category : SmCorQ (k := k)}
    (F G S : LinearPST category)
    (inl : F ⟶ S) (inr : G ⟶ S) :
    directSum F G ⟶ S := by
  letI := SmCorQCat category
  exact
    { app := fun X =>
        { toFun := fun value => inl.app X value.1 + inr.app X value.2
          map_add' := by
            rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
            change inl.app X (x₁ + y₁) + inr.app X (x₂ + y₂) =
              (inl.app X x₁ + inr.app X x₂) + (inl.app X y₁ + inr.app X y₂)
            rw [LinearMap.map_add, LinearMap.map_add]
            abel
          map_smul' := by
            rintro coeff ⟨x₁, x₂⟩
            change inl.app X (coeff • x₁) + inr.app X (coeff • x₂) =
              coeff • (inl.app X x₁ + inr.app X x₂)
            rw [LinearMap.map_smul, LinearMap.map_smul, smul_add] }
      naturality := by
        intro X Y f
        apply LinearMap.ext
        rintro ⟨x₁, x₂⟩
        change
          inl.app Y (F.toPST.map f x₁) + inr.app Y (G.toPST.map f x₂) =
            S.toPST.map f (inl.app X x₁ + inr.app X x₂)
        rw [LinearMap.map_add]
        have hInl :
            inl.app Y (F.toPST.map f x₁) =
              S.toPST.map f (inl.app X x₁) :=
          congrArg (fun φ => φ x₁) (inl.naturality f)
        have hInr :
            inr.app Y (G.toPST.map f x₂) =
              S.toPST.map f (inr.app X x₂) :=
          congrArg (fun φ => φ x₂) (inr.naturality f)
        rw [hInl, hInr] }

@[simp] theorem directSum_inl_desc {category : SmCorQ (k := k)}
    (F G S : LinearPST category)
    (inl : F ⟶ S) (inr : G ⟶ S) :
    directSum_inl F G ≫ directSum_desc F G S inl inr = inl := by
  letI := SmCorQCat category
  apply NatTrans.ext
  apply funext
  intro X
  apply LinearMap.ext
  intro x
  change inl.app X x + inr.app X 0 = inl.app X x
  rw [LinearMap.map_zero, add_zero]

@[simp] theorem directSum_inr_desc {category : SmCorQ (k := k)}
    (F G S : LinearPST category)
    (inl : F ⟶ S) (inr : G ⟶ S) :
    directSum_inr F G ≫ directSum_desc F G S inl inr = inr := by
  letI := SmCorQCat category
  apply NatTrans.ext
  apply funext
  intro X
  apply LinearMap.ext
  intro x
  change inl.app X 0 + inr.app X x = inr.app X x
  rw [LinearMap.map_zero, zero_add]

/-- The pointwise direct sum as a binary bicone. -/
def directSum_binaryBicone {category : SmCorQ (k := k)}
    (F G : LinearPST category) : BinaryBicone F G where
  pt := directSum F G
  fst := directSum_fst F G
  snd := directSum_snd F G
  inl := directSum_inl F G
  inr := directSum_inr F G
  inl_fst := directSum_inl_fst F G
  inl_snd := directSum_inl_snd F G
  inr_fst := directSum_inr_fst F G
  inr_snd := directSum_inr_snd F G

/-- The pointwise direct sum has the binary-product universal property. -/
def directSum_isLimit {category : SmCorQ (k := k)}
    (F G : LinearPST category) :
    IsLimit (directSum_binaryBicone F G).toCone :=
  BinaryFan.isLimitMk
    (fun s => directSum_lift s.pt F G s.fst s.snd)
    (fun s => directSum_lift_fst s.pt F G s.fst s.snd)
    (fun s => directSum_lift_snd s.pt F G s.fst s.snd)
    (fun s m hfst hsnd => by
      letI := SmCorQCat category
      apply NatTrans.ext
      apply funext
      intro X
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · change (m.app X x).1 = s.fst.app X x
        exact congrArg (fun η => η.app X x) hfst
      · change (m.app X x).2 = s.snd.app X x
        exact congrArg (fun η => η.app X x) hsnd)

/-- The pointwise direct sum has the binary-coproduct universal property. -/
def directSum_isColimit {category : SmCorQ (k := k)}
    (F G : LinearPST category) :
    IsColimit (directSum_binaryBicone F G).toCocone :=
  BinaryCofan.isColimitMk
    (fun s => directSum_desc F G s.pt s.inl s.inr)
    (fun s => directSum_inl_desc F G s.pt s.inl s.inr)
    (fun s => directSum_inr_desc F G s.pt s.inl s.inr)
    (fun s m hinl hinr => by
      letI := SmCorQCat category
      apply NatTrans.ext
      apply funext
      intro X
      apply LinearMap.ext
      rintro ⟨x₁, x₂⟩
      have hInl :
          m.app X (x₁, 0) =
            (directSum_desc F G s.pt s.inl s.inr).app X (x₁, 0) := by
        have h :
            directSum_inl F G ≫ m =
              directSum_inl F G ≫ directSum_desc F G s.pt s.inl s.inr := by
          have hinl' : directSum_inl F G ≫ m = s.inl := by
            simpa [directSum_binaryBicone] using hinl
          rw [hinl', directSum_inl_desc]
        exact congrArg (fun η => η.app X x₁) h
      have hInr :
          m.app X (0, x₂) =
            (directSum_desc F G s.pt s.inl s.inr).app X (0, x₂) := by
        have h :
            directSum_inr F G ≫ m =
              directSum_inr F G ≫ directSum_desc F G s.pt s.inl s.inr := by
          have hinr' : directSum_inr F G ≫ m = s.inr := by
            simpa [directSum_binaryBicone] using hinr
          rw [hinr', directSum_inr_desc]
        exact congrArg (fun η => η.app X x₂) h
      calc
        m.app X (x₁, x₂)
            = m.app X ((x₁, 0) + (0, x₂)) := by
              change m.app X (x₁, x₂) = m.app X (x₁ + 0, 0 + x₂)
              simp
        _ = m.app X (x₁, 0) + m.app X (0, x₂) := by
              rw [LinearMap.map_add]
        _ = (directSum_desc F G s.pt s.inl s.inr).app X (x₁, 0) +
              (directSum_desc F G s.pt s.inl s.inr).app X (0, x₂) := by
              rw [hInl, hInr]
        _ = (directSum_desc F G s.pt s.inl s.inr).app X ((x₁, 0) + (0, x₂)) := by
              rw [LinearMap.map_add]
        _ = (directSum_desc F G s.pt s.inl s.inr).app X (x₁, x₂) := by
              change (directSum_desc F G s.pt s.inl s.inr).app X (x₁ + 0, 0 + x₂) =
                (directSum_desc F G s.pt s.inl s.inr).app X (x₁, x₂)
              simp)

/-- The pointwise direct sum is a binary biproduct in `LinearPST`. -/
def directSum_isBilimit {category : SmCorQ (k := k)}
    (F G : LinearPST category) :
    (directSum_binaryBicone F G).IsBilimit where
  isLimit := directSum_isLimit F G
  isColimit := directSum_isColimit F G

/-- Any two linear presheaves with transfers have the constructed binary
biproduct given by their pointwise direct sum. -/
instance hasBinaryBiproduct {category : SmCorQ (k := k)}
    (F G : LinearPST category) :
    HasBinaryBiproduct F G :=
  HasBinaryBiproduct.mk
    { bicone := directSum_binaryBicone F G
      isBilimit := directSum_isBilimit F G }

/-- `LinearPST` has binary biproducts, constructed pointwise. -/
instance hasBinaryBiproducts {category : SmCorQ (k := k)} :
    HasBinaryBiproducts (LinearPST category) where
  has_binary_biproduct := fun F G => hasBinaryBiproduct F G

/-- The kernel of a morphism of linear presheaves, constructed as the
underlying pointwise kernel with transfer-linearity proved in this owner file. -/
def kernel {category : SmCorQ (k := k)}
    {F G : LinearPST category} (f : F ⟶ G)
    [HasKernel ((forgetToPST (category := category)).map f)] :
    LinearPST category :=
  ⟨Limits.kernel ((forgetToPST (category := category)).map f),
    IsTransferLinear.of_kernel ((forgetToPST (category := category)).map f) F.2 G.2⟩

/-- The kernel inclusion for the constructed kernel in `LinearPST`. -/
def kernel_ι {category : SmCorQ (k := k)}
    {F G : LinearPST category} (f : F ⟶ G)
    [HasKernel ((forgetToPST (category := category)).map f)] :
    kernel f ⟶ F := by
  letI := SmCorQCat category
  show (kernel f).toPST ⟶ F.toPST
  exact Limits.kernel.ι ((forgetToPST (category := category)).map f)

@[simp] theorem kernel_ι_comp {category : SmCorQ (k := k)}
    {F G : LinearPST category} (f : F ⟶ G)
    [HasKernel ((forgetToPST (category := category)).map f)] :
    kernel_ι f ≫ f = 0 := by
  letI := SmCorQCat category
  show (kernel_ι f : (kernel f).toPST ⟶ F.toPST) ≫
      (forgetToPST (category := category)).map f = 0
  exact Limits.kernel.condition ((forgetToPST (category := category)).map f)

/-- The kernel lift for the constructed kernel in `LinearPST`. -/
def kernel_lift {category : SmCorQ (k := k)}
    {S F G : LinearPST category} (f : F ⟶ G)
    [HasKernel ((forgetToPST (category := category)).map f)]
    (g : S ⟶ F) (hg : g ≫ f = 0) :
    S ⟶ kernel f := by
  letI := SmCorQCat category
  show S.toPST ⟶ (kernel f).toPST
  exact Limits.kernel.lift ((forgetToPST (category := category)).map f)
    ((forgetToPST (category := category)).map g)
    (by
      show (forgetToPST (category := category)).map g ≫
          (forgetToPST (category := category)).map f = 0
      exact hg)

@[simp] theorem kernel_lift_fac {category : SmCorQ (k := k)}
    {S F G : LinearPST category} (f : F ⟶ G)
    [HasKernel ((forgetToPST (category := category)).map f)]
    (g : S ⟶ F) (hg : g ≫ f = 0) :
    kernel_lift f g hg ≫ kernel_ι f = g := by
  letI := SmCorQCat category
  show (kernel_lift f g hg : S.toPST ⟶ (kernel f).toPST) ≫
      (kernel_ι f : (kernel f).toPST ⟶ F.toPST) =
        (forgetToPST (category := category)).map g
  exact Limits.kernel.lift_ι ((forgetToPST (category := category)).map f)
    ((forgetToPST (category := category)).map g) _

/-- Uniqueness of the kernel lift for the constructed kernel in `LinearPST`. -/
theorem kernel_lift_unique {category : SmCorQ (k := k)}
    {S F G : LinearPST category} (f : F ⟶ G)
    [HasKernel ((forgetToPST (category := category)).map f)]
    (g : S ⟶ F) (hg : g ≫ f = 0)
    (m : S ⟶ kernel f) (hm : m ≫ kernel_ι f = g) :
    m = kernel_lift f g hg := by
  letI := SmCorQCat category
  apply NatTrans.ext
  apply funext
  intro X
  apply LinearMap.ext
  intro x
  have hm' :
      (m : S.toPST ⟶ (kernel f).toPST) ≫
        (Limits.kernel.ι ((forgetToPST (category := category)).map f)) =
          (forgetToPST (category := category)).map g := by
    simpa [kernel_ι] using hm
  have hfac :
      (m : S.toPST ⟶ (kernel f).toPST) ≫
        (Limits.kernel.ι ((forgetToPST (category := category)).map f)) =
      (kernel_lift f g hg : S.toPST ⟶ (kernel f).toPST) ≫
        (Limits.kernel.ι ((forgetToPST (category := category)).map f)) := by
    rw [hm']
    exact (Limits.kernel.lift_ι ((forgetToPST (category := category)).map f)
      ((forgetToPST (category := category)).map g) _).symm
  have h :=
    Limits.Fork.IsLimit.hom_ext
      (Limits.kernelIsKernel ((forgetToPST (category := category)).map f)) hfac
  exact congrArg (fun η => η.app X x) h

/-- The cokernel of a morphism of linear presheaves, constructed as the
underlying pointwise cokernel with transfer-linearity proved in this owner file. -/
def cokernel {category : SmCorQ (k := k)}
    {F G : LinearPST category} (f : F ⟶ G)
    [HasCokernel ((forgetToPST (category := category)).map f)] :
    LinearPST category :=
  ⟨Limits.cokernel ((forgetToPST (category := category)).map f),
    IsTransferLinear.of_cokernel ((forgetToPST (category := category)).map f) F.2 G.2⟩

/-- The cokernel projection for the constructed cokernel in `LinearPST`. -/
def cokernel_π {category : SmCorQ (k := k)}
    {F G : LinearPST category} (f : F ⟶ G)
    [HasCokernel ((forgetToPST (category := category)).map f)] :
    G ⟶ cokernel f := by
  letI := SmCorQCat category
  show G.toPST ⟶ (cokernel f).toPST
  exact Limits.cokernel.π ((forgetToPST (category := category)).map f)

@[simp] theorem comp_cokernel_π {category : SmCorQ (k := k)}
    {F G : LinearPST category} (f : F ⟶ G)
    [HasCokernel ((forgetToPST (category := category)).map f)] :
    f ≫ cokernel_π f = 0 := by
  letI := SmCorQCat category
  show (forgetToPST (category := category)).map f ≫
      (cokernel_π f : G.toPST ⟶ (cokernel f).toPST) = 0
  exact Limits.cokernel.condition ((forgetToPST (category := category)).map f)

/-- The cokernel desc for the constructed cokernel in `LinearPST`. -/
def cokernel_desc {category : SmCorQ (k := k)}
    {F G S : LinearPST category} (f : F ⟶ G)
    [HasCokernel ((forgetToPST (category := category)).map f)]
    (g : G ⟶ S) (hg : f ≫ g = 0) :
    cokernel f ⟶ S := by
  letI := SmCorQCat category
  show (cokernel f).toPST ⟶ S.toPST
  exact Limits.cokernel.desc ((forgetToPST (category := category)).map f)
    ((forgetToPST (category := category)).map g)
    (by
      show (forgetToPST (category := category)).map f ≫
          (forgetToPST (category := category)).map g = 0
      exact hg)

@[simp] theorem cokernel_π_desc {category : SmCorQ (k := k)}
    {F G S : LinearPST category} (f : F ⟶ G)
    [HasCokernel ((forgetToPST (category := category)).map f)]
    (g : G ⟶ S) (hg : f ≫ g = 0) :
    cokernel_π f ≫ cokernel_desc f g hg = g := by
  letI := SmCorQCat category
  show (cokernel_π f : G.toPST ⟶ (cokernel f).toPST) ≫
      (cokernel_desc f g hg : (cokernel f).toPST ⟶ S.toPST) =
        (forgetToPST (category := category)).map g
  exact Limits.cokernel.π_desc ((forgetToPST (category := category)).map f)
    ((forgetToPST (category := category)).map g) _

/-- Uniqueness of the cokernel desc for the constructed cokernel in `LinearPST`. -/
theorem cokernel_desc_unique {category : SmCorQ (k := k)}
    {F G S : LinearPST category} (f : F ⟶ G)
    [HasCokernel ((forgetToPST (category := category)).map f)]
    (g : G ⟶ S) (hg : f ≫ g = 0)
    (m : cokernel f ⟶ S) (hm : cokernel_π f ≫ m = g) :
    m = cokernel_desc f g hg := by
  letI := SmCorQCat category
  apply NatTrans.ext
  apply funext
  intro X
  apply LinearMap.ext
  intro x
  have hm' :
      (Limits.cokernel.π ((forgetToPST (category := category)).map f)) ≫
        (m : (cokernel f).toPST ⟶ S.toPST) =
          (forgetToPST (category := category)).map g := by
    simpa [cokernel_π] using hm
  have hfac :
      (Limits.cokernel.π ((forgetToPST (category := category)).map f)) ≫
        (m : (cokernel f).toPST ⟶ S.toPST) =
      (Limits.cokernel.π ((forgetToPST (category := category)).map f)) ≫
        (cokernel_desc f g hg : (cokernel f).toPST ⟶ S.toPST) := by
    rw [hm']
    exact (Limits.cokernel.π_desc ((forgetToPST (category := category)).map f)
      ((forgetToPST (category := category)).map g) _).symm
  have h :=
    Limits.Cofork.IsColimit.hom_ext
      (Limits.cokernelIsCokernel ((forgetToPST (category := category)).map f)) hfac
  exact congrArg (fun η => η.app X x) h

/-- The constructed kernel fork is limiting in `LinearPST`. -/
def kernel_isLimit {category : SmCorQ (k := k)}
    {F G : LinearPST category} (f : F ⟶ G)
    [HasKernel ((forgetToPST (category := category)).map f)] :
    IsLimit (KernelFork.ofι (kernel_ι f) (kernel_ι_comp f)) :=
  KernelFork.IsLimit.ofι (kernel_ι f) (kernel_ι_comp f)
    (fun g hg => kernel_lift f g hg)
    (fun g hg => kernel_lift_fac f g hg)
    (fun g hg m hm => kernel_lift_unique f g hg m hm)

/-- Every morphism of linear presheaves has the constructed kernel. -/
instance hasKernel {category : SmCorQ (k := k)}
    {F G : LinearPST category} (f : F ⟶ G)
    [HasKernel ((forgetToPST (category := category)).map f)] :
    HasKernel f :=
  HasLimit.mk
    { cone := KernelFork.ofι (kernel_ι f) (kernel_ι_comp f)
      isLimit := kernel_isLimit f }

/-- `LinearPST` has kernels, constructed by the pointwise kernels in `PST`. -/
instance hasKernels {category : SmCorQ (k := k)} :
    HasKernels (LinearPST category) where
  has_limit := fun f => by
    letI := SmCorQCat category
    letI : HasKernel ((forgetToPST (category := category)).map f) := inferInstance
    exact hasKernel f

/-- The constructed cokernel cofork is colimiting in `LinearPST`. -/
def cokernel_isColimit {category : SmCorQ (k := k)}
    {F G : LinearPST category} (f : F ⟶ G)
    [HasCokernel ((forgetToPST (category := category)).map f)] :
    IsColimit (CokernelCofork.ofπ (cokernel_π f) (comp_cokernel_π f)) :=
  CokernelCofork.IsColimit.ofπ (cokernel_π f) (comp_cokernel_π f)
    (fun g hg => cokernel_desc f g hg)
    (fun g hg => cokernel_π_desc f g hg)
    (fun g hg m hm => cokernel_desc_unique f g hg m hm)

/-- Every morphism of linear presheaves has the constructed cokernel. -/
instance hasCokernel {category : SmCorQ (k := k)}
    {F G : LinearPST category} (f : F ⟶ G)
    [HasCokernel ((forgetToPST (category := category)).map f)] :
    HasCokernel f :=
  HasColimit.mk
    { cocone := CokernelCofork.ofπ (cokernel_π f) (comp_cokernel_π f)
      isColimit := cokernel_isColimit f }

/-- `LinearPST` has cokernels, constructed by the pointwise cokernels in `PST`. -/
instance hasCokernels {category : SmCorQ (k := k)} :
    HasCokernels (LinearPST category) where
  has_colimit := fun f => by
    letI := SmCorQCat category
    letI : HasCokernel ((forgetToPST (category := category)).map f) := inferInstance
    exact hasCokernel f

/-- `LinearPST` has finite products, by zero objects and binary biproducts. -/
instance hasFiniteProducts {category : SmCorQ (k := k)} :
    HasFiniteProducts (LinearPST category) := by
  letI := hasZeroObject (category := category)
  letI := hasBinaryBiproducts (category := category)
  exact hasFiniteProducts_of_has_binary_and_terminal

/-- `LinearPST` has finite coproducts, by zero objects and binary biproducts. -/
instance hasFiniteCoproducts {category : SmCorQ (k := k)} :
    HasFiniteCoproducts (LinearPST category) := by
  letI := hasZeroObject (category := category)
  letI := hasBinaryBiproducts (category := category)
  exact hasFiniteCoproducts_of_has_binary_and_initial

/-- `LinearPST` has finite biproducts, constructed from finite products in the
preadditive category. -/
instance hasFiniteBiproducts {category : SmCorQ (k := k)} :
    HasFiniteBiproducts (LinearPST category) := by
  letI := preadditive (category := category)
  letI := hasFiniteProducts (category := category)
  exact Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- `LinearPST` has finite limits, from finite products and equalizers
constructed via kernels in the preadditive category. -/
instance hasFiniteLimits {category : SmCorQ (k := k)} :
    HasFiniteLimits (LinearPST category) := by
  letI := preadditive (category := category)
  letI := hasKernels (category := category)
  letI : HasEqualizers (LinearPST category) :=
    Preadditive.hasEqualizers_of_hasKernels
  letI := hasFiniteProducts (category := category)
  exact hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- `LinearPST` has finite colimits, from finite coproducts and coequalizers
constructed via cokernels in the preadditive category. -/
instance hasFiniteColimits {category : SmCorQ (k := k)} :
    HasFiniteColimits (LinearPST category) := by
  letI := preadditive (category := category)
  letI := hasCokernels (category := category)
  letI : HasCoequalizers (LinearPST category) :=
    Preadditive.hasCoequalizers_of_hasCokernels
  letI := hasFiniteCoproducts (category := category)
  exact hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end LinearPST

/-- Top-level owner definition for the preadditive structure on
`LinearPST`, avoiding namespace-dot ambiguity with the `LinearPST` type
family in downstream files. -/
def linearPSTPreadditive {category : SmCorQ (k := k)} :
    Preadditive (LinearPST category) := by
  letI := SmCorQCat category
  change Preadditive (InducedCategory (PST category) LinearPST.toPST)
  infer_instance

end

end Boundary
