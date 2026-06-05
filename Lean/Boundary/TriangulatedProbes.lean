import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Triangulated probe interfaces

This file defines the base categorical interfaces for probe/profile constructions
in preadditive triangulated categories.

The first theorem target is that the restricted Yoneda/profile functor attached
to a probe datum is additive.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe vT vP uT uP

namespace Boundary

/-- A probe datum on a preadditive category `T` is a small preadditive source
category together with a functor into `T`. -/
structure ProbeDatum (T : Type uT) [Category.{vT} T] [Preadditive T] where
  Probe : Type uP
  probeCategory : Category.{vP} Probe
  probePreadditive : Preadditive Probe
  probe : Probe ⥤ T

attribute [instance] ProbeDatum.probeCategory ProbeDatum.probePreadditive

namespace ProbeDatum

variable {T : Type uT} [Category.{vT} T] [Preadditive T] (PD : ProbeDatum T)

/-- The profile of an object `X` against a probe datum is the additive presheaf
`P ↦ Hom_T(probe(P), X)`. -/
@[simps]
def profileObj (X : T) : PD.Probeᵒᵖ ⥤ AddCommGrp.{vT} where
  obj P := AddCommGrp.of (PD.probe.obj P.unop ⟶ X)
  map f :=
    AddCommGrp.ofHom <|
      AddMonoidHom.mk'
        (fun g => PD.probe.map f.unop ≫ g)
        (fun g h => by simp [Preadditive.add_comp])
  map_id P := by
    ext g
    simp [AddCommGrp.ofHom]
  map_comp f g := by
    ext h
    simp [AddCommGrp.ofHom]

/-- The restricted Yoneda/profile functor attached to a probe datum. -/
@[simps]
def profileFunctor : T ⥤ (PD.Probeᵒᵖ ⥤ AddCommGrp.{vT}) where
  obj X := PD.profileObj X
  map f :=
    { app := fun P =>
        AddCommGrp.ofHom <|
          AddMonoidHom.mk'
            (fun g => g ≫ f)
            (fun g h => by simp [Preadditive.comp_add])
      naturality := by
        intro P Q u
        ext g
        simp [AddCommGrp.ofHom] }
  map_id X := by
    ext P g
    simp [AddCommGrp.ofHom]
  map_comp f g := by
    ext P h
    simp [AddCommGrp.ofHom]

@[simp]
theorem profileObj_map_apply {X : T} {P Q : PD.Probeᵒᵖ} (f : P ⟶ Q)
    (g : PD.probe.obj P.unop ⟶ X) :
    ((PD.profileObj X).map f) g = PD.probe.map f.unop ≫ g :=
  rfl

@[simp]
theorem profileFunctor_obj_apply (X : T) (P : PD.Probeᵒᵖ) :
    (PD.profileFunctor.obj X).obj P = AddCommGrp.of (PD.probe.obj P.unop ⟶ X) :=
  rfl

@[simp]
theorem profileFunctor_map_app_apply {X Y : T} (f : X ⟶ Y) (P : PD.Probeᵒᵖ)
    (g : PD.probe.obj P.unop ⟶ X) :
    ((PD.profileFunctor.map f).app P) g = g ≫ f :=
  rfl

instance profileFunctor_additive : Functor.Additive PD.profileFunctor where
  map_add {X Y f g} := by
    ext P h
    change h ≫ (f + g) = h ≫ f + h ≫ g
    simp [Preadditive.comp_add]

theorem profileFunctor_isAdditive : Functor.Additive PD.profileFunctor :=
  inferInstance

end ProbeDatum

/-- A strictly full replete triangulated sector, presented as a predicate on
objects with explicit closure data. -/
structure TriangulatedSector (T : Type uT) [Category.{vT} T] [CategoryTheory.Limits.HasZeroObject T]
    [Preadditive T] [HasShift T ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor T n)]
    [Pretriangulated T] where
  mem : T → Prop
  zero_mem : mem (0 : T)
  iso_closed : ∀ {X Y : T}, CategoryTheory.Iso X Y → mem X → mem Y
  shift_closed : ∀ (X : T) (n : ℤ), mem X → mem (X⟦n⟧)
  triangle_closed :
    ∀ (Δ : Triangle T) (_ : Δ ∈ distTriang T),
      ((mem Δ.obj₁ ∧ mem Δ.obj₂) → mem Δ.obj₃) ∧
      ((mem Δ.obj₂ ∧ mem Δ.obj₃) → mem Δ.obj₁) ∧
      ((mem Δ.obj₃ ∧ mem Δ.obj₁) → mem Δ.obj₂)

namespace TriangulatedSector

variable {T : Type uT} [Category.{vT} T] [CategoryTheory.Limits.HasZeroObject T] [Preadditive T]
  [HasShift T ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor T n)] [Pretriangulated T]
  (S : TriangulatedSector T)

instance mem_closedUnderIsomorphisms : ClosedUnderIsomorphisms S.mem where
  of_iso := fun e hX => S.iso_closed e hX

/-- The mathlib `Triangulated.Subcategory` attached to a strict triangulated
sector. -/
def toSubcategory : CategoryTheory.Triangulated.Subcategory T :=
  CategoryTheory.Triangulated.Subcategory.mk'
    S.mem
    S.zero_mem
    S.shift_closed
    (fun Δ hΔ h₁ h₃ =>
      (S.triangle_closed Δ hΔ).2.2 ⟨h₃, h₁⟩)

/-- The full subcategory cut out by the sector predicate. -/
abbrev SectorCategory := FullSubcategory S.mem

/-- The inclusion of a sector into the ambient category. -/
abbrev inclusion : S.SectorCategory ⥤ T :=
  fullSubcategoryInclusion S.mem

end TriangulatedSector

section RestrictedProfile

variable {T : Type uT} [Category.{vT} T] [CategoryTheory.Limits.HasZeroObject T] [Preadditive T]
  [HasShift T ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor T n)] [Pretriangulated T]
  (PD : ProbeDatum T) (S : TriangulatedSector T)

/-- The profile functor restricted to a chosen sector. -/
abbrev restrictedProfileFunctor :
    S.SectorCategory ⥤ (PD.Probeᵒᵖ ⥤ AddCommGrp.{vT}) :=
  S.inclusion ⋙ PD.profileFunctor

/-- The boundary category of realizable probe profiles on a sector. -/
abbrev ProbeBoundary :=
  (restrictedProfileFunctor PD S).EssImageSubcategory

end RestrictedProfile

/-- A comparison witnessing that the probe family `PD₂` extends `PD₁` at the
level of profile categories. -/
structure ProbeFamilyLE (T : Type uT) [Category.{vT} T] [Preadditive T]
    (PD₁ PD₂ : ProbeDatum T) where
  profileRestriction :
    (PD₂.Probeᵒᵖ ⥤ AddCommGrp.{vT}) ⥤ (PD₁.Probeᵒᵖ ⥤ AddCommGrp.{vT})
  profileRestriction_full :
    profileRestriction.Full
  profileRestriction_faithful :
    profileRestriction.Faithful
  profileComparison :
    PD₂.profileFunctor ⋙ profileRestriction ≅ PD₁.profileFunctor

/-- A probe family is holographic on a sector when the restricted profile
functor is full and faithful. -/
structure HolographicProbeFamily (T : Type uT) [Category.{vT} T]
    [CategoryTheory.Limits.HasZeroObject T]
    [Preadditive T] [HasShift T ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor T n)]
    [Pretriangulated T] (PD : ProbeDatum T) (S : TriangulatedSector T) where
  isFull :
    (restrictedProfileFunctor PD S).Full
  isFaithful :
    (restrictedProfileFunctor PD S).Faithful

namespace HolographicProbeFamily

variable {T : Type uT} [Category.{vT} T] [CategoryTheory.Limits.HasZeroObject T] [Preadditive T]
  [HasShift T ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor T n)] [Pretriangulated T]
  {PD : ProbeDatum T} {S : TriangulatedSector T}
  (H : HolographicProbeFamily T PD S)

theorem holographic_hom_ext
    (H : HolographicProbeFamily T PD S)
    {X Y : S.SectorCategory} {f g : X ⟶ Y}
    (h :
      (restrictedProfileFunctor PD S).map f =
        (restrictedProfileFunctor PD S).map g) :
    f = g := by
  letI : (restrictedProfileFunctor PD S).Faithful := HolographicProbeFamily.isFaithful H
  exact (restrictedProfileFunctor PD S).map_injective h

def holographic_hom_reconstruct
    (H : HolographicProbeFamily T PD S)
    {X Y : S.SectorCategory}
    (η :
      (restrictedProfileFunctor PD S).obj X ⟶
        (restrictedProfileFunctor PD S).obj Y) :
    X ⟶ Y := by
  letI : (restrictedProfileFunctor PD S).Full := HolographicProbeFamily.isFull H
  exact (restrictedProfileFunctor PD S).preimage η

@[simp]
theorem holographic_hom_reconstruct_map
    (H : HolographicProbeFamily T PD S)
    {X Y : S.SectorCategory}
    (η :
      (restrictedProfileFunctor PD S).obj X ⟶
        (restrictedProfileFunctor PD S).obj Y) :
    (restrictedProfileFunctor PD S).map (holographic_hom_reconstruct (H := H) η) = η := by
  letI : (restrictedProfileFunctor PD S).Full := HolographicProbeFamily.isFull H
  simpa [holographic_hom_reconstruct] using
    (restrictedProfileFunctor PD S).map_preimage η

end HolographicProbeFamily

/-- If a larger probe family is holographic and restricts to a smaller probe
family through a fully faithful comparison of profile categories, then the
smaller probe family is also holographic. -/
theorem holographic_of_probeFamily_enlarged
    {T : Type uT} [Category.{vT} T] [CategoryTheory.Limits.HasZeroObject T]
    [Preadditive T] [HasShift T ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor T n)] [Pretriangulated T]
    {PD₁ PD₂ : ProbeDatum T} {S : TriangulatedSector T}
    (hle : ProbeFamilyLE T PD₁ PD₂)
    (H : HolographicProbeFamily T PD₂ S) :
    HolographicProbeFamily T PD₁ S := by
  letI : (restrictedProfileFunctor PD₂ S).Full := H.isFull
  letI : (restrictedProfileFunctor PD₂ S).Faithful := H.isFaithful
  letI : hle.profileRestriction.Full := hle.profileRestriction_full
  letI : hle.profileRestriction.Faithful := hle.profileRestriction_faithful
  let e :
      restrictedProfileFunctor PD₂ S ⋙ hle.profileRestriction ≅
        restrictedProfileFunctor PD₁ S :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft (TriangulatedSector.inclusion S)
      hle.profileComparison
  letI : (restrictedProfileFunctor PD₂ S ⋙ hle.profileRestriction).Full :=
    inferInstance
  letI : (restrictedProfileFunctor PD₂ S ⋙ hle.profileRestriction).Faithful :=
    inferInstance
  letI : (restrictedProfileFunctor PD₁ S).Full := Functor.Full.of_iso e
  letI : (restrictedProfileFunctor PD₁ S).Faithful := Functor.Faithful.of_iso e
  exact
    { isFull := inferInstance
      isFaithful := inferInstance }

/-- Holography transports across a fully faithful comparison of sector
categories when the two restricted profile functors agree up to natural
isomorphism after comparison. -/
theorem holographicProbeFamily_of_equivalence
    {T : Type uT} [Category.{vT} T] [CategoryTheory.Limits.HasZeroObject T]
    [Preadditive T] [HasShift T ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor T n)] [Pretriangulated T]
    {PD : ProbeDatum T}
    {S₁ S₂ : TriangulatedSector T}
    (E : S₁.SectorCategory ⥤ S₂.SectorCategory)
    [E.Full] [E.Faithful]
    (e :
      E ⋙ restrictedProfileFunctor PD S₂ ≅
        restrictedProfileFunctor PD S₁)
    (H : HolographicProbeFamily T PD S₂) :
    HolographicProbeFamily T PD S₁ := by
  letI : (restrictedProfileFunctor PD S₂).Full := H.isFull
  letI : (restrictedProfileFunctor PD S₂).Faithful := H.isFaithful
  letI : (E ⋙ restrictedProfileFunctor PD S₂).Full := inferInstance
  letI : (E ⋙ restrictedProfileFunctor PD S₂).Faithful := inferInstance
  letI : (restrictedProfileFunctor PD S₁).Full := Functor.Full.of_iso e
  letI : (restrictedProfileFunctor PD S₁).Faithful := Functor.Faithful.of_iso e
  exact
    { isFull := inferInstance
      isFaithful := inferInstance }

/-- Restricting to a sector presented by a fully faithful comparison functor
preserves holography when the restricted profile functor is unchanged up to
natural isomorphism. -/
theorem holographicProbeFamily_restrict_sector
    {T : Type uT} [Category.{vT} T] [CategoryTheory.Limits.HasZeroObject T]
    [Preadditive T] [HasShift T ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor T n)] [Pretriangulated T]
    {PD : ProbeDatum T}
    {S₁ S₂ : TriangulatedSector T}
    (E : S₁.SectorCategory ⥤ S₂.SectorCategory)
    [E.Full] [E.Faithful]
    (e :
      E ⋙ restrictedProfileFunctor PD S₂ ≅
        restrictedProfileFunctor PD S₁)
    (H : HolographicProbeFamily T PD S₂) :
    HolographicProbeFamily T PD S₁ :=
  holographicProbeFamily_of_equivalence E e H

/-- A Tate-flavored probe family. Concrete Tate probes are supplied later by
instantiation, not in this interface file. -/
structure TateProbeDatum (T : Type uT) [Category.{vT} T] [Preadditive T]
    extends ProbeDatum T

/-- A geometric probe family. Concrete geometric probes are supplied later by
instantiation, not in this interface file. -/
structure GeometricProbeDatum (T : Type uT) [Category.{vT} T] [Preadditive T]
    extends ProbeDatum T

/-- A boundary probe family. Concrete boundary probes are supplied later by
instantiation, not in this interface file. -/
structure BoundaryProbeDatum (T : Type uT) [Category.{vT} T] [Preadditive T]
    extends ProbeDatum T

/-- A motivic probe family together with its Tate, geometric, and boundary
subfamilies, each presented via a profile-level enlargement witness. -/
structure MotivicProbeDatum (T : Type uT) [Category.{vT} T] [Preadditive T]
    extends ProbeDatum T where
  tatePart : TateProbeDatum T
  geometricPart : GeometricProbeDatum T
  boundaryPart : BoundaryProbeDatum T
  tate_le_motivic : ProbeFamilyLE T tatePart.toProbeDatum toProbeDatum
  geometric_le_motivic : ProbeFamilyLE T geometricPart.toProbeDatum toProbeDatum
  boundary_le_motivic : ProbeFamilyLE T boundaryPart.toProbeDatum toProbeDatum

def tateProbeFamily_le_motivicProbeFamily
    {T : Type uT} [Category.{vT} T] [Preadditive T]
    (PD : MotivicProbeDatum T) :
    ProbeFamilyLE T PD.tatePart.toProbeDatum PD.toProbeDatum :=
  PD.tate_le_motivic

def geometricProbeFamily_le_motivicProbeFamily
    {T : Type uT} [Category.{vT} T] [Preadditive T]
    (PD : MotivicProbeDatum T) :
    ProbeFamilyLE T PD.geometricPart.toProbeDatum PD.toProbeDatum :=
  PD.geometric_le_motivic

def boundaryProbeFamily_le_motivicProbeFamily
    {T : Type uT} [Category.{vT} T] [Preadditive T]
    (PD : MotivicProbeDatum T) :
    ProbeFamilyLE T PD.boundaryPart.toProbeDatum PD.toProbeDatum :=
  PD.boundary_le_motivic

/-- A strengthened probe datum with chosen shifted probes and comparison
isomorphisms. -/
structure ShiftStableProbeDatum (T : Type uT) [Category.{vT} T] [Preadditive T]
    [HasShift T ℤ] extends ProbeDatum T where
  shiftProbe : ℤ → Probe ⥤ Probe
  shiftCompatibility :
    ∀ n : ℤ, probe ⋙ shiftFunctor T n ≅ shiftProbe n ⋙ probe

end Boundary
