import Boundary.EffectiveMotives
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Idempotents.Karoubi
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Canonical geometric effective motives

This file constructs the canonical proof object witnessing the smallest
triangulated subcategory of canonical effective motives that contains the
canonical effective motives of smooth schemes.

The construction is the intersection of all admissible triangulated
subcategories containing the canonical generator objects. When the full
functor `Sm/k ⥤ DM_eff,can` is exported on disk, the object-level generator
predicate here is expected to coincide with membership in its essential image.
-/

universe u

open CategoryTheory

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable (implementation :
  CanonicalA1NisLocalizationImplementation composition)

private abbrev localCanonicalEffectiveMotivesCategory :
    Type (u + 2) :=
  canonicalEffectiveMotivesFromA1NisImplementation composition implementation

private def localCanonicalEffectiveMotivesLocalizationFunctor :
    canonicalEffectiveAmbientDerivedCategory composition ⥤
      localCanonicalEffectiveMotivesCategory composition implementation :=
  canonicalEffectiveMotivesLocalizationFunctorFromA1NisImplementation
    composition implementation

private abbrev localCanonicalRepresentableLinearPST
    (X : Geometry.SmSchemeOver k) :
    LinearPST (Boundary.canonicalCategory composition) :=
  QtrLinear (category := Boundary.canonicalCategory composition) X

private def localCanonicalRepresentableComplex
    (X : Geometry.SmSchemeOver k) :
    canonicalEffectiveAmbientDerivedCategory composition :=
  ((DerivedCategory.singleFunctor
      (LinearPST (Boundary.canonicalCategory composition)) 0).obj
    (localCanonicalRepresentableLinearPST composition X))

private def localCanonicalEffectiveMotive
    (X : Geometry.SmSchemeOver k) :
    localCanonicalEffectiveMotivesCategory composition implementation :=
  (localCanonicalEffectiveMotivesLocalizationFunctor composition implementation).obj
    (localCanonicalRepresentableComplex composition X)

/-- Functor-indexed generator predicate, stated as essential-image membership.
This is the exact predicate to specialize once the on-disk functor
`canonicalEffectiveMotiveFunctor` is available. -/
def canonicalEffectiveMotiveGeneratorOf
    (F : Geometry.SmSchemeOver k ⥤
      localCanonicalEffectiveMotivesCategory composition implementation) :
    localCanonicalEffectiveMotivesCategory composition implementation → Prop :=
  fun M => M ∈ F.essImage

/-- The essential image of a candidate effective-motive functor, packaged as a
full subcategory. -/
abbrev canonicalEffectiveMotiveGeneratorEssImageSubcategory
    (F : Geometry.SmSchemeOver k ⥤
      localCanonicalEffectiveMotivesCategory composition implementation) :=
  F.EssImageSubcategory

/-- Current canonical generator predicate on disk: objects isomorphic to the
canonical effective motive of some smooth `k`-scheme. This is the object-level
form of the future essential-image predicate. -/
def canonicalEffectiveMotiveGenerator :
    localCanonicalEffectiveMotivesCategory composition implementation → Prop :=
  fun M => ∃ X : Geometry.SmSchemeOver k,
    Nonempty (localCanonicalEffectiveMotive composition implementation X ≅ M)

theorem canonicalEffectiveMotiveGeneratorOf_obj
    (F : Geometry.SmSchemeOver k ⥤
      localCanonicalEffectiveMotivesCategory composition implementation)
    (X : Geometry.SmSchemeOver k) :
    canonicalEffectiveMotiveGeneratorOf composition implementation F (F.obj X) :=
  Functor.obj_mem_essImage F X

theorem canonicalEffectiveMotiveGenerator_self
    (X : Geometry.SmSchemeOver k) :
    canonicalEffectiveMotiveGenerator composition implementation
      (localCanonicalEffectiveMotive composition implementation X) :=
  ⟨X, ⟨Iso.refl _⟩⟩

theorem canonicalEffectiveMotiveGenerator_eq_of_obj
    (F : Geometry.SmSchemeOver k ⥤
      localCanonicalEffectiveMotivesCategory composition implementation)
    (hobj : ∀ X : Geometry.SmSchemeOver k,
      F.obj X = localCanonicalEffectiveMotive composition implementation X) :
    canonicalEffectiveMotiveGenerator composition implementation =
      canonicalEffectiveMotiveGeneratorOf composition implementation F := by
  funext M
  apply propext
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X, ⟨eqToIso (hobj X) ≪≫ e⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X, ⟨(eqToIso (hobj X)).symm ≪≫ e⟩⟩

/-- An admissible candidate for the geometric effective part of
`canonicalEffectiveMotives`: a triangulated subcategory closed under
isomorphisms and containing all canonical effective motives of smooth schemes.

Direct-summand closure is handled afterwards by passing to `Karoubi`, since the
ambient `Triangulated.Subcategory` API here does not package idempotent
completeness directly. -/
structure GeometricEffectiveSubcategoryCandidate where
  carrier :
    Triangulated.Subcategory
      (localCanonicalEffectiveMotivesCategory composition implementation)
  closed_under_iso : ClosedUnderIsomorphisms carrier.P
  contains_generators :
    ∀ X : Geometry.SmSchemeOver k,
      carrier.P (localCanonicalEffectiveMotive composition implementation X)

namespace GeometricEffectiveSubcategoryCandidate

theorem contains_generator
    (C : GeometricEffectiveSubcategoryCandidate composition implementation)
    {M : localCanonicalEffectiveMotivesCategory composition implementation}
    (hM : canonicalEffectiveMotiveGenerator composition implementation M) :
    C.carrier.P M := by
  rcases hM with ⟨X, ⟨e⟩⟩
  letI := C.closed_under_iso
  exact mem_of_iso C.carrier.P e (C.contains_generators X)

end GeometricEffectiveSubcategoryCandidate

/-- The pointwise intersection predicate over all admissible geometric
effective candidates. -/
def canonicalGeometricEffectiveCandidate :
    localCanonicalEffectiveMotivesCategory composition implementation → Prop :=
  fun M =>
    ∀ C : GeometricEffectiveSubcategoryCandidate composition implementation,
      C.carrier.P M

/-- The canonical triangulated closure witness generated by the canonical
effective motives of smooth schemes. -/
def canonicalGeometricEffectiveThickSubcategory :
    Triangulated.Subcategory
      (localCanonicalEffectiveMotivesCategory composition implementation) :=
  Triangulated.Subcategory.mk'
    (canonicalGeometricEffectiveCandidate composition implementation)
    (by
      intro C
      letI := C.closed_under_iso
      exact C.carrier.zero)
    (fun X n hX C => C.carrier.shift X n (hX C))
    (fun T hT h₁ h₃ C => by
      letI := C.closed_under_iso
      exact C.carrier.ext₂ T hT (h₁ C) (h₃ C))

theorem canonicalGeometricEffectiveThickSubcategory_contains_generators
    (X : Geometry.SmSchemeOver k) :
    (canonicalGeometricEffectiveThickSubcategory composition implementation).P
      (localCanonicalEffectiveMotive composition implementation X) := by
  show canonicalGeometricEffectiveCandidate composition implementation
    (localCanonicalEffectiveMotive composition implementation X)
  intro C
  exact C.contains_generators X

theorem canonicalGeometricEffectiveThickSubcategory_contains_generator
    {M : localCanonicalEffectiveMotivesCategory composition implementation}
    (hM : canonicalEffectiveMotiveGenerator composition implementation M) :
    (canonicalGeometricEffectiveThickSubcategory composition implementation).P M := by
  show canonicalGeometricEffectiveCandidate composition implementation M
  intro C
  exact GeometricEffectiveSubcategoryCandidate.contains_generator
    (composition := composition) (implementation := implementation) C hM

theorem canonicalGeometricEffectiveThickSubcategory_le
    (C : GeometricEffectiveSubcategoryCandidate composition implementation)
    {M : localCanonicalEffectiveMotivesCategory composition implementation}
    (hM : (canonicalGeometricEffectiveThickSubcategory composition implementation).P M) :
    C.carrier.P M :=
  hM C

theorem canonicalGeometricEffectiveThickSubcategory_minimal
    (C : GeometricEffectiveSubcategoryCandidate composition implementation) :
    ∀ {M : localCanonicalEffectiveMotivesCategory composition implementation},
      (canonicalGeometricEffectiveThickSubcategory composition implementation).P M →
        C.carrier.P M :=
  canonicalGeometricEffectiveThickSubcategory_le composition implementation C

/-- The canonical geometric thick closure, repackaged as one admissible
candidate. -/
def canonicalGeometricEffectiveSubcategoryCandidate :
    GeometricEffectiveSubcategoryCandidate composition implementation where
  carrier := canonicalGeometricEffectiveThickSubcategory composition implementation
  closed_under_iso := by
    dsimp [canonicalGeometricEffectiveThickSubcategory]
    infer_instance
  contains_generators :=
    canonicalGeometricEffectiveThickSubcategory_contains_generators
      composition implementation

/-- The full subcategory of canonical effective motives cut out by the
canonical geometric thick-closure witness. -/
abbrev canonicalGeometricEffectiveMotives :=
  FullSubcategory
    (canonicalGeometricEffectiveThickSubcategory composition implementation).P

/-- The inclusion of canonical geometric effective motives into canonical
effective motives. -/
abbrev canonicalGeometricEffectiveMotivesInclusion :
    canonicalGeometricEffectiveMotives composition implementation ⥤
      localCanonicalEffectiveMotivesCategory composition implementation :=
  fullSubcategoryInclusion _

/-- The canonical effective motive of a smooth scheme, now regarded as an
object of the geometric effective full subcategory. -/
def canonicalGeometricEffectiveMotiveObject
    (X : Geometry.SmSchemeOver k) :
    canonicalGeometricEffectiveMotives composition implementation :=
  ⟨localCanonicalEffectiveMotive composition implementation X,
    canonicalGeometricEffectiveThickSubcategory_contains_generators
      composition implementation X⟩

/-- If one wants explicit idempotent completion on top of the thick closure,
the corresponding Karoubi envelope is available here. -/
abbrev canonicalGeometricEffectiveMotivesKaroubi :=
  CategoryTheory.Idempotents.Karoubi
    (canonicalGeometricEffectiveMotives composition implementation)

end

end Boundary
