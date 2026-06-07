import Boundary.A1NisNull
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
/-- Compatibility bundle of canonical A1/Nis localization structure for downstream
consumers that request multiple localization components at once.

Core A1/Nis constructions are provided in owner modules; this record packages
their stable projections for API compatibility during gradual downstream
migration. Reference: Gabriel–Zisman, `Calculus of Fractions and Homotopy
Theory`. -/
structure CanonicalA1NisLocalizationImplementation
    (composition : Boundary.CanonicalCompositionData (k := k)) where
  sourcePreadditive :
    Preadditive (LinearPST (Boundary.canonicalCategory composition)) := by
      exact Boundary.linearPSTPreadditive
        (category := Boundary.canonicalCategory composition)
  leftCalculus :
    CanonicalA1NisLeftCalculusPackage composition
  localizedPreadditive :
    Preadditive (canonicalA1NisLocalization composition) := by
      exact canonicalA1NisLocalization_preadditive_of_leftCalculus
        composition leftCalculus
  sourceHasZeroObject :
    CategoryTheory.Limits.HasZeroObject
      (LinearPST (Boundary.canonicalCategory composition)) := by
        exact LinearPST.hasZeroObject
          (category := Boundary.canonicalCategory composition)
  localizedHasZeroObject :
    CategoryTheory.Limits.HasZeroObject
      (canonicalA1NisLocalization composition) := by
        exact canonicalA1NisLocalization_hasZeroObject_of_leftCalculus
          composition leftCalculus
  sourceHasTerminal :
    CategoryTheory.Limits.HasTerminal
      (LinearPST (Boundary.canonicalCategory composition)) := by
        exact canonicalLinearPST_hasTerminal composition
  localizedHasTerminal :
    CategoryTheory.Limits.HasTerminal
      (canonicalA1NisLocalization composition) := by
        exact canonicalA1NisLocalization_hasTerminal_of_leftCalculus
          composition leftCalculus
  sourceHasZeroMorphisms :
    CategoryTheory.Limits.HasZeroMorphisms
      (LinearPST (Boundary.canonicalCategory composition)) := by
        letI := Boundary.linearPSTPreadditive
          (category := Boundary.canonicalCategory composition)
        infer_instance
  localizedHasZeroMorphisms :
    CategoryTheory.Limits.HasZeroMorphisms
      (canonicalA1NisLocalization composition) := by
        exact canonicalA1NisLocalization_hasZeroMorphisms_of_leftCalculus
          composition leftCalculus
  sourceHasBinaryBiproducts :
    CategoryTheory.Limits.HasBinaryBiproducts
      (LinearPST (Boundary.canonicalCategory composition)) := by
        exact LinearPST.hasBinaryBiproducts
          (category := Boundary.canonicalCategory composition)
  sourceHasFiniteBiproducts :
    CategoryTheory.Limits.HasFiniteBiproducts
      (LinearPST (Boundary.canonicalCategory composition)) := by
        exact LinearPST.hasFiniteBiproducts
          (category := Boundary.canonicalCategory composition)
  localizedHasFiniteBiproducts :
    CategoryTheory.Limits.HasFiniteBiproducts
      (canonicalA1NisLocalization composition) := by
        exact canonicalA1NisLocalization_hasFiniteBiproducts_of_leftCalculus
          composition leftCalculus
  sourceHasFiniteProducts :
    CategoryTheory.Limits.HasFiniteProducts
      (LinearPST (Boundary.canonicalCategory composition)) := by
        exact LinearPST.hasFiniteProducts
          (category := Boundary.canonicalCategory composition)
  localizedHasFiniteProducts :
    CategoryTheory.Limits.HasFiniteProducts
      (canonicalA1NisLocalization composition) := by
        exact canonicalA1NisLocalization_hasFiniteProducts_of_leftCalculus
          composition leftCalculus
  sourceHasFiniteCoproducts :
    CategoryTheory.Limits.HasFiniteCoproducts
      (LinearPST (Boundary.canonicalCategory composition)) := by
        exact LinearPST.hasFiniteCoproducts
          (category := Boundary.canonicalCategory composition)
  localizedHasFiniteCoproducts :
    CategoryTheory.Limits.HasFiniteCoproducts
      (canonicalA1NisLocalization composition) := by
        exact canonicalA1NisLocalization_hasFiniteCoproducts_of_leftCalculus
          composition leftCalculus
  sourceHasFiniteLimits :
    CategoryTheory.Limits.HasFiniteLimits
      (LinearPST (Boundary.canonicalCategory composition)) := by
        exact LinearPST.hasFiniteLimits
          (category := Boundary.canonicalCategory composition)
  localizedHasFiniteLimits :
    CategoryTheory.Limits.HasFiniteLimits
      (canonicalA1NisLocalization composition)
  sourceHasFiniteColimits :
    CategoryTheory.Limits.HasFiniteColimits
      (LinearPST (Boundary.canonicalCategory composition)) := by
        exact LinearPST.hasFiniteColimits
          (category := Boundary.canonicalCategory composition)
  localizedHasFiniteColimits :
    CategoryTheory.Limits.HasFiniteColimits
      (canonicalA1NisLocalization composition)
  localizationPreservesZeroMorphisms :
    letI := sourceHasZeroMorphisms
    letI := localizedHasZeroMorphisms
    (canonicalA1NisLocalizationFunctor composition).PreservesZeroMorphisms := by
      exact
        canonicalA1NisLocalizationFunctor_preservesZeroMorphisms_of_leftCalculus
          composition leftCalculus
  localizationPreservesFiniteBiproducts :
    letI := sourceHasZeroMorphisms
    letI := localizedHasZeroMorphisms
    letI := localizationPreservesZeroMorphisms
    CategoryTheory.Limits.PreservesFiniteBiproducts
      (canonicalA1NisLocalizationFunctor composition)
  localizationPreservesFiniteProducts :
    CategoryTheory.Limits.PreservesFiniteProducts
      (canonicalA1NisLocalizationFunctor composition) := by
        exact
          canonicalA1NisLocalizationFunctor_preservesFiniteProducts_of_leftCalculus
            composition leftCalculus
  localizationPreservesTerminal :
    CategoryTheory.Limits.PreservesLimit
      (Functor.empty.{0}
        (LinearPST (Boundary.canonicalCategory composition)))
      (canonicalA1NisLocalizationFunctor composition) := by
        exact
          canonicalA1NisLocalizationFunctor_preservesTerminal_of_leftCalculus
            composition leftCalculus
  localizationPreservesFiniteCoproducts :
    CategoryTheory.Limits.PreservesFiniteCoproducts
      (canonicalA1NisLocalizationFunctor composition)
  sourceAdditive :
    BoundaryAdditiveCategoryStructure
      (LinearPST (Boundary.canonicalCategory composition)) := by
        exact
          { preadditive := Boundary.linearPSTPreadditive
              (category := Boundary.canonicalCategory composition)
            hasZeroObject := LinearPST.hasZeroObject
              (category := Boundary.canonicalCategory composition)
            hasZeroMorphisms := by
              letI := Boundary.linearPSTPreadditive
                (category := Boundary.canonicalCategory composition)
              infer_instance
            hasFiniteBiproducts := LinearPST.hasFiniteBiproducts
              (category := Boundary.canonicalCategory composition) }
  localizedAdditive :
    BoundaryAdditiveCategoryStructure
      (canonicalA1NisLocalization composition)
  sourceHasKernels :
    CategoryTheory.Limits.HasKernels
      (LinearPST (Boundary.canonicalCategory composition)) := by
        exact LinearPST.hasKernels
          (category := Boundary.canonicalCategory composition)
  localizedHasKernels :
    CategoryTheory.Limits.HasKernels
      (canonicalA1NisLocalization composition)
  sourceHasCokernels :
    CategoryTheory.Limits.HasCokernels
      (LinearPST (Boundary.canonicalCategory composition)) := by
        exact LinearPST.hasCokernels
          (category := Boundary.canonicalCategory composition)
  localizedHasCokernels :
    CategoryTheory.Limits.HasCokernels
      (canonicalA1NisLocalization composition)
  sourceHasImages :
    CategoryTheory.Limits.HasImages
      (LinearPST (Boundary.canonicalCategory composition))
  localizedHasImages :
    CategoryTheory.Limits.HasImages
      (canonicalA1NisLocalization composition)
  weakEquivalences :
    CanonicalA1NisWeakEquivalencePackage composition
  reflector :
    letI := sourcePreadditive
    CanonicalA1NisReflectorPackage composition

def canonicalA1NisLocalizationFunctor_additive
    (composition : Boundary.CanonicalCompositionData (k := k))
    (implementation :
      CanonicalA1NisLocalizationImplementation composition) :
    letI := implementation.sourcePreadditive
    letI := implementation.localizedPreadditive
    (canonicalA1NisLocalizationFunctor composition).Additive := by
  exact canonicalA1NisLocalizationFunctor_additive_of_leftCalculus
    composition implementation.leftCalculus

/-- Finite-limit preservation of the canonical A1/Nis localization functor,
proved from the reflector comparison. -/
def canonicalA1NisLocalizationFunctor_preservesFiniteLimits
    (composition : Boundary.CanonicalCompositionData (k := k))
    (implementation :
      CanonicalA1NisLocalizationImplementation composition) :
    Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition) :=
  canonicalA1NisLocalizationFunctor_preservesFiniteLimits_of_reflector
    composition implementation.reflector

/-- Finite-colimit preservation of the canonical A1/Nis localization functor,
proved from the reflector comparison. -/
def canonicalA1NisLocalizationFunctor_preservesFiniteColimits
    (composition : Boundary.CanonicalCompositionData (k := k))
    (implementation :
      CanonicalA1NisLocalizationImplementation composition) :
    Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition) :=
  canonicalA1NisLocalizationFunctor_preservesFiniteColimits_of_reflector
    composition implementation.reflector

/-- The actual canonical A1/Nis sheafification functor, projected from the
owner implementation record. -/
def canonicalA1NisSheafification
    (composition : Boundary.CanonicalCompositionData (k := k))
    (implementation :
      CanonicalA1NisLocalizationImplementation composition) :
    LinearPST (Boundary.canonicalCategory composition) ⥤
      LinearA1NisLocalPST (Boundary.canonicalCategory composition) := by
  letI := implementation.sourcePreadditive
  exact implementation.reflector.reflector

/-- The actual A1/Nis sheafification adjunction.

Proof chain:

1. `LinearA1NisLocalPST.inclusion` is the full faithful inclusion of bundled
   local objects into `LinearPST`.
2. The implementation record carries the canonical reflector functor onto that
   full subcategory.
3. By construction, this reflector is left adjoint to the inclusion.

This is the owner-file realization of the A1/Nis sheafification adjunction
promised earlier in the file. -/
def canonicalA1NisSheafificationAdjunction
    (composition : Boundary.CanonicalCompositionData (k := k))
    (implementation :
      CanonicalA1NisLocalizationImplementation composition) :
    canonicalA1NisSheafification composition implementation ⊣
      LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition) := by
  letI := implementation.sourcePreadditive
  exact implementation.reflector.adjunction

/-- The canonical sheafification lands in the bundled subcategory of
`A1`+Nisnevich-local linear presheaves by construction. -/
theorem canonicalA1NisSheafification_obj_isLocal
    (composition : Boundary.CanonicalCompositionData (k := k))
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    (X : LinearPST (Boundary.canonicalCategory composition)) :
    letI := implementation.sourcePreadditive
    IsLinearA1NisLocal
      ((canonicalA1NisSheafification composition implementation).obj X).toLinearPST :=
  ((canonicalA1NisSheafification composition implementation).obj X).2

/-- The canonical A1/Nis sheafification preserves zero morphisms because the
implementation record carries it as an additive reflector. -/
theorem canonicalA1NisSheafification_preservesZeroMorphisms
    (composition : Boundary.CanonicalCompositionData (k := k))
    (implementation :
      CanonicalA1NisLocalizationImplementation composition) :
    letI := implementation.sourcePreadditive
    (canonicalA1NisSheafification composition implementation).PreservesZeroMorphisms := by
  letI := implementation.sourcePreadditive
  letI : Preadditive (LinearA1NisLocalPST (Boundary.canonicalCategory composition)) :=
    LinearA1NisLocalPST.preadditive
  letI : (canonicalA1NisSheafification composition implementation).Additive :=
    implementation.reflector.additive
  infer_instance

/-- The canonical A1/Nis sheafification preserves the terminal object. -/
theorem canonicalA1NisSheafification_preservesTerminal
    (composition : Boundary.CanonicalCompositionData (k := k))
    (implementation :
      CanonicalA1NisLocalizationImplementation composition) :
    letI := implementation.sourcePreadditive
    CategoryTheory.Limits.PreservesLimit
      (Functor.empty.{0}
        (LinearPST (Boundary.canonicalCategory composition)))
      (canonicalA1NisSheafification composition implementation) := by
  letI := implementation.sourcePreadditive
  letI : Preadditive (LinearA1NisLocalPST (Boundary.canonicalCategory composition)) :=
    LinearA1NisLocalPST.preadditive
  letI : CategoryTheory.Limits.HasZeroObject
      (LinearPST (Boundary.canonicalCategory composition)) :=
    LinearPST.hasZeroObject
      (category := Boundary.canonicalCategory composition)
  letI : CategoryTheory.Limits.HasZeroObject
      (LinearA1NisLocalPST (Boundary.canonicalCategory composition)) :=
    by infer_instance
  letI : (canonicalA1NisSheafification composition implementation).PreservesZeroMorphisms :=
    canonicalA1NisSheafification_preservesZeroMorphisms
      composition implementation
  exact
    CategoryTheory.preservesTerminalObject_of_preservesZeroMorphisms
      (canonicalA1NisSheafification composition implementation)

/-- Naturality of the canonical reflector counit on local objects. -/
theorem canonicalA1NisSheafification_map_isLocal
    (composition : Boundary.CanonicalCompositionData (k := k))
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    {L M : LinearA1NisLocalPST (Boundary.canonicalCategory composition)}
    (φ : L ⟶ M) :
    letI := implementation.sourcePreadditive
    (canonicalA1NisSheafification composition implementation).map
        ((LinearA1NisLocalPST.inclusion
          (Boundary.canonicalCategory composition)).map φ) ≫
      (canonicalA1NisSheafificationAdjunction composition implementation).counit.app M =
        (canonicalA1NisSheafificationAdjunction composition implementation).counit.app L ≫ φ := by
  letI := implementation.sourcePreadditive
  exact
    (canonicalA1NisSheafificationAdjunction
      composition implementation).counit.naturality φ

/-- On bundled local objects, canonical sheafification is the reflector: the
counit identifies the sheafification of the underlying ambient object with the
original local object. -/
noncomputable def canonicalA1NisSheafification_reflector_fac
    (composition : Boundary.CanonicalCompositionData (k := k))
    (implementation :
      CanonicalA1NisLocalizationImplementation composition)
    (L : LinearA1NisLocalPST (Boundary.canonicalCategory composition)) :
    letI := implementation.sourcePreadditive
    (canonicalA1NisSheafification composition implementation).obj
        ((LinearA1NisLocalPST.inclusion
          (Boundary.canonicalCategory composition)).obj L) ≅
      L := by
  letI := implementation.sourcePreadditive
  letI : IsIso
      ((canonicalA1NisSheafificationAdjunction composition implementation).counit.app L) :=
    implementation.reflector.counit_isIso L
  exact asIso
    ((canonicalA1NisSheafificationAdjunction composition implementation).counit.app L)

theorem canonicalA1NisSheafification_isLocalization
    (composition : Boundary.CanonicalCompositionData (k := k))
    (implementation :
      CanonicalA1NisLocalizationImplementation composition) :
    letI := implementation.sourcePreadditive
    (canonicalA1NisSheafification composition implementation).IsLocalization
      (Localization.LeftBousfield.W
        (· ∈ Set.range
          (LinearA1NisLocalPST.inclusion
            (Boundary.canonicalCategory composition)).obj)) := by
  letI := implementation.sourcePreadditive
  exact
    a1NisLocalization_of_adj
      (category := Boundary.canonicalCategory composition)
      (canonicalA1NisSheafification composition implementation)
      (canonicalA1NisSheafificationAdjunction composition implementation)

end Boundary
