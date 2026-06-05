import Boundary.A1NisLocalization
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
def canonicalA1NisNullObject
    (composition : Boundary.CanonicalCompositionData (k := k))
    [CategoryTheory.Limits.HasZeroObject
      (LinearPST (Boundary.canonicalCategory composition))]
    [CategoryTheory.Limits.HasZeroMorphisms
      (LinearPST (Boundary.canonicalCategory composition))]
    (X : LinearPST (Boundary.canonicalCategory composition)) : Prop :=
  canonicalA1NisLocalEquivalences composition
    (0 :
      LinearPST.zero
        (category := Boundary.canonicalCategory composition) ⟶ X)

/-- The full source subcategory of canonical A1/Nis null objects.  The Verdier
subcategory in motives is formed in the derived owner file from the same
zero-to-object local-equivalence predicate. -/
abbrev canonicalA1NisNullSubcategory
    (composition : Boundary.CanonicalCompositionData (k := k))
    [CategoryTheory.Limits.HasZeroObject
      (LinearPST (Boundary.canonicalCategory composition))]
    [CategoryTheory.Limits.HasZeroMorphisms
      (LinearPST (Boundary.canonicalCategory composition))] :=
  FullSubcategory (canonicalA1NisNullObject composition)

/-- The zero object is canonically A1/Nis-null. -/
theorem canonicalA1NisNullObject_zero
    (composition : Boundary.CanonicalCompositionData (k := k))
    [CategoryTheory.Limits.HasZeroObject
      (LinearPST (Boundary.canonicalCategory composition))]
    [CategoryTheory.Limits.HasZeroMorphisms
      (LinearPST (Boundary.canonicalCategory composition))] :
    canonicalA1NisNullObject composition
      (LinearPST.zero
        (category := Boundary.canonicalCategory composition)) := by
  change canonicalA1NisLocalEquivalences composition
    (0 :
      LinearPST.zero
        (category := Boundary.canonicalCategory composition) ⟶
          LinearPST.zero
            (category := Boundary.canonicalCategory composition))
  intro Z hZ
  rcases hZ with ⟨L, rfl⟩
  exact IsA1NisLocalEquivalence.id
    (LinearPST.zero
      (category := Boundary.canonicalCategory composition))
    L

/-- The canonical A1/Nis null predicate is closed under isomorphism. -/
theorem canonicalA1NisNullObject_of_iso

end Boundary
