import Boundary.PrimeSupport

/-!
# Cycle support atoms

This file fixes the public support atom used by the cycle lane.
The atom is the repo's integral closed subscheme package, reused directly.

This is the standard geometric input behind the cycle group and Chow group
formalism; cf. Fulton, *Intersection Theory*, §1.1, and Hartshorne,
*Algebraic Geometry*, Ch. I, §1–§2 for the underlying closed-subscheme
geometry.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary
namespace Cycles

noncomputable section

/-- The public cycle-support atom on a scheme: an integral closed immersion package. -/
structure CycleSupportAtom (X : Scheme.{u}) where
  scheme : Scheme.{u}
  inclusion : scheme ⟶ X
  isClosedImm : IsClosedImmersion inclusion
  isIntegral : IsIntegral scheme

attribute [instance] CycleSupportAtom.isIntegral

/-- A finite cycle support on a scheme. -/
abbrev CycleSupport (X : Scheme.{u}) : Type (u + 1) :=
  Finset (CycleSupportAtom X)

namespace CycleSupportAtom

/-- The underlying closed integral subscheme package. -/
def toIntClosedSubscheme {X : Scheme.{u}} (Z : CycleSupportAtom X) :
    IntClosedSubscheme X where
  scheme := Z.scheme
  inclusion := Z.inclusion
  isClosedImm := Z.isClosedImm
  isIntegral := Z.isIntegral

/-- The function field of a cycle-support atom. -/
def functionField {X : Scheme.{u}} (Z : CycleSupportAtom X) : CommRingCat :=
  IntClosedSubscheme.functionField Z.toIntClosedSubscheme

/-- The generic point image of a cycle-support atom. -/
noncomputable abbrev genericPoint {X : Scheme.{u}} (Z : CycleSupportAtom X) : X :=
  IntClosedSubscheme.genericPointImage Z.toIntClosedSubscheme

/-- Bridge constructor from an integral closed subscheme package. -/
def ofIntClosedSubscheme {X : Scheme.{u}} (Z : IntClosedSubscheme X) :
    CycleSupportAtom X where
  scheme := Z.scheme
  inclusion := Z.inclusion
  isClosedImm := Z.isClosedImm
  isIntegral := Z.isIntegral

@[simp] theorem toIntClosedSubscheme_ofIntClosedSubscheme {X : Scheme.{u}}
    (Z : IntClosedSubscheme X) :
    (ofIntClosedSubscheme Z).toIntClosedSubscheme = Z := rfl

@[simp] theorem ofIntClosedSubscheme_toIntClosedSubscheme {X : Scheme.{u}}
    (Z : CycleSupportAtom X) :
    ofIntClosedSubscheme Z.toIntClosedSubscheme = Z := by
  cases Z
  rfl

@[simp] theorem functionField_ofIntClosedSubscheme {X : Scheme.{u}}
    (Z : IntClosedSubscheme X) :
    (ofIntClosedSubscheme Z).functionField = Z.functionField := rfl

@[simp] theorem genericPoint_ofIntClosedSubscheme {X : Scheme.{u}}
    (Z : IntClosedSubscheme X) :
    (ofIntClosedSubscheme Z).genericPoint = Z.genericPointImage := rfl

end CycleSupportAtom

namespace CycleSupport

/-- The empty cycle support. -/
def empty {X : Scheme.{u}} : CycleSupport X :=
  ∅

/-- A singleton cycle support. -/
def singleton {X : Scheme.{u}} (Z : CycleSupportAtom X) : CycleSupport X :=
  {Z}

end CycleSupport

end

end Cycles
end Boundary
