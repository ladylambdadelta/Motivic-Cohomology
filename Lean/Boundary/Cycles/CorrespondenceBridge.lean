import Boundary.CorrespondenceSums

/-!
# Cycle-facing correspondence bridge

This file exposes the correspondence-side cycle objects under cycle-lane names.
The underlying theory is already owned by `Boundary.CorrespondenceSums` and
`Boundary.SupportEquivalence`; this file is just the stable public bridge
surface used by later Chow and Hodge work.

The correspondence package follows the standard cycle/correspondence formalism
of Voevodsky-Suslin-Friedlander, *Cycles, Transfers, and Motivic Homology
Theories*, Ch. 1, and Mazza-Voevodsky-Weibel, *Lecture Notes on Motivic
Cohomology*, Lect. 2.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

namespace Boundary
namespace Cycles

noncomputable section

/-- The geometric atom of the correspondence side: a quotient of represented
prime supports by the isomorphism-over-product relation. -/
abbrev CorrespondenceAtom (X Y : Geometry.SmSchemeOver k) :=
  PrimeFiniteCorrespondenceGeom X Y

/-- Integer-valued finite correspondences as a cycle-like free abelian group on
geometric prime correspondence atoms. -/
abbrev CorrespondenceGroup (X Y : Geometry.SmSchemeOver k) :=
  FiniteCorrespondence X Y

/-- Rational-valued finite correspondences as the rationalized correspondence
group. -/
abbrev RationalCorrespondenceGroup (X Y : Geometry.SmSchemeOver k) :=
  RationalFiniteCorrespondence X Y

/-- The canonical rationalization map from integral to rational correspondences. -/
abbrev toRational {X Y : Geometry.SmSchemeOver k} :
    CorrespondenceGroup X Y → RationalCorrespondenceGroup X Y :=
  FiniteCorrespondence.toRational

@[simp] theorem toRational_ofPrimeSupport
    {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport X Y) :
    toRational (X := X) (Y := Y) (FiniteCorrespondence.ofPrimeSupport Z) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented Z) (1 : ℚ) := by
  exact FiniteCorrespondence.toRational_ofPrimeSupport Z

@[simp] theorem toRational_ofWeightedPrimeSupport
    {X Y : Geometry.SmSchemeOver k}
    (Z : WeightedPrimeFiniteCorrespondenceSupport X Y) :
    toRational (X := X) (Y := Y) (FiniteCorrespondence.ofWeightedPrimeSupport Z) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented Z.prime)
        (Z.multiplicity : ℚ) := by
  exact FiniteCorrespondence.toRational_ofWeightedPrimeSupport Z

@[simp] theorem toRational_zero
    {X Y : Geometry.SmSchemeOver k} :
    toRational (X := X) (Y := Y) (0 : CorrespondenceGroup X Y) = 0 := by
  exact FiniteCorrespondence.toRational_zero

theorem toRational_add
    {X Y : Geometry.SmSchemeOver k} (left right : CorrespondenceGroup X Y) :
    toRational (X := X) (Y := Y) (left + right) =
      toRational (X := X) (Y := Y) left + toRational (X := X) (Y := Y) right := by
  exact FiniteCorrespondence.toRational_add left right

theorem toRational_smul
    {X Y : Geometry.SmSchemeOver k} (coeff : ℤ) (corr : CorrespondenceGroup X Y) :
    toRational (X := X) (Y := Y) (coeff • corr) =
      coeff • toRational (X := X) (Y := Y) corr := by
  exact FiniteCorrespondence.toRational_smul coeff corr

end

end Cycles
end Boundary
