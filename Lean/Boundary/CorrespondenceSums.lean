import Boundary.SupportEquivalence
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Correspondence Sums

This file packages finite formal sums of represented prime supports and their
pushforward to quotient-level geometric prime-support classes.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

namespace Boundary

noncomputable section

open PrimeFiniteCorrespondenceSupport

/-- Package a prime finite correspondence support with a positive multiplicity. -/
structure WeightedPrimeFiniteCorrespondenceSupport
    (X Y : Geometry.SmSchemeOver k) where
  multiplicity : ℕ
  prime : PrimeFiniteCorrespondenceSupport X Y

/-- An effective finite correspondence presentation is a finite formal
`ℕ`-linear combination of represented prime finite correspondence supports. -/
abbrev EffectiveFiniteCorrespondencePresentation
  (X Y : Geometry.SmSchemeOver k) : Type (u + 1) :=
  PrimeFiniteCorrespondenceSupport X Y →₀ ℕ

/-- A finite correspondence presentation is a finite formal `ℤ`-linear
combination of represented prime finite correspondence supports. -/
abbrev FiniteCorrespondencePresentation
  (X Y : Geometry.SmSchemeOver k) : Type (u + 1) :=
  PrimeFiniteCorrespondenceSupport X Y →₀ ℤ

/-- An effective finite correspondence is a finite formal `ℕ`-linear
combination of geometric prime finite correspondences. -/
abbrev EffectiveFiniteCorrespondence
  (X Y : Geometry.SmSchemeOver k) : Type (u + 1) :=
  PrimeFiniteCorrespondenceGeom X Y →₀ ℕ

/-- A finite correspondence is a finite formal `ℤ`-linear combination of
geometric prime finite correspondences. -/
abbrev FiniteCorrespondence
  (X Y : Geometry.SmSchemeOver k) : Type (u + 1) :=
  PrimeFiniteCorrespondenceGeom X Y →₀ ℤ

/-- A rational finite correspondence is a finite formal `ℚ`-linear
combination of geometric prime finite correspondences. This is the concrete
normal form of rationalizing `FiniteCorrespondence X Y` over `ℤ`. -/
abbrev RationalFiniteCorrespondence
  (X Y : Geometry.SmSchemeOver k) : Type (u + 1) :=
  PrimeFiniteCorrespondenceGeom X Y →₀ ℚ

namespace EffectiveFiniteCorrespondencePresentation

/-- The presentation associated to a single represented prime support with
multiplicity `1`. -/
def ofPrimeSupport {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport X Y) :
    EffectiveFiniteCorrespondencePresentation X Y := by
  classical
  exact Finsupp.single Z 1

/-- The presentation associated to a weighted represented prime support. -/
def ofWeightedPrimeSupport {X Y : Geometry.SmSchemeOver k}
    (Z : WeightedPrimeFiniteCorrespondenceSupport X Y) :
    EffectiveFiniteCorrespondencePresentation X Y := by
  classical
  exact Finsupp.single Z.prime Z.multiplicity

/-- Push a raw effective presentation forward along the quotient map from
represented prime supports to geometric prime supports. -/
def toGeom {X Y : Geometry.SmSchemeOver k}
    (c : EffectiveFiniteCorrespondencePresentation X Y) :
    EffectiveFiniteCorrespondence X Y :=
  c.mapDomain PrimeFiniteCorrespondenceGeom.ofRepresented

@[simp] theorem toGeom_zero {X Y : Geometry.SmSchemeOver k} :
    EffectiveFiniteCorrespondencePresentation.toGeom
      (0 : EffectiveFiniteCorrespondencePresentation X Y) = 0 := by
  change Finsupp.mapDomain PrimeFiniteCorrespondenceGeom.ofRepresented
      (0 : EffectiveFiniteCorrespondencePresentation X Y) = 0
  exact Finsupp.mapDomain_zero

@[simp] theorem toGeom_add {X Y : Geometry.SmSchemeOver k}
    (a b : EffectiveFiniteCorrespondencePresentation X Y) :
    EffectiveFiniteCorrespondencePresentation.toGeom (a + b) =
      EffectiveFiniteCorrespondencePresentation.toGeom a +
        EffectiveFiniteCorrespondencePresentation.toGeom b := by
  change Finsupp.mapDomain PrimeFiniteCorrespondenceGeom.ofRepresented (a + b) =
    Finsupp.mapDomain PrimeFiniteCorrespondenceGeom.ofRepresented a +
      Finsupp.mapDomain PrimeFiniteCorrespondenceGeom.ofRepresented b
  exact Finsupp.mapDomain_add

/-- The quotient projection sends a singleton represented prime support to the
corresponding singleton geometric prime support. -/
theorem toGeom_single {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) :
  EffectiveFiniteCorrespondencePresentation.toGeom
    (Finsupp.single P 1 : EffectiveFiniteCorrespondencePresentation X Y) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1 := by
  change Finsupp.mapDomain PrimeFiniteCorrespondenceGeom.ofRepresented
      (Finsupp.single P 1) =
    Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1
  exact Finsupp.mapDomain_single

end EffectiveFiniteCorrespondencePresentation

namespace FiniteCorrespondencePresentation

/-- The presentation associated to a single represented prime support with
coefficient `1`. -/
def ofPrimeSupport {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport X Y) :
    FiniteCorrespondencePresentation X Y := by
  classical
  exact Finsupp.single Z 1

/-- Regard a weighted represented prime support as a presentation with integer
coefficient equal to its multiplicity. -/
def ofWeightedPrimeSupport {X Y : Geometry.SmSchemeOver k}
    (Z : WeightedPrimeFiniteCorrespondenceSupport X Y) :
    FiniteCorrespondencePresentation X Y := by
  classical
  exact Finsupp.single Z.prime (Z.multiplicity : ℤ)

/-- Push a raw integral presentation forward along the quotient map from
represented prime supports to geometric prime supports. -/
def toGeom {X Y : Geometry.SmSchemeOver k}
    (c : FiniteCorrespondencePresentation X Y) :
    FiniteCorrespondence X Y :=
  c.mapDomain PrimeFiniteCorrespondenceGeom.ofRepresented

@[simp] theorem toGeom_zero {X Y : Geometry.SmSchemeOver k} :
    FiniteCorrespondencePresentation.toGeom
      (0 : FiniteCorrespondencePresentation X Y) = 0 := by
  change Finsupp.mapDomain PrimeFiniteCorrespondenceGeom.ofRepresented
      (0 : FiniteCorrespondencePresentation X Y) = 0
  exact Finsupp.mapDomain_zero

@[simp] theorem toGeom_add {X Y : Geometry.SmSchemeOver k}
    (a b : FiniteCorrespondencePresentation X Y) :
    FiniteCorrespondencePresentation.toGeom (a + b) =
      FiniteCorrespondencePresentation.toGeom a +
        FiniteCorrespondencePresentation.toGeom b := by
  change Finsupp.mapDomain PrimeFiniteCorrespondenceGeom.ofRepresented (a + b) =
    Finsupp.mapDomain PrimeFiniteCorrespondenceGeom.ofRepresented a +
      Finsupp.mapDomain PrimeFiniteCorrespondenceGeom.ofRepresented b
  exact Finsupp.mapDomain_add

/-- The quotient projection sends a singleton represented prime support to the
corresponding singleton geometric prime support. -/
theorem toGeom_single {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) :
  FiniteCorrespondencePresentation.toGeom
    (Finsupp.single P 1 : FiniteCorrespondencePresentation X Y) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1 := by
  change Finsupp.mapDomain PrimeFiniteCorrespondenceGeom.ofRepresented
      (Finsupp.single P 1) =
    Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1
  exact Finsupp.mapDomain_single

end FiniteCorrespondencePresentation

namespace EffectiveFiniteCorrespondence

/-- The effective correspondence associated to a single prime support with
multiplicity `1`. -/
def ofPrimeSupport {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport X Y) : EffectiveFiniteCorrespondence X Y := by
  classical
  exact Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented Z) 1

/-- The effective correspondence associated to a weighted prime support. -/
def ofWeightedPrimeSupport {X Y : Geometry.SmSchemeOver k}
    (Z : WeightedPrimeFiniteCorrespondenceSupport X Y) : EffectiveFiniteCorrespondence X Y := by
  classical
  exact Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented Z.prime) Z.multiplicity

/-- Equivalent represented prime supports determine the same singleton
effective correspondence. -/
theorem single_eq_of_primeSupportEquivalent {X Y : Geometry.SmSchemeOver k}
    {P Q : RepresentedPrimeSupport X Y} (h : PrimeSupportEquivalent P Q) :
    Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1 =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented Q) 1 := by
  rw [PrimeFiniteCorrespondenceGeom.eq_of_primeSupportEquivalent h]

end EffectiveFiniteCorrespondence

namespace FiniteCorrespondence

/-- The finite correspondence associated to a single prime support with
coefficient `1`. -/
def ofPrimeSupport {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport X Y) : FiniteCorrespondence X Y := by
  classical
  exact Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented Z) 1

/-- Regard a weighted prime support as a finite correspondence with integer
coefficient equal to its multiplicity. -/
def ofWeightedPrimeSupport {X Y : Geometry.SmSchemeOver k}
    (Z : WeightedPrimeFiniteCorrespondenceSupport X Y) : FiniteCorrespondence X Y := by
  classical
  exact Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented Z.prime)
    (Z.multiplicity : ℤ)

/-- Equivalent represented prime supports determine the same singleton finite
correspondence. -/
theorem single_eq_of_primeSupportEquivalent {X Y : Geometry.SmSchemeOver k}
    {P Q : RepresentedPrimeSupport X Y} (h : PrimeSupportEquivalent P Q) :
    Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1 =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented Q) 1 := by
  rw [PrimeFiniteCorrespondenceGeom.eq_of_primeSupportEquivalent h]

/-- Cast an integral finite correspondence to rational coefficients. -/
noncomputable def toRationalLinearMap {X Y : Geometry.SmSchemeOver k} :
    FiniteCorrespondence X Y →ₗ[ℤ] RationalFiniteCorrespondence X Y :=
  Finsupp.mapRange.linearMap (Algebra.linearMap ℤ ℚ)

/-- Cast an integral finite correspondence to rational coefficients. -/
def toRational {X Y : Geometry.SmSchemeOver k}
    (corr : FiniteCorrespondence X Y) :
    RationalFiniteCorrespondence X Y :=
  toRationalLinearMap corr

@[simp] theorem toRational_zero {X Y : Geometry.SmSchemeOver k} :
    toRational (0 : FiniteCorrespondence X Y) = 0 := by
  simp [toRational]

@[simp] theorem toRational_add {X Y : Geometry.SmSchemeOver k}
    (left right : FiniteCorrespondence X Y) :
    toRational (left + right) = toRational left + toRational right := by
  simpa [toRational] using (toRationalLinearMap.map_add left right)

@[simp] theorem toRational_smul {X Y : Geometry.SmSchemeOver k}
    (coeff : ℤ) (corr : FiniteCorrespondence X Y) :
    toRational (coeff • corr) = coeff • toRational corr := by
  simpa [toRational] using (toRationalLinearMap.map_smul coeff corr)

@[simp] theorem toRational_single {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ) :
    toRational (Finsupp.single prime coeff : FiniteCorrespondence X Y) =
      Finsupp.single prime (coeff : ℚ) := by
  ext otherPrime
  by_cases h : otherPrime = prime
  · subst h
    simp [toRational, toRationalLinearMap]
  · simp [toRational, toRationalLinearMap, h]

@[simp] theorem toRational_ofPrimeSupport {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport X Y) :
    toRational (ofPrimeSupport Z) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented Z) (1 : ℚ) := by
  simp [ofPrimeSupport]

@[simp] theorem toRational_ofWeightedPrimeSupport {X Y : Geometry.SmSchemeOver k}
    (Z : WeightedPrimeFiniteCorrespondenceSupport X Y) :
    toRational (ofWeightedPrimeSupport Z) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented Z.prime)
        (Z.multiplicity : ℚ) := by
  simp [ofWeightedPrimeSupport]

end FiniteCorrespondence

end

end Boundary
