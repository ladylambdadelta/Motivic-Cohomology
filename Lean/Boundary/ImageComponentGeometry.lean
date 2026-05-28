import Geometry.Cycles.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Image and Component Geometry

This file adds the generic geometric layers missing from the represented-prime
composition development:

* closed-image factorizations of arbitrary scheme morphisms;
* finite weighted decompositions of arbitrary schemes by integral closed
  subschemes;
* the combination of those two notions for a morphism viewed through its image.

These definitions are intentionally independent of the special support-fiber-
product geometry in `Boundary.CompositionGeometry`. They package the ambient
mathematics needed before one can build the concrete composition model from the
ground up.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Boundary

noncomputable section

/-- A factorization of a morphism through a closed image in the target. -/
structure ClosedImageFactorization
    {X Y : Scheme.{u}} (f : X ⟶ Y) where
  image : Scheme.{u}
  toImage : X ⟶ image
  imageToTarget : image ⟶ Y
  factorization : toImage ≫ imageToTarget = f
  imageClosedImmersion : IsClosedImmersion imageToTarget

namespace ClosedImageFactorization

@[reassoc (attr := simp)] theorem factorization_assoc
    {X Y Z : Scheme.{u}} {f : X ⟶ Y}
    (imageData : ClosedImageFactorization f)
    (g : Y ⟶ Z) :
    imageData.toImage ≫ imageData.imageToTarget ≫ g = f ≫ g := by
  simpa [Category.assoc] using congrArg (fun h => h ≫ g) imageData.factorization

end ClosedImageFactorization

/-- An integral closed subscheme equipped with a positive multiplicity. -/
structure WeightedIntClosedSubscheme (X : Scheme.{u}) where
  multiplicity : ℕ
  support : IntClosedSubscheme X

namespace WeightedIntClosedSubscheme

/-- The cycle contributed by a single weighted integral closed subscheme. -/
def toCycle {X : Scheme.{u}} (component : WeightedIntClosedSubscheme X) : AlgCycle X :=
  (component.multiplicity : ℤ) • AlgCycle.ofSubscheme component.support

@[simp] theorem toCycle_zero_coeff
    {X : Scheme.{u}} (component : WeightedIntClosedSubscheme X)
    (h : component.multiplicity = 0) :
    component.toCycle = 0 := by
  simp [WeightedIntClosedSubscheme.toCycle, h]

end WeightedIntClosedSubscheme

/-- A finite weighted decomposition of an arbitrary scheme by integral closed
subschemes. This is the raw finite family layer; cover theorems are recorded
separately below. -/
structure FiniteWeightedIntegralClosedFamily (X : Scheme.{u}) where
  index : Type u
  fintype_index : Fintype index
  decidableEq_index : DecidableEq index
  component : index → WeightedIntClosedSubscheme X

/-- A finite weighted decomposition of an arbitrary scheme by integral closed
subschemes whose images cover the ambient scheme. -/
structure FiniteWeightedIntegralClosedDecomposition (X : Scheme.{u})
    extends FiniteWeightedIntegralClosedFamily X where
  covers :
    ∀ x : X.carrier,
      ∃ i : index, x ∈ Set.range ((component i).support.inclusion.base)

namespace FiniteWeightedIntegralClosedFamily

/-- The cycle on the ambient scheme obtained by summing the weighted integral
components of the family. -/
def toCycle {X : Scheme.{u}}
    (family : FiniteWeightedIntegralClosedFamily X) : AlgCycle X := by
  classical
  letI := family.fintype_index
  letI := family.decidableEq_index
  exact Finset.univ.sum fun i => (family.component i).toCycle

end FiniteWeightedIntegralClosedFamily

namespace FiniteWeightedIntegralClosedDecomposition

/-- The cycle on the ambient scheme obtained by summing the weighted integral
components of the decomposition. -/
def toCycle {X : Scheme.{u}}
    (decomposition : FiniteWeightedIntegralClosedDecomposition X) : AlgCycle X := by
  exact decomposition.toFiniteWeightedIntegralClosedFamily.toCycle

theorem exists_mem_range_of_covers
    {X : Scheme.{u}}
    (decomposition : FiniteWeightedIntegralClosedDecomposition X)
    (x : X.carrier) :
    ∃ i : decomposition.index,
      x ∈ Set.range ((decomposition.component i).support.inclusion.base) :=
  decomposition.covers x

end FiniteWeightedIntegralClosedDecomposition

/-- A morphism equipped with a closed-image factorization together with a
finite weighted decomposition of that image by integral closed subschemes. -/
structure FiniteWeightedIntegralImageDecomposition
    {X Y : Scheme.{u}} (f : X ⟶ Y) where
  factorization : ClosedImageFactorization f
  decomposition :
    FiniteWeightedIntegralClosedDecomposition factorization.image

/-- A weaker image package recording only a finite weighted family on the image,
without yet asserting that the chosen components cover the whole image. This is
the direct generic target of the current support-fiber-product image
decomposition structures. -/
structure FiniteWeightedIntegralImageFamily
    {X Y : Scheme.{u}} (f : X ⟶ Y) where
  factorization : ClosedImageFactorization f
  family : FiniteWeightedIntegralClosedFamily factorization.image

namespace FiniteWeightedIntegralImageDecomposition

/-- View one weighted component of the image decomposition as a weighted
integral closed subscheme of the ambient target. -/
def componentInTarget
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (imageData : FiniteWeightedIntegralImageDecomposition f)
    (i : imageData.decomposition.index) :
    WeightedIntClosedSubscheme Y where
  multiplicity := (imageData.decomposition.component i).multiplicity
  support :=
    { scheme := (imageData.decomposition.component i).support.scheme
      inclusion :=
        (imageData.decomposition.component i).support.inclusion ≫
          imageData.factorization.imageToTarget
      isClosedImm := by
        letI := (imageData.decomposition.component i).support.isClosedImm
        letI := imageData.factorization.imageClosedImmersion
        infer_instance
      isIntegral := (imageData.decomposition.component i).support.isIntegral }

/-- The cycle on the ambient target obtained by pushing the image components
forward along the closed immersion of the image. -/
def toTargetCycle
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (imageData : FiniteWeightedIntegralImageDecomposition f) : AlgCycle Y := by
  classical
  letI := imageData.decomposition.fintype_index
  letI := imageData.decomposition.decidableEq_index
  exact Finset.univ.sum fun i => (imageData.componentInTarget i).toCycle

theorem exists_mem_target_range_of_covers
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (imageData : FiniteWeightedIntegralImageDecomposition f)
    (x : imageData.factorization.image.carrier) :
    ∃ i : imageData.decomposition.index,
      x ∈ Set.range
        ((imageData.decomposition.component i).support.inclusion.base) :=
  imageData.decomposition.covers x

end FiniteWeightedIntegralImageDecomposition

namespace FiniteWeightedIntegralImageFamily

/-- View one weighted image-family component as a weighted integral closed
subscheme of the ambient target. -/
def componentInTarget
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (imageData : FiniteWeightedIntegralImageFamily f)
    (i : imageData.family.index) :
    WeightedIntClosedSubscheme Y where
  multiplicity := (imageData.family.component i).multiplicity
  support :=
    { scheme := (imageData.family.component i).support.scheme
      inclusion :=
        (imageData.family.component i).support.inclusion ≫
          imageData.factorization.imageToTarget
      isClosedImm := by
        letI := (imageData.family.component i).support.isClosedImm
        letI := imageData.factorization.imageClosedImmersion
        infer_instance
      isIntegral := (imageData.family.component i).support.isIntegral }

/-- The cycle on the ambient target obtained from a finite weighted family on
the image by composing each closed immersion with the image inclusion. -/
def toTargetCycle
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (imageData : FiniteWeightedIntegralImageFamily f) : AlgCycle Y := by
  classical
  letI := imageData.family.fintype_index
  letI := imageData.family.decidableEq_index
  exact Finset.univ.sum fun i => (imageData.componentInTarget i).toCycle

end FiniteWeightedIntegralImageFamily

end

end Boundary
