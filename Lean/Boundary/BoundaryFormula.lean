import Boundary.DiagonalDecomposition

/-!
# Boundary Formula Foundations

This file packages pushforward support data, raw boundary formula geometry, and
the coefficient criterion that identifies a pushed boundary correspondence with
the diagonal identity correspondence.

The cycle-theoretic background is pushforward of cycles and diagonal
correspondences; cf. Fulton, *Intersection Theory*, Ch. 1, and
Voevodsky-Suslin-Friedlander, *Cycles, Transfers, and Motivic Homology
Theories*, Ch. 1.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

open PrimeFiniteCorrespondenceSupport

noncomputable section

/-- Data representing the pushforward of a represented prime support on `B`
along a morphism `ν : B → C`.

This record packages a pushed support on `C ×_k C` together with the geometric
maps relating it to the original support and to the ambient morphism `ν`.
Pushforward correspondences are obtained from such geometric data below; cf.
Fulton, *Intersection Theory*, §1.4 for cycle pushforward. -/
structure PushforwardPrimeSupportData {B C : Geometry.SmSchemeOver k}
    (ν : SmOverHom B C) (P : RepresentedPrimeSupport B B) where
  targetSourceComponent : SourceIrreducibleComponent C
  pushSupport : Scheme
  pushSupport_isIntegral : IsIntegral pushSupport
  sourceComponentMap :
    P.sourceImage.carrier.scheme ⟶ targetSourceComponent.carrier.scheme
  sourceComponentMap_toAmbient :
    sourceComponentMap ≫ targetSourceComponent.toAmbient =
      P.sourceImage.toAmbient ≫ ν.hom
  finiteOverTargetSource : pushSupport ⟶ targetSourceComponent.carrier.scheme
  finite_toTargetSource : IsFinite finiteOverTargetSource
  surjective_toTargetSource : Function.Surjective finiteOverTargetSource.base
  toTarget : pushSupport ⟶ C.scheme
  inclusion : pushSupport ⟶ overBaseProduct targetSourceComponent.carrier C
  inclusion_fst : inclusion ≫ overBaseProduct.fst targetSourceComponent.carrier C =
    finiteOverTargetSource
  inclusion_snd : inclusion ≫ overBaseProduct.snd targetSourceComponent.carrier C =
    toTarget
  isClosedImmersion : IsClosedImmersion inclusion
  mapFromOriginal : P.support ⟶ pushSupport
  mapFromOriginal_toSource :
    mapFromOriginal ≫ finiteOverTargetSource =
      P.finiteOverSourceComponent ≫ sourceComponentMap
  mapFromOriginal_toTarget :
    mapFromOriginal ≫ toTarget = P.toTarget ≫ ν.hom

namespace PushforwardPrimeSupportData

/-- The represented prime support on `C ×_k C` encoded by pushforward data. -/
def toRepresentedPrimeSupport {B C : Geometry.SmSchemeOver k}
    {ν : SmOverHom B C} {P : RepresentedPrimeSupport B B}
    (data : PushforwardPrimeSupportData ν P) :
    RepresentedPrimeSupport C C where
  sourceImage := SourceImageSubscheme.ofSourceIrreducibleComponent data.targetSourceComponent
  support := data.pushSupport
  isIntegral := data.pushSupport_isIntegral
  finiteOverSourceComponent := data.finiteOverTargetSource
  finite_toSourceComponent := data.finite_toTargetSource
  surjective_toSourceComponent := data.surjective_toTargetSource
  toTarget := data.toTarget
  inclusion := data.inclusion
  inclusion_fst := data.inclusion_fst
  inclusion_snd := data.inclusion_snd
  isClosedImmersion := data.isClosedImmersion

end PushforwardPrimeSupportData

/-- Geometry producing a future boundary formula over `C`.

This packages only geometric input data: a boundary source lying over `C`, a
finite family of represented prime supports on that source, and the integer
weights attached to those supports. No theorem identifying the resulting sum
with the identity correspondence is stored here. Such an identity must later be
proved from additional geometric lemmas, such as pushforward and coefficient
computations. -/
structure BoundaryFormulaGeometry (C : Geometry.SmSchemeOver k) where
  boundarySource : Geometry.SmSchemeOver k
  nu : SmOverHom boundarySource C
  nu_finite : IsFinite nu.hom
  boundaryIndex : Type u
  boundaryIndex_fintype : Fintype boundaryIndex
  boundarySupport : boundaryIndex → RepresentedPrimeSupport boundarySource boundarySource
  multiplicity : boundaryIndex → ℤ

namespace BoundaryFormulaGeometry

instance {C : Geometry.SmSchemeOver k} (geometry : BoundaryFormulaGeometry C) :
    Fintype geometry.boundaryIndex :=
  geometry.boundaryIndex_fintype

/-- The raw finite correspondence presentation produced by the indexed boundary
supports and their multiplicities. -/
def boundaryPresentation {C : Geometry.SmSchemeOver k}
    (geometry : BoundaryFormulaGeometry C) :
    FiniteCorrespondencePresentation geometry.boundarySource geometry.boundarySource := by
  classical
  exact Finset.univ.sum fun boundaryIndex =>
    Finsupp.single (geometry.boundarySupport boundaryIndex)
      (geometry.multiplicity boundaryIndex)

/-- The quotient-indexed finite correspondence on the boundary source obtained
from the raw boundary presentation. -/
def boundaryCorrespondence {C : Geometry.SmSchemeOver k}
    (geometry : BoundaryFormulaGeometry C) :
    FiniteCorrespondence geometry.boundarySource geometry.boundarySource :=
  geometry.boundaryPresentation.toGeom

/-- The raw finite correspondence presentation obtained by pushing each indexed
boundary support forward to a represented prime support on `C ×_k C`. -/
def pushedBoundaryPresentation {C : Geometry.SmSchemeOver k}
    (geometry : BoundaryFormulaGeometry C)
    (pushData : ∀ boundaryIndex,
      PushforwardPrimeSupportData geometry.nu (geometry.boundarySupport boundaryIndex)) :
    FiniteCorrespondencePresentation C C := by
  classical
  exact Finset.univ.sum fun boundaryIndex =>
    Finsupp.single ((pushData boundaryIndex).toRepresentedPrimeSupport)
      (geometry.multiplicity boundaryIndex)

/-- The quotient-indexed finite correspondence on `C` obtained from the pushed
boundary presentation. -/
def pushedBoundaryCorrespondence {C : Geometry.SmSchemeOver k}
    (geometry : BoundaryFormulaGeometry C)
    (pushData : ∀ boundaryIndex,
      PushforwardPrimeSupportData geometry.nu (geometry.boundarySupport boundaryIndex)) :
    FiniteCorrespondence C C :=
  (geometry.pushedBoundaryPresentation pushData).toGeom

/-- Coefficient formula for the raw boundary presentation at a represented
prime support. This is the first coefficient-level computation on the boundary
side before any pushforward or identity statement. -/
theorem boundaryPresentation_apply {C : Geometry.SmSchemeOver k}
    (geometry : BoundaryFormulaGeometry C)
    [DecidableEq
      (RepresentedPrimeSupport geometry.boundarySource geometry.boundarySource)]
    (support : RepresentedPrimeSupport geometry.boundarySource geometry.boundarySource) :
    geometry.boundaryPresentation support =
      Finset.univ.sum fun boundaryIndex : geometry.boundaryIndex =>
        if geometry.boundarySupport boundaryIndex = support then
          geometry.multiplicity boundaryIndex
        else
          0 := by
  classical
  simp [boundaryPresentation, Finsupp.single_apply, eq_comm]

/-- Coefficient formula for the pushed raw boundary presentation at a
represented prime support on `C ×_k C`. -/
theorem pushedBoundaryPresentation_apply {C : Geometry.SmSchemeOver k}
    (geometry : BoundaryFormulaGeometry C)
    (pushData : ∀ boundaryIndex,
      PushforwardPrimeSupportData geometry.nu (geometry.boundarySupport boundaryIndex))
    [DecidableEq (RepresentedPrimeSupport C C)]
    (support : RepresentedPrimeSupport C C) :
    geometry.pushedBoundaryPresentation pushData support =
      Finset.univ.sum fun boundaryIndex : geometry.boundaryIndex =>
        if (pushData boundaryIndex).toRepresentedPrimeSupport = support then
          geometry.multiplicity boundaryIndex
        else
          0 := by
  classical
  simp [pushedBoundaryPresentation, Finsupp.single_apply, eq_comm]

/-- Quotient-level coefficient formula for the pushed boundary correspondence. -/
theorem pushedBoundaryCorrespondence_apply {C : Geometry.SmSchemeOver k}
    (geometry : BoundaryFormulaGeometry C)
    (pushData : ∀ boundaryIndex,
      PushforwardPrimeSupportData geometry.nu (geometry.boundarySupport boundaryIndex))
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (primeClass : PrimeFiniteCorrespondenceGeom C C) :
    geometry.pushedBoundaryCorrespondence pushData primeClass =
      Finset.univ.sum fun boundaryIndex : geometry.boundaryIndex =>
        if PrimeFiniteCorrespondenceGeom.ofRepresented
            ((pushData boundaryIndex).toRepresentedPrimeSupport) = primeClass then
          geometry.multiplicity boundaryIndex
        else
          0 := by
  classical
  rw [pushedBoundaryCorrespondence, pushedBoundaryPresentation,
    FiniteCorrespondencePresentation.toGeom, Finsupp.mapDomain_finset_sum]
  simp [Finsupp.mapDomain_single, Finsupp.single_apply, eq_comm]

end BoundaryFormulaGeometry

/-- A geometric producer assigning pushforward support data to every boundary
index of a boundary formula geometry. -/
structure BoundaryPushforwardGeometry {C : Geometry.SmSchemeOver k}
    (geometry : BoundaryFormulaGeometry C) where
  pushData :
    (boundaryIndex : geometry.boundaryIndex) →
      PushforwardPrimeSupportData geometry.nu (geometry.boundarySupport boundaryIndex)

namespace BoundaryPushforwardGeometry

/-- The raw pushed boundary presentation produced by a pushforward geometry. -/
def pushedBoundaryPresentation {C : Geometry.SmSchemeOver k}
    {geometry : BoundaryFormulaGeometry C}
    (pushforwardGeometry : BoundaryPushforwardGeometry geometry) :
    FiniteCorrespondencePresentation C C :=
  geometry.pushedBoundaryPresentation pushforwardGeometry.pushData

/-- The quotient-indexed pushed boundary correspondence produced by a
pushforward geometry. -/
def pushedBoundaryCorrespondence {C : Geometry.SmSchemeOver k}
    {geometry : BoundaryFormulaGeometry C}
    (pushforwardGeometry : BoundaryPushforwardGeometry geometry) :
    FiniteCorrespondence C C :=
  geometry.pushedBoundaryCorrespondence pushforwardGeometry.pushData

/-- Specialized pushed coefficient formula through a pushforward geometry
package. -/
theorem pushedBoundaryCorrespondence_apply {C : Geometry.SmSchemeOver k}
    {geometry : BoundaryFormulaGeometry C}
    (pushforwardGeometry : BoundaryPushforwardGeometry geometry)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (primeClass : PrimeFiniteCorrespondenceGeom C C) :
    pushforwardGeometry.pushedBoundaryCorrespondence primeClass =
      Finset.univ.sum fun boundaryIndex : geometry.boundaryIndex =>
        if PrimeFiniteCorrespondenceGeom.ofRepresented
            ((pushforwardGeometry.pushData boundaryIndex).toRepresentedPrimeSupport) = primeClass then
          geometry.multiplicity boundaryIndex
        else
          0 :=
  geometry.pushedBoundaryCorrespondence_apply pushforwardGeometry.pushData primeClass

end BoundaryPushforwardGeometry

/-- A package of coefficient computations for the pushed boundary
correspondence. These are coefficient-level theorems, not the boundary formula
itself. -/
structure BoundaryCoefficientComputation {C : Geometry.SmSchemeOver k}
    (geometry : BoundaryFormulaGeometry C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    (pushforwardGeometry : BoundaryPushforwardGeometry geometry) where
  diagonal :
    ∀ primeClass : PrimeFiniteCorrespondenceGeom C C,
      primeClass ∈ decomposition.diagonalPrimeClasses →
        pushforwardGeometry.pushedBoundaryCorrespondence primeClass = 1
  offDiagonal :
    ∀ primeClass : PrimeFiniteCorrespondenceGeom C C,
      primeClass ∉ decomposition.diagonalPrimeClasses →
        pushforwardGeometry.pushedBoundaryCorrespondence primeClass = 0

/-- If the pushed boundary correspondence has coefficient `1` on the diagonal
geometric classes and coefficient `0` off the diagonal classes, then it equals
the certified component-sum identity correspondence. -/
theorem boundary_formula_of_coefficients {C : Geometry.SmSchemeOver k}
    (geometry : BoundaryFormulaGeometry C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    (pushforwardGeometry : BoundaryPushforwardGeometry geometry)
    (coefficients :
      BoundaryCoefficientComputation geometry decomposition pushforwardGeometry)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] :
    pushforwardGeometry.pushedBoundaryCorrespondence =
      decomposition.identityFiniteCorrespondence := by
  classical
  ext primeClass
  rw [FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_apply_eq_indicator
    decomposition primeClass]
  by_cases hprime : primeClass ∈ decomposition.diagonalPrimeClasses
  · rw [if_pos hprime]
    exact coefficients.diagonal primeClass hprime
  · rw [if_neg hprime]
    exact coefficients.offDiagonal primeClass hprime

end

end Boundary
