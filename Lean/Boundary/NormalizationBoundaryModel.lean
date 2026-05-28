import Boundary.Basic
import Boundary.CorrespondenceSums
import Boundary.Diagonal
import Boundary.DiagonalDecomposition
import Boundary.NormalizationBoundaryStratum

/-!
# Normalization Boundary Models

This file packages global normalization-based boundary models, their induced
pushforward correspondence calculus, and the target theorem interfaces for the
normalized boundary cycle identity.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

open SourceIrreducibleComponent

open PrimeFiniteCorrespondenceSupport

noncomputable section

/-- A global normalization or compactification boundary model over `C`.

This is the first point in the file where the boundary-side data is assembled as
one mathematical object: the normalization source, the ambient boundary chart,
the indexed boundary strata, the represented source-side supports `ε_η`, their
multiplicities, and the termwise geometric maps needed to push those supports
forward to `C ×_k C`.

No coefficient theorem and no boundary identity theorem is stored here. Those
remain downstream consequences of this geometric model. -/
structure NormalizationBoundaryModel (C : Geometry.SmSchemeOver k) where
  normalization : Geometry.SmSchemeOver k
  nu : SmOverHom normalization C
  nu_finite : IsFinite nu.hom
  chart : BoundaryChart k
  chart_interior_eq : chart.interior = normalization
  boundaryIndex : Type u
  boundaryIndex_fintype : Fintype boundaryIndex
  stratum : boundaryIndex → BoundaryStratum k
  stratum_chart_eq :
    ∀ boundaryIndex, (stratum boundaryIndex).chart = chart
  boundarySupport :
    boundaryIndex → RepresentedPrimeSupport normalization normalization
  multiplicity : boundaryIndex → ℤ
  branchMultiplicity : boundaryIndex → ℚ
  branchMultiplicity_ne_zero :
    ∀ boundaryIndex, branchMultiplicity boundaryIndex ≠ 0
  targetSourceComponent :
    boundaryIndex → SourceIrreducibleComponent C
  targetSourceComponent_complete :
    (component : SourceIrreducibleComponent C) →
      Σ boundaryIndex,
        SourceIrreducibleComponent.IsoOverAmbient
          (targetSourceComponent boundaryIndex) component
  targetSourceComponent_unique :
    ∀ {i j : boundaryIndex},
      SourceIrreducibleComponent.IsoOverAmbient
        (targetSourceComponent i)
        (targetSourceComponent j) →
      i = j
  pushSupport_isIntegral :
    ∀ boundaryIndex, IsIntegral (stratum boundaryIndex).support
  sourceComponentMap :
    (boundaryIndex : boundaryIndex) →
      (boundarySupport boundaryIndex).sourceComponent.carrier.scheme ⟶
        (targetSourceComponent boundaryIndex).carrier.scheme
  sourceComponentMap_toAmbient :
    ∀ boundaryIndex,
      sourceComponentMap boundaryIndex ≫ (targetSourceComponent boundaryIndex).toAmbient =
        (boundarySupport boundaryIndex).sourceComponent.toAmbient ≫ nu.hom
  finiteOverTargetSource :
    (boundaryIndex : boundaryIndex) →
      (stratum boundaryIndex).support ⟶ (targetSourceComponent boundaryIndex).carrier.scheme
  finite_toTargetSource :
    ∀ boundaryIndex, IsFinite (finiteOverTargetSource boundaryIndex)
  surjective_toTargetSource :
    ∀ boundaryIndex, Function.Surjective (finiteOverTargetSource boundaryIndex).base
  toTarget :
    (boundaryIndex : boundaryIndex) →
      (stratum boundaryIndex).support ⟶ C.scheme
  inclusion :
    (boundaryIndex : boundaryIndex) →
      (stratum boundaryIndex).support ⟶
        overBaseProduct (targetSourceComponent boundaryIndex).carrier C
  inclusion_fst :
    ∀ boundaryIndex,
      inclusion boundaryIndex ≫
          overBaseProduct.fst (targetSourceComponent boundaryIndex).carrier C =
        finiteOverTargetSource boundaryIndex
  inclusion_snd :
    ∀ boundaryIndex,
      inclusion boundaryIndex ≫
          overBaseProduct.snd (targetSourceComponent boundaryIndex).carrier C =
        toTarget boundaryIndex
  isClosedImmersion :
    ∀ boundaryIndex, IsClosedImmersion (inclusion boundaryIndex)
  mapFromOriginal :
    (boundaryIndex : boundaryIndex) →
      (boundarySupport boundaryIndex).support ⟶ (stratum boundaryIndex).support
  mapFromOriginal_toSource :
    ∀ boundaryIndex,
      mapFromOriginal boundaryIndex ≫ finiteOverTargetSource boundaryIndex =
        (boundarySupport boundaryIndex).toSourceComponent ≫ sourceComponentMap boundaryIndex
  mapFromOriginal_toTarget :
    ∀ boundaryIndex,
      mapFromOriginal boundaryIndex ≫ toTarget boundaryIndex =
        (boundarySupport boundaryIndex).toTargetScheme ≫ nu.hom

namespace NormalizationBoundaryModel

instance {C : Geometry.SmSchemeOver k} (model : NormalizationBoundaryModel C) :
    Fintype model.boundaryIndex :=
  model.boundaryIndex_fintype

/-- The source-side finite sum `∑_η e_η ε_η` attached to a normalization
boundary model. -/
def toBoundaryFormulaGeometry {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C) :
    BoundaryFormulaGeometry C where
  boundarySource := model.normalization
  nu := model.nu
  nu_finite := model.nu_finite
  boundaryIndex := model.boundaryIndex
  boundaryIndex_fintype := model.boundaryIndex_fintype
  boundarySupport := model.boundarySupport
  multiplicity := model.multiplicity

/-- The normalization or boundary-stratum geometry extracted from the global
boundary model. -/
def toStratumGeometry {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C) :
    NormalizationBoundaryStratumGeometry model.toBoundaryFormulaGeometry where
  chart := model.chart
  chart_interior_eq := model.chart_interior_eq
  stratum := model.stratum
  stratum_chart_eq := model.stratum_chart_eq
  targetSourceComponent := model.targetSourceComponent
  pushSupport_isIntegral := model.pushSupport_isIntegral
  sourceComponentMap := model.sourceComponentMap
  sourceComponentMap_toAmbient := model.sourceComponentMap_toAmbient
  finiteOverTargetSource := model.finiteOverTargetSource
  finite_toTargetSource := model.finite_toTargetSource
  surjective_toTargetSource := model.surjective_toTargetSource
  toTarget := model.toTarget
  inclusion := model.inclusion
  inclusion_fst := model.inclusion_fst
  inclusion_snd := model.inclusion_snd
  isClosedImmersion := model.isClosedImmersion
  mapFromOriginal := model.mapFromOriginal
  mapFromOriginal_toSource := model.mapFromOriginal_toSource
  mapFromOriginal_toTarget := model.mapFromOriginal_toTarget

/-- The pushed-support producer extracted from the global normalization
boundary model. -/
def toPushforwardGeometry {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C) :
    BoundaryPushforwardGeometry model.toBoundaryFormulaGeometry :=
  model.toStratumGeometry.toPushforwardGeometry

/-- Cycles on the normalized boundary branches indexed by the chosen boundary
components of the model. -/
abbrev NormalizedBoundaryCycle {C : Geometry.SmSchemeOver k}
  (model : NormalizationBoundaryModel C) :=
  model.boundaryIndex →₀ ℤ

/-- Rational cycles on the normalized boundary branches. -/
abbrev RationalNormalizedBoundaryCycle {C : Geometry.SmSchemeOver k}
  (model : NormalizationBoundaryModel C) :=
  model.boundaryIndex →₀ ℚ

/-- The weighted normalized boundary cycle `Σ_η e_η E_η`. -/
def weightedBoundaryCycle {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C) : NormalizedBoundaryCycle model := by
  classical
  exact Finsupp.onFinset Finset.univ model.multiplicity (by
    intro boundaryIndex _
    exact Finset.mem_univ boundaryIndex)

@[simp] theorem weightedBoundaryCycle_apply {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (boundaryIndex : model.boundaryIndex) :
    model.weightedBoundaryCycle boundaryIndex = model.multiplicity boundaryIndex := by
  classical
  simp [weightedBoundaryCycle]

/-- The normalized boundary divisor with coefficients `e_η⁻¹`. -/
def branchWeight {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C) (boundaryIndex : model.boundaryIndex) : ℚ :=
  (model.branchMultiplicity boundaryIndex)⁻¹

theorem branchWeight_eq_inv_multiplicity {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C) (boundaryIndex : model.boundaryIndex) :
    model.branchWeight boundaryIndex = (model.branchMultiplicity boundaryIndex)⁻¹ :=
  rfl

theorem branchWeight_mul_branchMultiplicity {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C) (boundaryIndex : model.boundaryIndex) :
    model.branchWeight boundaryIndex * model.branchMultiplicity boundaryIndex = 1 := by
  unfold branchWeight
  field_simp [model.branchMultiplicity_ne_zero boundaryIndex]

/-- The diagonal geometric class determined by the pushed boundary branch. -/
def landingClass {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C) (boundaryIndex : model.boundaryIndex) :
    PrimeFiniteCorrespondenceGeom C C :=
  SourceIrreducibleComponent.diagonalPrimeGeom
    (model.targetSourceComponent boundaryIndex)

theorem pushforward_branch_eq_diagonal {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C) (boundaryIndex : model.boundaryIndex) :
    model.landingClass boundaryIndex =
      SourceIrreducibleComponent.diagonalPrimeGeom
        (model.targetSourceComponent boundaryIndex) :=
  rfl

theorem landingClass_injective {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C) : Function.Injective model.landingClass := by
  intro boundaryIndex boundaryIndex' hlanding
  exact model.targetSourceComponent_unique
    (isoOverAmbient_of_diagonalPrimeGeom_eq hlanding)

def weightedBoundaryCycleQ {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C) : RationalNormalizedBoundaryCycle model := by
  classical
  exact Finsupp.onFinset Finset.univ model.branchWeight (by
    intro boundaryIndex _
    exact Finset.mem_univ boundaryIndex)

@[simp] theorem weightedBoundaryCycleQ_apply {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (boundaryIndex : model.boundaryIndex) :
    model.weightedBoundaryCycleQ boundaryIndex = model.branchWeight boundaryIndex := by
  classical
  simp [weightedBoundaryCycleQ]

/-- Push a normalized boundary cycle forward to the correspondence group by
sending each branch to the geometric class of its pushed support. -/
def pushforwardCycle {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (cycle : NormalizedBoundaryCycle model) :
    FiniteCorrespondence C C :=
  cycle.mapDomain fun boundaryIndex =>
    PrimeFiniteCorrespondenceGeom.ofRepresented
      (PushforwardPrimeSupportData.toRepresentedPrimeSupport
        ((model.toStratumGeometry.datum boundaryIndex).toPushforwardPrimeSupportData))

/-- Push forward a rational normalized boundary cycle, multiplying each branch
coefficient by the concrete branch multiplicity and landing on the diagonal
class supplied by the model. This is the cancellation surface for the divisor
identity `ν⁻¹(∂X) = Σ e_η E_η`. -/
def pushforwardCycleQ {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (cycle : RationalNormalizedBoundaryCycle model) :
    RationalFiniteCorrespondence C C := by
  classical
  exact Finset.univ.sum fun boundaryIndex : model.boundaryIndex =>
    Finsupp.single (model.landingClass boundaryIndex)
      (cycle boundaryIndex * model.branchMultiplicity boundaryIndex)

theorem pushforwardCycleQ_apply {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (cycle : RationalNormalizedBoundaryCycle model)
    (primeClass : PrimeFiniteCorrespondenceGeom C C) :
    model.pushforwardCycleQ cycle primeClass =
      Finset.univ.sum fun boundaryIndex : model.boundaryIndex =>
        if primeClass = model.landingClass boundaryIndex then
          cycle boundaryIndex * model.branchMultiplicity boundaryIndex
        else
          0 := by
  classical
  simp [pushforwardCycleQ, Finsupp.single_apply, eq_comm]

@[simp] theorem pushforwardCycle_zero {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] :
    model.pushforwardCycle (0 : NormalizedBoundaryCycle model) = 0 := by
  change Finsupp.mapDomain _ (0 : NormalizedBoundaryCycle model) = 0
  exact Finsupp.mapDomain_zero

@[simp] theorem pushforwardCycle_add {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (a b : NormalizedBoundaryCycle model) :
    model.pushforwardCycle (a + b) =
      model.pushforwardCycle a + model.pushforwardCycle b := by
  change Finsupp.mapDomain _ (a + b) = Finsupp.mapDomain _ a + Finsupp.mapDomain _ b
  exact Finsupp.mapDomain_add

@[simp] theorem pushforwardCycle_single {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (boundaryIndex : model.boundaryIndex) (coefficient : ℤ) :
    model.pushforwardCycle (Finsupp.single boundaryIndex coefficient) =
      Finsupp.single
        (PrimeFiniteCorrespondenceGeom.ofRepresented
          (PushforwardPrimeSupportData.toRepresentedPrimeSupport
            ((model.toStratumGeometry.datum boundaryIndex).toPushforwardPrimeSupportData)))
        coefficient := by
  change Finsupp.mapDomain _ (Finsupp.single boundaryIndex coefficient) = _
  exact Finsupp.mapDomain_single

/-- Coefficient formula for the pushforward of a normalized boundary cycle. -/
theorem pushforwardCycle_apply {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (cycle : NormalizedBoundaryCycle model)
    (primeClass : PrimeFiniteCorrespondenceGeom C C) :
    model.pushforwardCycle cycle primeClass =
      Finset.univ.sum fun boundaryIndex : model.boundaryIndex =>
        if PrimeFiniteCorrespondenceGeom.ofRepresented
            (PushforwardPrimeSupportData.toRepresentedPrimeSupport
              ((model.toStratumGeometry.datum boundaryIndex).toPushforwardPrimeSupportData)) = primeClass then
          cycle boundaryIndex
        else
          0 := by
  classical
  induction cycle using Finsupp.induction_linear with
    | h0 =>
      simp [pushforwardCycle_zero]
    | hadd a b ha hb =>
      rw [pushforwardCycle_add, Finsupp.add_apply, ha, hb, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro boundaryIndex _
      by_cases hclass : PrimeFiniteCorrespondenceGeom.ofRepresented
        (PushforwardPrimeSupportData.toRepresentedPrimeSupport
        ((model.toStratumGeometry.datum boundaryIndex).toPushforwardPrimeSupportData)) = primeClass
      · simp [hclass]
      · simp [hclass]
    | hsingle boundaryIndex coefficient =>
      by_cases hclass : PrimeFiniteCorrespondenceGeom.ofRepresented
        (PushforwardPrimeSupportData.toRepresentedPrimeSupport
        ((model.toStratumGeometry.datum boundaryIndex).toPushforwardPrimeSupportData)) = primeClass
      · rw [pushforwardCycle_single, Finset.sum_eq_single boundaryIndex]
        · simp [hclass, Finsupp.single_apply, eq_comm]
        · intro boundaryIndex' _ hneq
          have hneq' : boundaryIndex ≠ boundaryIndex' := by
            intro h
            exact hneq h.symm
          simp [Finsupp.single_apply, hneq', eq_comm]
        · simp
      · rw [pushforwardCycle_single]
        rw [show
            (Finsupp.single
              (PrimeFiniteCorrespondenceGeom.ofRepresented
                (PushforwardPrimeSupportData.toRepresentedPrimeSupport
                  ((model.toStratumGeometry.datum boundaryIndex).toPushforwardPrimeSupportData)))
              coefficient) primeClass = 0 by
              simp [Finsupp.single_apply, hclass, eq_comm]]
        symm
        apply Finset.sum_eq_zero
        intro boundaryIndex' _
        by_cases hneq : boundaryIndex = boundaryIndex'
        · subst hneq
          simp [hclass, eq_comm]
        · simp [Finsupp.single_apply, hneq, eq_comm]

/-- Pushing forward the weighted normalized boundary cycle recovers the raw
boundary correspondence attached to the model. -/
theorem pushforward_weightedBoundaryCycle {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] :
    model.pushforwardCycle model.weightedBoundaryCycle =
      model.toPushforwardGeometry.pushedBoundaryCorrespondence := by
  ext primeClass
  rw [BoundaryPushforwardGeometry.pushedBoundaryCorrespondence_apply]
  simpa [NormalizationBoundaryModel.toPushforwardGeometry,
    NormalizationBoundaryModel.toBoundaryFormulaGeometry,
    NormalizationBoundaryModel.toStratumGeometry,
    NormalizationBoundaryStratumGeometry.pushData,
    weightedBoundaryCycle_apply] using
      model.pushforwardCycle_apply model.weightedBoundaryCycle primeClass

/-- The diagonal class attached to any normalized boundary branch lies in the
certified diagonal support of any finite irreducible-component decomposition of
the target. -/
theorem landingClass_mem_diagonalPrimeClasses {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    (boundaryIndex : model.boundaryIndex) :
    model.landingClass boundaryIndex ∈ decomposition.diagonalPrimeClasses := by
  rcases decomposition.exhaustive (model.targetSourceComponent boundaryIndex) with
    ⟨listed, hiso⟩
  refine (FiniteIrreducibleComponentDecomposition.mem_diagonalPrimeClasses_iff
    decomposition (model.landingClass boundaryIndex)).2 ?_
  refine ⟨listed.1, listed.2, ?_⟩
  calc
    SourceIrreducibleComponent.diagonalPrimeGeom listed.1
      = SourceIrreducibleComponent.diagonalPrimeGeom
          (model.targetSourceComponent boundaryIndex) := by
            simpa using
              (SourceIrreducibleComponent.diagonalPrimeGeom_eq_of_isoOverAmbient hiso).symm
    _ = model.landingClass boundaryIndex := by
          symm
          exact model.pushforward_branch_eq_diagonal boundaryIndex

/-- Every diagonal prime class is hit by exactly one normalized boundary
branch, because the model stores the branch enumeration and diagonal landing
data concretely. -/
theorem exists_unique_boundaryIndex_of_diagonalPrimeClass
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    {primeClass : PrimeFiniteCorrespondenceGeom C C}
    (hprime : primeClass ∈ decomposition.diagonalPrimeClasses) :
    ∃! boundaryIndex : model.boundaryIndex,
      model.landingClass boundaryIndex = primeClass := by
  rcases (FiniteIrreducibleComponentDecomposition.mem_diagonalPrimeClasses_iff
      decomposition primeClass).1 hprime with ⟨component, _hcomponent, hdiag⟩
  rcases model.targetSourceComponent_complete component with ⟨boundaryIndex, hiso⟩
  have hboundaryIndex : model.landingClass boundaryIndex = primeClass := by
    calc
      model.landingClass boundaryIndex
        = SourceIrreducibleComponent.diagonalPrimeGeom
            (model.targetSourceComponent boundaryIndex) :=
              model.pushforward_branch_eq_diagonal boundaryIndex
      _ = SourceIrreducibleComponent.diagonalPrimeGeom component := by
            exact SourceIrreducibleComponent.diagonalPrimeGeom_eq_of_isoOverAmbient hiso
      _ = primeClass := hdiag
  refine ⟨boundaryIndex, hboundaryIndex, ?_⟩
  · intro boundaryIndex' hboundaryIndex'
    exact model.landingClass_injective (hboundaryIndex'.trans hboundaryIndex.symm)

/-- Coefficient theorem for the concretely weighted normalized boundary cycle.
The divisor multiplicity `e_η` and the normalization weight `e_η⁻¹` cancel on
diagonal classes, and no off-diagonal prime class appears in the pushforward
support. -/
theorem weightedBoundaryCycleQ_coeff_eq_indicator
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (primeClass : PrimeFiniteCorrespondenceGeom C C) :
    model.pushforwardCycleQ model.weightedBoundaryCycleQ primeClass =
      if primeClass ∈ decomposition.diagonalPrimeClasses then 1 else 0 := by
  classical
  rw [model.pushforwardCycleQ_apply]
  by_cases hprime : primeClass ∈ decomposition.diagonalPrimeClasses
  · rw [if_pos hprime]
    rcases model.exists_unique_boundaryIndex_of_diagonalPrimeClass decomposition hprime with
      ⟨boundaryIndex, hboundaryIndex, hunique⟩
    rw [Finset.sum_eq_single boundaryIndex]
    · simp [weightedBoundaryCycleQ_apply, hboundaryIndex,
        model.branchWeight_mul_branchMultiplicity]
    · intro boundaryIndex' _ hneq
      have hnot : primeClass ≠ model.landingClass boundaryIndex' := by
        intro hboundaryIndex'
        exact hneq ((hunique boundaryIndex') hboundaryIndex'.symm)
      simp [weightedBoundaryCycleQ_apply, hnot]
    · simp
  · rw [if_neg hprime]
    refine Finset.sum_eq_zero ?_
    intro boundaryIndex _
    have hdiag : model.landingClass boundaryIndex ∈ decomposition.diagonalPrimeClasses :=
      model.landingClass_mem_diagonalPrimeClasses decomposition boundaryIndex
    have hnot : primeClass ≠ model.landingClass boundaryIndex := by
      intro hboundaryIndex
      apply hprime
      simpa [hboundaryIndex] using hdiag
    simp [weightedBoundaryCycleQ_apply, hnot]

/-- Concrete normalization closeout theorem: the weighted normalized boundary
divisor pushes forward to the diagonal identity correspondence because the
branch multiplicities cancel against the normalization weights. -/
theorem rational_boundary_formula_of_coefficients
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (hcoeff :
      ∀ primeClass : PrimeFiniteCorrespondenceGeom C C,
        model.pushforwardCycleQ model.weightedBoundaryCycleQ primeClass =
          if primeClass ∈ decomposition.diagonalPrimeClasses then 1 else 0) :
    model.pushforwardCycleQ model.weightedBoundaryCycleQ =
      identityFiniteCorrespondenceQ decomposition := by
  ext primeClass
  rw [hcoeff primeClass,
    identityFiniteCorrespondenceQ_apply_eq_indicator decomposition]

/-- Concrete normalization closeout theorem: the rational weighted normalized
boundary divisor pushes forward to the rational diagonal identity
correspondence because the branch multiplicities cancel against the
normalization weights. -/
theorem weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] :
    model.pushforwardCycleQ model.weightedBoundaryCycleQ =
      identityFiniteCorrespondenceQ decomposition := by
  exact model.rational_boundary_formula_of_coefficients decomposition
    (model.weightedBoundaryCycleQ_coeff_eq_indicator decomposition)

/-- Honest rational geometric decomposition of the normalized boundary divisor.

This is the concrete closeout surface supported by the current model fields:
the rational weighted normalized boundary divisor equals the weighted branch
cycle `Σ e_η^{-1} E_η`, and its pushforward is the rational diagonal identity
correspondence. -/
structure RationalNormalizedBoundaryGeometricDecomposition
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] where
  normalizedBoundaryDivisorQ : RationalNormalizedBoundaryCycle model
  divisor_eq_weightedBoundaryQ :
    normalizedBoundaryDivisorQ = model.weightedBoundaryCycleQ
  pushforward_divisor_eq_identityQ :
    model.pushforwardCycleQ normalizedBoundaryDivisorQ =
      identityFiniteCorrespondenceQ decomposition

namespace RationalNormalizedBoundaryGeometricDecomposition

/-- If the rational weighted normalized boundary cycle already pushes forward
to the rational diagonal identity correspondence, then it itself supplies the
required honest rational geometric decomposition package. -/
def of_weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (hpush : model.pushforwardCycleQ model.weightedBoundaryCycleQ =
      identityFiniteCorrespondenceQ decomposition) :
    RationalNormalizedBoundaryGeometricDecomposition model decomposition where
  normalizedBoundaryDivisorQ := model.weightedBoundaryCycleQ
  divisor_eq_weightedBoundaryQ := rfl
  pushforward_divisor_eq_identityQ := hpush

/-- The current normalization-boundary model already proves the honest
rational geometric decomposition package, because branch multiplicities cancel
against the reciprocal normalization weights. -/
def canonical
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] :
    RationalNormalizedBoundaryGeometricDecomposition model decomposition :=
  of_weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ
    (model.weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ decomposition)

/-- Honest rational geometric decomposition data are always nonempty for the
current normalization-boundary model. -/
theorem nonempty
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] :
    Nonempty (RationalNormalizedBoundaryGeometricDecomposition model decomposition) :=
  ⟨canonical model decomposition⟩

/-- Any honest rational geometric decomposition gives back the same rational
weighted-boundary pushforward identity. -/
theorem weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      RationalNormalizedBoundaryGeometricDecomposition model decomposition) :
    model.pushforwardCycleQ model.weightedBoundaryCycleQ =
      identityFiniteCorrespondenceQ decomposition := by
  calc
    model.pushforwardCycleQ model.weightedBoundaryCycleQ =
        model.pushforwardCycleQ geometricDecomposition.normalizedBoundaryDivisorQ := by
          rw [← geometricDecomposition.divisor_eq_weightedBoundaryQ]
    _ = identityFiniteCorrespondenceQ decomposition :=
      geometricDecomposition.pushforward_divisor_eq_identityQ

/-- Honest rational geometric decomposition data exist exactly when the
rational weighted normalized boundary cycle pushes forward to the diagonal
identity correspondence. -/
theorem nonempty_iff_weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] :
    Nonempty (RationalNormalizedBoundaryGeometricDecomposition model decomposition) ↔
      model.pushforwardCycleQ model.weightedBoundaryCycleQ =
        identityFiniteCorrespondenceQ decomposition := by
  constructor
  · rintro ⟨geometricDecomposition⟩
    exact geometricDecomposition.weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ
  · intro hpush
    exact ⟨of_weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ hpush⟩

end RationalNormalizedBoundaryGeometricDecomposition

/-- Rational indicator-form target for the normalized boundary cycle identity.

This is the coefficient-level theorem surface naturally supported by the
current normalization-boundary model: each branch contributes the rational
coefficient `e_η^{-1} * e_η`, and the resulting sum is the diagonal indicator
function. -/
structure RationalNormalizedBoundaryCycleIdentityTarget
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] where
  pushedClass : model.boundaryIndex → PrimeFiniteCorrespondenceGeom C C
  pushedClass_eq :
    ∀ boundaryIndex,
      pushedClass boundaryIndex = model.landingClass boundaryIndex
  coefficient_eq_indicator :
    ∀ primeClass : PrimeFiniteCorrespondenceGeom C C,
      (Finset.univ.sum fun boundaryIndex : model.boundaryIndex =>
        if pushedClass boundaryIndex = primeClass then
          model.branchWeight boundaryIndex * model.branchMultiplicity boundaryIndex
        else
          0) = if primeClass ∈ decomposition.diagonalPrimeClasses then 1 else 0

namespace RationalNormalizedBoundaryCycleIdentityTarget

/-- Canonical API wrapper over the already-proved rational coefficient theorem.

This does not add new normalization input: it simply packages
`weightedBoundaryCycleQ_coeff_eq_indicator`, whose proof above uses only the
existing branch-weight cancellation theorem together with the landing-class
classification lemmas. -/
def canonical
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] :
    RationalNormalizedBoundaryCycleIdentityTarget model decomposition where
  pushedClass := model.landingClass
  pushedClass_eq := by
    intro boundaryIndex
    rfl
  coefficient_eq_indicator := by
    intro primeClass
    calc
      (Finset.univ.sum fun boundaryIndex : model.boundaryIndex =>
        if model.landingClass boundaryIndex = primeClass then
          model.branchWeight boundaryIndex * model.branchMultiplicity boundaryIndex
        else
          0)
          = model.pushforwardCycleQ model.weightedBoundaryCycleQ primeClass := by
              symm
              rw [model.pushforwardCycleQ_apply model.weightedBoundaryCycleQ primeClass]
              simp [weightedBoundaryCycleQ_apply, eq_comm]
      _ = if primeClass ∈ decomposition.diagonalPrimeClasses then 1 else 0 := by
            exact model.weightedBoundaryCycleQ_coeff_eq_indicator decomposition primeClass

/-- Any honest rational geometric decomposition induces the corresponding
coefficient-level rational cycle-identity target. -/
def ofGeometricDecomposition
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      RationalNormalizedBoundaryGeometricDecomposition model decomposition) :
    RationalNormalizedBoundaryCycleIdentityTarget model decomposition where
  pushedClass := model.landingClass
  pushedClass_eq := by
    intro boundaryIndex
    rfl
  coefficient_eq_indicator := by
    intro primeClass
    calc
      (Finset.univ.sum fun boundaryIndex : model.boundaryIndex =>
        if model.landingClass boundaryIndex = primeClass then
          model.branchWeight boundaryIndex * model.branchMultiplicity boundaryIndex
        else
          0)
          = model.pushforwardCycleQ model.weightedBoundaryCycleQ primeClass := by
              symm
              rw [model.pushforwardCycleQ_apply model.weightedBoundaryCycleQ primeClass]
              simp [weightedBoundaryCycleQ_apply, eq_comm]
      _ = model.pushforwardCycleQ geometricDecomposition.normalizedBoundaryDivisorQ primeClass := by
        rw [← geometricDecomposition.divisor_eq_weightedBoundaryQ]
      _ = identityFiniteCorrespondenceQ decomposition primeClass := by
            rw [geometricDecomposition.pushforward_divisor_eq_identityQ]
      _ = if primeClass ∈ decomposition.diagonalPrimeClasses then 1 else 0 := by
            exact identityFiniteCorrespondenceQ_apply_eq_indicator decomposition primeClass

/-- The rational cycle-identity target implies the rational weighted-boundary
pushforward theorem. -/
theorem weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (cycleIdentity : RationalNormalizedBoundaryCycleIdentityTarget model decomposition) :
    model.pushforwardCycleQ model.weightedBoundaryCycleQ =
      identityFiniteCorrespondenceQ decomposition := by
  ext primeClass
  rw [model.pushforwardCycleQ_apply model.weightedBoundaryCycleQ primeClass,
    identityFiniteCorrespondenceQ_apply_eq_indicator decomposition primeClass]
  simpa [weightedBoundaryCycleQ_apply, cycleIdentity.pushedClass_eq, eq_comm] using
    cycleIdentity.coefficient_eq_indicator primeClass

/-- The rational cycle-identity target already supplies an honest rational
geometric decomposition package. -/
def toGeometricDecomposition
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (cycleIdentity : RationalNormalizedBoundaryCycleIdentityTarget model decomposition) :
    RationalNormalizedBoundaryGeometricDecomposition model decomposition :=
  RationalNormalizedBoundaryGeometricDecomposition.of_weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ
    (RationalNormalizedBoundaryCycleIdentityTarget.weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ
      cycleIdentity)

end RationalNormalizedBoundaryCycleIdentityTarget

namespace RationalNormalizedBoundaryGeometricDecomposition

/-- The coefficient-level rational cycle-identity target induced by an honest
rational geometric decomposition of the normalized boundary divisor. -/
def toCycleIdentityTarget
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      RationalNormalizedBoundaryGeometricDecomposition model decomposition) :
    RationalNormalizedBoundaryCycleIdentityTarget model decomposition :=
  RationalNormalizedBoundaryCycleIdentityTarget.ofGeometricDecomposition geometricDecomposition

end RationalNormalizedBoundaryGeometricDecomposition

/-- Computational form of the normalized boundary theorem: after expanding the
weighted boundary cycle, the pushed-boundary correspondence agrees with the
identity correspondence exactly when the weighted cycle itself pushes forward to
that identity correspondence. -/
theorem integral_boundary_formula_iff_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] :
    model.toPushforwardGeometry.pushedBoundaryCorrespondence =
        decomposition.identityFiniteCorrespondence ↔
      model.pushforwardCycle model.weightedBoundaryCycle =
        decomposition.identityFiniteCorrespondence := by
  constructor
  · intro hboundary
    simpa [model.pushforward_weightedBoundaryCycle] using hboundary
  · intro hpush
    simpa [model.pushforward_weightedBoundaryCycle] using hpush

/-- A multiplicity analysis for a global normalization boundary model. This is
the theorem layer attached to the model, not part of the geometric data. -/
structure MultiplicityAnalysis
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] where
  pushedClass : model.boundaryIndex → PrimeFiniteCorrespondenceGeom C C
  pushedClass_eq :
    ∀ boundaryIndex,
      pushedClass boundaryIndex =
        PrimeFiniteCorrespondenceGeom.ofRepresented
          (PushforwardPrimeSupportData.toRepresentedPrimeSupport
            ((model.toStratumGeometry.datum boundaryIndex).toPushforwardPrimeSupportData))
  diagonalMultiplicity :
    ∀ primeClass : PrimeFiniteCorrespondenceGeom C C,
      primeClass ∈ decomposition.diagonalPrimeClasses →
        (Finset.univ.sum fun boundaryIndex : model.boundaryIndex =>
          if pushedClass boundaryIndex = primeClass then
            model.multiplicity boundaryIndex
          else
            0) = 1
  offDiagonalMultiplicity :
    ∀ primeClass : PrimeFiniteCorrespondenceGeom C C,
      primeClass ∉ decomposition.diagonalPrimeClasses →
        (Finset.univ.sum fun boundaryIndex : model.boundaryIndex =>
          if pushedClass boundaryIndex = primeClass then
            model.multiplicity boundaryIndex
          else
            0) = 0

namespace MultiplicityAnalysis

/-- The classification package induced by a multiplicity analysis of a global
normalization boundary model. -/
def toClassification {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (analysis : MultiplicityAnalysis model decomposition) :
    NormalizationBoundaryStratumClassification model.toBoundaryFormulaGeometry
      decomposition model.toStratumGeometry where
  pushedClass := analysis.pushedClass
  pushedClass_eq := analysis.pushedClass_eq
  diagonalMultiplicity := analysis.diagonalMultiplicity
  offDiagonalMultiplicity := analysis.offDiagonalMultiplicity

/-- The coefficient theorem package induced by a multiplicity analysis of a
global normalization boundary model. -/
def toCoefficientComputation {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (analysis : MultiplicityAnalysis model decomposition) :
    BoundaryCoefficientComputation model.toBoundaryFormulaGeometry
      decomposition model.toPushforwardGeometry :=
  analysis.toClassification.toCoefficientComputation

/-- The full boundary formula derived from a multiplicity analysis of a global
normalization boundary model. -/
theorem boundary_formula {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (analysis : MultiplicityAnalysis model decomposition) :
    model.toPushforwardGeometry.pushedBoundaryCorrespondence =
      decomposition.identityFiniteCorrespondence :=
  boundary_formula_of_coefficients model.toBoundaryFormulaGeometry decomposition
    model.toPushforwardGeometry analysis.toCoefficientComputation

/-- A multiplicity analysis already proves the central computational identity:
the weighted normalized boundary cycle pushes forward to the diagonal identity
correspondence. -/
theorem integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
  {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (analysis : MultiplicityAnalysis model decomposition) :
    model.pushforwardCycle model.weightedBoundaryCycle =
      decomposition.identityFiniteCorrespondence := by
  simpa [model.pushforward_weightedBoundaryCycle] using
    analysis.boundary_formula decomposition

end MultiplicityAnalysis

/-- Geometric decomposition of the normalized boundary divisor or cycle.

This is the place where the actual geometric theorem is expected to live: the
intrinsic normalized boundary divisor equals the weighted sum of the chosen
branches, and pushing that divisor forward yields the diagonal identity cycle on
`C ×_k C`. No coefficient target is assumed here. -/
structure NormalizedBoundaryGeometricDecomposition
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] where
  normalizedBoundaryDivisor : NormalizedBoundaryCycle model
  divisor_eq_weightedBoundary :
    normalizedBoundaryDivisor = model.weightedBoundaryCycle
  pushforward_divisor_eq_identity :
    model.pushforwardCycle normalizedBoundaryDivisor =
      decomposition.identityFiniteCorrespondence

/-- Target statement for the classical cycle identity on the normalized
boundary.

This is not an established geometric theorem merely because the record exists.
It should be treated as an unproved theorem target until its data are produced
from actual normalized-boundary divisor or cycle geometry, such as valuation,
length, ramification, or divisor-pullback computations realizing a statement of
the form `ν⁻¹(∂X) = Σ e_η E_η`.

The record packages only the coefficient-level shape of that target in the
current correspondence API. -/
structure NormalizedBoundaryCycleIdentityTarget
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] where
  pushedClass : model.boundaryIndex → PrimeFiniteCorrespondenceGeom C C
  pushedClass_eq :
    ∀ boundaryIndex,
      pushedClass boundaryIndex =
        PrimeFiniteCorrespondenceGeom.ofRepresented
          (PushforwardPrimeSupportData.toRepresentedPrimeSupport
            ((model.toStratumGeometry.datum boundaryIndex).toPushforwardPrimeSupportData))
  coefficient_eq_indicator :
    ∀ primeClass : PrimeFiniteCorrespondenceGeom C C,
      (Finset.univ.sum fun boundaryIndex : model.boundaryIndex =>
        if pushedClass boundaryIndex = primeClass then
          model.multiplicity boundaryIndex
        else
          0) = if primeClass ∈ decomposition.diagonalPrimeClasses then 1 else 0

namespace NormalizedBoundaryCycleIdentityTarget

/-- Construct the coefficient-level target from an actual geometric
decomposition of the normalized boundary divisor. This is the only unconditional
constructor in the file that produces the target package. -/
def ofGeometricDecomposition
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      NormalizedBoundaryGeometricDecomposition model decomposition) :
    NormalizedBoundaryCycleIdentityTarget model decomposition where
  pushedClass := fun boundaryIndex =>
    PrimeFiniteCorrespondenceGeom.ofRepresented
      (PushforwardPrimeSupportData.toRepresentedPrimeSupport
        ((model.toStratumGeometry.datum boundaryIndex).toPushforwardPrimeSupportData))
  pushedClass_eq := by
    intro boundaryIndex
    rfl
  coefficient_eq_indicator := by
    intro primeClass
    calc
      (Finset.univ.sum fun boundaryIndex : model.boundaryIndex =>
        if PrimeFiniteCorrespondenceGeom.ofRepresented
            (PushforwardPrimeSupportData.toRepresentedPrimeSupport
              ((model.toStratumGeometry.datum boundaryIndex).toPushforwardPrimeSupportData)) = primeClass then
          model.multiplicity boundaryIndex
        else
          0)
          = model.pushforwardCycle model.weightedBoundaryCycle primeClass := by
              symm
              simpa [weightedBoundaryCycle_apply] using
                model.pushforwardCycle_apply model.weightedBoundaryCycle primeClass
      _ = model.pushforwardCycle geometricDecomposition.normalizedBoundaryDivisor primeClass := by
        rw [← geometricDecomposition.divisor_eq_weightedBoundary]
      _ = decomposition.identityFiniteCorrespondence primeClass := by
            rw [geometricDecomposition.pushforward_divisor_eq_identity]
      _ = if primeClass ∈ decomposition.diagonalPrimeClasses then 1 else 0 := by
            exact FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_apply_eq_indicator
              decomposition primeClass

/-- Convert the indicator-form cycle identity into the split diagonal and
off-diagonal multiplicity theorems. -/
def toMultiplicityAnalysis
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
  (cycleIdentity : NormalizedBoundaryCycleIdentityTarget model decomposition) :
    MultiplicityAnalysis model decomposition where
  pushedClass := cycleIdentity.pushedClass
  pushedClass_eq := cycleIdentity.pushedClass_eq
  diagonalMultiplicity primeClass hprime := by
    rw [cycleIdentity.coefficient_eq_indicator primeClass, if_pos hprime]
  offDiagonalMultiplicity primeClass hprime := by
    rw [cycleIdentity.coefficient_eq_indicator primeClass, if_neg hprime]

/-- The classification package induced by the normalized boundary cycle
identity target. -/
def toClassification
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (cycleIdentity : NormalizedBoundaryCycleIdentityTarget model decomposition) :
    NormalizationBoundaryStratumClassification model.toBoundaryFormulaGeometry
      decomposition model.toStratumGeometry :=
  cycleIdentity.toMultiplicityAnalysis.toClassification

/-- The coefficient theorem package induced by the normalized boundary cycle
identity target. -/
def toCoefficientComputation
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (cycleIdentity : NormalizedBoundaryCycleIdentityTarget model decomposition) :
    BoundaryCoefficientComputation model.toBoundaryFormulaGeometry
      decomposition model.toPushforwardGeometry :=
  cycleIdentity.toMultiplicityAnalysis.toCoefficientComputation

/-- The full boundary formula implied by the normalized boundary cycle identity
target. This is an algebraic consequence of the target package, not a geometric
proof of that target. -/
theorem boundary_formula_of_target
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (cycleIdentity : NormalizedBoundaryCycleIdentityTarget model decomposition) :
    model.toPushforwardGeometry.pushedBoundaryCorrespondence =
      decomposition.identityFiniteCorrespondence :=
  MultiplicityAnalysis.boundary_formula decomposition cycleIdentity.toMultiplicityAnalysis

/-- The indicator-form normalized boundary cycle identity directly yields the
central weighted-boundary pushforward theorem. -/
theorem integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (cycleIdentity : NormalizedBoundaryCycleIdentityTarget model decomposition) :
    model.pushforwardCycle model.weightedBoundaryCycle =
      decomposition.identityFiniteCorrespondence := by
  simpa [model.pushforward_weightedBoundaryCycle] using
    cycleIdentity.boundary_formula_of_target decomposition

end NormalizedBoundaryCycleIdentityTarget

/-- Honest strengthened normalization-boundary theorem surface.

This is the place to start when we want the full integral geometric theorem
without losing the rational cancellation data that actually explains it. The
package records both:

* the integral divisor-level closeout `Σ e_η E_η -> id_Δ`, and
* the rational cancellation witness `Σ e_η^{-1} E_η -> id_Δ^Q`.

Downstream theorems can project either the integral or rational API from this
single strengthened surface, rather than treating the integral closeout as if
it already captured the rational mechanism. -/
structure HonestNormalizedBoundaryGeometricDecomposition
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] where
  normalizedBoundaryDivisor : NormalizedBoundaryCycle model
  divisor_eq_weightedBoundary :
    normalizedBoundaryDivisor = model.weightedBoundaryCycle
  pushforward_divisor_eq_identity :
    model.pushforwardCycle normalizedBoundaryDivisor =
      decomposition.identityFiniteCorrespondence
  normalizedBoundaryDivisorQ : RationalNormalizedBoundaryCycle model
  divisorQ_eq_weightedBoundaryQ :
    normalizedBoundaryDivisorQ = model.weightedBoundaryCycleQ
  pushforward_divisorQ_eq_identityQ :
    model.pushforwardCycleQ normalizedBoundaryDivisorQ =
      identityFiniteCorrespondenceQ decomposition

namespace NormalizedBoundaryGeometricDecomposition

/-- If the weighted normalized boundary cycle already pushes forward to the
diagonal identity correspondence, then it itself supplies the required
geometric decomposition package. -/
def of_integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (hpush : model.pushforwardCycle model.weightedBoundaryCycle =
      decomposition.identityFiniteCorrespondence) :
    NormalizedBoundaryGeometricDecomposition model decomposition where
  normalizedBoundaryDivisor := model.weightedBoundaryCycle
  divisor_eq_weightedBoundary := rfl
  pushforward_divisor_eq_identity := hpush

/-- The coefficient-level target induced by an actual geometric decomposition of
the normalized boundary divisor. -/
def toCycleIdentityTarget
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      NormalizedBoundaryGeometricDecomposition model decomposition) :
    NormalizedBoundaryCycleIdentityTarget model decomposition :=
  NormalizedBoundaryCycleIdentityTarget.ofGeometricDecomposition geometricDecomposition

/-- The multiplicity analysis induced directly by an honest geometric
decomposition of the normalized boundary divisor. -/
def toMultiplicityAnalysis
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      NormalizedBoundaryGeometricDecomposition model decomposition) :
    MultiplicityAnalysis model decomposition :=
  geometricDecomposition.toCycleIdentityTarget.toMultiplicityAnalysis

/-- The coefficient theorem package induced directly by an honest geometric
decomposition of the normalized boundary divisor. -/
def toCoefficientComputation
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      NormalizedBoundaryGeometricDecomposition model decomposition) :
    BoundaryCoefficientComputation model.toBoundaryFormulaGeometry
      decomposition model.toPushforwardGeometry :=
  geometricDecomposition.toMultiplicityAnalysis.toCoefficientComputation

/-- The full boundary formula implied directly by an honest geometric
decomposition of the normalized boundary divisor. -/
theorem boundary_formula
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      NormalizedBoundaryGeometricDecomposition model decomposition) :
    model.toPushforwardGeometry.pushedBoundaryCorrespondence =
      decomposition.identityFiniteCorrespondence :=
  MultiplicityAnalysis.boundary_formula decomposition
    geometricDecomposition.toMultiplicityAnalysis

/-- An honest geometric decomposition of the normalized boundary divisor gives
the weighted-boundary pushforward identity directly. -/
theorem integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      NormalizedBoundaryGeometricDecomposition model decomposition) :
    model.pushforwardCycle model.weightedBoundaryCycle =
      decomposition.identityFiniteCorrespondence := by
  calc
    model.pushforwardCycle model.weightedBoundaryCycle =
        model.pushforwardCycle geometricDecomposition.normalizedBoundaryDivisor := by
        rw [← geometricDecomposition.divisor_eq_weightedBoundary]
    _ = decomposition.identityFiniteCorrespondence :=
      geometricDecomposition.pushforward_divisor_eq_identity

/-- A direct weighted-boundary pushforward identity already implies the full
boundary formula, without separately packaging the same cycle as an abstract
normalized boundary divisor. -/
theorem boundary_formula_of_integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (hpush : model.pushforwardCycle model.weightedBoundaryCycle =
      decomposition.identityFiniteCorrespondence) :
    model.toPushforwardGeometry.pushedBoundaryCorrespondence =
      decomposition.identityFiniteCorrespondence :=
  boundary_formula decomposition
    (of_integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence hpush)

/-- Honest geometric decomposition data exist exactly when the weighted
normalized boundary cycle pushes forward to the identity correspondence. -/
theorem nonempty_iff_integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] :
    Nonempty (NormalizedBoundaryGeometricDecomposition model decomposition) ↔
      model.pushforwardCycle model.weightedBoundaryCycle =
        decomposition.identityFiniteCorrespondence := by
  constructor
  · rintro ⟨geometricDecomposition⟩
    calc
      model.pushforwardCycle model.weightedBoundaryCycle =
          model.pushforwardCycle geometricDecomposition.normalizedBoundaryDivisor := by
            rw [← geometricDecomposition.divisor_eq_weightedBoundary]
      _ = decomposition.identityFiniteCorrespondence :=
        geometricDecomposition.pushforward_divisor_eq_identity
  · intro hpush
    exact ⟨of_integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence hpush⟩

/-- Upgrade an honest integral geometric decomposition to the strengthened
surface by adjoining the rational cancellation witness already proved from the
model data. -/
def toHonestGeometricDecomposition
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      NormalizedBoundaryGeometricDecomposition model decomposition) :
    HonestNormalizedBoundaryGeometricDecomposition model decomposition where
  normalizedBoundaryDivisor := geometricDecomposition.normalizedBoundaryDivisor
  divisor_eq_weightedBoundary := geometricDecomposition.divisor_eq_weightedBoundary
  pushforward_divisor_eq_identity := geometricDecomposition.pushforward_divisor_eq_identity
  normalizedBoundaryDivisorQ := model.weightedBoundaryCycleQ
  divisorQ_eq_weightedBoundaryQ := rfl
  pushforward_divisorQ_eq_identityQ :=
    model.weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ
      decomposition

end NormalizedBoundaryGeometricDecomposition

namespace NormalizedBoundaryCycleIdentityTarget

/-- The indicator-form normalized boundary cycle identity target already
supplies an honest geometric decomposition package, because it implies the
weighted-boundary pushforward identity. -/
def toGeometricDecomposition
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (cycleIdentity : NormalizedBoundaryCycleIdentityTarget model decomposition) :
    NormalizedBoundaryGeometricDecomposition model decomposition :=
  NormalizedBoundaryGeometricDecomposition.of_integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
    (NormalizedBoundaryCycleIdentityTarget.integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
      decomposition cycleIdentity)

/-- The coefficient-level normalized boundary cycle identity target guarantees
that honest geometric decomposition data are nonempty. -/
theorem nonempty_geometricDecomposition
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (cycleIdentity : NormalizedBoundaryCycleIdentityTarget model decomposition) :
    Nonempty (NormalizedBoundaryGeometricDecomposition model decomposition) :=
  ⟨cycleIdentity.toGeometricDecomposition⟩

/-- The indicator-form target exists exactly when honest geometric
decomposition data exist. -/
theorem nonempty_iff_nonempty_geometricDecomposition
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] :
    Nonempty (NormalizedBoundaryCycleIdentityTarget model decomposition) ↔
      Nonempty (NormalizedBoundaryGeometricDecomposition model decomposition) := by
  constructor
  · rintro ⟨cycleIdentity⟩
    exact cycleIdentity.nonempty_geometricDecomposition
  · rintro ⟨geometricDecomposition⟩
    exact ⟨geometricDecomposition.toCycleIdentityTarget⟩

/-- The indicator-form normalized boundary cycle identity target exists exactly
when the weighted normalized boundary cycle pushes forward to the diagonal
identity correspondence. -/
theorem nonempty_iff_integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] :
    Nonempty (NormalizedBoundaryCycleIdentityTarget model decomposition) ↔
      model.pushforwardCycle model.weightedBoundaryCycle =
        decomposition.identityFiniteCorrespondence := by
  constructor
  · rintro ⟨cycleIdentity⟩
    exact cycleIdentity.integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
      decomposition
  · intro hpush
    exact ⟨(NormalizedBoundaryGeometricDecomposition.of_integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
      hpush).toCycleIdentityTarget⟩

/-- Upgrade the integral coefficient-level target to the strengthened honest
surface by first recovering the integral geometric decomposition and then
adjoining the model's rational cancellation witness. -/
def toHonestGeometricDecomposition
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (cycleIdentity : NormalizedBoundaryCycleIdentityTarget model decomposition) :
    HonestNormalizedBoundaryGeometricDecomposition model decomposition :=
  cycleIdentity.toGeometricDecomposition.toHonestGeometricDecomposition

end NormalizedBoundaryCycleIdentityTarget

namespace MultiplicityAnalysis

/-- The indicator-form normalized boundary cycle identity target induced by a
multiplicity analysis of a global normalization boundary model. -/
def toCycleIdentityTarget
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (analysis : MultiplicityAnalysis model decomposition) :
    NormalizedBoundaryCycleIdentityTarget model decomposition where
  pushedClass := analysis.pushedClass
  pushedClass_eq := analysis.pushedClass_eq
  coefficient_eq_indicator := by
    intro primeClass
    by_cases hprime : primeClass ∈ decomposition.diagonalPrimeClasses
    · rw [if_pos hprime]
      exact analysis.diagonalMultiplicity primeClass hprime
    · rw [if_neg hprime]
      exact analysis.offDiagonalMultiplicity primeClass hprime

/-- A multiplicity analysis already supplies honest geometric decomposition
data, via its induced indicator-form cycle identity target. -/
def toGeometricDecomposition
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (analysis : MultiplicityAnalysis model decomposition) :
    NormalizedBoundaryGeometricDecomposition model decomposition :=
  analysis.toCycleIdentityTarget.toGeometricDecomposition

/-- A multiplicity analysis guarantees that honest geometric decomposition data
are nonempty. -/
theorem nonempty_geometricDecomposition
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (analysis : MultiplicityAnalysis model decomposition) :
    Nonempty (NormalizedBoundaryGeometricDecomposition model decomposition) :=
  ⟨analysis.toGeometricDecomposition⟩

/-- Multiplicity analyses exist exactly when the indicator-form normalized
boundary cycle identity target exists. -/
theorem nonempty_iff_nonempty_cycleIdentityTarget
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] :
    Nonempty (MultiplicityAnalysis model decomposition) ↔
      Nonempty (NormalizedBoundaryCycleIdentityTarget model decomposition) := by
  constructor
  · rintro ⟨analysis⟩
    exact ⟨analysis.toCycleIdentityTarget⟩
  · rintro ⟨cycleIdentity⟩
    exact ⟨cycleIdentity.toMultiplicityAnalysis⟩

/-- Multiplicity analyses exist exactly when the weighted normalized boundary
cycle pushes forward to the diagonal identity correspondence. -/
theorem nonempty_iff_integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] :
    Nonempty (MultiplicityAnalysis model decomposition) ↔
      model.pushforwardCycle model.weightedBoundaryCycle =
        decomposition.identityFiniteCorrespondence := by
  rw [nonempty_iff_nonempty_cycleIdentityTarget]
  exact NormalizedBoundaryCycleIdentityTarget.nonempty_iff_integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence

/-- Upgrade a multiplicity analysis to the strengthened honest normalization
surface. The integral part comes from the multiplicity analysis itself, and the
rational witness comes from the model's proved branch-cancellation theorem. -/
def toHonestGeometricDecomposition
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (analysis : MultiplicityAnalysis model decomposition) :
    HonestNormalizedBoundaryGeometricDecomposition model decomposition :=
  analysis.toGeometricDecomposition.toHonestGeometricDecomposition

end MultiplicityAnalysis

namespace HonestNormalizedBoundaryGeometricDecomposition

/-- Forget the rational cancellation witness and recover the legacy integral
geometric closeout package. -/
def toIntegralGeometricDecomposition
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      HonestNormalizedBoundaryGeometricDecomposition model decomposition) :
    NormalizedBoundaryGeometricDecomposition model decomposition where
  normalizedBoundaryDivisor := geometricDecomposition.normalizedBoundaryDivisor
  divisor_eq_weightedBoundary := geometricDecomposition.divisor_eq_weightedBoundary
  pushforward_divisor_eq_identity := geometricDecomposition.pushforward_divisor_eq_identity

/-- Forget the integral divisor-level closeout and recover the rational
cancellation package. -/
def toRationalGeometricDecomposition
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      HonestNormalizedBoundaryGeometricDecomposition model decomposition) :
    RationalNormalizedBoundaryGeometricDecomposition model decomposition where
  normalizedBoundaryDivisorQ := geometricDecomposition.normalizedBoundaryDivisorQ
  divisor_eq_weightedBoundaryQ := geometricDecomposition.divisorQ_eq_weightedBoundaryQ
  pushforward_divisor_eq_identityQ := geometricDecomposition.pushforward_divisorQ_eq_identityQ

/-- The strengthened surface implies the integral weighted-boundary pushforward
identity. -/
theorem integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      HonestNormalizedBoundaryGeometricDecomposition model decomposition) :
    model.pushforwardCycle model.weightedBoundaryCycle =
      decomposition.identityFiniteCorrespondence := by
  exact NormalizedBoundaryGeometricDecomposition.integral_weightedBoundaryCycle_pushforward_eq_identityFiniteCorrespondence
    geometricDecomposition.toIntegralGeometricDecomposition

/-- The strengthened surface implies the rational weighted-boundary pushforward
identity. -/
theorem weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      HonestNormalizedBoundaryGeometricDecomposition model decomposition) :
    model.pushforwardCycleQ model.weightedBoundaryCycleQ =
      identityFiniteCorrespondenceQ decomposition := by
  exact RationalNormalizedBoundaryGeometricDecomposition.weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ
    geometricDecomposition.toRationalGeometricDecomposition

/-- Project the integral coefficient-level target from the strengthened
surface. -/
def toCycleIdentityTarget
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      HonestNormalizedBoundaryGeometricDecomposition model decomposition) :
    NormalizedBoundaryCycleIdentityTarget model decomposition :=
  geometricDecomposition.toIntegralGeometricDecomposition.toCycleIdentityTarget

/-- Project the rational coefficient-level target from the strengthened
surface. -/
def toRationalCycleIdentityTarget
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      HonestNormalizedBoundaryGeometricDecomposition model decomposition) :
    RationalNormalizedBoundaryCycleIdentityTarget model decomposition :=
  geometricDecomposition.toRationalGeometricDecomposition.toCycleIdentityTarget

/-- Project the integral multiplicity-analysis package from the strengthened
surface. This is the preferred route for downstream theorem consumers that
still speak in the existing coefficient-classification API. -/
def toMultiplicityAnalysis
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      HonestNormalizedBoundaryGeometricDecomposition model decomposition) :
    MultiplicityAnalysis model decomposition :=
  geometricDecomposition.toCycleIdentityTarget.toMultiplicityAnalysis

/-- Project the integral classification package from the strengthened surface.
-/
def toClassification
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      HonestNormalizedBoundaryGeometricDecomposition model decomposition) :
    NormalizationBoundaryStratumClassification model.toBoundaryFormulaGeometry
      decomposition model.toStratumGeometry :=
  geometricDecomposition.toMultiplicityAnalysis.toClassification

/-- Project the integral coefficient theorem package from the strengthened
surface. -/
def toCoefficientComputation
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      HonestNormalizedBoundaryGeometricDecomposition model decomposition) :
    BoundaryCoefficientComputation model.toBoundaryFormulaGeometry
      decomposition model.toPushforwardGeometry :=
  geometricDecomposition.toMultiplicityAnalysis.toCoefficientComputation

/-- The strengthened surface implies the full integral boundary formula. -/
theorem boundary_formula
    {C : Geometry.SmSchemeOver k}
    {model : NormalizationBoundaryModel C}
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      HonestNormalizedBoundaryGeometricDecomposition model decomposition) :
    model.toPushforwardGeometry.pushedBoundaryCorrespondence =
      decomposition.identityFiniteCorrespondence :=
  MultiplicityAnalysis.boundary_formula decomposition
    geometricDecomposition.toMultiplicityAnalysis

/-- Assemble the strengthened surface from the already-proved integral and
rational closeout data. This is packaging, not a new assumption. -/
def ofModelCloseoutTheorems
    {C : Geometry.SmSchemeOver k}
    (model : NormalizationBoundaryModel C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (geometricDecomposition :
      NormalizedBoundaryGeometricDecomposition model decomposition) :
    HonestNormalizedBoundaryGeometricDecomposition model decomposition where
  normalizedBoundaryDivisor := geometricDecomposition.normalizedBoundaryDivisor
  divisor_eq_weightedBoundary := geometricDecomposition.divisor_eq_weightedBoundary
  pushforward_divisor_eq_identity := geometricDecomposition.pushforward_divisor_eq_identity
  normalizedBoundaryDivisorQ := model.weightedBoundaryCycleQ
  divisorQ_eq_weightedBoundaryQ := rfl
  pushforward_divisorQ_eq_identityQ :=
    model.weightedBoundaryCycleQ_pushforward_eq_identityFiniteCorrespondenceQ
      decomposition

end HonestNormalizedBoundaryGeometricDecomposition

end NormalizationBoundaryModel

end

end Boundary
