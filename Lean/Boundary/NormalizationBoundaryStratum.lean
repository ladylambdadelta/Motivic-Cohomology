import Boundary.Basic
import Boundary.BoundaryFormula

/-!
# Normalization Boundary Strata

This file packages per-stratum pushforward geometry for normalization-based
boundary formulas and the multiplicity classification interface used to derive
coefficient computations.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

open PrimeFiniteCorrespondenceSupport

noncomputable section

/-- Normalization or boundary-stratum geometry whose multiplicity theorems
classify the pushed supports by geometric prime class.

This record still does not state the final boundary identity. Its data is the
termwise pushforward construction together with class-level multiplicity
computations from which the coefficient theorem package can be derived. -/
structure NormalizationBoundaryStratumDatum {C : Geometry.SmSchemeOver k}
    (geometry : BoundaryFormulaGeometry C)
    (boundaryIndex : geometry.boundaryIndex) where
  chart : BoundaryChart k
  chart_interior_eq : chart.interior = geometry.boundarySource
  stratum : BoundaryStratum k
  stratum_chart_eq : stratum.chart = chart
  targetSourceComponent : SourceIrreducibleComponent C
  pushSupport_isIntegral : IsIntegral stratum.support
  sourceComponentMap :
    (geometry.boundarySupport boundaryIndex).sourceComponent.carrier.scheme ⟶
      targetSourceComponent.carrier.scheme
  sourceComponentMap_toAmbient :
    sourceComponentMap ≫ targetSourceComponent.toAmbient =
      (geometry.boundarySupport boundaryIndex).sourceComponent.toAmbient ≫ geometry.nu.hom
  finiteOverTargetSource : stratum.support ⟶ targetSourceComponent.carrier.scheme
  finite_toTargetSource : IsFinite finiteOverTargetSource
  surjective_toTargetSource : Function.Surjective finiteOverTargetSource.base
  toTarget : stratum.support ⟶ C.scheme
  inclusion : stratum.support ⟶ overBaseProduct targetSourceComponent.carrier C
  inclusion_fst : inclusion ≫ overBaseProduct.fst targetSourceComponent.carrier C =
    finiteOverTargetSource
  inclusion_snd : inclusion ≫ overBaseProduct.snd targetSourceComponent.carrier C =
    toTarget
  isClosedImmersion : IsClosedImmersion inclusion
  mapFromOriginal : (geometry.boundarySupport boundaryIndex).support ⟶ stratum.support
  mapFromOriginal_toSource :
    mapFromOriginal ≫ finiteOverTargetSource =
      (geometry.boundarySupport boundaryIndex).toSourceComponent ≫ sourceComponentMap
  mapFromOriginal_toTarget :
    mapFromOriginal ≫ toTarget =
      (geometry.boundarySupport boundaryIndex).toTargetScheme ≫ geometry.nu.hom

namespace NormalizationBoundaryStratumDatum

/-- The explicit termwise pushforward package produced by a normalization or
boundary stratum datum. -/
def toPushforwardPrimeSupportData {C : Geometry.SmSchemeOver k}
    {geometry : BoundaryFormulaGeometry C}
    {boundaryIndex : geometry.boundaryIndex}
    (datum : NormalizationBoundaryStratumDatum geometry boundaryIndex) :
    PushforwardPrimeSupportData geometry.nu (geometry.boundarySupport boundaryIndex) where
  targetSourceComponent := datum.targetSourceComponent
  pushSupport := datum.stratum.support
  pushSupport_isIntegral := datum.pushSupport_isIntegral
  sourceComponentMap := datum.sourceComponentMap
  sourceComponentMap_toAmbient := datum.sourceComponentMap_toAmbient
  finiteOverTargetSource := datum.finiteOverTargetSource
  finite_toTargetSource := datum.finite_toTargetSource
  surjective_toTargetSource := datum.surjective_toTargetSource
  toTarget := datum.toTarget
  inclusion := datum.inclusion
  inclusion_fst := datum.inclusion_fst
  inclusion_snd := datum.inclusion_snd
  isClosedImmersion := datum.isClosedImmersion
  mapFromOriginal := datum.mapFromOriginal
  mapFromOriginal_toSource := datum.mapFromOriginal_toSource
  mapFromOriginal_toTarget := datum.mapFromOriginal_toTarget

end NormalizationBoundaryStratumDatum

structure NormalizationBoundaryStratumGeometry {C : Geometry.SmSchemeOver k}
    (geometry : BoundaryFormulaGeometry C)
  where
  chart : BoundaryChart k
  chart_interior_eq : chart.interior = geometry.boundarySource
  stratum : (boundaryIndex : geometry.boundaryIndex) → BoundaryStratum k
  stratum_chart_eq :
    ∀ boundaryIndex, (stratum boundaryIndex).chart = chart
  targetSourceComponent :
    (boundaryIndex : geometry.boundaryIndex) → SourceIrreducibleComponent C
  pushSupport_isIntegral :
    ∀ boundaryIndex, IsIntegral (stratum boundaryIndex).support
  sourceComponentMap :
    (boundaryIndex : geometry.boundaryIndex) →
      (geometry.boundarySupport boundaryIndex).sourceComponent.carrier.scheme ⟶
        (targetSourceComponent boundaryIndex).carrier.scheme
  sourceComponentMap_toAmbient :
    ∀ boundaryIndex,
      sourceComponentMap boundaryIndex ≫ (targetSourceComponent boundaryIndex).toAmbient =
        (geometry.boundarySupport boundaryIndex).sourceComponent.toAmbient ≫ geometry.nu.hom
  finiteOverTargetSource :
    (boundaryIndex : geometry.boundaryIndex) →
      (stratum boundaryIndex).support ⟶ (targetSourceComponent boundaryIndex).carrier.scheme
  finite_toTargetSource :
    ∀ boundaryIndex, IsFinite (finiteOverTargetSource boundaryIndex)
  surjective_toTargetSource :
    ∀ boundaryIndex, Function.Surjective (finiteOverTargetSource boundaryIndex).base
  toTarget :
    (boundaryIndex : geometry.boundaryIndex) →
      (stratum boundaryIndex).support ⟶ C.scheme
  inclusion :
    (boundaryIndex : geometry.boundaryIndex) →
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
    (boundaryIndex : geometry.boundaryIndex) →
      (geometry.boundarySupport boundaryIndex).support ⟶ (stratum boundaryIndex).support
  mapFromOriginal_toSource :
    ∀ boundaryIndex,
      mapFromOriginal boundaryIndex ≫ finiteOverTargetSource boundaryIndex =
        (geometry.boundarySupport boundaryIndex).toSourceComponent ≫
          sourceComponentMap boundaryIndex
  mapFromOriginal_toTarget :
    ∀ boundaryIndex,
      mapFromOriginal boundaryIndex ≫ toTarget boundaryIndex =
        (geometry.boundarySupport boundaryIndex).toTargetScheme ≫ geometry.nu.hom

namespace NormalizationBoundaryStratumGeometry

/-- The per-index normalization or boundary-stratum datum extracted from the
global normalization geometry package. -/
def datum {C : Geometry.SmSchemeOver k}
    {geometry : BoundaryFormulaGeometry C}
  (stratumGeometry : NormalizationBoundaryStratumGeometry geometry)
    (boundaryIndex : geometry.boundaryIndex) :
    NormalizationBoundaryStratumDatum geometry boundaryIndex where
  chart := stratumGeometry.chart
  chart_interior_eq := stratumGeometry.chart_interior_eq
  stratum := stratumGeometry.stratum boundaryIndex
  stratum_chart_eq := stratumGeometry.stratum_chart_eq boundaryIndex
  targetSourceComponent := stratumGeometry.targetSourceComponent boundaryIndex
  pushSupport_isIntegral := stratumGeometry.pushSupport_isIntegral boundaryIndex
  sourceComponentMap := stratumGeometry.sourceComponentMap boundaryIndex
  sourceComponentMap_toAmbient :=
    stratumGeometry.sourceComponentMap_toAmbient boundaryIndex
  finiteOverTargetSource := stratumGeometry.finiteOverTargetSource boundaryIndex
  finite_toTargetSource := stratumGeometry.finite_toTargetSource boundaryIndex
  surjective_toTargetSource :=
    stratumGeometry.surjective_toTargetSource boundaryIndex
  toTarget := stratumGeometry.toTarget boundaryIndex
  inclusion := stratumGeometry.inclusion boundaryIndex
  inclusion_fst := stratumGeometry.inclusion_fst boundaryIndex
  inclusion_snd := stratumGeometry.inclusion_snd boundaryIndex
  isClosedImmersion := stratumGeometry.isClosedImmersion boundaryIndex
  mapFromOriginal := stratumGeometry.mapFromOriginal boundaryIndex
  mapFromOriginal_toSource :=
    stratumGeometry.mapFromOriginal_toSource boundaryIndex
  mapFromOriginal_toTarget :=
    stratumGeometry.mapFromOriginal_toTarget boundaryIndex

/-- The termwise pushforward packages derived from the explicit normalization or
boundary-stratum data. -/
def pushData {C : Geometry.SmSchemeOver k}
    {geometry : BoundaryFormulaGeometry C}
  (stratumGeometry : NormalizationBoundaryStratumGeometry geometry) :
    (boundaryIndex : geometry.boundaryIndex) →
      PushforwardPrimeSupportData geometry.nu (geometry.boundarySupport boundaryIndex) :=
  fun boundaryIndex =>
    (stratumGeometry.datum boundaryIndex).toPushforwardPrimeSupportData

/-- The pushed-support producer extracted from normalization or boundary-stratum
geometry. -/
def toPushforwardGeometry {C : Geometry.SmSchemeOver k}
    {geometry : BoundaryFormulaGeometry C}
    (stratumGeometry : NormalizationBoundaryStratumGeometry geometry) :
    BoundaryPushforwardGeometry geometry where
  pushData := stratumGeometry.pushData

end NormalizationBoundaryStratumGeometry

/-- Geometric multiplicity classification for the pushed boundary strata coming
from a fixed normalization or boundary-stratum geometry package. -/
structure NormalizationBoundaryStratumClassification {C : Geometry.SmSchemeOver k}
    (geometry : BoundaryFormulaGeometry C)
    (decomposition : FiniteIrreducibleComponentDecomposition C)
    (stratumGeometry : NormalizationBoundaryStratumGeometry geometry)
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)] where
  pushedClass : geometry.boundaryIndex → PrimeFiniteCorrespondenceGeom C C
  pushedClass_eq :
    ∀ boundaryIndex,
      pushedClass boundaryIndex =
        PrimeFiniteCorrespondenceGeom.ofRepresented
          (((stratumGeometry.datum boundaryIndex).toPushforwardPrimeSupportData).toRepresentedPrimeSupport)
  diagonalMultiplicity :
    ∀ primeClass : PrimeFiniteCorrespondenceGeom C C,
      primeClass ∈ decomposition.diagonalPrimeClasses →
        (Finset.univ.sum fun boundaryIndex : geometry.boundaryIndex =>
          if pushedClass boundaryIndex = primeClass then
            geometry.multiplicity boundaryIndex
          else
            0) = 1
  offDiagonalMultiplicity :
    ∀ primeClass : PrimeFiniteCorrespondenceGeom C C,
      primeClass ∉ decomposition.diagonalPrimeClasses →
        (Finset.univ.sum fun boundaryIndex : geometry.boundaryIndex =>
          if pushedClass boundaryIndex = primeClass then
            geometry.multiplicity boundaryIndex
          else
            0) = 0

namespace NormalizationBoundaryStratumClassification

/-– The coefficient theorem package derived from multiplicity theorems on the
geometric prime classes of the pushed supports. -/
def toCoefficientComputation {C : Geometry.SmSchemeOver k}
    {geometry : BoundaryFormulaGeometry C}
    {decomposition : FiniteIrreducibleComponentDecomposition C}
    {stratumGeometry : NormalizationBoundaryStratumGeometry geometry}
    [DecidableEq (PrimeFiniteCorrespondenceGeom C C)]
    (classification :
      NormalizationBoundaryStratumClassification geometry decomposition stratumGeometry) :
    BoundaryCoefficientComputation geometry decomposition
      (NormalizationBoundaryStratumGeometry.toPushforwardGeometry stratumGeometry) where
  diagonal primeClass hprime := by
    rw [BoundaryPushforwardGeometry.pushedBoundaryCorrespondence_apply
      (NormalizationBoundaryStratumGeometry.toPushforwardGeometry stratumGeometry) primeClass]
    simpa [NormalizationBoundaryStratumGeometry.pushData,
      NormalizationBoundaryStratumGeometry.toPushforwardGeometry,
      classification.pushedClass_eq] using
      classification.diagonalMultiplicity primeClass hprime
  offDiagonal primeClass hprime := by
    rw [BoundaryPushforwardGeometry.pushedBoundaryCorrespondence_apply
      (NormalizationBoundaryStratumGeometry.toPushforwardGeometry stratumGeometry) primeClass]
    simpa [NormalizationBoundaryStratumGeometry.pushData,
      NormalizationBoundaryStratumGeometry.toPushforwardGeometry,
      classification.pushedClass_eq] using
      classification.offDiagonalMultiplicity primeClass hprime

end NormalizationBoundaryStratumClassification

end

end Boundary
