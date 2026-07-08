import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Contractible.IdentityCone.IsIso.Composites.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.IdentityCone.Maps.Owner

/-!
# Identity-cone composites for the normalized cone-comparison cone object

This file specializes the identity-cone comparison composites to the
normalized cone-to-upper cochain map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The forward-then-backward composite for the normalized cone-comparison
identity-cone maps. -/
def additiveNormalizedConeComparisonForwardBackwardComposite
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) ⟶
      CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoIdentityConeForwardBackwardComposite
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The backward-then-forward composite for the normalized cone-comparison
identity-cone maps. -/
def additiveNormalizedConeComparisonBackwardForwardComposite
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    CochainComplex.mappingCone
        (𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)) ⟶
      CochainComplex.mappingCone
        (𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoIdentityConeBackwardForwardComposite
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The single-map normal form for the normalized forward-then-backward
composite. -/
def additiveNormalizedConeComparisonForwardBackwardSingleMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) ⟶
      CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoForwardBackwardSingleMap
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The single-map normal form for the normalized backward-then-forward
composite. -/
def additiveNormalizedConeComparisonBackwardForwardSingleMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    CochainComplex.mappingCone
        (𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)) ⟶
      CochainComplex.mappingCone
        (𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoBackwardForwardSingleMap
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The identity single-map normal form on the concrete mapping cone of the
normalized cone-to-upper cochain map. -/
def additiveNormalizedConeComparisonForwardBackwardIdentitySingleMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) ⟶
      CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoForwardBackwardIdentitySingleMap
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The identity single-map normal form on the upper-truncation identity cone. -/
def additiveNormalizedConeComparisonBackwardForwardIdentitySingleMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    CochainComplex.mappingCone
        (𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)) ⟶
      CochainComplex.mappingCone
        (𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoBackwardForwardIdentitySingleMap
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The normalized forward-then-backward single-map normal form after replacing
the source component by an identity but before replacing the target component. -/
def additiveNormalizedConeComparisonForwardBackwardSourceIdentitySingleMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) ⟶
      CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoForwardBackwardSourceIdentitySingleMap
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The normalized backward-then-forward single-map normal form after replacing
the source component by an identity but before replacing the target component. -/
def additiveNormalizedConeComparisonBackwardForwardSourceIdentitySingleMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    CochainComplex.mappingCone
        (𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)) ⟶
      CochainComplex.mappingCone
        (𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoBackwardForwardSourceIdentitySingleMap
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The actual identity morphism on the concrete mapping cone of the normalized
cone-to-upper cochain map. -/
def additiveNormalizedConeComparisonForwardBackwardIdentityMorphism
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) ⟶
      CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoForwardBackwardIdentityMorphism
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The actual identity morphism on the upper-truncation identity cone. -/
def additiveNormalizedConeComparisonBackwardForwardIdentityMorphism
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    CochainComplex.mappingCone
        (𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)) ⟶
      CochainComplex.mappingCone
        (𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoBackwardForwardIdentityMorphism
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- Projection formula for the normalized forward-then-backward composite. -/
theorem additiveNormalizedConeComparisonForwardBackwardComposite_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardComposite
          cut
          complex =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoIdentityConeForwardBackwardComposite
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex) :=
  rfl

/-- Projection formula for the normalized backward-then-forward composite. -/
theorem additiveNormalizedConeComparisonBackwardForwardComposite_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardComposite
          cut
          complex =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoIdentityConeBackwardForwardComposite
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex) :=
  rfl

/-- Projection formula for the normalized forward-then-backward single-map
normal form. -/
theorem additiveNormalizedConeComparisonForwardBackwardSingleMap_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardSingleMap
          cut
          complex =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardSingleMap
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex) :=
  rfl

/-- Projection formula for the normalized backward-then-forward single-map
normal form. -/
theorem additiveNormalizedConeComparisonBackwardForwardSingleMap_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardSingleMap
          cut
          complex =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardSingleMap
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex) :=
  rfl

/-- Projection formula for the normalized forward-then-backward source-identity
single-map normal form. -/
theorem additiveNormalizedConeComparisonForwardBackwardSourceIdentitySingleMap_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardSourceIdentitySingleMap
          cut
          complex =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardSourceIdentitySingleMap
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex) :=
  rfl

/-- Projection formula for the normalized backward-then-forward source-identity
single-map normal form. -/
theorem additiveNormalizedConeComparisonBackwardForwardSourceIdentitySingleMap_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardSourceIdentitySingleMap
          cut
          complex =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardSourceIdentitySingleMap
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex) :=
  rfl

/-- The normalized forward-then-backward composite is its single-map normal
form. -/
theorem additiveNormalizedConeComparisonForwardBackwardComposite_eq_singleMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardComposite
          cut
          complex =
      TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardSingleMap
          cut
          complex :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoForwardBackwardComposite_eq_singleMap
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The normalized backward-then-forward composite is its single-map normal
form. -/
theorem additiveNormalizedConeComparisonBackwardForwardComposite_eq_singleMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardComposite
          cut
          complex =
      TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardSingleMap
          cut
          complex :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoBackwardForwardComposite_eq_singleMap
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- Projection formula for the normalized forward-then-backward identity
single-map normal form. -/
theorem additiveNormalizedConeComparisonForwardBackwardIdentitySingleMap_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardIdentitySingleMap
          cut
          complex =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoForwardBackwardIdentitySingleMap
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex) :=
  rfl

/-- Projection formula for the normalized backward-then-forward identity
single-map normal form. -/
theorem additiveNormalizedConeComparisonBackwardForwardIdentitySingleMap_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardIdentitySingleMap
          cut
          complex =
      TraceAnalyticAdditiveHomotopyCategory
        .mappingConeIsoBackwardForwardIdentitySingleMap
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex) :=
  rfl

/-- Projection formula for the actual normalized forward-then-backward identity
morphism. -/
theorem additiveNormalizedConeComparisonForwardBackwardIdentityMorphism_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardIdentityMorphism
          cut
          complex =
      𝟙
        (CochainComplex.mappingCone
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex)) :=
  rfl

/-- Projection formula for the actual normalized backward-then-forward identity
morphism. -/
theorem additiveNormalizedConeComparisonBackwardForwardIdentityMorphism_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardIdentityMorphism
          cut
          complex =
      𝟙
        (CochainComplex.mappingCone
          (𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex))) :=
  rfl

/-- Source-component equality for the normalized forward-then-backward
single-map normal form. -/
theorem additiveNormalizedConeComparisonForwardBackward_sourceComponent_eq_identity
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex ≫
      inv
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) =
      𝟙
        (CochainComplex.mappingCone
          (TraceAnalyticMotivicTStructure
            .additiveDecompositionTruncLEInclusionMap cut complex)) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoForwardBackwardSingleMap_sourceComponent_eq_identity
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- Target-component equality for the normalized forward-then-backward
single-map normal form. -/
theorem additiveNormalizedConeComparisonForwardBackward_targetComponent_eq_identity
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex) ≫
      𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex) =
      𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoForwardBackwardSingleMap_targetComponent_eq_identity
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- Source-component equality for the normalized backward-then-forward
single-map normal form. -/
theorem additiveNormalizedConeComparisonBackwardForward_sourceComponent_eq_identity
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    inv
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) ≫
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex =
      𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoBackwardForwardSingleMap_sourceComponent_eq_identity
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- Target-component equality for the normalized backward-then-forward
single-map normal form. -/
theorem additiveNormalizedConeComparisonBackwardForward_targetComponent_eq_identity
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex) ≫
      𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex) =
      𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoBackwardForwardSingleMap_targetComponent_eq_identity
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The normalized forward-then-backward single-map normal form equals its
source-identity intermediate map. -/
theorem additiveNormalizedConeComparisonForwardBackwardSingleMap_eq_sourceIdentitySingleMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardSingleMap
          cut
          complex =
      TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardSourceIdentitySingleMap
          cut
          complex :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoForwardBackwardSingleMap_eq_sourceIdentitySingleMap
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The normalized forward-then-backward source-identity intermediate map equals
the identity single-map normal form. -/
theorem additiveNormalizedConeComparisonForwardBackwardSourceIdentitySingleMap_eq_identitySingleMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardSourceIdentitySingleMap
          cut
          complex =
      TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardIdentitySingleMap
          cut
          complex :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoForwardBackwardSourceIdentitySingleMap_eq_identitySingleMap
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The normalized backward-then-forward single-map normal form equals its
source-identity intermediate map. -/
theorem additiveNormalizedConeComparisonBackwardForwardSingleMap_eq_sourceIdentitySingleMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardSingleMap
          cut
          complex =
      TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardSourceIdentitySingleMap
          cut
          complex :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoBackwardForwardSingleMap_eq_sourceIdentitySingleMap
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The normalized backward-then-forward source-identity intermediate map equals
the identity single-map normal form. -/
theorem additiveNormalizedConeComparisonBackwardForwardSourceIdentitySingleMap_eq_identitySingleMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardSourceIdentitySingleMap
          cut
          complex =
      TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardIdentitySingleMap
          cut
          complex :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoBackwardForwardSourceIdentitySingleMap_eq_identitySingleMap
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The normalized forward-then-backward identity single-map normal form is the
actual identity morphism. -/
theorem additiveNormalizedConeComparisonForwardBackwardIdentitySingleMap_eq_identityMorphism
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardIdentitySingleMap
          cut
          complex =
      TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardIdentityMorphism
          cut
          complex :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoForwardBackwardIdentitySingleMap_eq_identityMorphism
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The normalized backward-then-forward identity single-map normal form is the
actual identity morphism. -/
theorem additiveNormalizedConeComparisonBackwardForwardIdentitySingleMap_eq_identityMorphism
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardIdentitySingleMap
          cut
          complex =
      TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardIdentityMorphism
          cut
          complex :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoBackwardForwardIdentitySingleMap_eq_identityMorphism
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The normalized forward-then-backward identity-cone comparison composite is
the actual identity morphism. -/
theorem additiveNormalizedConeComparisonForwardBackwardComposite_eq_identityMorphism
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardComposite
          cut
          complex =
      TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonForwardBackwardIdentityMorphism
          cut
          complex :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoForwardBackwardComposite_eq_identityMorphism
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The normalized backward-then-forward identity-cone comparison composite is
the actual identity morphism. -/
theorem additiveNormalizedConeComparisonBackwardForwardComposite_eq_identityMorphism
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardComposite
          cut
          complex =
      TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBackwardForwardIdentityMorphism
          cut
          complex :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoBackwardForwardComposite_eq_identityMorphism
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

/-- The concrete mapping cone of the normalized cone-comparison cochain map is
isomorphic to the upper-truncation identity cone. -/
def additiveNormalizedConeComparisonIdentityConeIso
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) ≅
      CochainComplex.mappingCone
        (𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)) :=
  TraceAnalyticAdditiveHomotopyCategory
    .mappingConeIsoIdentityConeIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
