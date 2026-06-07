import Boundary.CanonicalDMgmConstruction

/-!
# Boundary DMgm Input Surface

This file exports the canonical Boundary-side input package consumed by the
classical `DM_gm(Q)_Q` construction layer.

Boundary has a formal geometric-motives stabilization surface in
`Boundary.GeometricMotives`; this module intentionally exposes the separate
input bundle used by downstream classical recognition APIs.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

namespace Boundary

noncomputable section


/-- Final Boundary-side input bundle for the classical `DM_gm(Q)_Q`
construction. Boundary exports the effective presentation and canonical
Tate-stabilization input expected by the classical recognition layer. -/
structure CanonicalDMgmInputDataQ (category : SmCorQ (k := k)) where
  effectivePresentation : CanonicalEffectiveMotivicPresentationQ category
  tateStabilizationInput :
    CanonicalTateStabilizationInputQ category effectivePresentation

namespace CanonicalDMgmInputDataQ

abbrev internalPresentation
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :=
  input.effectivePresentation.internalPresentation

abbrev composition
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :=
  input.tateStabilizationInput.tateObjectData.witnessData.composition

@[simp] theorem internalPresentation_eq_effectivePresentation_internalPresentation
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :
    input.internalPresentation = input.effectivePresentation.internalPresentation :=
  rfl

abbrev motiveOf
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :=
  input.tateStabilizationInput.canonicalTateDatum

@[simp] theorem motiveOf_eq_canonicalTateDatum
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :
    input.motiveOf = input.tateStabilizationInput.canonicalTateDatum :=
  rfl

abbrev reducedProjectiveLineMotive
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :=
  input.tateStabilizationInput.canonicalReducedProjectiveLineMotive

@[simp] theorem reducedProjectiveLineMotive_eq_canonicalReducedProjectiveLineMotive
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :
    input.reducedProjectiveLineMotive =
      input.tateStabilizationInput.canonicalReducedProjectiveLineMotive :=
  rfl

/-- Owner theorem that the reduced projective-line motive is the cone of the
canonical basepoint map `M(Spec k) ⟶ M(P¹)`. -/
theorem reducedProjectiveLineMotive_isCone
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :
    ∃ (projectiveLineToReduced :
          boundaryProjectiveLineMotive
              (composition := input.composition) ⟶
            input.reducedProjectiveLineMotive)
        (reducedToShiftedUnit :
          input.reducedProjectiveLineMotive ⟶
            (shiftFunctor
              (canonicalEffectiveMotives input.composition)
              (1 : ℤ)).obj
              (canonicalUnitMotive input.composition)),
      ({ obj₁ := canonicalUnitMotive input.composition
         obj₂ := boundaryProjectiveLineMotive
            (composition := input.composition)
         obj₃ := input.reducedProjectiveLineMotive
         mor₁ := boundaryUnitToProjectiveLineMotive
            (composition := input.composition)
         mor₂ := projectiveLineToReduced
         mor₃ := reducedToShiftedUnit } :
          CategoryTheory.Pretriangulated.Triangle
            (canonicalEffectiveMotives input.composition)) ∈
        distTriang (canonicalEffectiveMotives input.composition) :=
  input.tateStabilizationInput.reducedProjectiveLineMotive_isCone

/-- Owner theorem identifying the twice-shifted effective Tate object with the
reduced projective-line motive. -/
theorem motiveOf_shifted_iso_reducedProjectiveLineMotive
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :
    Nonempty
      (((shiftFunctor
          (canonicalEffectiveMotives input.composition)
          (2 : ℤ)).obj input.motiveOf) ≅
        input.reducedProjectiveLineMotive) :=
  input.tateStabilizationInput.effectiveTateObject_shifted_iso_reducedProjectiveLine

/-- Canonical theorem-surface alias for localization compatibility, proved in
the effective-motives owner layer. -/
abbrev localizationCompatibility :=
  CanonicalTateStabilizationInputQ.localizationCompatibility

@[simp] theorem localizationCompatibility_eq_canonical :
    localizationCompatibility (k := k) =
      CanonicalTateStabilizationInputQ.localizationCompatibility (k := k) :=
  rfl

abbrev canonicalExternalProduct
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :=
  input.tateStabilizationInput.canonicalExternalProduct

@[simp] theorem canonicalExternalProduct_eq_canonicalExternalProductData
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :
    input.canonicalExternalProduct = input.tateStabilizationInput.canonicalExternalProduct :=
  rfl

/-- Consume the canonical DMgm stabilization universal property associated to
the projective-geometric Tate object. -/
abbrev dmgmUniversalProperty
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :
    VoevodskyDMgmTateStabilizationUniversalProperty
      (composition := input.composition) :=
  input.tateStabilizationInput.dmgmUniversalProperty

@[simp] theorem dmgmUniversalProperty_eq_dmgmUniversalPropertyInput
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :
    input.dmgmUniversalProperty = input.tateStabilizationInput.dmgmUniversalProperty :=
  rfl

/-- Recognition-facing extension data for a functor out of the DMgm
stabilization associated to this input. -/
abbrev dmgmStabilizationExtension
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category)
    (D : Type (u + 2)) [Category D] :=
  VoevodskyDMgmTateStabilizationExtension
    (composition := input.composition)
    D

/-- Recognition-facing lift from the DMgm stabilization universal property. -/
def dmgmStabilizationExtensionLift
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category)
    {D : Type (u + 2)} [Category D]
    (extension : input.dmgmStabilizationExtension D) :
    VoevodskyDMgmQ_Q
        (composition := input.composition) ⥤ D :=
  VoevodskyDMgmTateStabilizationExtension.lift
    (composition := input.composition)
    extension

@[simp] theorem dmgmStabilizationExtensionLift_obj
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category)
    {D : Type (u + 2)} [Category D]
    (extension : input.dmgmStabilizationExtension D)
    (X :
      VoevodskyDMgmQ_Q
        (composition := input.composition)) :
    (input.dmgmStabilizationExtensionLift extension).obj X =
      extension.obj X.effectiveObj X.tateTwist :=
  rfl

@[simp] theorem dmgmStabilizationExtensionLift_map
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category)
    {D : Type (u + 2)} [Category D]
    (extension : input.dmgmStabilizationExtension D)
    {X Y :
      VoevodskyDMgmQ_Q
        (composition := input.composition)}
    (f : X ⟶ Y) :
    (input.dmgmStabilizationExtensionLift extension).map f =
      extension.map f X.tateTwist Y.tateTwist :=
  rfl

/-- Project the canonical Boundary input to the pair of the effective
presentation data and the Tate-stabilization input needed by the classical
motives layer. -/
def toPresentationAndStabilization
    {category : SmCorQ (k := k)}
    (input : CanonicalDMgmInputDataQ category) :
    CanonicalEffectiveMotivicPresentationQ category ×
      CanonicalTateStabilizationInputQ category input.effectivePresentation :=
  (input.effectivePresentation,
    input.tateStabilizationInput)

end CanonicalDMgmInputDataQ

end

end Boundary
