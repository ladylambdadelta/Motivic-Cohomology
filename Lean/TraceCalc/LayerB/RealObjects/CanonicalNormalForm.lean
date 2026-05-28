import TraceCalc.LayerB.RealObjects.ResidueNFCode

/-!
# Real-objects formalization: canonical word / CanNF scaffold

This file starts the next manuscript layer after internal holography: a
canonical-word carrier attached to completed records, and a CanNF package over
that carrier. It deliberately stays at the contract/scaffold level: no fake
normalizer is implemented here.
-/

universe u v

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord
open CompletedReconstructionRecord.PeelChain

variable {setup : RewriteCalculusSetup.{u}}

/-- Canonical-word carrier for the equality-detection layer.

At this stage the honest carrier is still the frontier word attached to the
record. Future CanNF constructions may refine the internal representation while
keeping this as the record-facing entry point. -/
structure CanonicalWord (setup : RewriteCalculusSetup.{u}) where
  frontier : FrontierWord setup

namespace CanonicalWord

@[ext] theorem ext
    {w₁ w₂ : CanonicalWord setup}
    (hFrontier : w₁.frontier = w₂.frontier) : w₁ = w₂ := by
  cases w₁
  cases w₂
  cases hFrontier
  rfl

/-- Canonical word obtained directly from a completed record by forgetting down
to the current frontier-word carrier. -/
def ofResidue (R : CompletedReconstructionRecord setup) : CanonicalWord setup :=
  ⟨FrontierWord.ofResidue R⟩

@[simp] theorem ofResidue_frontier
    (R : CompletedReconstructionRecord setup) :
    (CanonicalWord.ofResidue R).frontier = FrontierWord.ofResidue R :=
  rfl

end CanonicalWord

/-- Assignment of canonical words to completed records.

This is the first explicit interface for the manuscript's
canonical-reconstruction-to-canonical-word step. The current soundness target
is exactly compatibility with the boundary-admin quotient relation already used
by `FrontierWord.Equiv`. -/
structure CanonicalWordAssignment (setup : RewriteCalculusSetup.{u}) where
  assign : CompletedReconstructionRecord setup → CanonicalWord setup
  sound :
    ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂ →
        FrontierWord.Equiv (assign R₁).frontier (assign R₂).frontier

namespace CanonicalWordAssignment

@[ext] theorem ext
    {A B : CanonicalWordAssignment setup}
    (hAssign : A.assign = B.assign) : A = B := by
  cases A
  cases B
  cases hAssign
  rfl

/-- The current residue/frontier layer already gives the minimal canonical-word
assignment: send a completed record to its frontier-word wrapper. -/
def ofResidue (setup : RewriteCalculusSetup.{u}) : CanonicalWordAssignment setup where
  assign := CanonicalWord.ofResidue
  sound := by
    intro R₁ R₂ h
    exact h

@[simp] theorem ofResidue_assign
    (R : CompletedReconstructionRecord setup) :
    (ofResidue setup).assign R = CanonicalWord.ofResidue R :=
  rfl

theorem ofResidue_sound
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂) :
    FrontierWord.Equiv
      ((ofResidue setup).assign R₁).frontier
      ((ofResidue setup).assign R₂).frontier :=
  (ofResidue setup).sound h

end CanonicalWordAssignment

/-- Canonical normal-form package for completed records.

The package consists of a canonical-word assignment together with a complete
normalizer on the frontier-word carrier reached through that assignment. -/
structure CanNF (setup : RewriteCalculusSetup.{u}) where
  assignment : CanonicalWordAssignment setup
  normalizer : FrontierWordCompleteNormalizer setup

namespace CanNF

@[ext] theorem ext
    {C₁ C₂ : CanNF setup}
    (hAssignment : C₁.assignment = C₂.assignment)
    (hNormalizer : C₁.normalizer = C₂.normalizer) : C₁ = C₂ := by
  cases C₁
  cases C₂
  cases hAssignment
  cases hNormalizer
  rfl

/-- Normal form assigned to a completed record by a CanNF package. -/
def normalize (C : CanNF setup) (R : CompletedReconstructionRecord setup) :
    C.normalizer.NF :=
  C.normalizer.normalize (C.assignment.assign R).frontier

@[simp] theorem normalize_eq
    (C : CanNF setup) (R : CompletedReconstructionRecord setup) :
    C.normalize R = C.normalizer.normalize (C.assignment.assign R).frontier :=
  rfl

/-- Soundness of the CanNF package on completed records: admin-equivalent
records have equal canonical-normal-form values. -/
theorem CanNF_sound (C : CanNF setup)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂) :
    C.normalize R₁ = C.normalize R₂ :=
  C.normalizer.sound (C.assignment.sound h)

/-- Completeness of the CanNF package on completed records relative to the
canonical-word assignment: equal normal-form values force canonical-word
equivalence. -/
theorem CanNF_complete (C : CanNF setup)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : C.normalize R₁ = C.normalize R₂) :
    FrontierWord.Equiv
      (C.assignment.assign R₁).frontier
      (C.assignment.assign R₂).frontier :=
  C.normalizer.complete h

theorem equiv_of_normalize_eq (C : CanNF setup)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : C.normalize R₁ = C.normalize R₂) :
    FrontierWord.Equiv
      (C.assignment.assign R₁).frontier
      (C.assignment.assign R₂).frontier :=
  C.CanNF_complete h

theorem normalize_eq_of_equiv (C : CanNF setup)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : FrontierWord.Equiv
      (C.assignment.assign R₁).frontier
      (C.assignment.assign R₂).frontier) :
    C.normalize R₁ = C.normalize R₂ :=
  C.normalizer.sound h

/-- Equality detection theorem for the current canonical-word / CanNF layer. -/
theorem CanNF_detects_equality (C : CanNF setup)
    (R₁ R₂ : CompletedReconstructionRecord setup) :
    C.normalize R₁ = C.normalize R₂ ↔
      FrontierWord.Equiv
        (C.assignment.assign R₁).frontier
        (C.assignment.assign R₂).frontier :=
  ⟨CanNF_complete C, C.normalizer.sound⟩

theorem normalize_eq_iff_equiv (C : CanNF setup)
    (R₁ R₂ : CompletedReconstructionRecord setup) :
    C.normalize R₁ = C.normalize R₂ ↔
      FrontierWord.Equiv
        (C.assignment.assign R₁).frontier
        (C.assignment.assign R₂).frontier :=
  C.CanNF_detects_equality R₁ R₂

end CanNF

/-- Relation-parameterized frontier-word normalizer contract.

This is the generic variant of `FrontierWordCompleteNormalizer`: equality of
normal forms detects an arbitrary chosen frontier-word relation `Rel`, not
necessarily plain `FrontierWord.Equiv`. -/
structure FrontierWordRelativeNormalizer
    (setup : RewriteCalculusSetup.{u})
    (Rel : FrontierWord setup → FrontierWord setup → Prop) where
  NF : Type v
  normalize : FrontierWord setup → NF
  sound :
    ∀ {w₁ w₂ : FrontierWord setup},
      Rel w₁ w₂ → normalize w₁ = normalize w₂
  complete :
    ∀ {w₁ w₂ : FrontierWord setup},
      normalize w₁ = normalize w₂ → Rel w₁ w₂

namespace FrontierWordRelativeNormalizer

theorem rel_of_normalize_eq
    {Rel : FrontierWord setup → FrontierWord setup → Prop}
    (N : FrontierWordRelativeNormalizer setup Rel)
    {w₁ w₂ : FrontierWord setup}
    (h : N.normalize w₁ = N.normalize w₂) :
    Rel w₁ w₂ :=
  N.complete h

theorem normalize_eq_iff_rel
    {Rel : FrontierWord setup → FrontierWord setup → Prop}
    (N : FrontierWordRelativeNormalizer setup Rel)
    {w₁ w₂ : FrontierWord setup} :
    N.normalize w₁ = N.normalize w₂ ↔ Rel w₁ w₂ :=
  ⟨N.complete, N.sound⟩

end FrontierWordRelativeNormalizer

/-- Relation-parameterized record-facing CanNF scaffold.

This is the generic variant of `CanNF`: the packaged normalizer detects a
chosen frontier-word relation on the canonical-word assignment, not necessarily
plain `FrontierWord.Equiv`. -/
structure RelativeCanNF
    (setup : RewriteCalculusSetup.{u})
    (Rel : FrontierWord setup → FrontierWord setup → Prop) where
  assignment : CanonicalWordAssignment setup
  normalizer : FrontierWordRelativeNormalizer setup Rel

namespace RelativeCanNF

def normalize
    {Rel : FrontierWord setup → FrontierWord setup → Prop}
    (C : RelativeCanNF setup Rel)
    (R : CompletedReconstructionRecord setup) :
    C.normalizer.NF :=
  C.normalizer.normalize (C.assignment.assign R).frontier

@[simp] theorem normalize_eq
    {Rel : FrontierWord setup → FrontierWord setup → Prop}
    (C : RelativeCanNF setup Rel)
    (R : CompletedReconstructionRecord setup) :
    C.normalize R = C.normalizer.normalize (C.assignment.assign R).frontier :=
  rfl

theorem sound
    {Rel : FrontierWord setup → FrontierWord setup → Prop}
    (C : RelativeCanNF setup Rel)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : Rel (C.assignment.assign R₁).frontier (C.assignment.assign R₂).frontier) :
    C.normalize R₁ = C.normalize R₂ :=
  C.normalizer.sound h

theorem complete
    {Rel : FrontierWord setup → FrontierWord setup → Prop}
    (C : RelativeCanNF setup Rel)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : C.normalize R₁ = C.normalize R₂) :
    Rel (C.assignment.assign R₁).frontier (C.assignment.assign R₂).frontier :=
  C.normalizer.complete h

theorem normalize_eq_iff_rel
    {Rel : FrontierWord setup → FrontierWord setup → Prop}
    (C : RelativeCanNF setup Rel)
    (R₁ R₂ : CompletedReconstructionRecord setup) :
    C.normalize R₁ = C.normalize R₂ ↔
      Rel (C.assignment.assign R₁).frontier (C.assignment.assign R₂).frontier :=
  ⟨C.complete, C.sound⟩

end RelativeCanNF

/-- First generic bridge from a relation-parameterized frontier-word
normalizer to the record-facing relative CanNF scaffold. -/
def FrontierWordRelativeCanNF
    (Rel : FrontierWord setup → FrontierWord setup → Prop)
    (N : FrontierWordRelativeNormalizer setup Rel) :
    RelativeCanNF setup Rel where
  assignment := CanonicalWordAssignment.ofResidue setup
  normalizer := N

@[simp] theorem FrontierWordRelativeCanNF_assignment
    (Rel : FrontierWord setup → FrontierWord setup → Prop)
    (N : FrontierWordRelativeNormalizer setup Rel) :
    (FrontierWordRelativeCanNF (setup := setup) Rel N).assignment =
      CanonicalWordAssignment.ofResidue setup :=
  rfl

@[simp] theorem FrontierWordRelativeCanNF_normalizer
    (Rel : FrontierWord setup → FrontierWord setup → Prop)
    (N : FrontierWordRelativeNormalizer setup Rel) :
    (FrontierWordRelativeCanNF (setup := setup) Rel N).normalizer = N :=
  rfl

@[simp] theorem FrontierWordRelativeCanNF_normalize
    (Rel : FrontierWord setup → FrontierWord setup → Prop)
    (N : FrontierWordRelativeNormalizer setup Rel)
    (R : CompletedReconstructionRecord setup) :
    (FrontierWordRelativeCanNF Rel N).normalize R =
      N.normalize (FrontierWord.ofResidue R) :=
  rfl

theorem frontierWordRelativeCanNF_normalize_eq_iff_rel
    (Rel : FrontierWord setup → FrontierWord setup → Prop)
    (N : FrontierWordRelativeNormalizer setup Rel)
    (R₁ R₂ : CompletedReconstructionRecord setup) :
    (FrontierWordRelativeCanNF Rel N).normalize R₁ =
      (FrontierWordRelativeCanNF Rel N).normalize R₂ ↔
      Rel (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂) := by
  simpa [FrontierWordRelativeCanNF, CanonicalWordAssignment.ofResidue, CanonicalWord.ofResidue]
    using (RelativeCanNF.normalize_eq_iff_rel
      (C := FrontierWordRelativeCanNF (setup := setup) Rel N) R₁ R₂)

theorem frontierWordRelativeCanNF_of_normalize_eq
    (Rel : FrontierWord setup → FrontierWord setup → Prop)
    (N : FrontierWordRelativeNormalizer setup Rel)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : (FrontierWordRelativeCanNF Rel N).normalize R₁ =
      (FrontierWordRelativeCanNF Rel N).normalize R₂) :
    Rel (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂) :=
  (frontierWordRelativeCanNF_normalize_eq_iff_rel
    (setup := setup) Rel N R₁ R₂).1 h

theorem frontierWordRelativeCanNF_normalize_eq_of_rel
    (Rel : FrontierWord setup → FrontierWord setup → Prop)
    (N : FrontierWordRelativeNormalizer setup Rel)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : Rel (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂)) :
    (FrontierWordRelativeCanNF Rel N).normalize R₁ =
      (FrontierWordRelativeCanNF Rel N).normalize R₂ :=
  (frontierWordRelativeCanNF_normalize_eq_iff_rel
    (setup := setup) Rel N R₁ R₂).2 h

namespace FrontierWordCompleteNormalizer

def ofFields
    (NF : Type v)
    (normalize : FrontierWord setup → NF)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → normalize w₁ = normalize w₂)
    (complete :
      ∀ {w₁ w₂ : FrontierWord setup},
        normalize w₁ = normalize w₂ → FrontierWord.Equiv w₁ w₂) :
    FrontierWordCompleteNormalizer.{u, v} setup where
  toFrontierWordSoundNormalizer := {
    NF := NF
    normalize := normalize
    sound := sound
  }
  complete := complete

@[simp] theorem ofFields_normalize
    (NF : Type v)
    (normalize : FrontierWord setup → NF)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → normalize w₁ = normalize w₂)
    (complete :
      ∀ {w₁ w₂ : FrontierWord setup},
        normalize w₁ = normalize w₂ → FrontierWord.Equiv w₁ w₂)
    (w : FrontierWord setup) :
    (ofFields (setup := setup) NF normalize @sound @complete).normalize w = normalize w :=
  rfl

@[simp] theorem ofFields_sound
    (NF : Type v)
    (normalize : FrontierWord setup → NF)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → normalize w₁ = normalize w₂)
    (complete :
      ∀ {w₁ w₂ : FrontierWord setup},
        normalize w₁ = normalize w₂ → FrontierWord.Equiv w₁ w₂)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    (ofFields (setup := setup) NF normalize @sound @complete).sound h = sound h :=
  rfl

@[simp] theorem ofFields_complete
    (NF : Type v)
    (normalize : FrontierWord setup → NF)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → normalize w₁ = normalize w₂)
    (complete :
      ∀ {w₁ w₂ : FrontierWord setup},
        normalize w₁ = normalize w₂ → FrontierWord.Equiv w₁ w₂)
    {w₁ w₂ : FrontierWord setup}
    (h : normalize w₁ = normalize w₂) :
    (ofFields (setup := setup) NF normalize @sound @complete).complete h = complete h :=
  rfl

theorem equiv_of_normalize_eq (N : FrontierWordCompleteNormalizer.{u, v} setup)
    {w₁ w₂ : FrontierWord setup} (h : N.normalize w₁ = N.normalize w₂) :
    FrontierWord.Equiv w₁ w₂ :=
  N.complete h

theorem normalize_eq_iff_equiv (N : FrontierWordCompleteNormalizer.{u, v} setup)
    {w₁ w₂ : FrontierWord setup} :
    N.normalize w₁ = N.normalize w₂ ↔ FrontierWord.Equiv w₁ w₂ :=
  ⟨N.complete, N.sound⟩

end FrontierWordCompleteNormalizer

/-! ### Computational CanNF interface (Type-level traces) -/

/-- Proof-relevant interface for a computational frontier normalizer.

This interface is intentionally separate from the semantic quotient normalizer:
it exposes a decoded representative, a `Type`-level trace from input to decoded
normal form, extensional sound/complete laws, a canonicality witness, and
decidable normal-form codes. -/
structure ComputationalFrontierNormalizer
    (setup : RewriteCalculusSetup.{u}) where
  NF : Type v
  decode : NF → FrontierWord setup
  normalize : FrontierWord setup → NF
  NormalizationTrace : FrontierWord setup → FrontierWord setup → Type u
  trace : (w : FrontierWord setup) →
    NormalizationTrace w (decode (normalize w))
  sound :
    ∀ {w₁ w₂ : FrontierWord setup},
      FrontierWord.Equiv w₁ w₂ → normalize w₁ = normalize w₂
  complete :
    ∀ {w₁ w₂ : FrontierWord setup},
      normalize w₁ = normalize w₂ → FrontierWord.Equiv w₁ w₂
  canonical :
    ∀ (w : FrontierWord setup),
      FrontierWord.Equiv w (decode (normalize w))
  decidableCode : DecidableEq NF

namespace ComputationalFrontierNormalizer

/-- Forgetful bridge from a computational normalizer to the extensional
`FrontierWordCompleteNormalizer` contract consumed by the current engine. -/
def toFrontierWordCompleteNormalizer
    (N : ComputationalFrontierNormalizer setup) :
    FrontierWordCompleteNormalizer setup :=
  FrontierWordCompleteNormalizer.ofFields N.NF N.normalize
    (fun h => N.sound h)
    (fun h => N.complete h)

@[simp] theorem toFrontierWordCompleteNormalizer_normalize
    (N : ComputationalFrontierNormalizer setup)
    (w : FrontierWord setup) :
    N.toFrontierWordCompleteNormalizer.normalize w = N.normalize w :=
  rfl

@[simp] theorem toFrontierWordCompleteNormalizer_sound
    (N : ComputationalFrontierNormalizer setup)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    N.toFrontierWordCompleteNormalizer.sound h = N.sound h :=
  rfl

@[simp] theorem toFrontierWordCompleteNormalizer_complete
    (N : ComputationalFrontierNormalizer setup)
    {w₁ w₂ : FrontierWord setup}
    (h : N.normalize w₁ = N.normalize w₂) :
    N.toFrontierWordCompleteNormalizer.complete h = N.complete h :=
  rfl

end ComputationalFrontierNormalizer

/-- Upgrade path: every computational frontier normalizer induces the
extensional complete-normalizer contract used by the closed engine. -/
def computational_to_quotient_complete
    (N : ComputationalFrontierNormalizer setup) :
    FrontierWordCompleteNormalizer setup :=
  N.toFrontierWordCompleteNormalizer

/-- First concrete bridge from the existing frontier-word normalizer interface
to the record-facing CanNF scaffold. -/
def FrontierWordCanNF
    (N : FrontierWordCompleteNormalizer setup) :
    CanNF setup where
  assignment := CanonicalWordAssignment.ofResidue setup
  normalizer := N

def FrontierWordCanNF.ofNormalizer
    (N : FrontierWordCompleteNormalizer setup) :
    CanNF setup :=
  FrontierWordCanNF N

@[simp] theorem FrontierWordCanNF_assignment
    (N : FrontierWordCompleteNormalizer setup) :
    (FrontierWordCanNF (setup := setup) N).assignment =
      CanonicalWordAssignment.ofResidue setup :=
  rfl

@[simp] theorem FrontierWordCanNF_normalizer
    (N : FrontierWordCompleteNormalizer setup) :
    (FrontierWordCanNF (setup := setup) N).normalizer = N :=
  rfl

@[simp] theorem FrontierWordCanNF_normalize
    (N : FrontierWordCompleteNormalizer setup)
    (R : CompletedReconstructionRecord setup) :
    (FrontierWordCanNF N).normalize R = N.normalize (FrontierWord.ofResidue R) :=
  rfl

/-- Soundness of the frontier-word CanNF bridge on completed records. -/
theorem frontierWordCanNF_sound
    (N : FrontierWordCompleteNormalizer setup)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂) :
    (FrontierWordCanNF N).normalize R₁ = (FrontierWordCanNF N).normalize R₂ :=
  (FrontierWordCanNF N).CanNF_sound h

/-- Completeness of the frontier-word CanNF bridge: equal normal forms detect
frontier-word equivalence. -/
theorem frontierWordCanNF_complete
    (N : FrontierWordCompleteNormalizer setup)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : (FrontierWordCanNF N).normalize R₁ = (FrontierWordCanNF N).normalize R₂) :
    FrontierWord.Equiv
      ((FrontierWordCanNF N).assignment.assign R₁).frontier
      ((FrontierWordCanNF N).assignment.assign R₂).frontier :=
  (FrontierWordCanNF N).CanNF_complete h

/-- Equality detection for the frontier-word CanNF bridge. -/
theorem frontierWordCanNF_detects_equivalence
    (N : FrontierWordCompleteNormalizer setup)
    (R₁ R₂ : CompletedReconstructionRecord setup) :
    (FrontierWordCanNF N).normalize R₁ = (FrontierWordCanNF N).normalize R₂ ↔
      FrontierWord.Equiv
        ((FrontierWordCanNF N).assignment.assign R₁).frontier
        ((FrontierWordCanNF N).assignment.assign R₂).frontier :=
  (FrontierWordCanNF N).CanNF_detects_equality R₁ R₂

theorem frontierWordCanNF_normalize_eq_iff_equiv
    (N : FrontierWordCompleteNormalizer setup)
    (R₁ R₂ : CompletedReconstructionRecord setup) :
    (FrontierWordCanNF N).normalize R₁ = (FrontierWordCanNF N).normalize R₂ ↔
      FrontierWord.Equiv (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂) := by
  simpa [FrontierWordCanNF, CanonicalWordAssignment.ofResidue, CanonicalWord.ofResidue]
    using frontierWordCanNF_detects_equivalence (setup := setup) N R₁ R₂

theorem frontierWordCanNF_of_normalize_eq
    (N : FrontierWordCompleteNormalizer setup)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : (FrontierWordCanNF N).normalize R₁ = (FrontierWordCanNF N).normalize R₂) :
    FrontierWord.Equiv (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂) := by
  simpa [FrontierWordCanNF, CanonicalWordAssignment.ofResidue, CanonicalWord.ofResidue]
    using (FrontierWordCompleteNormalizer.equiv_of_normalize_eq N h)

theorem frontierWordCanNF_normalize_eq_of_equiv
    (N : FrontierWordCompleteNormalizer setup)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : FrontierWord.Equiv (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂)) :
    (FrontierWordCanNF N).normalize R₁ = (FrontierWordCanNF N).normalize R₂ := by
  simpa [FrontierWordCanNF, CanonicalWordAssignment.ofResidue, CanonicalWord.ofResidue]
    using (N.sound h)

/-- Any residue NF-code contract packages directly into the record-facing CanNF
scaffold through its existing complete frontier-word normalizer bridge. -/
def ResidueNFCodeContract.toFrontierWordCanNF
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueNFCodeContract O) :
    CanNF setup :=
  FrontierWordCanNF (ResidueNFCodeContract.toFrontierWordCompleteNormalizer C)

/-- The stricter residue word-normalization contract also packages directly into
the record-facing CanNF scaffold. -/
def ResidueCanNFContract.toFrontierWordCanNF
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueCanNFContract O) :
    CanNF setup :=
  FrontierWordCanNF C.toCompleteNormalizer

/-- First honest concrete record-facing CanNF package.

This packages the quotient-coded residue NF contract built from
`FrontierWord.Equiv` classes. It is concrete and faithful for equality
detection, but it does not claim to construct a stricter residue-normal
witness. -/
def frontierWordEquivFrontierWordCanNF
    (O : ResidueCanonicalOrder.{u, v} setup) :
    CanNF setup :=
  (ResidueNFCodeContract.frontierWordEquivResidueNFCodeContract
    (setup := setup) O).toFrontierWordCanNF

def frontierWordEquivFrontierWordCanNF.ofResidue
    (O : ResidueCanonicalOrder.{u, v} setup) :
    CanNF setup :=
  frontierWordEquivFrontierWordCanNF (setup := setup) O

@[simp] theorem frontierWordEquivFrontierWordCanNF_assignment
    {O : ResidueCanonicalOrder.{u, v} setup} :
    (frontierWordEquivFrontierWordCanNF (setup := setup) O).assignment =
      CanonicalWordAssignment.ofResidue setup :=
  rfl

@[simp] theorem frontierWordEquivFrontierWordCanNF_normalizer
    {O : ResidueCanonicalOrder.{u, v} setup} :
    (frontierWordEquivFrontierWordCanNF (setup := setup) O).normalizer =
      (ResidueNFCodeContract.frontierWordEquivResidueNFCodeContract
        (setup := setup) O).toFrontierWordCompleteNormalizer :=
  rfl

@[simp] theorem ResidueNFCodeContract.toFrontierWordCanNF_assignment
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueNFCodeContract O) :
    C.toFrontierWordCanNF.assignment = CanonicalWordAssignment.ofResidue setup :=
  rfl

@[simp] theorem ResidueNFCodeContract.toFrontierWordCanNF_normalizer
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueNFCodeContract O) :
    C.toFrontierWordCanNF.normalizer = C.toFrontierWordCompleteNormalizer :=
  rfl

@[simp] theorem ResidueCanNFContract.toFrontierWordCanNF_assignment
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueCanNFContract O) :
    C.toFrontierWordCanNF.assignment = CanonicalWordAssignment.ofResidue setup :=
  rfl

@[simp] theorem ResidueCanNFContract.toFrontierWordCanNF_normalizer
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueCanNFContract O) :
    C.toFrontierWordCanNF.normalizer = C.toCompleteNormalizer :=
  rfl

@[simp] theorem ResidueNFCodeContract.toFrontierWordCanNF_normalize
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueNFCodeContract O)
    (R : CompletedReconstructionRecord setup) :
    C.toFrontierWordCanNF.normalize R =
      C.code (CanonicalWord.ofResidue R).frontier :=
  rfl

@[simp] theorem ResidueCanNFContract.toFrontierWordCanNF_normalize
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueCanNFContract O)
    (R : CompletedReconstructionRecord setup) :
    C.toFrontierWordCanNF.normalize R =
      (C.normalize (CanonicalWord.ofResidue R).frontier).word :=
  rfl

@[simp] theorem frontierWordEquivFrontierWordCanNF_normalize
    {O : ResidueCanonicalOrder.{u, v} setup}
    (R : CompletedReconstructionRecord setup) :
    (frontierWordEquivFrontierWordCanNF (setup := setup) O).normalize R =
      FrontierWord.EquivClass.mk (CanonicalWord.ofResidue R).frontier :=
  rfl

/-- Equality detection for the first honest concrete quotient-based CanNF
package. This is `CanNF_detects_equality` specialized to the residue/frontier
assignment already carried by `CanonicalWordAssignment.ofResidue`. -/
theorem frontierWordEquivFrontierWordCanNF_detects_equality
    {O : ResidueCanonicalOrder.{u, v} setup}
    (R₁ R₂ : CompletedReconstructionRecord setup) :
    (frontierWordEquivFrontierWordCanNF (setup := setup) O).normalize R₁ =
        (frontierWordEquivFrontierWordCanNF (setup := setup) O).normalize R₂ ↔
      FrontierWord.Equiv (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂) := by
  simpa [frontierWordEquivFrontierWordCanNF, FrontierWordCanNF,
    CanonicalWordAssignment.ofResidue, CanonicalWord.ofResidue]
    using (CanNF.CanNF_detects_equality
      (frontierWordEquivFrontierWordCanNF (setup := setup) O) R₁ R₂)

theorem frontierWordEquivFrontierWordCanNF_of_normalize_eq
    {O : ResidueCanonicalOrder.{u, v} setup}
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : (frontierWordEquivFrontierWordCanNF (setup := setup) O).normalize R₁ =
      (frontierWordEquivFrontierWordCanNF (setup := setup) O).normalize R₂) :
    FrontierWord.Equiv (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂) :=
  (frontierWordEquivFrontierWordCanNF_detects_equality
    (setup := setup) (O := O) R₁ R₂).1 h

theorem frontierWordEquivFrontierWordCanNF_normalize_eq_of_equiv
    {O : ResidueCanonicalOrder.{u, v} setup}
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : FrontierWord.Equiv (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂)) :
    (frontierWordEquivFrontierWordCanNF (setup := setup) O).normalize R₁ =
      (frontierWordEquivFrontierWordCanNF (setup := setup) O).normalize R₂ :=
  (frontierWordEquivFrontierWordCanNF_detects_equality
    (setup := setup) (O := O) R₁ R₂).2 h

/-! ## Concrete closed CanNF objects (no external obligations)

All objects below are **fully closed** — they require no external contract obligation.
Based on the honest `Quotient` construction (NF = equivalence class, normalize = mk).

Soundness: `Quotient.sound`.  Completeness: `Quotient.exact`.
No `sorry`, `admit`, `True`, or external assumption. -/

/-! ### Proof-relevant normalization trace (in `Type`) -/

/-- **Proof-relevant normalization trace** (`Type`-level, not `Prop`).

The zero-or-one step record produced by the quotient normalizer:
- `already_normal`: source word already equals its `Quotient.out` representative.
- `one_step`: source word takes exactly one step to the canonical representative. -/
inductive QuotientNormalizationTrace (setup : RewriteCalculusSetup.{u}) :
    FrontierWord setup → FrontierWord setup → Type u where
  | already_normal (w : FrontierWord setup)
      (h : w = Quotient.out (FrontierWord.EquivClass.mk w)) :
      QuotientNormalizationTrace setup w w
  | one_step (w : FrontierWord setup)
      (h : w ≠ Quotient.out (FrontierWord.EquivClass.mk w)) :
      QuotientNormalizationTrace setup w (Quotient.out (FrontierWord.EquivClass.mk w))

/-- Interpretation theorem: every trace witnesses `FrontierWord.Equiv`
    between its source and target (in `Type`, not `Prop`). -/
theorem QuotientNormalizationTrace.toEquiv
    {setup : RewriteCalculusSetup.{u}} {w₁ w₂ : FrontierWord setup}
    (t : QuotientNormalizationTrace setup w₁ w₂) :
    FrontierWord.Equiv w₁ w₂ := by
  cases t with
  | already_normal => exact FrontierWord.Equiv.refl w₁
  | one_step => exact Quotient.exact (Quotient.out_eq (FrontierWord.EquivClass.mk w₁)).symm

/-! ### Semantic quotient `FrontierWordCompleteNormalizer` -/

/-- **Semantic quotient `FrontierWordCompleteNormalizer`**.

Sends each `FrontierWord` to its `FrontierWord.Equiv` equivalence class.
*   `NF := FrontierWord.EquivClass setup`
*   `normalize w := FrontierWord.EquivClass.mk w`
*   `sound h := Quotient.sound h`
*   `complete h := Quotient.exact h`

This is extensional/semantic closure, not an executable CanNF algorithm. -/
def semanticQuotientFrontierWordCompleteNormalizer :
    FrontierWordCompleteNormalizer.{u, u} setup :=
  FrontierWordCompleteNormalizer.ofFields
    (FrontierWord.EquivClass setup)
    FrontierWord.EquivClass.mk
    (fun h => Quotient.sound h)
    (fun h => Quotient.exact h)

/-- Backward-compatible alias for existing call sites.

Prefer `semanticQuotientFrontierWordCompleteNormalizer` in manuscript-facing
code to avoid algorithmic overclaim. -/
abbrev quotientFrontierWordCompleteNormalizer :
    FrontierWordCompleteNormalizer.{u, u} setup :=
  semanticQuotientFrontierWordCompleteNormalizer

@[simp] theorem quotientFrontierWordCompleteNormalizer_normalize
    (w : FrontierWord setup) :
    quotientFrontierWordCompleteNormalizer.normalize w =
      FrontierWord.EquivClass.mk w :=
  rfl

@[simp] theorem semanticQuotientFrontierWordCompleteNormalizer_normalize
    (w : FrontierWord setup) :
    semanticQuotientFrontierWordCompleteNormalizer.normalize w =
      FrontierWord.EquivClass.mk w :=
  rfl

theorem quotientFrontierWordCompleteNormalizer_sound
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    quotientFrontierWordCompleteNormalizer.normalize w₁ =
      quotientFrontierWordCompleteNormalizer.normalize w₂ :=
  Quotient.sound h

theorem quotientFrontierWordCompleteNormalizer_complete
    {w₁ w₂ : FrontierWord setup}
    (h : quotientFrontierWordCompleteNormalizer.normalize w₁ =
      quotientFrontierWordCompleteNormalizer.normalize w₂) :
    FrontierWord.Equiv w₁ w₂ :=
  Quotient.exact h

theorem semanticQuotientFrontierWordCompleteNormalizer_sound
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    semanticQuotientFrontierWordCompleteNormalizer.normalize w₁ =
      semanticQuotientFrontierWordCompleteNormalizer.normalize w₂ :=
  Quotient.sound h

theorem semanticQuotientCanNF_is_complete
    {w₁ w₂ : FrontierWord setup}
    (h : semanticQuotientFrontierWordCompleteNormalizer.normalize w₁ =
      semanticQuotientFrontierWordCompleteNormalizer.normalize w₂) :
    FrontierWord.Equiv w₁ w₂ :=
  Quotient.exact h

/-! ### Helpers for the quotient canonical representative -/

/-- `IsNormal` predicate: a word is normal iff it is its own `Quotient.out`. -/
def QuotientIsNormal (setup : RewriteCalculusSetup.{u}) (w : FrontierWord setup) : Prop :=
  w = Quotient.out (FrontierWord.EquivClass.mk w)

/-- `Quotient.out ⟦w⟧` is always normal. -/
theorem quotientOut_isNormal (setup : RewriteCalculusSetup.{u})
    (w : FrontierWord setup) :
    QuotientIsNormal setup (Quotient.out (FrontierWord.EquivClass.mk w)) := by
  show Quotient.out (FrontierWord.EquivClass.mk w) =
    Quotient.out (FrontierWord.EquivClass.mk (Quotient.out (FrontierWord.EquivClass.mk w)))
  congr 1
  exact (Quotient.out_eq (FrontierWord.EquivClass.mk w)).symm

/-- Every word is `FrontierWord.Equiv` to its `Quotient.out` representative. -/
theorem equiv_quotientOut (setup : RewriteCalculusSetup.{u})
    (w : FrontierWord setup) :
    FrontierWord.Equiv w (Quotient.out (FrontierWord.EquivClass.mk w)) := by
  show (FrontierWord.equivSetoid setup).r w (Quotient.out (FrontierWord.EquivClass.mk w))
  exact Quotient.exact (Quotient.out_eq (FrontierWord.EquivClass.mk w)).symm

/-! ### Concrete `FrontierReductionSystem` -/

/-- The closed `CanNF` package using the quotient normalizer. -/
noncomputable def quotientCanNF : CanNF setup :=
  FrontierWordCanNF semanticQuotientFrontierWordCompleteNormalizer

@[simp] theorem quotientCanNF_normalize
    (R : CompletedReconstructionRecord setup) :
    quotientCanNF.normalize R =
      FrontierWord.EquivClass.mk (FrontierWord.ofResidue R) :=
  rfl

theorem quotientCanNF_detects_equality
    (R₁ R₂ : CompletedReconstructionRecord setup) :
    quotientCanNF.normalize R₁ = quotientCanNF.normalize R₂ ↔
      FrontierWord.Equiv (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Extensional completeness statement for the semantic quotient CanNF package. -/
theorem quotientCanNF_extensional_complete
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : quotientCanNF.normalize R₁ = quotientCanNF.normalize R₂) :
    FrontierWord.Equiv (FrontierWord.ofResidue R₁) (FrontierWord.ofResidue R₂) :=
  (quotientCanNF_detects_equality (setup := setup) R₁ R₂).1 h

/-- The current closed `quotientCanNF` is definitionally the semantic quotient
construction. This theorem is a naming guardrail: executable computational CanNF
must be introduced via `ComputationalFrontierNormalizer`. -/
theorem quotientCanNF_not_computational (setup : RewriteCalculusSetup.{u}) :
    @quotientCanNF setup =
      FrontierWordCanNF (semanticQuotientFrontierWordCompleteNormalizer (setup := setup)) :=
  rfl

end RewriteCalculusSetup
end RealObjects
end LayerB
end TraceCalc
