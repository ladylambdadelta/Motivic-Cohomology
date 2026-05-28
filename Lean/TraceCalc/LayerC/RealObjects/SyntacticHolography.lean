import TraceCalc.LayerC.RealObjects.SyntacticBoundary
import TraceCalc.LayerC.RealObjects.HolographicReconstruction

/-!
# Real-objects formalization: syntactic-boundary holography packaging (Phase 9j–9n)

**Phase 9 items 9j–9n (2026-04-24).** Package the constructive Path B
boundary-presentation theorem all the way up to the residue-level holographic
reconstruction theorem.

This file does **not** introduce new boundary structure. It only composes
existing layers:

* `SyntacticBoundaryPresentation setup`
  ⇒ `FrontierQuotientRealization setup`
  from [SyntacticBoundary.lean](Lean/TraceCalc/LayerB/RealObjects/SyntacticBoundary.lean),
* `FrontierQuotientRealization setup`
  ⇒ holographic reconstruction iff
  from [QuotientRealization.lean](Lean/TraceCalc/LayerB/RealObjects/QuotientRealization.lean).

So the new theorem target is explicit and constructive:

  syntactic boundary presentation
  ⇒ faithful frontier quotient realization
  ⇒ residue-level holographic reconstruction.

## Honest scope

* `RewriteCalculusSetup` is not mutated.
* No arbitrary opaque `setup.BoundaryObject` is claimed canonicalizable.
* No trace-level CanNF is instantiated.
* `FrontierWord` is not enriched.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-! ## Item 9j — Quotient realization from a syntactic presentation -/

/-- **Item 9j**: a syntactic boundary presentation gives a faithful frontier
quotient realization.

This is the explicit packaging alias for the constructive Path B theorem from
`SyntacticBoundary.lean`. -/
def syntactic_boundary_presentation_gives_holographic_quotient_realization
    (P : SyntacticBoundaryPresentation setup) :
    FrontierQuotientRealization.{u, u} setup :=
  syntactic_boundary_presentation_gives_frontier_quotient_realization P

/-! ## Item 9k — Holographic reconstruction via a syntactic presentation -/

/-- **Item 9k**: if the boundary admits a syntactic presentation, then
residue-level holographic reconstruction is detected by the induced quotient
code.

This is the main manuscript-facing theorem for the Path B consolidation layer. -/
theorem syntactic_boundary_holographic_reconstruction
    (P : SyntacticBoundaryPresentation setup)
    (D : HolographicReconstructionData setup)
    {R₁ R₂ : CompletedReconstructionRecord setup} :
    (syntactic_boundary_presentation_gives_holographic_quotient_realization P).realize
        (D.toFrontierWord R₁)
      =
      (syntactic_boundary_presentation_gives_holographic_quotient_realization P).realize
        (D.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (D.toFrontierWord R₁) (D.toFrontierWord R₂) :=
  holographic_reconstruction_via_quotient_realization
    (syntactic_boundary_presentation_gives_holographic_quotient_realization P) D

/-! ## Item 9l — Sound-only version -/

/-- **Item 9l**: sound-only holographic consequence of a syntactic boundary
presentation.

This uses only the invariant half of the quotient realization: admin-equivalent
records have equal realized images. -/
theorem syntactic_boundary_holographic_sound
    (P : SyntacticBoundaryPresentation setup)
    (D : HolographicReconstructionData setup)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂) :
    ((syntactic_boundary_presentation_gives_holographic_quotient_realization P).realize)
        (D.toFrontierWord R₁)
      =
      ((syntactic_boundary_presentation_gives_holographic_quotient_realization P).realize)
        (D.toFrontierWord R₂) := by
  let Q := syntactic_boundary_presentation_gives_holographic_quotient_realization P
  exact holographic_invariant_sound_on_records Q.toFrontierQuotientInvariant D h

/-! ## Item 9m — Non-overclaim alias -/

/-- **Item 9m**: generic boundary holography is available only under the
explicit hypothesis of a syntactic boundary presentation.

This records the non-overclaim in the theorem signature itself: the first
argument is the required presentation hypothesis. -/
theorem generic_opaque_boundary_requires_presentation
    (P : SyntacticBoundaryPresentation setup)
    (D : HolographicReconstructionData setup)
    {R₁ R₂ : CompletedReconstructionRecord setup} :
    (syntactic_boundary_presentation_gives_holographic_quotient_realization P).realize
        (D.toFrontierWord R₁)
      =
      (syntactic_boundary_presentation_gives_holographic_quotient_realization P).realize
        (D.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (D.toFrontierWord R₁) (D.toFrontierWord R₂) :=
  syntactic_boundary_holographic_reconstruction P D

/-! ## Item 9n — Manuscript-facing aliases -/

/-- Manuscript alias: a syntactic boundary presentation implies a faithful
frontier quotient realization. -/
def theorem_syntactic_boundary_presentation_implies_frontier_quotient_realization
    (P : SyntacticBoundaryPresentation setup) :
    FrontierQuotientRealization.{u, u} setup :=
  syntactic_boundary_presentation_gives_holographic_quotient_realization P

/-- Manuscript alias: a syntactic boundary presentation implies residue-level
holographic reconstruction. -/
theorem theorem_syntactic_boundary_holographic_reconstruction
    (P : SyntacticBoundaryPresentation setup)
    (D : HolographicReconstructionData setup)
    {R₁ R₂ : CompletedReconstructionRecord setup} :
    (syntactic_boundary_presentation_gives_holographic_quotient_realization P).realize
        (D.toFrontierWord R₁)
      =
      (syntactic_boundary_presentation_gives_holographic_quotient_realization P).realize
        (D.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (D.toFrontierWord R₁) (D.toFrontierWord R₂) :=
  syntactic_boundary_holographic_reconstruction P D

/-- Manuscript alias: generic boundary holography requires an explicit
syntactic boundary presentation. -/
theorem theorem_generic_boundary_holography_requires_boundary_presentation
    (P : SyntacticBoundaryPresentation setup)
    (D : HolographicReconstructionData setup)
    {R₁ R₂ : CompletedReconstructionRecord setup} :
    (syntactic_boundary_presentation_gives_holographic_quotient_realization P).realize
        (D.toFrontierWord R₁)
      =
      (syntactic_boundary_presentation_gives_holographic_quotient_realization P).realize
        (D.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (D.toFrontierWord R₁) (D.toFrontierWord R₂) :=
  generic_opaque_boundary_requires_presentation P D

/-
TEX ref: our_paper_draft.tex, label rem:infty-holography (L1084)
Paper role: full ∞-categorical holography; rem environment (not a numbered theorem)
Lean status: OVERCLAIM → M0 quarantined; content reclassified as CONDITIONAL SUPPORT
-/
/-- **Quarantine marker (M0)**: conditional-only support for `rem:infty-holography`.

The holographic reconstruction theorems in this file
(`syntactic_boundary_holographic_reconstruction`, etc.) are CONDITIONAL on
an explicit `SyntacticBoundaryPresentation` hypothesis. They do NOT establish
the unconditional completed/∞-level holography described in `rem:infty-holography`.

**What the theorems here prove:**
- Given a `SyntacticBoundaryPresentation P`, the quotient realization via P
  detects frontier-word equivalence (`syntactic_boundary_holographic_reconstruction`).
- The sound direction (admin-equivalent records → equal realizations) holds
  independently (item 9l / `syntactic_boundary_holographic_sound`).

**What `rem:infty-holography` claims beyond this:**
- Unconditional completed holography at the π₀-level (requires
  `prop:reconstruction-existence`, MISSING).
- The ∞-categorical version requires `rem:infty-categorical-completion` (MISSING).
- Requires `lem:deterministic-assembly` (MISSING) and
  `cor:reconstruction-retraction` (MISSING).

Downstream spine assemblers must treat these declarations as CONDITIONAL SUPPORT,
not unconditional completed-holography closure. -/
def infty_holography_conditional_support_note : Prop :=
  ∀ {setup : RewriteCalculusSetup.{0}}
    (P : SyntacticBoundaryPresentation setup)
    (D : HolographicReconstructionData setup)
    {R₁ R₂ : CompletedReconstructionRecord setup},
    (syntactic_boundary_presentation_gives_holographic_quotient_realization P).realize
        (D.toFrontierWord R₁)
      =
      (syntactic_boundary_presentation_gives_holographic_quotient_realization P).realize
          (D.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (D.toFrontierWord R₁) (D.toFrontierWord R₂)

theorem infty_holography_conditional_support_note_holds :
    infty_holography_conditional_support_note :=
  fun P D => syntactic_boundary_holographic_reconstruction P D

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc