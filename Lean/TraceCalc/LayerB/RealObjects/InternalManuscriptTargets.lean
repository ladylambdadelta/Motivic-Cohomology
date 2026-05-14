import TraceCalc.LayerB.RealObjects.Composition
import TraceCalc.LayerB.RealObjects.SyntacticBoundary
import TraceCalc.LayerB.RealObjects.QuotientRealization
import TraceCalc.LayerB.RealObjects.CanonicalNormalForm
import TraceCalc.LayerB.RealObjects.CanonicalReconstructionEngine
import TraceCalc.LayerB.RealObjects.ConcreteBoundaryPresentation
import TraceCalc.LayerB.RealObjects.ConcreteBoundaryContent
import TraceCalc.LayerA.CategoryInfra.FreeDG
import TraceCalc.LayerA.CategoryInfra.Pretriangulated
import TraceCalc.LayerA.CategoryInfra.H0Category
import TraceCalc.LayerA.CategoryInfra.Karoubi
import TraceCalc.LayerA.CategoryInfra.MonoidalTransport
import TraceCalc.LayerA.CategoryInfra.ExactnessTransport

/-!
# Real-objects formalization: internal manuscript theorem targets

This file introduces theorem-target records for the internal manuscript spine.
When a result is already available in the current real-objects development, the
record is inhabited by a direct constructor. When the corresponding manuscript
claim lives outside the current scoped formalization, the record carries only
the Prop-shaped theorem surface so later work fills proofs rather than inventing
new target declarations.
-/

universe u v

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-- The composition target for certified traces: the concrete composition
operations and the congruence theorem that makes them descend to trace
classes. -/
structure CertifiedTraceCompositionTarget (setup : RewriteCalculusSetup.{u}) where
  traceEquivalenceCongruence :
    ∀ {X Y Z : setup.State}
      {σ σ' : setup.ReplayRepresentative X Y}
      {τ τ' : setup.ReplayRepresentative Y Z},
      TraceEquiv setup σ σ' →
        TraceEquiv setup τ τ' →
        TraceEquiv setup (σ.append τ) (σ'.append τ')
  traceClassCompose :
    ∀ {X Y Z : setup.State},
      setup.TraceClass X Y → setup.TraceClass Y Z → setup.TraceClass X Z
  traceClassId : ∀ X : setup.State, setup.TraceClass X X
  certifiedTraceCompose :
    ∀ {X Y Z : setup.State},
      setup.CertifiedTrace X Y → setup.CertifiedTrace Y Z →
        setup.CertifiedTrace X Z
  certifiedTraceId : ∀ X : setup.State, setup.CertifiedTrace X X

namespace CertifiedTraceCompositionTarget

/-- The current real-objects composition development already fills the concrete
composition target. -/
def ofCurrentDevelopment (setup : RewriteCalculusSetup.{u}) :
    CertifiedTraceCompositionTarget setup where
  traceEquivalenceCongruence := by
    intro X Y Z σ σ' τ τ' hσ hτ
    exact trace_equivalence_congruence hσ hτ
  traceClassCompose := fun T T' => T.compose T'
  traceClassId := TraceClass.id
  certifiedTraceCompose := fun T T' => T.compose T'
  certifiedTraceId := idCertifiedTrace

end CertifiedTraceCompositionTarget

/-- Category-law target for the certified-trace layer. The current scoped
development proves these laws at the trace-class level and, for certified
traces, on the `cls` projection. -/
structure TraceCategoryLawsTarget (setup : RewriteCalculusSetup.{u}) where
  traceClassLeftIdentity :
    ∀ {X Y : setup.State} (T : setup.TraceClass X Y),
      (TraceClass.id X).compose T = T
  traceClassRightIdentity :
    ∀ {X Y : setup.State} (T : setup.TraceClass X Y),
      T.compose (TraceClass.id Y) = T
  traceClassAssociative :
    ∀ {X Y Z W : setup.State}
      (T : setup.TraceClass X Y) (T' : setup.TraceClass Y Z)
      (T'' : setup.TraceClass Z W),
      (T.compose T').compose T'' = T.compose (T'.compose T'')
  certifiedTraceLeftIdentityOnCls :
    ∀ {X Y : setup.State} (T : setup.CertifiedTrace X Y),
      ((idCertifiedTrace X).compose T).cls = T.cls
  certifiedTraceRightIdentityOnCls :
    ∀ {X Y : setup.State} (T : setup.CertifiedTrace X Y),
      (T.compose (idCertifiedTrace Y)).cls = T.cls
  certifiedTraceAssociativeOnCls :
    ∀ {X Y Z W : setup.State}
      (T : setup.CertifiedTrace X Y) (T' : setup.CertifiedTrace Y Z)
      (T'' : setup.CertifiedTrace Z W),
      ((T.compose T').compose T'').cls = (T.compose (T'.compose T'')).cls

namespace TraceCategoryLawsTarget

/-- The current real-objects composition file already proves the current
category-law target. -/
def ofCurrentDevelopment (setup : RewriteCalculusSetup.{u}) :
    TraceCategoryLawsTarget setup where
  traceClassLeftIdentity := TraceClass.id_compose
  traceClassRightIdentity := TraceClass.compose_id
  traceClassAssociative := TraceClass.compose_assoc
  certifiedTraceLeftIdentityOnCls := CertifiedTrace.id_compose_cls
  certifiedTraceRightIdentityOnCls := CertifiedTrace.compose_id_cls
  certifiedTraceAssociativeOnCls := CertifiedTrace.compose_assoc_cls

end TraceCategoryLawsTarget

/-- The minimal-completion theorem surface for the manuscript completion lane.
These fields intentionally remain Prop-valued in the current scope. -/
structure MinimumCompletionTarget where
  completedTraceCategoryExists : Prop
  completionExtensionProperty : Prop
  stableCompletionModel : Prop

/-- Immediate theorem target for the manuscript's completed trace category
existence claim. -/
structure CompletedTraceCategoryExistenceTarget where
  completedTraceCategoryExists : Prop

namespace CompletedTraceCategoryExistenceTarget

def ofProp (completedTraceCategoryExists : Prop) :
    CompletedTraceCategoryExistenceTarget where
  completedTraceCategoryExists := completedTraceCategoryExists

end CompletedTraceCategoryExistenceTarget

/-- Immediate theorem target for the manuscript's extension-property claim for
the completed trace category. -/
structure CompletionExtensionPropertyTarget where
  completionExtensionProperty : Prop

namespace CompletionExtensionPropertyTarget

def ofProp (completionExtensionProperty : Prop) :
    CompletionExtensionPropertyTarget where
  completionExtensionProperty := completionExtensionProperty

end CompletionExtensionPropertyTarget

/-- Immediate theorem target for the manuscript's explicit stable-completion
model. -/
structure StableCompletionModelTarget where
  stableCompletionModel : Prop

namespace StableCompletionModelTarget

def ofProp (stableCompletionModel : Prop) :
    StableCompletionModelTarget where
  stableCompletionModel := stableCompletionModel

end StableCompletionModelTarget

/-- Bundle the three manuscript-facing immediate consequences of a stable
completion construction. This separates "the construction exists" from the
first theorem surfaces it should discharge. -/
structure MinimumCompletionConsequencesTarget where
  completedTraceCategory : CompletedTraceCategoryExistenceTarget
  extensionProperty : CompletionExtensionPropertyTarget
  stableModel : StableCompletionModelTarget

namespace MinimumCompletionConsequencesTarget

def toMinimumCompletionTarget
    (T : MinimumCompletionConsequencesTarget) :
    MinimumCompletionTarget :=
  MinimumCompletionTarget.mk
    T.completedTraceCategory.completedTraceCategoryExists
    T.extensionProperty.completionExtensionProperty
    T.stableModel.stableCompletionModel

def ofTargets
    (completedTraceCategory : CompletedTraceCategoryExistenceTarget)
    (extensionProperty : CompletionExtensionPropertyTarget)
    (stableModel : StableCompletionModelTarget) :
    MinimumCompletionConsequencesTarget where
  completedTraceCategory := completedTraceCategory
  extensionProperty := extensionProperty
  stableModel := stableModel

end MinimumCompletionConsequencesTarget

/-- Existence target for the manuscript's free dg envelope step.

The current real-objects scope does not expose an actual dg-category
construction, so the first honest lower obligation is just that the free dg
envelope exists. -/
structure FreeDGEnvelopeExistenceTarget where
  dgEnvelopeExists : Prop

namespace FreeDGEnvelopeExistenceTarget

def ofProp (dgEnvelopeExists : Prop) : FreeDGEnvelopeExistenceTarget where
  dgEnvelopeExists := dgEnvelopeExists

def ofInfrastructure {presentation : Type u}
    (E : CategoryInfra.FreeDGEnvelope.{u, v} presentation) :
    FreeDGEnvelopeExistenceTarget :=
  ofProp E.existenceTarget

theorem ofInfrastructure_holds {presentation : Type u}
    (E : CategoryInfra.FreeDGEnvelope.{u, v} presentation) :
    (ofInfrastructure E).dgEnvelopeExists :=
  E.existenceTarget_holds

end FreeDGEnvelopeExistenceTarget

/-- Universal-property target for the manuscript's free dg envelope step.

This isolates the adjoint/free characterization from mere existence so later
dg work can discharge the two claims independently. -/
structure FreeDGEnvelopeUniversalPropertyTarget where
  dgEnvelopeUniversalProperty : Prop

namespace FreeDGEnvelopeUniversalPropertyTarget

def ofProp
    (dgEnvelopeUniversalProperty : Prop) :
    FreeDGEnvelopeUniversalPropertyTarget where
  dgEnvelopeUniversalProperty := dgEnvelopeUniversalProperty

def ofInfrastructure {presentation : Type u}
    (E : CategoryInfra.FreeDGEnvelope.{u, v} presentation) :
    FreeDGEnvelopeUniversalPropertyTarget :=
  ofProp E.universalPropertyTarget

theorem ofInfrastructure_holds {presentation : Type u}
    (E : CategoryInfra.FreeDGEnvelope.{u, v} presentation) :
    (ofInfrastructure E).dgEnvelopeUniversalProperty :=
  E.universalPropertyTarget_holds

end FreeDGEnvelopeUniversalPropertyTarget

/-- Bundle the smallest lower-level theorem surfaces currently visible for the
free dg envelope step. In manuscript terms, the dg step reduces to existence of
the free dg envelope together with its universal property. -/
structure FreeDGEnvelopeFieldTargets where
  existence : FreeDGEnvelopeExistenceTarget
  universalProperty : FreeDGEnvelopeUniversalPropertyTarget

namespace FreeDGEnvelopeFieldTargets

def ofTargets
    (existence : FreeDGEnvelopeExistenceTarget)
    (universalProperty : FreeDGEnvelopeUniversalPropertyTarget) :
    FreeDGEnvelopeFieldTargets where
  existence := existence
  universalProperty := universalProperty

def dgEnvelopeUniversality
    (T : FreeDGEnvelopeFieldTargets) : Prop :=
  T.existence.dgEnvelopeExists ∧
    T.universalProperty.dgEnvelopeUniversalProperty

def ofInfrastructure {presentation : Type u}
    (E : CategoryInfra.FreeDGEnvelope.{u, v} presentation) :
    FreeDGEnvelopeFieldTargets :=
  ofTargets
    (FreeDGEnvelopeExistenceTarget.ofInfrastructure E)
    (FreeDGEnvelopeUniversalPropertyTarget.ofInfrastructure E)

end FreeDGEnvelopeFieldTargets

/-- The current development does not yet contain a concrete dg-category
infrastructure for the completion lane, so the dg step remains a theorem-target
wrapper. -/
structure FreeDGEnvelopeTarget where
  dgEnvelopeUniversality : Prop

namespace FreeDGEnvelopeTarget

def ofProp (dgEnvelopeUniversality : Prop) : FreeDGEnvelopeTarget where
  dgEnvelopeUniversality := dgEnvelopeUniversality

def ofExistenceAndUniversalProperty
    (existence : FreeDGEnvelopeExistenceTarget)
    (universalProperty : FreeDGEnvelopeUniversalPropertyTarget) :
    FreeDGEnvelopeTarget :=
  FreeDGEnvelopeTarget.ofProp
    (existence.dgEnvelopeExists ∧
      universalProperty.dgEnvelopeUniversalProperty)

def ofFieldTargets
    (T : FreeDGEnvelopeFieldTargets) : FreeDGEnvelopeTarget :=
  FreeDGEnvelopeTarget.ofProp T.dgEnvelopeUniversality

def ofInfrastructure {presentation : Type u}
    (E : CategoryInfra.FreeDGEnvelope.{u, v} presentation) :
    FreeDGEnvelopeTarget :=
  ofFieldTargets (FreeDGEnvelopeFieldTargets.ofInfrastructure E)

end FreeDGEnvelopeTarget

/-- Existence target for the manuscript's pretriangulated hull step.

The current Layer B scope does not provide a concrete pretriangulated-hull
construction, so the first lower obligation is just that the hull exists. -/
structure PretriangulatedHullExistenceTarget where
  pretriangulatedHullExists : Prop

namespace PretriangulatedHullExistenceTarget

def ofProp
    (pretriangulatedHullExists : Prop) :
    PretriangulatedHullExistenceTarget where
  pretriangulatedHullExists := pretriangulatedHullExists

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    (P : CategoryInfra.PretriangulatedHull C) :
    PretriangulatedHullExistenceTarget :=
  ofProp P.existenceTarget

theorem ofInfrastructure_holds {C : CategoryInfra.DGCategoryLike.{u, v}}
    (P : CategoryInfra.PretriangulatedHull C) :
    (ofInfrastructure P).pretriangulatedHullExists :=
  P.existenceTarget_holds

end PretriangulatedHullExistenceTarget

/-- Shift-closure target for the manuscript's pretriangulated hull step.

This names the closure-under-shifts part of the pretriangulated story without
pretending the ambient dg package already exists. -/
structure ShiftClosureTarget where
  shiftClosure : Prop

namespace ShiftClosureTarget

def ofProp (shiftClosure : Prop) : ShiftClosureTarget where
  shiftClosure := shiftClosure

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    (P : CategoryInfra.PretriangulatedHull C) : ShiftClosureTarget :=
  ofProp P.shiftClosureTarget

theorem ofInfrastructure_holds {C : CategoryInfra.DGCategoryLike.{u, v}}
    (P : CategoryInfra.PretriangulatedHull C) :
    (ofInfrastructure P).shiftClosure :=
  P.shiftClosureTarget_holds

end ShiftClosureTarget

/-- Cone-closure target for the manuscript's pretriangulated hull step.

This isolates the closure-under-cones obligation from existence and universal
property so later work can discharge them independently. -/
structure ConeClosureTarget where
  coneClosure : Prop

namespace ConeClosureTarget

def ofProp (coneClosure : Prop) : ConeClosureTarget where
  coneClosure := coneClosure

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    (P : CategoryInfra.PretriangulatedHull C) : ConeClosureTarget :=
  ofProp P.coneClosureTarget

theorem ofInfrastructure_holds {C : CategoryInfra.DGCategoryLike.{u, v}}
    (P : CategoryInfra.PretriangulatedHull C) :
    (ofInfrastructure P).coneClosure :=
  P.coneClosureTarget_holds

end ConeClosureTarget

/-- Universal-property target for the manuscript's pretriangulated hull step.

This records the free pretriangulated extension claim separately from the raw
closure data. -/
structure PretriangulatedHullUniversalPropertyTarget where
  pretriangulatedHullUniversalProperty : Prop

namespace PretriangulatedHullUniversalPropertyTarget

def ofProp
    (pretriangulatedHullUniversalProperty : Prop) :
    PretriangulatedHullUniversalPropertyTarget where
  pretriangulatedHullUniversalProperty := pretriangulatedHullUniversalProperty

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    (P : CategoryInfra.PretriangulatedHull C) :
    PretriangulatedHullUniversalPropertyTarget :=
  ofProp P.universalPropertyTarget

theorem ofInfrastructure_holds {C : CategoryInfra.DGCategoryLike.{u, v}}
    (P : CategoryInfra.PretriangulatedHull C) :
    (ofInfrastructure P).pretriangulatedHullUniversalProperty :=
  P.universalPropertyTarget_holds

end PretriangulatedHullUniversalPropertyTarget

/-- Bundle the smallest manuscript-aligned theorem surfaces currently visible
for the pretriangulated hull step. -/
structure PretriangulatedHullFieldTargets where
  existence : PretriangulatedHullExistenceTarget
  shifts : ShiftClosureTarget
  cones : ConeClosureTarget
  universalProperty : PretriangulatedHullUniversalPropertyTarget

namespace PretriangulatedHullFieldTargets

def ofTargets
    (existence : PretriangulatedHullExistenceTarget)
    (shifts : ShiftClosureTarget)
    (cones : ConeClosureTarget)
    (universalProperty : PretriangulatedHullUniversalPropertyTarget) :
    PretriangulatedHullFieldTargets where
  existence := existence
  shifts := shifts
  cones := cones
  universalProperty := universalProperty

def pretriangulatedHullUniversality
    (T : PretriangulatedHullFieldTargets) : Prop :=
  T.existence.pretriangulatedHullExists ∧
    T.shifts.shiftClosure ∧
      T.cones.coneClosure ∧
        T.universalProperty.pretriangulatedHullUniversalProperty

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    (P : CategoryInfra.PretriangulatedHull C) :
    PretriangulatedHullFieldTargets :=
  ofTargets
    (PretriangulatedHullExistenceTarget.ofInfrastructure P)
    (ShiftClosureTarget.ofInfrastructure P)
    (ConeClosureTarget.ofInfrastructure P)
    (PretriangulatedHullUniversalPropertyTarget.ofInfrastructure P)

end PretriangulatedHullFieldTargets

/-- The pretriangulated-hull step is recorded as its own theorem target until a
concrete pretriangulated completion package exists in scope. -/
structure PretriangulatedHullUniversalTarget where
  pretriangulatedHullUniversality : Prop

namespace PretriangulatedHullUniversalTarget

def ofProp
    (pretriangulatedHullUniversality : Prop) :
    PretriangulatedHullUniversalTarget where
  pretriangulatedHullUniversality := pretriangulatedHullUniversality

def ofFields
    (existence : PretriangulatedHullExistenceTarget)
    (shifts : ShiftClosureTarget)
    (cones : ConeClosureTarget)
    (universalProperty : PretriangulatedHullUniversalPropertyTarget) :
    PretriangulatedHullUniversalTarget :=
  PretriangulatedHullUniversalTarget.ofProp
    (existence.pretriangulatedHullExists ∧
      shifts.shiftClosure ∧
        cones.coneClosure ∧
          universalProperty.pretriangulatedHullUniversalProperty)

def ofFieldTargets
    (T : PretriangulatedHullFieldTargets) :
    PretriangulatedHullUniversalTarget :=
  PretriangulatedHullUniversalTarget.ofProp
    T.pretriangulatedHullUniversality

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    (P : CategoryInfra.PretriangulatedHull C) :
    PretriangulatedHullUniversalTarget :=
  ofFieldTargets (PretriangulatedHullFieldTargets.ofInfrastructure P)

end PretriangulatedHullUniversalTarget

/-- The `H^0` passage is kept separate from the surrounding completion steps so
it can later be discharged independently of dg and Karoubi packaging. -/
structure H0CategoryExistenceTarget where
  hZeroCategoryExists : Prop

namespace H0CategoryExistenceTarget

def ofProp (hZeroCategoryExists : Prop) : H0CategoryExistenceTarget where
  hZeroCategoryExists := hZeroCategoryExists

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (H : CategoryInfra.H0Category P) : H0CategoryExistenceTarget :=
  ofProp H.existenceTarget

def ofPieces {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (quotientData : CategoryInfra.H0QuotientData P)
    (triangulatedData : CategoryInfra.H0TriangulatedData P) :
    H0CategoryExistenceTarget :=
  ofInfrastructure (CategoryInfra.H0Category.ofPieces quotientData triangulatedData)

theorem ofInfrastructure_holds {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (H : CategoryInfra.H0Category P) :
    (ofInfrastructure H).hZeroCategoryExists :=
  H.existenceTarget_holds

end H0CategoryExistenceTarget

/-- Distinguished-triangle target for the `H^0` step.

In the manuscript this is the point where the homotopy category inherits the
triangle class coming from the pretriangulated dg hull. -/
structure H0DistinguishedTrianglesTarget where
  hZeroDistinguishedTriangles : Prop

namespace H0DistinguishedTrianglesTarget

def ofProp
    (hZeroDistinguishedTriangles : Prop) :
    H0DistinguishedTrianglesTarget where
  hZeroDistinguishedTriangles := hZeroDistinguishedTriangles

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (H : CategoryInfra.H0Category P) : H0DistinguishedTrianglesTarget :=
  ofProp H.distinguishedTrianglesTarget

def ofPieces {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (quotientData : CategoryInfra.H0QuotientData P)
    (triangulatedData : CategoryInfra.H0TriangulatedData P) :
    H0DistinguishedTrianglesTarget :=
  ofInfrastructure (CategoryInfra.H0Category.ofPieces quotientData triangulatedData)

theorem ofInfrastructure_holds {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (H : CategoryInfra.H0Category P) :
    (ofInfrastructure H).hZeroDistinguishedTriangles :=
  H.distinguishedTrianglesTarget_holds

end H0DistinguishedTrianglesTarget

/-- Triangulated-axioms target for the `H^0` step.

This isolates the Verdier-style theorem surface from the existence of the
category and its triangle class. -/
structure H0TriangulatedAxiomsTarget where
  hZeroTriangulatedAxioms : Prop

namespace H0TriangulatedAxiomsTarget

def ofProp
    (hZeroTriangulatedAxioms : Prop) :
    H0TriangulatedAxiomsTarget where
  hZeroTriangulatedAxioms := hZeroTriangulatedAxioms

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (H : CategoryInfra.H0Category P) : H0TriangulatedAxiomsTarget :=
  ofProp H.triangulatedAxiomsTarget

def ofPieces {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (quotientData : CategoryInfra.H0QuotientData P)
    (triangulatedData : CategoryInfra.H0TriangulatedData P) :
    H0TriangulatedAxiomsTarget :=
  ofInfrastructure (CategoryInfra.H0Category.ofPieces quotientData triangulatedData)

theorem ofInfrastructure_holds {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (H : CategoryInfra.H0Category P) :
    (ofInfrastructure H).hZeroTriangulatedAxioms :=
  H.triangulatedAxiomsTarget_holds

end H0TriangulatedAxiomsTarget

/-- Localization target for the `H^0` step.

The manuscript describes `H^0` as localization at acyclic objects, so that
localization claim is recorded separately from the triangulated consequences. -/
structure H0LocalizationAtAcyclicsTarget where
  hZeroLocalizationAtAcyclics : Prop

namespace H0LocalizationAtAcyclicsTarget

def ofProp
    (hZeroLocalizationAtAcyclics : Prop) :
    H0LocalizationAtAcyclicsTarget where
  hZeroLocalizationAtAcyclics := hZeroLocalizationAtAcyclics

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (H : CategoryInfra.H0Category P) : H0LocalizationAtAcyclicsTarget :=
  ofProp H.localizationAtAcyclicsTarget

def ofPieces {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (quotientData : CategoryInfra.H0QuotientData P)
    (triangulatedData : CategoryInfra.H0TriangulatedData P) :
    H0LocalizationAtAcyclicsTarget :=
  ofInfrastructure (CategoryInfra.H0Category.ofPieces quotientData triangulatedData)

theorem ofInfrastructure_holds {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (H : CategoryInfra.H0Category P) :
    (ofInfrastructure H).hZeroLocalizationAtAcyclics :=
  H.localizationAtAcyclicsTarget_holds

end H0LocalizationAtAcyclicsTarget

/-- Bundle the smallest manuscript-aligned theorem surfaces currently visible
for the `H^0` passage. -/
structure H0TriangulatedFieldTargets where
  category : H0CategoryExistenceTarget
  distinguishedTriangles : H0DistinguishedTrianglesTarget
  triangulatedAxioms : H0TriangulatedAxiomsTarget
  localizationAtAcyclics : H0LocalizationAtAcyclicsTarget

namespace H0TriangulatedFieldTargets

def ofTargets
    (category : H0CategoryExistenceTarget)
    (distinguishedTriangles : H0DistinguishedTrianglesTarget)
    (triangulatedAxioms : H0TriangulatedAxiomsTarget)
    (localizationAtAcyclics : H0LocalizationAtAcyclicsTarget) :
    H0TriangulatedFieldTargets where
  category := category
  distinguishedTriangles := distinguishedTriangles
  triangulatedAxioms := triangulatedAxioms
  localizationAtAcyclics := localizationAtAcyclics

def hZeroTriangulatedPassage
    (T : H0TriangulatedFieldTargets) : Prop :=
  T.category.hZeroCategoryExists ∧
    T.distinguishedTriangles.hZeroDistinguishedTriangles ∧
      T.triangulatedAxioms.hZeroTriangulatedAxioms ∧
        T.localizationAtAcyclics.hZeroLocalizationAtAcyclics

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (H : CategoryInfra.H0Category P) : H0TriangulatedFieldTargets :=
  ofTargets
    (H0CategoryExistenceTarget.ofInfrastructure H)
    (H0DistinguishedTrianglesTarget.ofInfrastructure H)
    (H0TriangulatedAxiomsTarget.ofInfrastructure H)
    (H0LocalizationAtAcyclicsTarget.ofInfrastructure H)

def ofPieces {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (quotientData : CategoryInfra.H0QuotientData P)
    (triangulatedData : CategoryInfra.H0TriangulatedData P) :
    H0TriangulatedFieldTargets :=
  ofInfrastructure (CategoryInfra.H0Category.ofPieces quotientData triangulatedData)

theorem ofInfrastructure_holds {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (H : CategoryInfra.H0Category P) :
    (ofInfrastructure H).hZeroTriangulatedPassage :=
  H.theoremTarget_holds

end H0TriangulatedFieldTargets

/-- The `H^0` passage is kept separate from the surrounding completion steps so
it can later be discharged independently of dg and Karoubi packaging. -/
structure H0TriangulatedTarget where
  hZeroTriangulatedPassage : Prop

namespace H0TriangulatedTarget

def ofProp (hZeroTriangulatedPassage : Prop) : H0TriangulatedTarget where
  hZeroTriangulatedPassage := hZeroTriangulatedPassage

def ofFields
    (category : H0CategoryExistenceTarget)
    (distinguishedTriangles : H0DistinguishedTrianglesTarget)
    (triangulatedAxioms : H0TriangulatedAxiomsTarget)
    (localizationAtAcyclics : H0LocalizationAtAcyclicsTarget) :
    H0TriangulatedTarget :=
  H0TriangulatedTarget.ofProp
    (category.hZeroCategoryExists ∧
      distinguishedTriangles.hZeroDistinguishedTriangles ∧
        triangulatedAxioms.hZeroTriangulatedAxioms ∧
          localizationAtAcyclics.hZeroLocalizationAtAcyclics)

def ofFieldTargets
    (T : H0TriangulatedFieldTargets) : H0TriangulatedTarget :=
  H0TriangulatedTarget.ofProp T.hZeroTriangulatedPassage

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (H : CategoryInfra.H0Category P) : H0TriangulatedTarget :=
  ofFieldTargets (H0TriangulatedFieldTargets.ofInfrastructure H)

def ofPieces {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (quotientData : CategoryInfra.H0QuotientData P)
    (triangulatedData : CategoryInfra.H0TriangulatedData P) :
    H0TriangulatedTarget :=
  ofInfrastructure (CategoryInfra.H0Category.ofPieces quotientData triangulatedData)

theorem ofInfrastructure_holds {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    (H : CategoryInfra.H0Category P) :
    (ofInfrastructure H).hZeroTriangulatedPassage :=
  H0TriangulatedFieldTargets.ofInfrastructure_holds H

end H0TriangulatedTarget

/-- Existence target for the manuscript's Karoubi-envelope step.

The current Layer B scope does not expose a concrete idempotent-completion
construction, so the first honest lower obligation is that the Karoubi envelope
exists. -/
structure KaroubiEnvelopeExistenceTarget where
  karoubiEnvelopeExists : Prop

namespace KaroubiEnvelopeExistenceTarget

def ofProp
    (karoubiEnvelopeExists : Prop) :
    KaroubiEnvelopeExistenceTarget where
  karoubiEnvelopeExists := karoubiEnvelopeExists

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    {H : CategoryInfra.H0Category P}
    (K : CategoryInfra.KaroubiEnvelope H) : KaroubiEnvelopeExistenceTarget :=
  ofProp K.existenceTarget

theorem ofInfrastructure_holds {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    {H : CategoryInfra.H0Category P}
    (K : CategoryInfra.KaroubiEnvelope H) :
    (ofInfrastructure K).karoubiEnvelopeExists :=
  K.existenceTarget_holds

end KaroubiEnvelopeExistenceTarget

/-- Idempotent-splitting target for the manuscript's Karoubi-envelope step.

This isolates the direct categorical content of the Karoubi envelope from the
broader universal-property statement. -/
structure IdempotentSplittingTarget where
  idempotentSplitting : Prop

namespace IdempotentSplittingTarget

def ofProp (idempotentSplitting : Prop) : IdempotentSplittingTarget where
  idempotentSplitting := idempotentSplitting

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    {H : CategoryInfra.H0Category P}
    (K : CategoryInfra.KaroubiEnvelope H) : IdempotentSplittingTarget :=
  ofProp K.idempotentSplittingTarget

theorem ofInfrastructure_holds {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    {H : CategoryInfra.H0Category P}
    (K : CategoryInfra.KaroubiEnvelope H) :
    (ofInfrastructure K).idempotentSplitting :=
  K.idempotentSplittingTarget_holds

end IdempotentSplittingTarget

/-- Universal-property target for the manuscript's Karoubi-envelope step.

Monoidal compatibility stays in the separate completion-step target, so this
records only the free idempotent-completion claim itself. -/
structure KaroubiUniversalPropertyTarget where
  karoubiUniversalProperty : Prop

namespace KaroubiUniversalPropertyTarget

def ofProp
    (karoubiUniversalProperty : Prop) :
    KaroubiUniversalPropertyTarget where
  karoubiUniversalProperty := karoubiUniversalProperty

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    {H : CategoryInfra.H0Category P}
    (K : CategoryInfra.KaroubiEnvelope H) : KaroubiUniversalPropertyTarget :=
  ofProp K.universalPropertyTarget

theorem ofInfrastructure_holds {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    {H : CategoryInfra.H0Category P}
    (K : CategoryInfra.KaroubiEnvelope H) :
    (ofInfrastructure K).karoubiUniversalProperty :=
  K.universalPropertyTarget_holds

end KaroubiUniversalPropertyTarget

/-- Bundle the smallest manuscript-aligned theorem surfaces currently visible
for the Karoubi-envelope step. -/
structure KaroubiEnvelopeFieldTargets where
  existence : KaroubiEnvelopeExistenceTarget
  idempotentSplitting : IdempotentSplittingTarget
  universalProperty : KaroubiUniversalPropertyTarget

namespace KaroubiEnvelopeFieldTargets

def ofTargets
    (existence : KaroubiEnvelopeExistenceTarget)
    (idempotentSplitting : IdempotentSplittingTarget)
    (universalProperty : KaroubiUniversalPropertyTarget) :
    KaroubiEnvelopeFieldTargets where
  existence := existence
  idempotentSplitting := idempotentSplitting
  universalProperty := universalProperty

def karoubianEnvelopeUniversality
    (T : KaroubiEnvelopeFieldTargets) : Prop :=
  T.existence.karoubiEnvelopeExists ∧
    T.idempotentSplitting.idempotentSplitting ∧
      T.universalProperty.karoubiUniversalProperty

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    {H : CategoryInfra.H0Category P}
    (K : CategoryInfra.KaroubiEnvelope H) : KaroubiEnvelopeFieldTargets :=
  ofTargets
    (KaroubiEnvelopeExistenceTarget.ofInfrastructure K)
    (IdempotentSplittingTarget.ofInfrastructure K)
    (KaroubiUniversalPropertyTarget.ofInfrastructure K)

end KaroubiEnvelopeFieldTargets

/-- The Karoubi-envelope step is named separately because the current scoped
files do not yet expose an idempotent-completion construction package. -/
structure KaroubiEnvelopeUniversalTarget where
  karoubianEnvelopeUniversality : Prop

namespace KaroubiEnvelopeUniversalTarget

def ofProp
    (karoubianEnvelopeUniversality : Prop) :
    KaroubiEnvelopeUniversalTarget where
  karoubianEnvelopeUniversality := karoubianEnvelopeUniversality

def ofFields
    (existence : KaroubiEnvelopeExistenceTarget)
    (idempotentSplitting : IdempotentSplittingTarget)
    (universalProperty : KaroubiUniversalPropertyTarget) :
    KaroubiEnvelopeUniversalTarget :=
  KaroubiEnvelopeUniversalTarget.ofProp
    (existence.karoubiEnvelopeExists ∧
      idempotentSplitting.idempotentSplitting ∧
        universalProperty.karoubiUniversalProperty)

def ofFieldTargets
    (T : KaroubiEnvelopeFieldTargets) :
    KaroubiEnvelopeUniversalTarget :=
  KaroubiEnvelopeUniversalTarget.ofProp
    T.karoubianEnvelopeUniversality

def ofInfrastructure {C : CategoryInfra.DGCategoryLike.{u, v}}
    {P : CategoryInfra.PretriangulatedHull C}
    {H : CategoryInfra.H0Category P}
    (K : CategoryInfra.KaroubiEnvelope H) : KaroubiEnvelopeUniversalTarget :=
  ofFieldTargets (KaroubiEnvelopeFieldTargets.ofInfrastructure K)

end KaroubiEnvelopeUniversalTarget

/-- The monoidal-lift step is isolated as its own theorem target because the
current real-objects layer does not yet carry a completion-stage monoidal
package. -/
structure MonoidalLiftThroughDGEnvelopeTarget where
  monoidalLiftThroughDGEnvelope : Prop

namespace MonoidalLiftThroughDGEnvelopeTarget

def ofProp
    (monoidalLiftThroughDGEnvelope : Prop) :
    MonoidalLiftThroughDGEnvelopeTarget where
  monoidalLiftThroughDGEnvelope := monoidalLiftThroughDGEnvelope

def ofInfrastructure {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (M : CategoryInfra.MonoidalTransport F P H K) :
    MonoidalLiftThroughDGEnvelopeTarget :=
  ofProp M.throughDGEnvelope

theorem ofInfrastructure_holds {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (M : CategoryInfra.MonoidalTransport F P H K) :
    (ofInfrastructure M).monoidalLiftThroughDGEnvelope :=
  M.throughDGEnvelope_holds

end MonoidalLiftThroughDGEnvelopeTarget

/-- Monoidal-lift target for the pretriangulated hull stage.

This records the tensor extension to twisted complexes separately from the dg
envelope and later `H^0`/Karoubi transport steps. -/
structure MonoidalLiftThroughPretriangulatedHullTarget where
  monoidalLiftThroughPretriangulatedHull : Prop

namespace MonoidalLiftThroughPretriangulatedHullTarget

def ofProp
    (monoidalLiftThroughPretriangulatedHull : Prop) :
    MonoidalLiftThroughPretriangulatedHullTarget where
  monoidalLiftThroughPretriangulatedHull :=
    monoidalLiftThroughPretriangulatedHull

def ofInfrastructure {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (M : CategoryInfra.MonoidalTransport F P H K) :
    MonoidalLiftThroughPretriangulatedHullTarget :=
  ofProp M.throughPretriangulatedHull

theorem ofInfrastructure_holds {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (M : CategoryInfra.MonoidalTransport F P H K) :
    (ofInfrastructure M).monoidalLiftThroughPretriangulatedHull :=
  M.throughPretriangulatedHull_holds

end MonoidalLiftThroughPretriangulatedHullTarget

/-- Monoidal-lift target for the `H^0` stage.

This is the manuscript's claim that the induced tensor on zeroth cohomology is
well-defined and compatible with the surrounding triangulated structure. -/
structure MonoidalLiftThroughH0Target where
  monoidalLiftThroughH0 : Prop

namespace MonoidalLiftThroughH0Target

def ofProp
    (monoidalLiftThroughH0 : Prop) :
    MonoidalLiftThroughH0Target where
  monoidalLiftThroughH0 := monoidalLiftThroughH0

def ofInfrastructure {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (M : CategoryInfra.MonoidalTransport F P H K) :
    MonoidalLiftThroughH0Target :=
  ofProp M.throughH0

theorem ofInfrastructure_holds {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (M : CategoryInfra.MonoidalTransport F P H K) :
    (ofInfrastructure M).monoidalLiftThroughH0 :=
  M.throughH0_holds

end MonoidalLiftThroughH0Target

/-- Monoidal-lift target for the Karoubi-envelope stage.

This isolates the idempotent-completion tensor transport from the earlier
monoidal lift through dg, pretriangulated, and `H^0` stages. -/
structure MonoidalLiftThroughKaroubiEnvelopeTarget where
  monoidalLiftThroughKaroubiEnvelope : Prop

namespace MonoidalLiftThroughKaroubiEnvelopeTarget

def ofProp
    (monoidalLiftThroughKaroubiEnvelope : Prop) :
    MonoidalLiftThroughKaroubiEnvelopeTarget where
  monoidalLiftThroughKaroubiEnvelope := monoidalLiftThroughKaroubiEnvelope

def ofInfrastructure {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (M : CategoryInfra.MonoidalTransport F P H K) :
    MonoidalLiftThroughKaroubiEnvelopeTarget :=
  ofProp M.throughKaroubiEnvelope

theorem ofInfrastructure_holds {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (M : CategoryInfra.MonoidalTransport F P H K) :
    (ofInfrastructure M).monoidalLiftThroughKaroubiEnvelope :=
  M.throughKaroubiEnvelope_holds

end MonoidalLiftThroughKaroubiEnvelopeTarget

/-- Coherence-transport target for the full monoidal-lift step.

This records the final transport of associator/unit/braiding coherence through
the whole completion ladder. -/
structure MonoidalCoherenceTransportTarget where
  monoidalCoherenceTransport : Prop

namespace MonoidalCoherenceTransportTarget

def ofProp
    (monoidalCoherenceTransport : Prop) :
    MonoidalCoherenceTransportTarget where
  monoidalCoherenceTransport := monoidalCoherenceTransport

def ofInfrastructure {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (M : CategoryInfra.MonoidalTransport F P H K) :
    MonoidalCoherenceTransportTarget :=
  ofProp M.coherenceTransport

theorem ofInfrastructure_holds {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (M : CategoryInfra.MonoidalTransport F P H K) :
    (ofInfrastructure M).monoidalCoherenceTransport :=
  M.coherenceTransport_holds

end MonoidalCoherenceTransportTarget

/-- Bundle the smallest manuscript-aligned theorem surfaces currently visible
for monoidal lift through the completion ladder. -/
structure MonoidalLiftFieldTargets where
  dgEnvelope : MonoidalLiftThroughDGEnvelopeTarget
  pretriangulatedHull : MonoidalLiftThroughPretriangulatedHullTarget
  hZero : MonoidalLiftThroughH0Target
  karoubiEnvelope : MonoidalLiftThroughKaroubiEnvelopeTarget
  coherenceTransport : MonoidalCoherenceTransportTarget

namespace MonoidalLiftFieldTargets

def ofTargets
    (dgEnvelope : MonoidalLiftThroughDGEnvelopeTarget)
    (pretriangulatedHull : MonoidalLiftThroughPretriangulatedHullTarget)
    (hZero : MonoidalLiftThroughH0Target)
    (karoubiEnvelope : MonoidalLiftThroughKaroubiEnvelopeTarget)
    (coherenceTransport : MonoidalCoherenceTransportTarget) :
    MonoidalLiftFieldTargets where
  dgEnvelope := dgEnvelope
  pretriangulatedHull := pretriangulatedHull
  hZero := hZero
  karoubiEnvelope := karoubiEnvelope
  coherenceTransport := coherenceTransport

def monoidalLiftThroughCompletion
    (T : MonoidalLiftFieldTargets) : Prop :=
  T.dgEnvelope.monoidalLiftThroughDGEnvelope ∧
    T.pretriangulatedHull.monoidalLiftThroughPretriangulatedHull ∧
      T.hZero.monoidalLiftThroughH0 ∧
        T.karoubiEnvelope.monoidalLiftThroughKaroubiEnvelope ∧
          T.coherenceTransport.monoidalCoherenceTransport

def ofInfrastructure {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (M : CategoryInfra.MonoidalTransport F P H K) : MonoidalLiftFieldTargets :=
  ofTargets
    (MonoidalLiftThroughDGEnvelopeTarget.ofInfrastructure M)
    (MonoidalLiftThroughPretriangulatedHullTarget.ofInfrastructure M)
    (MonoidalLiftThroughH0Target.ofInfrastructure M)
    (MonoidalLiftThroughKaroubiEnvelopeTarget.ofInfrastructure M)
    (MonoidalCoherenceTransportTarget.ofInfrastructure M)

end MonoidalLiftFieldTargets

/-- The monoidal-lift step is isolated as its own theorem target because the
current real-objects layer does not yet carry a completion-stage monoidal
package. -/
structure MonoidalLiftThroughCompletionTarget where
  monoidalLiftThroughCompletion : Prop

namespace MonoidalLiftThroughCompletionTarget

def ofProp
    (monoidalLiftThroughCompletion : Prop) :
    MonoidalLiftThroughCompletionTarget where
  monoidalLiftThroughCompletion := monoidalLiftThroughCompletion

def ofFields
    (dgEnvelope : MonoidalLiftThroughDGEnvelopeTarget)
    (pretriangulatedHull : MonoidalLiftThroughPretriangulatedHullTarget)
    (hZero : MonoidalLiftThroughH0Target)
    (karoubiEnvelope : MonoidalLiftThroughKaroubiEnvelopeTarget)
    (coherenceTransport : MonoidalCoherenceTransportTarget) :
    MonoidalLiftThroughCompletionTarget :=
  MonoidalLiftThroughCompletionTarget.ofProp
    (dgEnvelope.monoidalLiftThroughDGEnvelope ∧
      pretriangulatedHull.monoidalLiftThroughPretriangulatedHull ∧
        hZero.monoidalLiftThroughH0 ∧
          karoubiEnvelope.monoidalLiftThroughKaroubiEnvelope ∧
            coherenceTransport.monoidalCoherenceTransport)

def ofFieldTargets
    (T : MonoidalLiftFieldTargets) :
    MonoidalLiftThroughCompletionTarget :=
  MonoidalLiftThroughCompletionTarget.ofProp
    T.monoidalLiftThroughCompletion

def ofInfrastructure {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (M : CategoryInfra.MonoidalTransport F P H K) :
    MonoidalLiftThroughCompletionTarget :=
  ofFieldTargets (MonoidalLiftFieldTargets.ofInfrastructure M)

end MonoidalLiftThroughCompletionTarget

/-- Exactness transport through the completion steps is recorded separately so
it can be discharged without pretending the full completion construction is
already available. -/
structure ExactnessForDGEnvelopeTarget where
  exactnessForDGEnvelope : Prop

namespace ExactnessForDGEnvelopeTarget

def ofProp
    (exactnessForDGEnvelope : Prop) :
    ExactnessForDGEnvelopeTarget where
  exactnessForDGEnvelope := exactnessForDGEnvelope

def ofInfrastructure {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (E : CategoryInfra.ExactnessTransport F P H K) :
    ExactnessForDGEnvelopeTarget :=
  ofProp E.exactnessForDGEnvelope

theorem ofInfrastructure_holds {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (E : CategoryInfra.ExactnessTransport F P H K) :
    (ofInfrastructure E).exactnessForDGEnvelope :=
  E.exactnessForDGEnvelope_holds

end ExactnessForDGEnvelopeTarget

/-- Exactness-transport target for the pretriangulated hull stage.

This is the stage where shifts and cones become the generators of exactness for
the later completion route. -/
structure ExactnessForPretriangulatedHullTarget where
  exactnessForPretriangulatedHull : Prop

namespace ExactnessForPretriangulatedHullTarget

def ofProp
    (exactnessForPretriangulatedHull : Prop) :
    ExactnessForPretriangulatedHullTarget where
  exactnessForPretriangulatedHull := exactnessForPretriangulatedHull

def ofInfrastructure {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (E : CategoryInfra.ExactnessTransport F P H K) :
    ExactnessForPretriangulatedHullTarget :=
  ofProp E.exactnessForPretriangulatedHull

theorem ofInfrastructure_holds {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (E : CategoryInfra.ExactnessTransport F P H K) :
    (ofInfrastructure E).exactnessForPretriangulatedHull :=
  E.exactnessForPretriangulatedHull_holds

end ExactnessForPretriangulatedHullTarget

/-- Exactness-transport target for the `H^0` stage.

This records that exactness survives passage to zeroth cohomology. -/
structure ExactnessForH0Target where
  exactnessForH0 : Prop

namespace ExactnessForH0Target

def ofProp
    (exactnessForH0 : Prop) :
    ExactnessForH0Target where
  exactnessForH0 := exactnessForH0

def ofInfrastructure {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (E : CategoryInfra.ExactnessTransport F P H K) :
    ExactnessForH0Target :=
  ofProp E.exactnessForH0

theorem ofInfrastructure_holds {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (E : CategoryInfra.ExactnessTransport F P H K) :
    (ofInfrastructure E).exactnessForH0 :=
  E.exactnessForH0_holds

end ExactnessForH0Target

/-- Exactness-transport target for the Karoubi-envelope stage.

This isolates the direct-summand / idempotent-completion part of exactness from
the earlier cone-level and `H^0` transport steps. -/
structure ExactnessForKaroubiEnvelopeTarget where
  exactnessForKaroubiEnvelope : Prop

namespace ExactnessForKaroubiEnvelopeTarget

def ofProp
    (exactnessForKaroubiEnvelope : Prop) :
    ExactnessForKaroubiEnvelopeTarget where
  exactnessForKaroubiEnvelope := exactnessForKaroubiEnvelope

def ofInfrastructure {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (E : CategoryInfra.ExactnessTransport F P H K) :
    ExactnessForKaroubiEnvelopeTarget :=
  ofProp E.exactnessForKaroubiEnvelope

theorem ofInfrastructure_holds {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (E : CategoryInfra.ExactnessTransport F P H K) :
    (ofInfrastructure E).exactnessForKaroubiEnvelope :=
  E.exactnessForKaroubiEnvelope_holds

end ExactnessForKaroubiEnvelopeTarget

/-- Final distinguished-triangle transport target for exactness through the
completion ladder. -/
structure DistinguishedTriangleTransportTarget where
  distinguishedTriangleTransport : Prop

namespace DistinguishedTriangleTransportTarget

def ofProp
    (distinguishedTriangleTransport : Prop) :
    DistinguishedTriangleTransportTarget where
  distinguishedTriangleTransport := distinguishedTriangleTransport

def ofInfrastructure {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (E : CategoryInfra.ExactnessTransport F P H K) :
    DistinguishedTriangleTransportTarget :=
  ofProp E.distinguishedTriangleTransport

theorem ofInfrastructure_holds {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (E : CategoryInfra.ExactnessTransport F P H K) :
    (ofInfrastructure E).distinguishedTriangleTransport :=
  E.distinguishedTriangleTransport_holds

end DistinguishedTriangleTransportTarget

/-- Bundle the smallest manuscript-aligned theorem surfaces currently visible
for exactness transport through the completion ladder. -/
structure ExactnessTransportFieldTargets where
  dgEnvelope : ExactnessForDGEnvelopeTarget
  pretriangulatedHull : ExactnessForPretriangulatedHullTarget
  hZero : ExactnessForH0Target
  karoubiEnvelope : ExactnessForKaroubiEnvelopeTarget
  distinguishedTriangles : DistinguishedTriangleTransportTarget

namespace ExactnessTransportFieldTargets

def ofTargets
    (dgEnvelope : ExactnessForDGEnvelopeTarget)
    (pretriangulatedHull : ExactnessForPretriangulatedHullTarget)
    (hZero : ExactnessForH0Target)
    (karoubiEnvelope : ExactnessForKaroubiEnvelopeTarget)
    (distinguishedTriangles : DistinguishedTriangleTransportTarget) :
    ExactnessTransportFieldTargets where
  dgEnvelope := dgEnvelope
  pretriangulatedHull := pretriangulatedHull
  hZero := hZero
  karoubiEnvelope := karoubiEnvelope
  distinguishedTriangles := distinguishedTriangles

def exactnessTransportThroughCompletion
    (T : ExactnessTransportFieldTargets) : Prop :=
  T.dgEnvelope.exactnessForDGEnvelope ∧
    T.pretriangulatedHull.exactnessForPretriangulatedHull ∧
      T.hZero.exactnessForH0 ∧
        T.karoubiEnvelope.exactnessForKaroubiEnvelope ∧
          T.distinguishedTriangles.distinguishedTriangleTransport

def ofInfrastructure {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (E : CategoryInfra.ExactnessTransport F P H K) :
    ExactnessTransportFieldTargets :=
  ofTargets
    (ExactnessForDGEnvelopeTarget.ofInfrastructure E)
    (ExactnessForPretriangulatedHullTarget.ofInfrastructure E)
    (ExactnessForH0Target.ofInfrastructure E)
    (ExactnessForKaroubiEnvelopeTarget.ofInfrastructure E)
    (DistinguishedTriangleTransportTarget.ofInfrastructure E)

end ExactnessTransportFieldTargets

/-- Exactness transport through the completion steps is recorded separately so
it can be discharged without pretending the full completion construction is
already available. -/
structure ExactnessTransportThroughCompletionTarget where
  exactnessTransportThroughCompletion : Prop

namespace ExactnessTransportThroughCompletionTarget

def ofProp
    (exactnessTransportThroughCompletion : Prop) :
    ExactnessTransportThroughCompletionTarget where
  exactnessTransportThroughCompletion := exactnessTransportThroughCompletion

def ofFields
    (dgEnvelope : ExactnessForDGEnvelopeTarget)
    (pretriangulatedHull : ExactnessForPretriangulatedHullTarget)
    (hZero : ExactnessForH0Target)
    (karoubiEnvelope : ExactnessForKaroubiEnvelopeTarget)
    (distinguishedTriangles : DistinguishedTriangleTransportTarget) :
    ExactnessTransportThroughCompletionTarget :=
  ExactnessTransportThroughCompletionTarget.ofProp
    (dgEnvelope.exactnessForDGEnvelope ∧
      pretriangulatedHull.exactnessForPretriangulatedHull ∧
        hZero.exactnessForH0 ∧
          karoubiEnvelope.exactnessForKaroubiEnvelope ∧
            distinguishedTriangles.distinguishedTriangleTransport)

def ofFieldTargets
    (T : ExactnessTransportFieldTargets) :
    ExactnessTransportThroughCompletionTarget :=
  ExactnessTransportThroughCompletionTarget.ofProp
    T.exactnessTransportThroughCompletion

def ofInfrastructure {presentation : Type u}
    {F : CategoryInfra.FreeDGEnvelope.{u, v} presentation}
    {P : CategoryInfra.PretriangulatedHull F.envelope}
    {H : CategoryInfra.H0Category P}
    {K : CategoryInfra.KaroubiEnvelope H}
    (E : CategoryInfra.ExactnessTransport F P H K) :
    ExactnessTransportThroughCompletionTarget :=
  ofFieldTargets (ExactnessTransportFieldTargets.ofInfrastructure E)

end ExactnessTransportThroughCompletionTarget

/-- Bundle the six manuscript-named completion steps before they are assembled
into the single stable-completion construction target. -/
structure StableCompletionFieldTargets where
  dgEnvelope : FreeDGEnvelopeTarget
  pretriangulatedHull : PretriangulatedHullUniversalTarget
  hZeroPassage : H0TriangulatedTarget
  karoubiEnvelope : KaroubiEnvelopeUniversalTarget
  monoidalLift : MonoidalLiftThroughCompletionTarget
  exactnessTransport : ExactnessTransportThroughCompletionTarget

namespace StableCompletionFieldTargets

def ofTargets
    (dgEnvelope : FreeDGEnvelopeTarget)
    (pretriangulatedHull : PretriangulatedHullUniversalTarget)
    (hZeroPassage : H0TriangulatedTarget)
    (karoubiEnvelope : KaroubiEnvelopeUniversalTarget)
    (monoidalLift : MonoidalLiftThroughCompletionTarget)
    (exactnessTransport : ExactnessTransportThroughCompletionTarget) :
    StableCompletionFieldTargets where
  dgEnvelope := dgEnvelope
  pretriangulatedHull := pretriangulatedHull
  hZeroPassage := hZeroPassage
  karoubiEnvelope := karoubiEnvelope
  monoidalLift := monoidalLift
  exactnessTransport := exactnessTransport

end StableCompletionFieldTargets

/-- Stepwise theorem targets named explicitly by the manuscript's verification
of the stable-completion construction. These do not yet build the completion,
but they isolate the exact proof surfaces that should combine into it. -/
structure StableCompletionStepTargets where
  dgEnvelopeUniversality : Prop
  pretriangulatedHullUniversality : Prop
  hZeroTriangulatedPassage : Prop
  karoubianEnvelopeUniversality : Prop
  monoidalLiftThroughCompletion : Prop
  exactnessTransportThroughCompletion : Prop
  steps_realize_stableCompletionConstruction :
    dgEnvelopeUniversality →
      pretriangulatedHullUniversality →
      hZeroTriangulatedPassage →
      karoubianEnvelopeUniversality →
      monoidalLiftThroughCompletion →
      exactnessTransportThroughCompletion →
      Prop

namespace StableCompletionStepTargets

def dgEnvelopeTarget (T : StableCompletionStepTargets) : FreeDGEnvelopeTarget :=
  FreeDGEnvelopeTarget.ofProp T.dgEnvelopeUniversality

def pretriangulatedHullTarget
    (T : StableCompletionStepTargets) :
    PretriangulatedHullUniversalTarget :=
  PretriangulatedHullUniversalTarget.ofProp T.pretriangulatedHullUniversality

def hZeroTarget (T : StableCompletionStepTargets) : H0TriangulatedTarget :=
  H0TriangulatedTarget.ofProp T.hZeroTriangulatedPassage

def karoubiEnvelopeTarget
    (T : StableCompletionStepTargets) :
    KaroubiEnvelopeUniversalTarget :=
  KaroubiEnvelopeUniversalTarget.ofProp T.karoubianEnvelopeUniversality

def monoidalLiftTarget
    (T : StableCompletionStepTargets) :
    MonoidalLiftThroughCompletionTarget :=
  MonoidalLiftThroughCompletionTarget.ofProp T.monoidalLiftThroughCompletion

def exactnessTransportTarget
    (T : StableCompletionStepTargets) :
    ExactnessTransportThroughCompletionTarget :=
  ExactnessTransportThroughCompletionTarget.ofProp
    T.exactnessTransportThroughCompletion

def fieldTargets
    (T : StableCompletionStepTargets) :
    StableCompletionFieldTargets :=
  StableCompletionFieldTargets.ofTargets
    T.dgEnvelopeTarget
    T.pretriangulatedHullTarget
    T.hZeroTarget
    T.karoubiEnvelopeTarget
    T.monoidalLiftTarget
    T.exactnessTransportTarget

def ofFieldTargets
    (F : StableCompletionFieldTargets)
    (hSteps :
      F.dgEnvelope.dgEnvelopeUniversality →
        F.pretriangulatedHull.pretriangulatedHullUniversality →
        F.hZeroPassage.hZeroTriangulatedPassage →
        F.karoubiEnvelope.karoubianEnvelopeUniversality →
        F.monoidalLift.monoidalLiftThroughCompletion →
        F.exactnessTransport.exactnessTransportThroughCompletion →
        Prop) :
    StableCompletionStepTargets where
  dgEnvelopeUniversality := F.dgEnvelope.dgEnvelopeUniversality
  pretriangulatedHullUniversality :=
    F.pretriangulatedHull.pretriangulatedHullUniversality
  hZeroTriangulatedPassage := F.hZeroPassage.hZeroTriangulatedPassage
  karoubianEnvelopeUniversality :=
    F.karoubiEnvelope.karoubianEnvelopeUniversality
  monoidalLiftThroughCompletion :=
    F.monoidalLift.monoidalLiftThroughCompletion
  exactnessTransportThroughCompletion :=
    F.exactnessTransport.exactnessTransportThroughCompletion
  steps_realize_stableCompletionConstruction := hSteps

def stableCompletionConstruction
    (T : StableCompletionStepTargets) :
    Prop :=
  ∃ hDg : T.dgEnvelopeUniversality,
    ∃ hPretr : T.pretriangulatedHullUniversality,
      ∃ hH0 : T.hZeroTriangulatedPassage,
        ∃ hKar : T.karoubianEnvelopeUniversality,
          ∃ hMonoidal : T.monoidalLiftThroughCompletion,
            ∃ hExact : T.exactnessTransportThroughCompletion,
              T.steps_realize_stableCompletionConstruction
                hDg hPretr hH0 hKar hMonoidal hExact

end StableCompletionStepTargets

/-- Smallest precise missing theorem target for the completion lane.

The current real-objects development does not yet package the stable-completion
construction itself. Once that single construction target is supplied, it is
expected to simultaneously discharge:

- existence of the completed trace category;
- the completion extension property;
- the concrete stable-completion model.

So the missing object is not three unrelated proofs, but one construction-level
theorem surface plus its immediate consequences. -/
structure MinimumCompletionConstructionTarget where
  stableCompletionConstruction : Prop
  construction_realizes_consequences :
    stableCompletionConstruction → MinimumCompletionConsequencesTarget

namespace MinimumCompletionConstructionTarget

/-- Forget the construction witness down to the immediate manuscript-facing
consequences of stable completion. -/
def toConsequencesTarget
    (T : MinimumCompletionConstructionTarget)
    (h : T.stableCompletionConstruction) :
    MinimumCompletionConsequencesTarget :=
  T.construction_realizes_consequences h

/-- Forget the construction witness down to the three-field completion target. -/
def toMinimumCompletionTarget
    (T : MinimumCompletionConstructionTarget)
    (h : T.stableCompletionConstruction) :
    MinimumCompletionTarget :=
  (T.toConsequencesTarget h).toMinimumCompletionTarget

end MinimumCompletionConstructionTarget

namespace StableCompletionStepTargets

def toConstructionTarget
    (T : StableCompletionStepTargets) :
    MinimumCompletionConstructionTarget where
  stableCompletionConstruction := StableCompletionStepTargets.stableCompletionConstruction T
  construction_realizes_consequences := by
    intro h
    exact {
      completedTraceCategory :=
        CompletedTraceCategoryExistenceTarget.ofProp
          (StableCompletionStepTargets.stableCompletionConstruction T)
      extensionProperty :=
        CompletionExtensionPropertyTarget.ofProp
          (StableCompletionStepTargets.stableCompletionConstruction T)
      stableModel :=
        StableCompletionModelTarget.ofProp
          (StableCompletionStepTargets.stableCompletionConstruction T)
    }

end StableCompletionStepTargets

namespace MinimumCompletionTarget

def ofFields
    (completedTraceCategoryExists : Prop)
    (completionExtensionProperty : Prop)
    (stableCompletionModel : Prop) :
    MinimumCompletionTarget where
  completedTraceCategoryExists := completedTraceCategoryExists
  completionExtensionProperty := completionExtensionProperty
  stableCompletionModel := stableCompletionModel

/-- Repackage the three manuscript-facing completion claims as the immediate
consequences of one stable-completion construction target. -/
def ofConstructionTarget
    (T : MinimumCompletionConstructionTarget)
    (h : T.stableCompletionConstruction) :
    MinimumCompletionTarget :=
  T.toMinimumCompletionTarget h

/-- Repackage the intermediate consequence bundle as the coarse three-field
minimum-completion target. -/
def ofConsequencesTarget
    (T : MinimumCompletionConsequencesTarget) :
    MinimumCompletionTarget :=
  T.toMinimumCompletionTarget

end MinimumCompletionTarget

/-- Universal-property bridge target for the internal/classical comparison
lane. These obligations remain intentionally Prop-shaped here. -/
structure UniversalBridgeTarget where
  commonPresentationPackage : Prop
  piZeroComparisonBridge : Prop
  infinityComparisonBridge : Prop

namespace UniversalBridgeTarget

def ofFields
    (commonPresentationPackage : Prop)
    (piZeroComparisonBridge : Prop)
    (infinityComparisonBridge : Prop) :
    UniversalBridgeTarget where
  commonPresentationPackage := commonPresentationPackage
  piZeroComparisonBridge := piZeroComparisonBridge
  infinityComparisonBridge := infinityComparisonBridge

end UniversalBridgeTarget

/-- Comparison-isomorphism target for the manuscript's `\phi` lane. The actual
comparison content is intentionally left as Prop fields in the current scope. -/
structure PhiEquivalenceTarget where
  sourceComparisonCompatibility : Prop
  targetComparisonCompatibility : Prop
  comparisonIsoCompatibility : Prop

namespace PhiEquivalenceTarget

def ofFields
    (sourceComparisonCompatibility : Prop)
    (targetComparisonCompatibility : Prop)
    (comparisonIsoCompatibility : Prop) :
    PhiEquivalenceTarget where
  sourceComparisonCompatibility := sourceComparisonCompatibility
  targetComparisonCompatibility := targetComparisonCompatibility
  comparisonIsoCompatibility := comparisonIsoCompatibility

end PhiEquivalenceTarget

/-- Boundary-presentation target: a syntactic presentation together with the
two generic boundary-side contracts it induces. -/
structure BoundaryPresentationTheoremTarget (setup : RewriteCalculusSetup.{u}) where
  presentation : SyntacticBoundaryPresentation setup
  boundaryAdminContract : BoundaryAdminCodeContract.{u, u} setup
  externalOutContract : ExternalOutCodeContract.{u, u} setup
  boundaryAdmin_from_presentation :
    boundaryAdminContract = presentation.toBoundaryAdminCodeContract
  externalOut_from_presentation :
    externalOutContract = presentation.toExternalOutCodeContract

namespace BoundaryPresentationTheoremTarget

/-- Any concrete syntactic presentation fills the corresponding boundary
presentation target immediately. -/
def ofPresentation (P : SyntacticBoundaryPresentation setup) :
    BoundaryPresentationTheoremTarget setup where
  presentation := P
  boundaryAdminContract := P.toBoundaryAdminCodeContract
  externalOutContract := P.toExternalOutCodeContract
  boundaryAdmin_from_presentation := rfl
  externalOut_from_presentation := rfl

end BoundaryPresentationTheoremTarget

/-- Syntactic boundary presentations already yield the quotient-realization
holography target via the existing bridge theorem. -/
structure SyntacticBoundaryPresentationHolographyTarget
    (setup : RewriteCalculusSetup.{u}) where
  boundaryPresentation : BoundaryPresentationTheoremTarget setup
  quotientRealization : FrontierQuotientRealization.{u, u} setup
  quotientRealization_from_presentation :
    quotientRealization =
      theorem_syntactic_boundary_presentation_gives_frontier_quotient_realization
        boundaryPresentation.presentation

namespace SyntacticBoundaryPresentationHolographyTarget

def ofPresentation (P : SyntacticBoundaryPresentation setup) :
    SyntacticBoundaryPresentationHolographyTarget setup where
  boundaryPresentation := BoundaryPresentationTheoremTarget.ofPresentation P
  quotientRealization :=
    theorem_syntactic_boundary_presentation_gives_frontier_quotient_realization P
  quotientRealization_from_presentation := rfl

end SyntacticBoundaryPresentationHolographyTarget

/-- Comparison-to-boundary faithfulness target: a quotient realization detects
boundary/admin equivalence exactly. This is a thin theorem-target wrapper over
the existing quotient-realization interface. -/
structure ComparisonToBoundaryFaithfulnessTarget
    (Q : FrontierQuotientRealization.{u, v} setup) where
  faithful_on_boundary :
    ∀ {w₁ w₂ : FrontierWord setup},
      Q.realize w₁ = Q.realize w₂ → FrontierWord.Equiv w₁ w₂
  realize_eq_iff_boundary :
    ∀ {w₁ w₂ : FrontierWord setup},
      Q.realize w₁ = Q.realize w₂ ↔ FrontierWord.Equiv w₁ w₂

namespace ComparisonToBoundaryFaithfulnessTarget

def ofQuotientRealization
    (Q : FrontierQuotientRealization.{u, v} setup) :
    ComparisonToBoundaryFaithfulnessTarget Q where
  faithful_on_boundary := Q.faithful
  realize_eq_iff_boundary := Q.realize_eq_iff_equiv

end ComparisonToBoundaryFaithfulnessTarget

/-- Boundary-presentation to residue/frontier quotient target. This threads a
syntactic presentation through the existing quotient-realization bridge and
packages the induced faithfulness target. -/
structure BoundaryPresentationToResidueQuotientTarget
    (setup : RewriteCalculusSetup.{u}) where
  holographyTarget : SyntacticBoundaryPresentationHolographyTarget setup
  comparisonFaithfulness :
    ComparisonToBoundaryFaithfulnessTarget holographyTarget.quotientRealization

namespace BoundaryPresentationToResidueQuotientTarget

def ofPresentation (P : SyntacticBoundaryPresentation setup) :
    BoundaryPresentationToResidueQuotientTarget setup where
  holographyTarget := SyntacticBoundaryPresentationHolographyTarget.ofPresentation P
  comparisonFaithfulness :=
    ComparisonToBoundaryFaithfulnessTarget.ofQuotientRealization _

end BoundaryPresentationToResidueQuotientTarget

/-- Realized-comparison reconstruction target: once a quotient realization is
fixed, equal realized images recover boundary/admin equivalence of the
underlying completed reconstruction records. -/
structure RealizedComparisonReconstructsBoundaryTarget
    (Q : FrontierQuotientRealization.{u, v} setup)
    (D : HolographicReconstructionData setup) where
  reconstructs_boundary :
    ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      Q.realize (D.toFrontierWord R₁) = Q.realize (D.toFrontierWord R₂) ↔
        FrontierWord.Equiv (D.toFrontierWord R₁) (D.toFrontierWord R₂)

namespace RealizedComparisonReconstructsBoundaryTarget

def ofQuotientRealization
    (Q : FrontierQuotientRealization.{u, v} setup)
    (D : HolographicReconstructionData setup) :
    RealizedComparisonReconstructsBoundaryTarget Q D where
  reconstructs_boundary := by
    intro R₁ R₂
    exact holographic_reconstruction_via_quotient_realization Q D

end RealizedComparisonReconstructsBoundaryTarget

/-- CanNF equality-detection target. This is the internal theorem surface used
later in the manuscript spine to reduce equality to canonical normalization. -/
structure CanNFEqualityDetectionTarget (C : CanNF setup) where
  detects_equality :
    ∀ (R₁ R₂ : CompletedReconstructionRecord setup),
      C.normalize R₁ = C.normalize R₂ ↔
        FrontierWord.Equiv
          (C.assignment.assign R₁).frontier
          (C.assignment.assign R₂).frontier

namespace CanNFEqualityDetectionTarget

def ofCanNF (C : CanNF setup) :
    CanNFEqualityDetectionTarget C where
  detects_equality := C.CanNF_detects_equality

end CanNFEqualityDetectionTarget

/-- Manuscript theorem-target surface for the canonical reconstruction engine
(Phase 3B items 3–10). Packages the `CanonicalReconstructionEngine` as an
explicit manuscript obligation carrier.

Field **(H)** carries a `FrontierWordCompleteNormalizer` closed by
`semanticQuotientFrontierWordCompleteNormalizer` (see `INV CanNF-Contract`).
This is extensional/semantic quotient closure, not the executable CanNF
algorithm. -/
structure CanonicalReconstructionEngineTarget (setup : RewriteCalculusSetup.{u}) where
  engine : CanonicalReconstructionEngine setup

namespace CanonicalReconstructionEngineTarget

/-- Construct a `CanonicalReconstructionEngineTarget` from the current LayerB
development. The `canNF_norm` argument supplies the concrete
`FrontierWordCompleteNormalizer` for field H. -/
noncomputable def ofCurrentDevelopment
    {setup : RewriteCalculusSetup.{u}}
    (canNF_norm : FrontierWordCompleteNormalizer setup) :
    CanonicalReconstructionEngineTarget setup where
  engine := CanonicalReconstructionEngine.ofCurrentDevelopment canNF_norm

/-- Construct a `CanonicalReconstructionEngineTarget` using the
**semantic quotient normalizer** (`semanticQuotientFrontierWordCompleteNormalizer`).
This provides extensional/semantic CanNF closure — not executable algorithmic
normalization. Use `ofCurrentDevelopment` with a `ComputationalFrontierNormalizer`
for an algorithmic upgrade. -/
noncomputable def ofClosedCanNF
    {setup : RewriteCalculusSetup.{u}} :
    CanonicalReconstructionEngineTarget setup where
  engine := CanonicalReconstructionEngine.ofClosedCanNF

/-- Construct a `CanonicalReconstructionEngineTarget` from a proof-relevant
`ComputationalFrontierNormalizer`, exposing the executable CanNF upgrade path
at the manuscript-wrapper layer. -/
noncomputable def ofComputationalCanNF
    {setup : RewriteCalculusSetup.{u}}
    (N : ComputationalFrontierNormalizer setup) :
    CanonicalReconstructionEngineTarget setup where
  engine := CanonicalReconstructionEngine.ofComputationalCanNF N

end CanonicalReconstructionEngineTarget

/-- Named theorem-target surface for the hard slot-level reconstruction step in
the structured-comparison lane. This remains Prop-shaped until the honest
comparison-slot reconstruction theorem is supplied. -/
structure StructuredComparisonSlotSeparationTarget
    {α : Type v}
    (_comparison : CompletedReconstructionRecord setup → α) where
  slotSeparationTarget : Prop

namespace StructuredComparisonSlotSeparationTarget

def ofProp
    {α : Type v}
    (comparison : CompletedReconstructionRecord setup → α)
    (slotSeparationTarget : Prop) :
    StructuredComparisonSlotSeparationTarget comparison where
  slotSeparationTarget := slotSeparationTarget

end StructuredComparisonSlotSeparationTarget

/-- Hard-input theorem target for the comparison-to-boundary attack: once the
structured comparison data determine the visible boundary, the remaining steps
can be discharged by the existing internal holography / CanNF spine. -/
structure StructuredComparisonDeterminesVisibleBoundaryTarget
    {α : Type v} {β : Sort _}
    (comparison : CompletedReconstructionRecord setup → α)
    (visibleBoundary : CompletedReconstructionRecord setup → β) where
  slotSeparation : StructuredComparisonSlotSeparationTarget comparison
  determinesVisibleBoundary :
    ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      comparison R₁ = comparison R₂ → visibleBoundary R₁ = visibleBoundary R₂

namespace StructuredComparisonDeterminesVisibleBoundaryTarget

def ofImplication
    {α : Type v} {β : Sort _}
    (comparison : CompletedReconstructionRecord setup → α)
    (visibleBoundary : CompletedReconstructionRecord setup → β)
    (slotSeparation : StructuredComparisonSlotSeparationTarget comparison)
    (determinesVisibleBoundary :
      ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
        comparison R₁ = comparison R₂ → visibleBoundary R₁ = visibleBoundary R₂) :
    StructuredComparisonDeterminesVisibleBoundaryTarget comparison visibleBoundary where
  slotSeparation := slotSeparation
  determinesVisibleBoundary := determinesVisibleBoundary

end StructuredComparisonDeterminesVisibleBoundaryTarget

/-- Downstream theorem target asserting that visible-boundary equality already
determines the frontier-word equality seen by the current CanNF layer. -/
structure VisibleBoundaryDeterminesFrontierWordTarget
    {β : Sort _}
    (visibleBoundary : CompletedReconstructionRecord setup → β)
    (frontierWord : CompletedReconstructionRecord setup → FrontierWord setup) where
  determinesFrontierWord :
    ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      visibleBoundary R₁ = visibleBoundary R₂ →
        FrontierWord.Equiv (frontierWord R₁) (frontierWord R₂)

namespace VisibleBoundaryDeterminesFrontierWordTarget

def ofImplication
    {β : Sort _}
    (visibleBoundary : CompletedReconstructionRecord setup → β)
    (frontierWord : CompletedReconstructionRecord setup → FrontierWord setup)
    (determinesFrontierWord :
      ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
        visibleBoundary R₁ = visibleBoundary R₂ →
          FrontierWord.Equiv (frontierWord R₁) (frontierWord R₂)) :
    VisibleBoundaryDeterminesFrontierWordTarget visibleBoundary frontierWord where
  determinesFrontierWord := determinesFrontierWord

end VisibleBoundaryDeterminesFrontierWordTarget

/-- SETUP-BRIDGE-TARGET for the remaining preferred-visible-boundary to
concrete generated-trace seam.

This is intentionally narrower than a full preferred-to-concrete record map:
the current generated trace/frontier layer only needs a concrete frontier-word
assignment on preferred completed records, together with preservation of the
preferred frontier equivalence and explicit zero-boundary proofs on the
concrete side. The target is parameterized by the preferred reconstruction map,
so compatibility with the canonical/preferred frontier words is part of the
target surface itself. -/
structure PreferredVisibleBoundaryToConcreteZeroBoundaryTarget
    {primitive : NamedPrimitiveInterfacePresentation}
    {presentation : NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (RI : Type v) [DecidableEq RI] [LinearOrder RI]
    (preferredFrontierWord :
      CompletedReconstructionRecord
          (FoundationsBoundaryBridgeAuxiliaryData.PreferredFoundationsBridgeSetup
            presentation.toDoctrine aux) →
        FrontierWord
          (FoundationsBoundaryBridgeAuxiliaryData.PreferredFoundationsBridgeSetup
            presentation.toDoctrine aux)) where
  concreteFrontierWord :
    CompletedReconstructionRecord
        (FoundationsBoundaryBridgeAuxiliaryData.PreferredFoundationsBridgeSetup
          presentation.toDoctrine aux) →
      FrontierWord (concreteBoundaryMinimalSetup RI)
  preserves_frontier_equiv :
    ∀ {R₁ R₂ :
      CompletedReconstructionRecord
        (FoundationsBoundaryBridgeAuxiliaryData.PreferredFoundationsBridgeSetup
          presentation.toDoctrine aux)},
      FrontierWord.Equiv (preferredFrontierWord R₁) (preferredFrontierWord R₂) →
        FrontierWord.Equiv (concreteFrontierWord R₁) (concreteFrontierWord R₂)
  zero_boundary_source :
    ∀ R,
      (concreteFrontierWord R).residue.X =
        (0 : Multiset (ConcreteBoundaryAtom RI))
  zero_boundary_target :
    ∀ R,
      (concreteFrontierWord R).residue.Y =
        (0 : Multiset (ConcreteBoundaryAtom RI))

/-- CanNF equality-detection target specialized to the current notion of
"morphism equality" available in the scaffold: frontier-word equivalence of the
residue/frontier representatives. -/
structure CanNFEqualityDetectsMorphismEqualityTarget
    (C : CanNF setup)
    (frontierWord : CompletedReconstructionRecord setup → FrontierWord setup) where
  detectsMorphismEquality :
    ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      C.normalize R₁ = C.normalize R₂ →
        FrontierWord.Equiv (frontierWord R₁) (frontierWord R₂)

namespace CanNFEqualityDetectsMorphismEqualityTarget

def ofImplication
    (C : CanNF setup)
    (frontierWord : CompletedReconstructionRecord setup → FrontierWord setup)
    (detectsMorphismEquality :
      ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
        C.normalize R₁ = C.normalize R₂ →
          FrontierWord.Equiv (frontierWord R₁) (frontierWord R₂)) :
    CanNFEqualityDetectsMorphismEqualityTarget C frontierWord where
  detectsMorphismEquality := detectsMorphismEquality

def ofCanNFEqualityDetection
    (C : CanNF setup) :
    CanNFEqualityDetectsMorphismEqualityTarget C
      (fun R => (C.assignment.assign R).frontier) where
  detectsMorphismEquality := by
    intro R₁ R₂ hEq
    exact (C.CanNF_detects_equality R₁ R₂).1 hEq

end CanNFEqualityDetectsMorphismEqualityTarget

/-- Decomposition target for comparison-to-boundary faithfulness. The only hard
input is the comparison-to-visible-boundary reconstruction theorem; the
remaining fields package the already-provable downstream consequences. -/
structure ComparisonToBoundaryFaithfulnessDecompositionTarget
    {α : Type v} {β : Sort _}
    (comparison : CompletedReconstructionRecord setup → α)
    (visibleBoundary : CompletedReconstructionRecord setup → β)
    (frontierWord : CompletedReconstructionRecord setup → FrontierWord setup)
    (C : CanNF setup) where
  structuredComparisonDeterminesVisibleBoundary :
    StructuredComparisonDeterminesVisibleBoundaryTarget comparison visibleBoundary
  visibleBoundaryDeterminesFrontierWord :
    VisibleBoundaryDeterminesFrontierWordTarget visibleBoundary frontierWord
  canNFEqualityDetectsMorphismEquality :
    CanNFEqualityDetectsMorphismEqualityTarget C frontierWord
  comparisonToCanNFEquality :
    ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      comparison R₁ = comparison R₂ → C.normalize R₁ = C.normalize R₂
  comparisonToBoundaryFaithfulness :
    ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      comparison R₁ = comparison R₂ → FrontierWord.Equiv (frontierWord R₁) (frontierWord R₂)

namespace ComparisonToBoundaryFaithfulnessDecompositionTarget

def ofFields
    {α : Type v} {β : Sort _}
    (comparison : CompletedReconstructionRecord setup → α)
    (visibleBoundary : CompletedReconstructionRecord setup → β)
    (frontierWord : CompletedReconstructionRecord setup → FrontierWord setup)
    (C : CanNF setup)
    (structuredComparisonDeterminesVisibleBoundary :
      StructuredComparisonDeterminesVisibleBoundaryTarget comparison visibleBoundary)
    (visibleBoundaryDeterminesFrontierWord :
      VisibleBoundaryDeterminesFrontierWordTarget visibleBoundary frontierWord)
    (canNFEqualityDetectsMorphismEquality :
      CanNFEqualityDetectsMorphismEqualityTarget C frontierWord)
    (comparisonToCanNFEquality :
      ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
        comparison R₁ = comparison R₂ → C.normalize R₁ = C.normalize R₂)
    (comparisonToBoundaryFaithfulness :
      ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
        comparison R₁ = comparison R₂ → FrontierWord.Equiv (frontierWord R₁) (frontierWord R₂)) :
    ComparisonToBoundaryFaithfulnessDecompositionTarget comparison visibleBoundary frontierWord C where
  structuredComparisonDeterminesVisibleBoundary := structuredComparisonDeterminesVisibleBoundary
  visibleBoundaryDeterminesFrontierWord := visibleBoundaryDeterminesFrontierWord
  canNFEqualityDetectsMorphismEquality := canNFEqualityDetectsMorphismEquality
  comparisonToCanNFEquality := comparisonToCanNFEquality
  comparisonToBoundaryFaithfulness := comparisonToBoundaryFaithfulness

end ComparisonToBoundaryFaithfulnessDecompositionTarget

/-- Internal comparison-faithfulness target: a chosen internal comparison on
completed records is detected exactly by a chosen CanNF package. -/
structure InternalComparisonFaithfulnessTarget
    {α : Type v}
    (comparison : CompletedReconstructionRecord setup → α)
    (C : CanNF setup) where
  comparison_detected_by_cannf :
    ∀ (R₁ R₂ : CompletedReconstructionRecord setup),
      comparison R₁ = comparison R₂ ↔ C.normalize R₁ = C.normalize R₂

namespace InternalComparisonFaithfulnessTarget

def ofIff
    {α : Type v}
    (comparison : CompletedReconstructionRecord setup → α)
    (C : CanNF setup)
    (h :
      ∀ (R₁ R₂ : CompletedReconstructionRecord setup),
        comparison R₁ = comparison R₂ ↔ C.normalize R₁ = C.normalize R₂) :
    InternalComparisonFaithfulnessTarget comparison C where
  comparison_detected_by_cannf := h

end InternalComparisonFaithfulnessTarget

/-- Summary target for the internal manuscript spine. It packages the existing
trace-category laws, a chosen boundary-presentation lane, the resulting
comparison-to-boundary faithfulness target, an internal comparison-faithfulness
target, CanNF equality detection, and the canonical reconstruction engine
(Phase 3B items 3–10). -/
structure InternalManuscriptSpineTarget
    {α : Type v}
    (setup : RewriteCalculusSetup.{u})
    (P : SyntacticBoundaryPresentation setup)
    (comparison : CompletedReconstructionRecord setup → α)
    (C : CanNF setup) where
  traceCategory : TraceCategoryLawsTarget setup
  boundaryPresentation : BoundaryPresentationTheoremTarget setup
  comparisonToBoundary :
    ComparisonToBoundaryFaithfulnessTarget
      (SyntacticBoundaryPresentationHolographyTarget.ofPresentation P).quotientRealization
  internalComparisonFaithfulness : InternalComparisonFaithfulnessTarget comparison C
  canNFEqualityDetection : CanNFEqualityDetectionTarget C
  canonicalReconstructionEngine : CanonicalReconstructionEngineTarget setup

namespace InternalManuscriptSpineTarget

noncomputable def ofPresentationAndCanNF
    {α : Type v}
    (P : SyntacticBoundaryPresentation setup)
    (comparison : CompletedReconstructionRecord setup → α)
    (C : CanNF setup)
    (hInternal : InternalComparisonFaithfulnessTarget comparison C)
    (canNF_norm : FrontierWordCompleteNormalizer setup) :
    InternalManuscriptSpineTarget setup P comparison C where
  traceCategory := TraceCategoryLawsTarget.ofCurrentDevelopment setup
  boundaryPresentation := BoundaryPresentationTheoremTarget.ofPresentation P
  comparisonToBoundary :=
    ComparisonToBoundaryFaithfulnessTarget.ofQuotientRealization _
  internalComparisonFaithfulness := hInternal
  canNFEqualityDetection := CanNFEqualityDetectionTarget.ofCanNF C
  canonicalReconstructionEngine :=
    CanonicalReconstructionEngineTarget.ofCurrentDevelopment canNF_norm

/-- **Semantically closed constructor**: uses
`semanticQuotientFrontierWordCompleteNormalizer` for the engine's H field.
Extensional/semantic CanNF closure only — not executable algorithmic
normalization. No external obligation parameter needed. -/
noncomputable def ofPresentationClosed
    {α : Type v}
    (P : SyntacticBoundaryPresentation setup)
    (comparison : CompletedReconstructionRecord setup → α)
    (C : CanNF setup)
    (hInternal : InternalComparisonFaithfulnessTarget comparison C) :
    InternalManuscriptSpineTarget setup P comparison C where
  traceCategory := TraceCategoryLawsTarget.ofCurrentDevelopment setup
  boundaryPresentation := BoundaryPresentationTheoremTarget.ofPresentation P
  comparisonToBoundary :=
    ComparisonToBoundaryFaithfulnessTarget.ofQuotientRealization _
  internalComparisonFaithfulness := hInternal
  canNFEqualityDetection := CanNFEqualityDetectionTarget.ofCanNF C
  canonicalReconstructionEngine := CanonicalReconstructionEngineTarget.ofClosedCanNF

/-- **Computationally closed constructor**: packages the internal spine using a
proof-relevant `ComputationalFrontierNormalizer`, so the reconstruction engine
is assembled through the executable CanNF route rather than the semantic
quotient closure. -/
noncomputable def ofPresentationComputational
    {α : Type v}
    (P : SyntacticBoundaryPresentation setup)
    (comparison : CompletedReconstructionRecord setup → α)
    (C : CanNF setup)
    (hInternal : InternalComparisonFaithfulnessTarget comparison C)
    (N : ComputationalFrontierNormalizer setup) :
    InternalManuscriptSpineTarget setup P comparison C where
  traceCategory := TraceCategoryLawsTarget.ofCurrentDevelopment setup
  boundaryPresentation := BoundaryPresentationTheoremTarget.ofPresentation P
  comparisonToBoundary :=
    ComparisonToBoundaryFaithfulnessTarget.ofQuotientRealization _
  internalComparisonFaithfulness := hInternal
  canNFEqualityDetection := CanNFEqualityDetectionTarget.ofCanNF C
  canonicalReconstructionEngine :=
    CanonicalReconstructionEngineTarget.ofComputationalCanNF N

end InternalManuscriptSpineTarget

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc