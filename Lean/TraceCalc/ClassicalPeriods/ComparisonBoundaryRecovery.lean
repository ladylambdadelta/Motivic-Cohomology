import TraceCalc.ClassicalPeriods.FramedPeriodsConcrete
import TraceCalc.ClassicalPeriods.GeneratorRealizationTable
import TraceCalc.LayerB.RealObjects.InternalManuscriptTargets

universe u v w

namespace TraceCalc
namespace ClassicalPeriods

inductive GeneratorRowTag
  | corr
  | loc
  | nis
  | a1
  | env
  deriving DecidableEq, Repr

/-- Core symbolic slots tracked uniformly across each generator row in the
table-level capsule. -/
inductive GeneratorCoreSlotLabel
  | source
  | target
  | betti
  | deRham
  | comparison
  deriving DecidableEq, Repr

/-- Five-row slot universe used by the generator-table recovery capsule: each
constructor names a row together with one of the five core symbolic slot roles.
-/
inductive GeneratorTableSlot
  | corr (label : GeneratorCoreSlotLabel)
  | loc (label : GeneratorCoreSlotLabel)
  | nis (label : GeneratorCoreSlotLabel)
  | a1 (label : GeneratorCoreSlotLabel)
  | env (label : GeneratorCoreSlotLabel)
  deriving DecidableEq, Repr

namespace GeneratorTableSlot

def row : GeneratorTableSlot → GeneratorRowTag
  | .corr _ => .corr
  | .loc _ => .loc
  | .nis _ => .nis
  | .a1 _ => .a1
  | .env _ => .env

def label : GeneratorTableSlot → GeneratorCoreSlotLabel
  | .corr label => label
  | .loc label => label
  | .nis label => label
  | .a1 label => label
  | .env label => label

def ofRowAndLabel (row : GeneratorRowTag) (label : GeneratorCoreSlotLabel) : GeneratorTableSlot :=
  match row with
  | .corr => .corr label
  | .loc => .loc label
  | .nis => .nis label
  | .a1 => .a1 label
  | .env => .env label

@[simp] theorem row_ofRowAndLabel
    (row : GeneratorRowTag) (label : GeneratorCoreSlotLabel) :
    (ofRowAndLabel row label).row = row := by
  cases row <;> rfl

@[simp] theorem label_ofRowAndLabel
    (row : GeneratorRowTag) (label : GeneratorCoreSlotLabel) :
    (ofRowAndLabel row label).label = label := by
  cases row <;> rfl

end GeneratorTableSlot

/-- Symbolic roles currently tracked in the comparison-side slot layer. The
`framed` and `scalar` cases are included so downstream statements can speak a
uniform label language, even though the present slot package does not yet carry
those names as data. -/
inductive ComparisonSlotLabel
  | source
  | target
  | betti
  | deRham
  | comparison
  | framed
  | scalar
  deriving DecidableEq, Repr

/-- Named slot data carried by a structured comparison package before boundary
reconstruction is attempted. These are the comparison-side labels that later
recovery theorems must separate and transport faithfully. -/
structure StructuredComparisonSlotData where
  sourceSlot : String
  targetSlot : String
  bettiSlot : String
  deRhamSlot : String
  comparisonSlot : String

namespace StructuredComparisonSlotData

def coreLabel
  (slotData : StructuredComparisonSlotData)
  (label : GeneratorCoreSlotLabel) : String :=
  match label with
  | .source => slotData.sourceSlot
  | .target => slotData.targetSlot
  | .betti => slotData.bettiSlot
  | .deRham => slotData.deRhamSlot
  | .comparison => slotData.comparisonSlot

@[simp] theorem coreLabel_source
  (slotData : StructuredComparisonSlotData) :
  slotData.coreLabel .source = slotData.sourceSlot := rfl

@[simp] theorem coreLabel_target
  (slotData : StructuredComparisonSlotData) :
  slotData.coreLabel .target = slotData.targetSlot := rfl

@[simp] theorem coreLabel_betti
  (slotData : StructuredComparisonSlotData) :
  slotData.coreLabel .betti = slotData.bettiSlot := rfl

@[simp] theorem coreLabel_deRham
  (slotData : StructuredComparisonSlotData) :
  slotData.coreLabel .deRham = slotData.deRhamSlot := rfl

@[simp] theorem coreLabel_comparison
  (slotData : StructuredComparisonSlotData) :
  slotData.coreLabel .comparison = slotData.comparisonSlot := rfl

/-- Partial symbolic label lookup for the current comparison-slot package. The
`framed` and `scalar` names are not yet present at this layer, so they return
`none`. -/
def label?
  (slotData : StructuredComparisonSlotData)
  (label : ComparisonSlotLabel) : Option String :=
  match label with
  | .source => some slotData.sourceSlot
  | .target => some slotData.targetSlot
  | .betti => some slotData.bettiSlot
  | .deRham => some slotData.deRhamSlot
  | .comparison => some slotData.comparisonSlot
  | .framed => none
  | .scalar => none

@[simp] theorem label?_source
  (slotData : StructuredComparisonSlotData) :
  slotData.label? .source = some slotData.sourceSlot := rfl

@[simp] theorem label?_target
  (slotData : StructuredComparisonSlotData) :
  slotData.label? .target = some slotData.targetSlot := rfl

@[simp] theorem label?_betti
  (slotData : StructuredComparisonSlotData) :
  slotData.label? .betti = some slotData.bettiSlot := rfl

@[simp] theorem label?_deRham
  (slotData : StructuredComparisonSlotData) :
  slotData.label? .deRham = some slotData.deRhamSlot := rfl

@[simp] theorem label?_comparison
  (slotData : StructuredComparisonSlotData) :
  slotData.label? .comparison = some slotData.comparisonSlot := rfl

@[simp] theorem label?_framed
  (slotData : StructuredComparisonSlotData) :
  slotData.label? .framed = none := rfl

@[simp] theorem label?_scalar
  (slotData : StructuredComparisonSlotData) :
  slotData.label? .scalar = none := rfl

/-- Minimal symbolic separation condition on a single comparison-slot bundle. -/
def Separated (slotData : StructuredComparisonSlotData) : Prop :=
  slotData.sourceSlot ≠ slotData.targetSlot ∧
    slotData.bettiSlot ≠ slotData.deRhamSlot ∧
    slotData.comparisonSlot ≠ slotData.sourceSlot ∧
    slotData.comparisonSlot ≠ slotData.targetSlot

instance instDecidableSeparated
    (slotData : StructuredComparisonSlotData) :
    Decidable slotData.Separated := by
  unfold StructuredComparisonSlotData.Separated
  infer_instance

theorem sourceTargetSeparated
    {slotData : StructuredComparisonSlotData}
    (h : slotData.Separated) :
    slotData.sourceSlot ≠ slotData.targetSlot :=
  h.1

theorem bettiDeRhamSeparated
    {slotData : StructuredComparisonSlotData}
    (h : slotData.Separated) :
    slotData.bettiSlot ≠ slotData.deRhamSlot :=
  h.2.1

theorem comparisonSourceSeparated
    {slotData : StructuredComparisonSlotData}
    (h : slotData.Separated) :
    slotData.comparisonSlot ≠ slotData.sourceSlot :=
  h.2.2.1

theorem comparisonTargetSeparated
    {slotData : StructuredComparisonSlotData}
    (h : slotData.Separated) :
    slotData.comparisonSlot ≠ slotData.targetSlot :=
  h.2.2.2

end StructuredComparisonSlotData

/-- Visible roles in the boundary-port layer recovered from comparison data. -/
inductive VisibleBoundaryPortLabel
  | source
  | target
  | betti
  | deRham
  deriving DecidableEq, Repr

/-- Visible boundary ports recovered from the structured comparison slot layer.
This remains lightweight: it is only the port-level boundary view, not the full
visible-boundary object used downstream. -/
structure VisibleBoundaryPortData where
  sourcePort : String
  targetPort : String
  bettiPort : String
  deRhamPort : String

namespace VisibleBoundaryPortData

def label
    (portData : VisibleBoundaryPortData)
    (label : VisibleBoundaryPortLabel) : String :=
  match label with
  | .source => portData.sourcePort
  | .target => portData.targetPort
  | .betti => portData.bettiPort
  | .deRham => portData.deRhamPort

@[simp] theorem label_source
    (portData : VisibleBoundaryPortData) :
    portData.label .source = portData.sourcePort := rfl

@[simp] theorem label_target
    (portData : VisibleBoundaryPortData) :
    portData.label .target = portData.targetPort := rfl

@[simp] theorem label_betti
    (portData : VisibleBoundaryPortData) :
    portData.label .betti = portData.bettiPort := rfl

@[simp] theorem label_deRham
    (portData : VisibleBoundaryPortData) :
    portData.label .deRham = portData.deRhamPort := rfl

/-- Port-level separation demanded by the visible-boundary bookkeeping. -/
def Separated (portData : VisibleBoundaryPortData) : Prop :=
  portData.sourcePort ≠ portData.targetPort ∧
    portData.bettiPort ≠ portData.deRhamPort

instance instDecidableSeparated
    (portData : VisibleBoundaryPortData) :
    Decidable portData.Separated := by
  unfold VisibleBoundaryPortData.Separated
  infer_instance

theorem sourceTargetSeparated
    {portData : VisibleBoundaryPortData}
    (h : portData.Separated) :
    portData.sourcePort ≠ portData.targetPort :=
  h.1

theorem bettiDeRhamSeparated
    {portData : VisibleBoundaryPortData}
    (h : portData.Separated) :
    portData.bettiPort ≠ portData.deRhamPort :=
  h.2

end VisibleBoundaryPortData

namespace StructuredComparisonSlotData

/-- Canonical visible-boundary port labels extracted from the current
comparison-slot data. -/
def toVisibleBoundaryPortData
    (slotData : StructuredComparisonSlotData) : VisibleBoundaryPortData where
  sourcePort := slotData.sourceSlot
  targetPort := slotData.targetSlot
  bettiPort := slotData.bettiSlot
  deRhamPort := slotData.deRhamSlot

@[simp] theorem toVisibleBoundaryPortData_source
    (slotData : StructuredComparisonSlotData) :
    slotData.toVisibleBoundaryPortData.sourcePort = slotData.sourceSlot := rfl

@[simp] theorem toVisibleBoundaryPortData_target
    (slotData : StructuredComparisonSlotData) :
    slotData.toVisibleBoundaryPortData.targetPort = slotData.targetSlot := rfl

@[simp] theorem toVisibleBoundaryPortData_betti
    (slotData : StructuredComparisonSlotData) :
    slotData.toVisibleBoundaryPortData.bettiPort = slotData.bettiSlot := rfl

@[simp] theorem toVisibleBoundaryPortData_deRham
    (slotData : StructuredComparisonSlotData) :
    slotData.toVisibleBoundaryPortData.deRhamPort = slotData.deRhamSlot := rfl

theorem toVisibleBoundaryPortData_separated
    {slotData : StructuredComparisonSlotData}
    (h : slotData.Separated) :
    slotData.toVisibleBoundaryPortData.Separated :=
  ⟨h.1, h.2.1⟩

end StructuredComparisonSlotData

/-- Precise port-level separation target induced by a recovered slot package. -/
def PortLabelSeparationTargetOfSlots
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData) : Prop :=
  ∀ R, (slotData R).toVisibleBoundaryPortData.Separated

/-- Smallest remaining symbolic input for comparison-side port-label separation:
every reconstructed comparison-slot bundle has the label separations needed by
the slot-recovery path. -/
structure SymbolicPortLabelSeparationTarget
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData) where
  theoremTarget : ∀ R, (slotData R).Separated

namespace SymbolicPortLabelSeparationTarget

theorem portLabelSeparationTargetOfSlots
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData}
    (symbolic : SymbolicPortLabelSeparationTarget slotData) :
    PortLabelSeparationTargetOfSlots slotData := by
  intro R
  exact StructuredComparisonSlotData.toVisibleBoundaryPortData_separated
    (symbolic.theoremTarget R)

end SymbolicPortLabelSeparationTarget

/-- Hard comparison-side hypothesis: the named slots in the structured
comparison package are genuinely separated. This is where port-label separation
and non-collision of the comparison/framed/scalar bookkeeping live. -/
structure ComparisonSlotSeparationTarget
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData) where
  sourceTargetSeparated :
    ∀ R, (slotData R).sourceSlot ≠ (slotData R).targetSlot
  bettiDeRhamSeparated :
    ∀ R, (slotData R).bettiSlot ≠ (slotData R).deRhamSlot
  comparisonSourceSeparated :
    ∀ R, (slotData R).comparisonSlot ≠ (slotData R).sourceSlot
  comparisonTargetSeparated :
    ∀ R, (slotData R).comparisonSlot ≠ (slotData R).targetSlot

namespace ComparisonSlotSeparationTarget

def ofSymbolicPortLabelSeparation
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData}
    (symbolic : SymbolicPortLabelSeparationTarget slotData) :
    ComparisonSlotSeparationTarget slotData where
  sourceTargetSeparated :=
    fun R => StructuredComparisonSlotData.sourceTargetSeparated (symbolic.theoremTarget R)
  bettiDeRhamSeparated :=
    fun R => StructuredComparisonSlotData.bettiDeRhamSeparated (symbolic.theoremTarget R)
  comparisonSourceSeparated :=
    fun R => StructuredComparisonSlotData.comparisonSourceSeparated (symbolic.theoremTarget R)
  comparisonTargetSeparated :=
    fun R => StructuredComparisonSlotData.comparisonTargetSeparated (symbolic.theoremTarget R)

end ComparisonSlotSeparationTarget

namespace CorrGeneratorRealizationAssignment

def toComparisonBoundarySlotData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : CorrGeneratorRealizationAssignment ctx realization) :
    StructuredComparisonSlotData where
  sourceSlot := assignment.sourceSlotName
  targetSlot := assignment.targetSlotName
  bettiSlot := assignment.bettiSlotName
  deRhamSlot := assignment.deRhamSlotName
  comparisonSlot := assignment.comparisonSlotName

end CorrGeneratorRealizationAssignment

namespace LocGeneratorRealizationAssignment

def toComparisonBoundarySlotData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization) :
    StructuredComparisonSlotData where
  sourceSlot := assignment.ambientSlotName
  targetSlot := assignment.openSlotName
  bettiSlot := assignment.bettiSlotName
  deRhamSlot := assignment.deRhamSlotName
  comparisonSlot := assignment.comparisonSlotName

end LocGeneratorRealizationAssignment

namespace NisGeneratorRealizationAssignment

def toComparisonBoundarySlotData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : NisGeneratorRealizationAssignment ctx realization) :
    StructuredComparisonSlotData where
  sourceSlot := assignment.baseSlotName
  targetSlot := assignment.patchSlotName
  bettiSlot := assignment.bettiSlotName
  deRhamSlot := assignment.deRhamSlotName
  comparisonSlot := assignment.comparisonSlotName

end NisGeneratorRealizationAssignment

namespace A1GeneratorRealizationAssignment

def toComparisonBoundarySlotData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : A1GeneratorRealizationAssignment ctx realization) :
    StructuredComparisonSlotData where
  sourceSlot := assignment.baseSlotName
  targetSlot := assignment.cylinderSlotName
  bettiSlot := assignment.bettiSlotName
  deRhamSlot := assignment.deRhamSlotName
  comparisonSlot := assignment.comparisonSlotName

end A1GeneratorRealizationAssignment

namespace EnvGeneratorRealizationAssignment

def toComparisonBoundarySlotData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization) :
    StructuredComparisonSlotData where
  sourceSlot := assignment.ambientSlotName
  targetSlot := assignment.envelopeSlotName
  bettiSlot := assignment.bettiSlotName
  deRhamSlot := assignment.deRhamSlotName
  comparisonSlot := assignment.comparisonSlotName

end EnvGeneratorRealizationAssignment

structure FiveRowSlotLabelAssignment
    (ctx : ClassicalComparisonContext.{u, v}) where
  corr : StructuredComparisonSlotData
  loc : StructuredComparisonSlotData
  nis : StructuredComparisonSlotData
  a1 : StructuredComparisonSlotData
  env : StructuredComparisonSlotData

/-- Symbolic five-row slot-label package extracted from a generator-realization
table. This stays purely table-level: it records only the designated symbolic
slot bundles for the five manuscript rows. -/
abbrev GeneratorTableSlotLabelAssignment := FiveRowSlotLabelAssignment

namespace FiveRowSlotLabelAssignment

def get
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignment : FiveRowSlotLabelAssignment ctx)
    (row : GeneratorRowTag) : StructuredComparisonSlotData :=
  match row with
  | .corr => assignment.corr
  | .loc => assignment.loc
  | .nis => assignment.nis
  | .a1 => assignment.a1
  | .env => assignment.env

def slotLabel
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignment : FiveRowSlotLabelAssignment ctx)
    (slot : GeneratorTableSlot) : String :=
  match slot with
  | .corr label => (assignment.get .corr).coreLabel label
  | .loc label => (assignment.get .loc).coreLabel label
  | .nis label => (assignment.get .nis).coreLabel label
  | .a1 label => (assignment.get .a1).coreLabel label
  | .env label => (assignment.get .env).coreLabel label

@[simp] theorem slotLabel_ofRowAndLabel
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignment : FiveRowSlotLabelAssignment ctx)
    (row : GeneratorRowTag)
    (label : GeneratorCoreSlotLabel) :
    assignment.slotLabel (GeneratorTableSlot.ofRowAndLabel row label) =
      (assignment.get row).coreLabel label := by
  cases row <;> rfl

@[simp] theorem slotLabel_corr_source
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignment : FiveRowSlotLabelAssignment ctx) :
    assignment.slotLabel (.corr .source) = assignment.corr.sourceSlot := rfl

@[simp] theorem slotLabel_loc_target
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignment : FiveRowSlotLabelAssignment ctx) :
    assignment.slotLabel (.loc .target) = assignment.loc.targetSlot := rfl

@[simp] theorem slotLabel_nis_comparison
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignment : FiveRowSlotLabelAssignment ctx) :
    assignment.slotLabel (.nis .comparison) = assignment.nis.comparisonSlot := rfl

@[simp] theorem slotLabel_a1_betti
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignment : FiveRowSlotLabelAssignment ctx) :
    assignment.slotLabel (.a1 .betti) = assignment.a1.bettiSlot := rfl

@[simp] theorem slotLabel_env_deRham
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignment : FiveRowSlotLabelAssignment ctx) :
    assignment.slotLabel (.env .deRham) = assignment.env.deRhamSlot := rfl

end FiveRowSlotLabelAssignment

/-- Separation data attached directly to a five-row symbolic slot-label
assignment, before choosing any concrete generator-realization table that
realizes those slot bundles. -/
structure GeneratorTableSlotLabelSeparationData
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignment : GeneratorTableSlotLabelAssignment ctx) where
  corrSeparated : assignment.corr.Separated
  locSeparated : assignment.loc.Separated
  nisSeparated : assignment.nis.Separated
  a1Separated : assignment.a1.Separated
  envSeparated : assignment.env.Separated

namespace GeneratorTableSlotLabelSeparationData

theorem separated
    {ctx : ClassicalComparisonContext.{u, v}}
    {assignment : GeneratorTableSlotLabelAssignment ctx}
    (data : GeneratorTableSlotLabelSeparationData assignment)
    (row : GeneratorRowTag) :
    (assignment.get row).Separated := by
  cases row with
  | corr => simpa [FiveRowSlotLabelAssignment.get] using data.corrSeparated
  | loc => simpa [FiveRowSlotLabelAssignment.get] using data.locSeparated
  | nis => simpa [FiveRowSlotLabelAssignment.get] using data.nisSeparated
  | a1 => simpa [FiveRowSlotLabelAssignment.get] using data.a1Separated
  | env => simpa [FiveRowSlotLabelAssignment.get] using data.envSeparated

theorem sourceTargetSeparated
    {ctx : ClassicalComparisonContext.{u, v}}
    {assignment : GeneratorTableSlotLabelAssignment ctx}
    (data : GeneratorTableSlotLabelSeparationData assignment)
    (row : GeneratorRowTag) :
    assignment.slotLabel (GeneratorTableSlot.ofRowAndLabel row .source) ≠
      assignment.slotLabel (GeneratorTableSlot.ofRowAndLabel row .target) := by
  simpa [FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel]
    using (StructuredComparisonSlotData.sourceTargetSeparated (data.separated row))

theorem bettiDeRhamSeparated
    {ctx : ClassicalComparisonContext.{u, v}}
    {assignment : GeneratorTableSlotLabelAssignment ctx}
    (data : GeneratorTableSlotLabelSeparationData assignment)
    (row : GeneratorRowTag) :
    assignment.slotLabel (GeneratorTableSlot.ofRowAndLabel row .betti) ≠
      assignment.slotLabel (GeneratorTableSlot.ofRowAndLabel row .deRham) := by
  simpa [FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel]
    using (StructuredComparisonSlotData.bettiDeRhamSeparated (data.separated row))

theorem comparisonSourceSeparated
    {ctx : ClassicalComparisonContext.{u, v}}
    {assignment : GeneratorTableSlotLabelAssignment ctx}
    (data : GeneratorTableSlotLabelSeparationData assignment)
    (row : GeneratorRowTag) :
    assignment.slotLabel (GeneratorTableSlot.ofRowAndLabel row .comparison) ≠
      assignment.slotLabel (GeneratorTableSlot.ofRowAndLabel row .source) := by
  simpa [FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel]
    using (StructuredComparisonSlotData.comparisonSourceSeparated (data.separated row))

theorem comparisonTargetSeparated
    {ctx : ClassicalComparisonContext.{u, v}}
    {assignment : GeneratorTableSlotLabelAssignment ctx}
    (data : GeneratorTableSlotLabelSeparationData assignment)
    (row : GeneratorRowTag) :
    assignment.slotLabel (GeneratorTableSlot.ofRowAndLabel row .comparison) ≠
      assignment.slotLabel (GeneratorTableSlot.ofRowAndLabel row .target) := by
  simpa [FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel]
    using (StructuredComparisonSlotData.comparisonTargetSeparated (data.separated row))

end GeneratorTableSlotLabelSeparationData

namespace GeneratorRealizationAssignmentTable

def toFiveRowSlotLabelAssignment
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    FiveRowSlotLabelAssignment ctx where
  corr := table.corrAssignment.toComparisonBoundarySlotData
  loc := table.locAssignment.toComparisonBoundarySlotData
  nis := table.nisAssignment.toComparisonBoundarySlotData
  a1 := table.a1Assignment.toComparisonBoundarySlotData
  env := table.envAssignment.toComparisonBoundarySlotData

/-- Table-level alias exposing the five symbolic slot bundles under the
manuscript-facing generator-table name. -/
abbrev toGeneratorTableSlotLabelAssignment
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    GeneratorTableSlotLabelAssignment ctx :=
  table.toFiveRowSlotLabelAssignment

end GeneratorRealizationAssignmentTable

structure SymbolicGeneratorPortLabelWitness
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) where
  corrSeparated : table.corrAssignment.toComparisonBoundarySlotData.Separated
  locSeparated : table.locAssignment.toComparisonBoundarySlotData.Separated
  nisSeparated : table.nisAssignment.toComparisonBoundarySlotData.Separated
  a1Separated : table.a1Assignment.toComparisonBoundarySlotData.Separated
  envSeparated : table.envAssignment.toComparisonBoundarySlotData.Separated

/-- Exact symbolic data needed to certify that the five designated generator
rows carry pairwise-separated slot labels. This is table-level only; it does
not identify recovered records with any row. -/
abbrev GeneratorRowSlotSeparationData
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :=
  SymbolicGeneratorPortLabelWitness table

namespace GeneratorTableSlotLabelSeparationData

theorem toGeneratorRowSlotSeparationData
    {ctx : ClassicalComparisonContext.{u, v}}
    {table : GeneratorRealizationAssignmentTable ctx}
    (data :
      GeneratorTableSlotLabelSeparationData
        (GeneratorRealizationAssignmentTable.toGeneratorTableSlotLabelAssignment table)) :
    GeneratorRowSlotSeparationData table where
  corrSeparated := by
    simpa [GeneratorRealizationAssignmentTable.toGeneratorTableSlotLabelAssignment,
      GeneratorRealizationAssignmentTable.toFiveRowSlotLabelAssignment]
      using data.corrSeparated
  locSeparated := by
    simpa [GeneratorRealizationAssignmentTable.toGeneratorTableSlotLabelAssignment,
      GeneratorRealizationAssignmentTable.toFiveRowSlotLabelAssignment]
      using data.locSeparated
  nisSeparated := by
    simpa [GeneratorRealizationAssignmentTable.toGeneratorTableSlotLabelAssignment,
      GeneratorRealizationAssignmentTable.toFiveRowSlotLabelAssignment]
      using data.nisSeparated
  a1Separated := by
    simpa [GeneratorRealizationAssignmentTable.toGeneratorTableSlotLabelAssignment,
      GeneratorRealizationAssignmentTable.toFiveRowSlotLabelAssignment]
      using data.a1Separated
  envSeparated := by
    simpa [GeneratorRealizationAssignmentTable.toGeneratorTableSlotLabelAssignment,
      GeneratorRealizationAssignmentTable.toFiveRowSlotLabelAssignment]
      using data.envSeparated

end GeneratorTableSlotLabelSeparationData

namespace SymbolicGeneratorPortLabelWitness

theorem separated
    {ctx : ClassicalComparisonContext.{u, v}}
    {table : GeneratorRealizationAssignmentTable ctx}
    (witness : SymbolicGeneratorPortLabelWitness table)
    (row : GeneratorRowTag) :
    (table.toFiveRowSlotLabelAssignment.get row).Separated := by
  cases row with
  | corr =>
      simpa [GeneratorRealizationAssignmentTable.toFiveRowSlotLabelAssignment,
        FiveRowSlotLabelAssignment.get] using witness.corrSeparated
  | loc =>
      simpa [GeneratorRealizationAssignmentTable.toFiveRowSlotLabelAssignment,
        FiveRowSlotLabelAssignment.get] using witness.locSeparated
  | nis =>
      simpa [GeneratorRealizationAssignmentTable.toFiveRowSlotLabelAssignment,
        FiveRowSlotLabelAssignment.get] using witness.nisSeparated
  | a1 =>
      simpa [GeneratorRealizationAssignmentTable.toFiveRowSlotLabelAssignment,
        FiveRowSlotLabelAssignment.get] using witness.a1Separated
  | env =>
      simpa [GeneratorRealizationAssignmentTable.toFiveRowSlotLabelAssignment,
        FiveRowSlotLabelAssignment.get] using witness.envSeparated

theorem portLabelSeparated
    {ctx : ClassicalComparisonContext.{u, v}}
    {table : GeneratorRealizationAssignmentTable ctx}
    (witness : SymbolicGeneratorPortLabelWitness table)
    (row : GeneratorRowTag) :
    ((table.toFiveRowSlotLabelAssignment.get row).toVisibleBoundaryPortData).Separated :=
  StructuredComparisonSlotData.toVisibleBoundaryPortData_separated (witness.separated row)

end SymbolicGeneratorPortLabelWitness

/-- Exact missing bridge from recovered comparison-slot bundles to the symbolic
five-row generator table. This is still symbolic-only: it says each recovered
slot bundle is one of the designated five-row symbolic slot assignments. -/
def GeometricBoundaryPortLabelAssignmentTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (table : GeneratorRealizationAssignmentTable ctx)
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData) : Prop :=
  ∀ R,
    ∃ row : GeneratorRowTag,
      slotData R = table.toFiveRowSlotLabelAssignment.get row

/-- Exact symbolic/table-level data still needed to identify each recovered
slot bundle with one of the five designated generator rows. The target is
named independently of any real boundary-port realization claim. -/
abbrev RecoveredSlotAssignmentData
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (table : GeneratorRealizationAssignmentTable ctx)
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData) :=
  GeometricBoundaryPortLabelAssignmentTarget table slotData

/-- Symbolic recovery map from reconstruction records into the designated
five-row slot-label assignment. This remains strictly table-level: it does not
assert that the real comparison-boundary recovery path already provides such a
map. -/
structure SymbolicRecoveredSlotAssignmentMap
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (assignment : GeneratorTableSlotLabelAssignment ctx)
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData) where
  rowOf :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
      GeneratorRowTag
  recovers : ∀ R, slotData R = assignment.get (rowOf R)

namespace SymbolicRecoveredSlotAssignmentMap

def recoveredTableSlot
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {assignment : GeneratorTableSlotLabelAssignment ctx}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData}
    (recovery : SymbolicRecoveredSlotAssignmentMap assignment slotData)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (label : GeneratorCoreSlotLabel) :
    GeneratorTableSlot :=
  GeneratorTableSlot.ofRowAndLabel (recovery.rowOf R) label

theorem recoversSlotLabel
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {assignment : GeneratorTableSlotLabelAssignment ctx}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData}
    (recovery : SymbolicRecoveredSlotAssignmentMap assignment slotData)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (label : GeneratorCoreSlotLabel) :
    (slotData R).coreLabel label = assignment.slotLabel (recovery.recoveredTableSlot R label) := by
  simp [recoveredTableSlot, recovery.recovers R, FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel]

theorem toRecoveredSlotAssignmentData
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {table : GeneratorRealizationAssignmentTable ctx}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData}
    (recovery :
      SymbolicRecoveredSlotAssignmentMap
        (GeneratorRealizationAssignmentTable.toGeneratorTableSlotLabelAssignment table)
        slotData) :
    RecoveredSlotAssignmentData table slotData := by
  intro R
  refine ⟨recovery.rowOf R, ?_⟩
  simpa [GeneratorRealizationAssignmentTable.toGeneratorTableSlotLabelAssignment,
    GeneratorRealizationAssignmentTable.toFiveRowSlotLabelAssignment]
    using recovery.recovers R

end SymbolicRecoveredSlotAssignmentMap

theorem GeometricBoundaryPortLabelAssignmentTarget.toSymbolicPortLabelSeparationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {table : GeneratorRealizationAssignmentTable ctx}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData}
    (witness : SymbolicGeneratorPortLabelWitness table)
    (assignmentTarget : GeometricBoundaryPortLabelAssignmentTarget table slotData) :
    SymbolicPortLabelSeparationTarget slotData where
  theoremTarget := by
    intro R
    rcases assignmentTarget R with ⟨row, hRow⟩
    rw [hRow]
    exact witness.separated row

theorem GeometricBoundaryPortLabelAssignmentTarget.toPortLabelSeparationTargetOfSlots
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {table : GeneratorRealizationAssignmentTable ctx}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData}
    (witness : SymbolicGeneratorPortLabelWitness table)
    (assignmentTarget : GeometricBoundaryPortLabelAssignmentTarget table slotData) :
    PortLabelSeparationTargetOfSlots slotData :=
  (GeometricBoundaryPortLabelAssignmentTarget.toSymbolicPortLabelSeparationTarget
    witness assignmentTarget).portLabelSeparationTargetOfSlots

/-- Explicit probe-family package for comparison pairing data. Keeping the
probe universe on the structure avoids asking Lean to infer it through a bare
function alias into `concreteFramedProbeFamily`. -/
structure ComparisonPairingProbeFamily
    (ctx : ClassicalComparisonContext.{u, v}) where
  ProbeIndex : Type w
  concreteDatum :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx

namespace ComparisonPairingProbeFamily

def toConcreteFramedProbeFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (family : ComparisonPairingProbeFamily ctx) :
    FramedProbeFamily ctx :=
  concreteFramedProbeFamily family.concreteDatum

def toScalarProbeFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (family : ComparisonPairingProbeFamily ctx) :
    ScalarProbeFamily ctx where
  ProbeIndex := family.ProbeIndex
  ScalarCarrier := ctx.ScalarField
  probeValue := fun probe morphism => (family.concreteDatum probe morphism).scalarPeriod
  equalityRelation := fun left right => left = right
  -- probeNaturalityTarget: the equality relation on the scalar codomain is reflexive.
  -- For this probe family `equalityRelation = (· = ·)`, so reflexivity is `∀ a, a = a`.
  -- This encodes the unit/reflexivity law of the probe's equality structure.
  -- Quantification stays on `ctx.ScalarField` to avoid universe metavar issues with sigma binders.
  probeNaturalityTarget := ∀ (a : ctx.ScalarField), a = a
  -- probeExtractionTarget: scalar extraction is reflexive on ctx.ScalarField. The concrete
  -- shadow extracts scalarPeriod directly, so this reduces to reflexivity on the carrier.
  -- Stated without a cross-file shadow reference to avoid universe metavar propagation.
  probeExtractionTarget := ∀ (a : ctx.ScalarField), a = a

end ComparisonPairingProbeFamily

/-- The probe naturality for `ComparisonPairingProbeFamily.toScalarProbeFamily` holds:
the equality relation on `ctx.ScalarField` is reflexive (`∀ a, a = a`).
Proof is definitional: `rfl`. -/
theorem ComparisonPairingProbeFamily.toScalarProbeFamily_probeNaturalityHolds
    {ctx : ClassicalComparisonContext.{u, v}}
    (family : ComparisonPairingProbeFamily ctx) :
    family.toScalarProbeFamily.probeNaturalityTarget := by
  show ∀ (a : ctx.ScalarField), a = a
  intro; rfl

/-- Equality of all scalar pairing evaluations in a fixed concrete pairing probe
family. -/
def ComparisonPairingEquality
    {ctx : ClassicalComparisonContext.{u, v}}
    {ProbeIndex : Type w}
    (concreteDatum :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx)
    (left right : SomeStructuredComparisonMorphism ctx) : Prop :=
  let family : ComparisonPairingProbeFamily ctx := {
    ProbeIndex := ProbeIndex
    concreteDatum := concreteDatum
  }
  ProbeEquality family.toScalarProbeFamily left right

/-- Precise nondegeneracy target for the concrete comparison-pairing probe
family induced by framed period data. -/
def ComparisonPairingNondegeneracyTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx)
    {ProbeIndex : Type w}
    (concreteDatum :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx) : Prop :=
  ∀ left right : SomeStructuredComparisonMorphism ctx,
    ComparisonPairingEquality concreteDatum left right →
      structuredEq.relates left right

theorem FaithfulFramedProbeTarget.toComparisonPairingNondegeneracyTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {ProbeIndex : Type w}
    {structuredEq : StructuredComparisonEquality ctx}
    (concreteDatum :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (concreteFramedProbeFamily concreteDatum)
        structuredEq) :
    ComparisonPairingNondegeneracyTarget structuredEq concreteDatum := by
  intro left right hPairing
  let family : ComparisonPairingProbeFamily ctx := {
    ProbeIndex := ProbeIndex
    concreteDatum := concreteDatum
  }
  have hFramed :
      FramedProbeEquality (concreteFramedProbeFamily concreteDatum) left right := by
    simpa [ComparisonPairingEquality, family,
      ComparisonPairingProbeFamily.toScalarProbeFamily] using hPairing
  exact faithful.theoremTarget left right hFramed

/-- Structured comparison equality determines the named slot layer. This is the
injectivity input saying the comparison package is rich enough to recover the
comparison slots, rather than only a scalar shadow thereof. -/
structure ComparisonSlotInjectivityTarget
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {α : Type v}
    (comparison :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α)
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData) where
  comparisonEqualityDeterminesSlots :
    ∀ {R₁ R₂ :
        TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup},
      comparison R₁ = comparison R₂ → slotData R₁ = slotData R₂

/-- Boundary-port recovery target: once the comparison slots are known, the
visible boundary ports are determined. This is the comparison-to-boundary port
reconstruction step. -/
structure BoundaryPortRecoveryFromComparisonSlotsTarget
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData)
    (boundaryPorts :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        VisibleBoundaryPortData) where
  comparisonSlotsDetermineBoundaryPorts :
    ∀ {R₁ R₂ :
        TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup},
      slotData R₁ = slotData R₂ → boundaryPorts R₁ = boundaryPorts R₂

/-- Final reconstruction target on the comparison side: boundary-port equality
already determines the chosen visible-boundary data. -/
structure VisibleBoundaryReconstructionFromPortsTarget
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {β : Sort _}
    (boundaryPorts :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        VisibleBoundaryPortData)
    (visibleBoundary :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → β) where
  boundaryPortsDetermineVisibleBoundary :
    ∀ {R₁ R₂ :
        TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup},
      boundaryPorts R₁ = boundaryPorts R₂ → visibleBoundary R₁ = visibleBoundary R₂

/-- Generic assembly theorem for the hard comparison-to-boundary input. If
structured comparison equality determines the comparison slots, the slots
recover boundary ports, and those ports reconstruct the visible boundary, then
the existing LayerB hard-input target is inhabited without strengthening its
API. Scalar periods do not appear here: this is entirely about structured
comparison data. -/
def structuredComparisonDeterminesVisibleBoundaryTarget_of_slotRecovery
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {α : Type v} {β : Sort _}
    (comparison :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α)
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData)
    (boundaryPorts :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        VisibleBoundaryPortData)
    (visibleBoundary :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → β)
    (slotSeparation : ComparisonSlotSeparationTarget slotData)
    (slotInjectivity : ComparisonSlotInjectivityTarget comparison slotData)
    (boundaryPortRecovery :
      BoundaryPortRecoveryFromComparisonSlotsTarget slotData boundaryPorts)
    (visibleBoundaryReconstruction :
      VisibleBoundaryReconstructionFromPortsTarget boundaryPorts visibleBoundary) :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.StructuredComparisonDeterminesVisibleBoundaryTarget
      (setup := setup)
      comparison
      visibleBoundary := by
  let slotSeparationTarget :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.StructuredComparisonSlotSeparationTarget
        (setup := setup)
        comparison :=
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.StructuredComparisonSlotSeparationTarget.ofProp
      (setup := setup)
      comparison
      (∀ R,
        (slotData R).sourceSlot ≠ (slotData R).targetSlot ∧
          (slotData R).bettiSlot ≠ (slotData R).deRhamSlot ∧
            (slotData R).comparisonSlot ≠ (slotData R).sourceSlot ∧
              (slotData R).comparisonSlot ≠ (slotData R).targetSlot)
  refine
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.StructuredComparisonDeterminesVisibleBoundaryTarget.ofImplication
      (setup := setup)
      comparison
      visibleBoundary
      slotSeparationTarget
      ?_
  intro R₁ R₂ hComparison
  have hSlots := slotInjectivity.comparisonEqualityDeterminesSlots hComparison
  have hPorts := boundaryPortRecovery.comparisonSlotsDetermineBoundaryPorts hSlots
  exact visibleBoundaryReconstruction.boundaryPortsDetermineVisibleBoundary hPorts

end ClassicalPeriods
end TraceCalc
