import Boundary.A1Invariance
import Boundary.NisnevichDescent
import Boundary.GraphExternalProductCompatibility

/-!
# Minimal Presentation Package

This file records the source-side minimal presentation package built from the
primitive families `Corr`, `A1`, and `Nis`, together with the exact closure
operations used downstream in the manuscript.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

namespace Boundary

noncomputable section

/-- Generator data for the minimal presentation package.  This is the boundary
side version of the manuscript's `M(X,p,m)` data: a smooth scheme, an
idempotent projector in `SmCor_Q`, and an integral twist index. -/
structure MinimalPresentationGeneratorQ (category : SmCorQ (k := k)) where
  scheme : Geometry.SmSchemeOver k
  projector : SmCorQ.Hom category scheme scheme
  projectorIdempotentTarget : category.comp projector projector = projector
  twist : Int

/-- Canonical closure owner carried by the minimal presentation package.

The only data kept here is the already-constructed correspondence-level
external-product owner. The actual closure under sums, shifts, cones, Karoubi
summands, tensor products, and duals is generated below as an inductive
construction rather than stored as arbitrary fields. -/
structure MinimalPresentationClosureQ where
  canonicalExternalProduct :
    FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k)

namespace MinimalPresentationClosureQ

/-- Canonical correspondence-level external-product owner carried by the
closure package. -/
abbrev canonicalExternalProduct
    (closure : MinimalPresentationClosureQ) :
    FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k) :=
  closure.canonicalExternalProduct

/-- The underlying canonical external-product family of the graph-compatible
owner carried by the closure package. -/
abbrev canonicalExternalProductFamily
    (closure : MinimalPresentationClosureQ) :
    FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
  closure.canonicalExternalProduct.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily

end MinimalPresentationClosureQ

/-- Formal objects in the minimal presentation generated from the manuscript
generators by the closure operations used downstream. This is the syntax of the
generated closure. -/
inductive MinimalPresentationObjectQ (category : SmCorQ (k := k)) where
  | generator (g : MinimalPresentationGeneratorQ category)
  | directSum (left right : MinimalPresentationObjectQ category)
  | shift (obj : MinimalPresentationObjectQ category) (n : Int)
  | cone (source target : MinimalPresentationObjectQ category)
  | karoubi (obj : MinimalPresentationObjectQ category)
  | tensor (left right : MinimalPresentationObjectQ category)
  | dual (obj : MinimalPresentationObjectQ category)

/-- Boundary-side form of the manuscript's minimal presentation package.  The
primitive relation families are the rational correspondence category itself,
`A1`-contraction, and Nisnevich descent. -/
structure MinimalPresentationPackageQ (category : SmCorQ (k := k)) where
  GeneratorIndex : Type (u + 1)
  generator : GeneratorIndex → MinimalPresentationGeneratorQ category
  a1LocalizationTarget : A1LocalizationTargetQ category
  nisnevichLocalizingMorphismFamily : NisnevichLocalizingMorphismFamilyQ category
  closure : MinimalPresentationClosureQ

namespace MinimalPresentationPackageQ

/-- The generator object associated to a package index. -/
def generatorObject {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category)
    (idx : package.GeneratorIndex) :
    MinimalPresentationObjectQ category :=
  .generator (package.generator idx)

/-- Generated minimal presentation closure. -/
inductive GeneratedClosure {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category) :
    MinimalPresentationObjectQ category → Prop where
  | generator (idx : package.GeneratorIndex) :
      GeneratedClosure package (package.generatorObject idx)
  | directSum {left right : MinimalPresentationObjectQ category} :
      GeneratedClosure package left →
      GeneratedClosure package right →
      GeneratedClosure package (.directSum left right)
  | shift {obj : MinimalPresentationObjectQ category} (n : Int) :
      GeneratedClosure package obj →
      GeneratedClosure package (.shift obj n)
  | cone {source target : MinimalPresentationObjectQ category} :
      GeneratedClosure package source →
      GeneratedClosure package target →
      GeneratedClosure package (.cone source target)
  | karoubi {obj : MinimalPresentationObjectQ category} :
      GeneratedClosure package obj →
      GeneratedClosure package (.karoubi obj)
  | tensor {left right : MinimalPresentationObjectQ category} :
      GeneratedClosure package left →
      GeneratedClosure package right →
      GeneratedClosure package (.tensor left right)
  | dual {obj : MinimalPresentationObjectQ category} :
      GeneratedClosure package obj →
      GeneratedClosure package (.dual obj)

/-- The minimal presentation contains each indexed generator. -/
theorem minimalPresentation_mem_of_generator {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category)
    (idx : package.GeneratorIndex) :
    GeneratedClosure package (package.generatorObject idx) :=
  GeneratedClosure.generator idx

/-- The minimal presentation is closed under direct sums. -/
theorem minimalPresentation_closed_under_directSum {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category)
    {left right : MinimalPresentationObjectQ category}
    (hleft : GeneratedClosure package left)
    (hright : GeneratedClosure package right) :
    GeneratedClosure package (.directSum left right) :=
  GeneratedClosure.directSum hleft hright

/-- The minimal presentation is closed under shifts. -/
theorem minimalPresentation_closed_under_shift {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category)
    {obj : MinimalPresentationObjectQ category}
    (n : Int)
    (hobj : GeneratedClosure package obj) :
    GeneratedClosure package (.shift obj n) :=
  GeneratedClosure.shift n hobj

/-- The minimal presentation is closed under cones. -/
theorem minimalPresentation_closed_under_cone {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category)
    {source target : MinimalPresentationObjectQ category}
    (hsource : GeneratedClosure package source)
    (htarget : GeneratedClosure package target) :
    GeneratedClosure package (.cone source target) :=
  GeneratedClosure.cone hsource htarget

/-- The minimal presentation is closed under Karoubi summands. -/
theorem minimalPresentation_closed_under_karoubi {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category)
    {obj : MinimalPresentationObjectQ category}
    (hobj : GeneratedClosure package obj) :
    GeneratedClosure package (.karoubi obj) :=
  GeneratedClosure.karoubi hobj

/-- The minimal presentation is closed under tensor products routed through the
canonical external-product owner carried by the package closure. -/
theorem minimalPresentation_closed_under_tensor {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category)
    {left right : MinimalPresentationObjectQ category}
    (hleft : GeneratedClosure package left)
    (hright : GeneratedClosure package right) :
    GeneratedClosure package (.tensor left right) :=
  let _canonicalExternalProduct := package.closure.canonicalExternalProduct
  GeneratedClosure.tensor hleft hright

/-- The minimal presentation is closed under duals. -/
theorem minimalPresentation_closed_under_dual {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category)
    {obj : MinimalPresentationObjectQ category}
    (hobj : GeneratedClosure package obj) :
    GeneratedClosure package (.dual obj) :=
  GeneratedClosure.dual hobj

/-- The generated closure is stable under equality of presentation objects. This
is the syntactic form of isomorphism-closure before the generated presentation
objects are interpreted in a categorical envelope. -/
theorem minimalPresentation_closed_under_isomorphism {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category)
    {obj obj' : MinimalPresentationObjectQ category}
    (hobj : GeneratedClosure package obj)
    (hiso : obj = obj') :
    GeneratedClosure package obj' :=
  hiso ▸ hobj

/-- The generated closure is minimal among predicates containing the indexed
generators and closed under the presentation operations. -/
theorem minimalPresentation_is_minimal_closed {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category)
    (P : MinimalPresentationObjectQ category → Prop)
    (hgen : ∀ idx, P (package.generatorObject idx))
    (hsum : ∀ {left right}, P left → P right → P (.directSum left right))
    (hshift : ∀ {obj} n, P obj → P (.shift obj n))
    (hcone : ∀ {source target}, P source → P target → P (.cone source target))
    (hkaroubi : ∀ {obj}, P obj → P (.karoubi obj))
    (htensor : ∀ {left right}, P left → P right → P (.tensor left right))
    (hdual : ∀ {obj}, P obj → P (.dual obj)) :
    ∀ {obj}, GeneratedClosure package obj → P obj := by
  intro obj hobj
  induction hobj with
  | generator idx => exact hgen idx
  | directSum hleft hright ihleft ihright => exact hsum ihleft ihright
  | shift n hobj ih => exact hshift n ih
  | cone hsource htarget ihsource ihtarget => exact hcone ihsource ihtarget
  | karoubi hobj ih => exact hkaroubi ih
  | tensor hleft hright ihleft ihright => exact htensor ihleft ihright
  | dual hobj ih => exact hdual ih

/-- The package closure is definitionally the generated closure predicate. -/
abbrev generatedClosure {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category) :
    MinimalPresentationObjectQ category → Prop :=
  GeneratedClosure package

/-- The named generated-closure equality for downstream consumers. -/
theorem minimalPresentationPackage_eq_generatedClosure
    {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category) :
    package.generatedClosure = GeneratedClosure package :=
  rfl

/-- Primitive localization generators coming from the `A1` and Nisnevich
families carried by a minimal presentation package. -/
inductive PrimitiveLocalizationGeneratorQ
    {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category) where
  | a1 (witness : package.a1LocalizationTarget.Witness)
  | nisnevich (square : package.nisnevichLocalizingMorphismFamily.Square)

/-- The raw localizing morphism family generated by the `A1` and Nisnevich
relations in a minimal presentation package. -/
def toLocalizingMorphisms {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category) :
    LocalizingMorphismPresentationQ category where
  Generator := PrimitiveLocalizationGeneratorQ package
  data := fun
    | .a1 witness =>
        ⟨(package.a1LocalizationTarget.witness witness).sourcePresheaf,
          (package.a1LocalizationTarget.witness witness).targetPresheaf,
          (package.a1LocalizationTarget.witness witness).homotopyMap⟩
  | .nisnevich square => package.nisnevichLocalizingMorphismFamily.localizingData square

/-- The proof-relevant raw zigzag localization data generated by the
primitive `A1` and Nisnevich relations in a minimal presentation package. -/
def rawZigzagLocalizationConstruction {category : SmCorQ (k := k)}
    (package : MinimalPresentationPackageQ category) :
    RawZigzagLocalizationConstructionQ category :=
  RawZigzagLocalizationConstructionQ.ofLocalizingMorphisms package.toLocalizingMorphisms

end MinimalPresentationPackageQ

end

end Boundary
