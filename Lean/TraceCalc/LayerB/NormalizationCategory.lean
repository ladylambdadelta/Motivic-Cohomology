import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso
import TraceCalc.LayerB.RealObjects.SwapSquare
import TraceCalc.LayerB.RealObjects.TraceDifferential
import TraceCalc.LayerB.RealObjects.UnpeelChain
import TraceCalc.LayerB.Reconstruction

/-!
# Strict normalization record-map and coherence substrate

This file is the strict pi0 / 1-categorical substrate for normalized completed
records. It defines object wrappers, strict record maps, identity/composition of
those maps, and cut inclusions over the existing `ShadowModel.CompletedRecord`
calculus.

It also defines proof-relevant low-dimensional coherence data over those strict
maps: map homotopies, composable 1-simplices, 2-simplex witnesses, and 3-simplex
boundary witnesses. These structures are the beginning of the machinery needed
for a later simplicial/Segal/computadic enhancement, but they are not themselves
an infinity-category.

This is not a stable category, not a derived category, not a motivic category,
and not a t-structure. The strict maps below are the spine on which later replay
and coherence data must be added before any mapping-space, localization, or
stable infinity-categorical claim is made.

The total-to-upper cut projection remains cofiber/projection data from the lower
cut calculus. It is not treated here as an ordinary strict record map because
dependency preservation for such a map is not available in general.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace Normalization

open CategoryTheory
open ShadowModel

structure CompletedRecordMap {sourceLength targetLength : Nat}
    (source : CompletedRecord sourceLength)
    (target : CompletedRecord targetLength) where
  packetMap : Fin sourceLength → Option (Fin targetLength)
  preservesRequires :
    ∀ {j i : Fin sourceLength}, i ∈ source.requires j →
      ∀ {j' : Fin targetLength}, packetMap j = some j' →
        ∃ i' : Fin targetLength,
          packetMap i = some i' ∧ i' ∈ target.requires j'
  preservesTraceOrder :
    ∀ {j i : Fin sourceLength}, i ∈ source.requires j →
      ∀ {j' i' : Fin targetLength},
        packetMap j = some j' → packetMap i = some i' → i'.val < j'.val

namespace CompletedRecordMap

def id {length : Nat} (record : CompletedRecord length) : CompletedRecordMap record record where
  packetMap i := some i
  preservesRequires := by
    intro j i hi j' hj'
    obtain rfl : j' = j := by simpa using hj'.symm
    exact ⟨i, rfl, hi⟩
  preservesTraceOrder := by
    intro j i hi j' i' hj' hi'
    have hjEq : j' = j := by simpa using hj'.symm
    have hiEq : i' = i := by simpa using hi'.symm
    subst hjEq
    subst hiEq
    exact record.dep.upper _ _ (record.c1 _ _ hi)

def comp
    {firstLength middleLength lastLength : Nat}
    {first : CompletedRecord firstLength}
    {middle : CompletedRecord middleLength}
    {last : CompletedRecord lastLength}
    (left : CompletedRecordMap first middle)
    (right : CompletedRecordMap middle last) :
    CompletedRecordMap first last where
  packetMap i := (left.packetMap i).bind right.packetMap
  preservesRequires := by
    intro j i hi j'' hj''
    simp only [Option.bind_eq_bind] at hj''
    cases hjmid : left.packetMap j with
    | none => simp [hjmid] at hj''
    | some j' =>
        have hjLast : right.packetMap j' = some j'' := by
          simpa [hjmid] using hj''
        obtain ⟨i', hiMid, hiReq⟩ := left.preservesRequires hi hjmid
        obtain ⟨i'', hiLast, hiReqLast⟩ := right.preservesRequires hiReq hjLast
        refine ⟨i'', ?_, hiReqLast⟩
        simp [hiMid, hiLast]
  preservesTraceOrder := by
    intro j i hi j'' i'' hj'' hi''
    cases hjmid : left.packetMap j with
    | none => simp [hjmid] at hj''
    | some j' =>
        have hjLast : right.packetMap j' = some j'' := by
          simpa [hjmid] using hj''
        cases himid : left.packetMap i with
        | none => simp [himid] at hi''
        | some i' =>
            have hiLast : right.packetMap i' = some i'' := by
              simpa [himid] using hi''
            obtain ⟨iTarget, hiTarget, hiReqTarget⟩ := left.preservesRequires hi hjmid
            have hiTarget_eq : iTarget = i' := by
              simpa [himid] using hiTarget.symm
            subst hiTarget_eq
            exact right.preservesTraceOrder hiReqTarget hjLast hiLast

@[simp] theorem id_packetMap {length : Nat} (record : CompletedRecord length) (i : Fin length) :
    (id record).packetMap i = some i :=
  rfl

@[simp] theorem comp_packetMap
    {firstLength middleLength lastLength : Nat}
    {first : CompletedRecord firstLength}
    {middle : CompletedRecord middleLength}
    {last : CompletedRecord lastLength}
    (left : CompletedRecordMap first middle)
    (right : CompletedRecordMap middle last)
    (i : Fin firstLength) :
    (comp left right).packetMap i = (left.packetMap i).bind right.packetMap :=
  rfl

end CompletedRecordMap

structure CompletedRecordMapHomotopy
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (left right : CompletedRecordMap source target) where
  point : Fin sourceLength → Type
  witness : ∀ i : Fin sourceLength, point i
  sourceFiber : ∀ i : Fin sourceLength,
    left.packetMap i = none ∨ ∃ j : Fin targetLength, left.packetMap i = some j
  targetFiber : ∀ i : Fin sourceLength,
    right.packetMap i = none ∨ ∃ j : Fin targetLength, right.packetMap i = some j
  relatesMappedPackets : ∀ {i : Fin sourceLength} (j k : Fin targetLength),
    left.packetMap i = some j → right.packetMap i = some k → Prop
  relatesMappedPacketsWitness : ∀ {i : Fin sourceLength} {j k : Fin targetLength},
    (hLeft : left.packetMap i = some j) →
    (hRight : right.packetMap i = some k) →
      relatesMappedPackets j k hLeft hRight
  rightMappedOfLeftMapped : ∀ {i : Fin sourceLength} {j : Fin targetLength},
    left.packetMap i = some j → ∃ k : Fin targetLength, right.packetMap i = some k
  leftMappedOfRightMapped : ∀ {i : Fin sourceLength} {k : Fin targetLength},
    right.packetMap i = some k → ∃ j : Fin targetLength, left.packetMap i = some j
  respectsRequires : ∀ {j i : Fin sourceLength}, i ∈ source.requires j →
    ∀ {jLeft iLeft jRight iRight : Fin targetLength},
      left.packetMap j = some jLeft → left.packetMap i = some iLeft →
      right.packetMap j = some jRight → right.packetMap i = some iRight →
        iLeft.val < jLeft.val ∧ iRight.val < jRight.val

namespace CompletedRecordMapHomotopy

def refl
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (map : CompletedRecordMap source target) :
    CompletedRecordMapHomotopy map map where
  point _ := PUnit
  witness _ := PUnit.unit
  sourceFiber i := by
    cases h : map.packetMap i with
    | none => exact Or.inl rfl
    | some j => exact Or.inr ⟨j, rfl⟩
  targetFiber i := by
    cases h : map.packetMap i with
    | none => exact Or.inl rfl
    | some j => exact Or.inr ⟨j, rfl⟩
  relatesMappedPackets j k _ _ := j = k
  relatesMappedPacketsWitness hLeft hRight := by
    rw [hLeft] at hRight
    obtain rfl := Option.some.inj hRight
    rfl
  rightMappedOfLeftMapped hLeft := ⟨_, hLeft⟩
  leftMappedOfRightMapped hRight := ⟨_, hRight⟩
  respectsRequires := by
    intro j i hi jLeft iLeft jRight iRight hjLeft hiLeft hjRight hiRight
    exact ⟨map.preservesTraceOrder hi hjLeft hiLeft,
      map.preservesTraceOrder hi hjRight hiRight⟩

def ofPointwiseEq
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    {left right : CompletedRecordMap source target}
    (hEq : ∀ i : Fin sourceLength, left.packetMap i = right.packetMap i) :
    CompletedRecordMapHomotopy left right where
  point _ := PUnit
  witness _ := PUnit.unit
  sourceFiber i := by
    cases h : left.packetMap i with
    | none => exact Or.inl rfl
    | some j => exact Or.inr ⟨j, rfl⟩
  targetFiber i := by
    cases h : right.packetMap i with
    | none => exact Or.inl rfl
    | some j => exact Or.inr ⟨j, rfl⟩
  relatesMappedPackets j k _ _ := j = k
  relatesMappedPacketsWitness := by
    intro i j k hLeft hRight
    rw [hEq _] at hLeft
    have hSome : some j = some k := hLeft.symm.trans hRight
    exact Option.some.inj hSome
  rightMappedOfLeftMapped hLeft := by
    exact ⟨_, (hEq _).symm.trans hLeft⟩
  leftMappedOfRightMapped hRight := by
    exact ⟨_, (hEq _).trans hRight⟩
  respectsRequires := by
    intro j i hi jLeft iLeft jRight iRight hjLeft hiLeft hjRight hiRight
    have hjRight' : left.packetMap j = some jRight := by
      rw [hEq j]
      exact hjRight
    have hiRight' : left.packetMap i = some iRight := by
      rw [hEq i]
      exact hiRight
    exact ⟨left.preservesTraceOrder hi hjLeft hiLeft,
      left.preservesTraceOrder hi hjRight' hiRight'⟩

def symm
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    {left right : CompletedRecordMap source target}
    (homotopy : CompletedRecordMapHomotopy left right) :
    CompletedRecordMapHomotopy right left where
  point := homotopy.point
  witness := homotopy.witness
  sourceFiber := homotopy.targetFiber
  targetFiber := homotopy.sourceFiber
  relatesMappedPackets j k hRight hLeft := homotopy.relatesMappedPackets k j hLeft hRight
  relatesMappedPacketsWitness hRight hLeft :=
    homotopy.relatesMappedPacketsWitness hLeft hRight
  rightMappedOfLeftMapped := homotopy.leftMappedOfRightMapped
  leftMappedOfRightMapped := homotopy.rightMappedOfLeftMapped
  respectsRequires := by
    intro j i hi jRight iRight jLeft iLeft hjRight hiRight hjLeft hiLeft
    have h := homotopy.respectsRequires hi hjLeft hiLeft hjRight hiRight
    exact ⟨h.2, h.1⟩

def trans
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    {first middle last : CompletedRecordMap source target}
    (leftHomotopy : CompletedRecordMapHomotopy first middle)
    (rightHomotopy : CompletedRecordMapHomotopy middle last) :
    CompletedRecordMapHomotopy first last where
  point i := leftHomotopy.point i × rightHomotopy.point i
  witness i := ⟨leftHomotopy.witness i, rightHomotopy.witness i⟩
  sourceFiber := leftHomotopy.sourceFiber
  targetFiber := rightHomotopy.targetFiber
  relatesMappedPackets j k hFirst hLast := ∃ middleTarget hMiddle,
    leftHomotopy.relatesMappedPackets j middleTarget hFirst hMiddle ∧
    rightHomotopy.relatesMappedPackets middleTarget k hMiddle hLast
  relatesMappedPacketsWitness hFirst hLast := by
    obtain ⟨middleTarget, hMiddle⟩ := leftHomotopy.rightMappedOfLeftMapped hFirst
    exact ⟨middleTarget, hMiddle, leftHomotopy.relatesMappedPacketsWitness hFirst hMiddle,
      rightHomotopy.relatesMappedPacketsWitness hMiddle hLast⟩
  rightMappedOfLeftMapped hFirst := by
    obtain ⟨middleTarget, hMiddle⟩ := leftHomotopy.rightMappedOfLeftMapped hFirst
    exact rightHomotopy.rightMappedOfLeftMapped hMiddle
  leftMappedOfRightMapped hLast := by
    obtain ⟨middleTarget, hMiddle⟩ := rightHomotopy.leftMappedOfRightMapped hLast
    exact leftHomotopy.leftMappedOfRightMapped hMiddle
  respectsRequires := by
    intro j i hi jFirst iFirst jLast iLast hjFirst hiFirst hjLast hiLast
    exact ⟨first.preservesTraceOrder hi hjFirst hiFirst,
      last.preservesTraceOrder hi hjLast hiLast⟩

end CompletedRecordMapHomotopy

structure CompletedRecordTwoSimplex
    {aLength bLength cLength : Nat}
    {a : CompletedRecord aLength}
    {b : CompletedRecord bLength}
    {c : CompletedRecord cLength}
    (ab : CompletedRecordMap a b)
    (bc : CompletedRecordMap b c)
    (ac : CompletedRecordMap a c) where
  filler : CompletedRecordMapHomotopy (CompletedRecordMap.comp ab bc) ac

namespace CompletedRecordTwoSimplex

def ofComp
    {aLength bLength cLength : Nat}
    {a : CompletedRecord aLength}
    {b : CompletedRecord bLength}
    {c : CompletedRecord cLength}
    (ab : CompletedRecordMap a b)
    (bc : CompletedRecordMap b c) :
    CompletedRecordTwoSimplex ab bc (CompletedRecordMap.comp ab bc) where
  filler := CompletedRecordMapHomotopy.refl _

end CompletedRecordTwoSimplex

structure CompletedRecordThreeSimplex
    {aLength bLength cLength dLength : Nat}
    {a : CompletedRecord aLength}
    {b : CompletedRecord bLength}
    {c : CompletedRecord cLength}
    {d : CompletedRecord dLength}
    (ab : CompletedRecordMap a b)
    (bc : CompletedRecordMap b c)
    (cd : CompletedRecordMap c d)
    (ad : CompletedRecordMap a d) where
  leftComposite : CompletedRecordMap a d
  rightComposite : CompletedRecordMap a d
  leftFace : CompletedRecordTwoSimplex (CompletedRecordMap.comp ab bc) cd leftComposite
  rightFace : CompletedRecordTwoSimplex ab (CompletedRecordMap.comp bc cd) rightComposite
  boundaryHomotopy : CompletedRecordMapHomotopy leftComposite rightComposite
  targetHomotopy : CompletedRecordMapHomotopy leftComposite ad

namespace CompletedRecordThreeSimplex

def associator
    {aLength bLength cLength dLength : Nat}
    {a : CompletedRecord aLength}
    {b : CompletedRecord bLength}
    {c : CompletedRecord cLength}
    {d : CompletedRecord dLength}
    (ab : CompletedRecordMap a b)
    (bc : CompletedRecordMap b c)
    (cd : CompletedRecordMap c d) :
    CompletedRecordThreeSimplex ab bc cd
      (CompletedRecordMap.comp (CompletedRecordMap.comp ab bc) cd) :=
  let leftComposite := CompletedRecordMap.comp (CompletedRecordMap.comp ab bc) cd
  let rightComposite := CompletedRecordMap.comp ab (CompletedRecordMap.comp bc cd)
  let boundaryHomotopy : CompletedRecordMapHomotopy leftComposite rightComposite := {
    point := fun _ => PUnit
    witness := fun _ => PUnit.unit
    sourceFiber := by
      intro i
      cases h : leftComposite.packetMap i with
      | none => exact Or.inl rfl
      | some j => exact Or.inr ⟨j, rfl⟩
    targetFiber := by
      intro i
      cases h : rightComposite.packetMap i with
      | none => exact Or.inl rfl
      | some j => exact Or.inr ⟨j, rfl⟩
    relatesMappedPackets := fun j k _ _ => j = k
    relatesMappedPacketsWitness := by
      intro i j k hLeft hRight
      have hAssoc : leftComposite.packetMap i = rightComposite.packetMap i := by
        simp [leftComposite, rightComposite, CompletedRecordMap.comp, Option.bind_assoc]
      rw [hAssoc, hRight] at hLeft
      obtain rfl := Option.some.inj hLeft
      rfl
    rightMappedOfLeftMapped := by
      intro i target hLeft
      have hAssoc : leftComposite.packetMap i = rightComposite.packetMap i := by
        simp [leftComposite, rightComposite, CompletedRecordMap.comp, Option.bind_assoc]
      rw [hAssoc] at hLeft
      exact ⟨target, hLeft⟩
    leftMappedOfRightMapped := by
      intro i target hRight
      have hAssoc : leftComposite.packetMap i = rightComposite.packetMap i := by
        simp [leftComposite, rightComposite, CompletedRecordMap.comp, Option.bind_assoc]
      rw [hAssoc]
      exact ⟨target, hRight⟩
    respectsRequires := by
      intro j i hi jLeft iLeft jRight iRight hjLeft hiLeft hjRight hiRight
      exact ⟨leftComposite.preservesTraceOrder hi hjLeft hiLeft,
        rightComposite.preservesTraceOrder hi hjRight hiRight⟩
  }
  {
  leftComposite := CompletedRecordMap.comp (CompletedRecordMap.comp ab bc) cd
  rightComposite := CompletedRecordMap.comp ab (CompletedRecordMap.comp bc cd)
  leftFace := CompletedRecordTwoSimplex.ofComp (CompletedRecordMap.comp ab bc) cd
  rightFace := CompletedRecordTwoSimplex.ofComp ab (CompletedRecordMap.comp bc cd)
  boundaryHomotopy := boundaryHomotopy
  targetHomotopy := CompletedRecordMapHomotopy.refl _
  }

end CompletedRecordThreeSimplex

structure CompletedRecordWeakEquivalence
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (map : CompletedRecordMap source target) where
  inverse : CompletedRecordMap target source
  leftHomotopy : CompletedRecordMapHomotopy
    (CompletedRecordMap.comp map inverse) (CompletedRecordMap.id source)
  rightHomotopy : CompletedRecordMapHomotopy
    (CompletedRecordMap.comp inverse map) (CompletedRecordMap.id target)

namespace CompletedRecordWeakEquivalence

def id {length : Nat} (record : CompletedRecord length) :
    CompletedRecordWeakEquivalence (CompletedRecordMap.id record) where
  inverse := CompletedRecordMap.id record
  leftHomotopy := CompletedRecordMapHomotopy.refl _
  rightHomotopy := CompletedRecordMapHomotopy.refl _

end CompletedRecordWeakEquivalence

structure AdmNormObj where
  length : Nat
  record : CompletedRecord length

structure AdmNormHom (source target : AdmNormObj) where
  recordMap : CompletedRecordMap source.record target.record

namespace AdmNormHom

def id (obj : AdmNormObj) : AdmNormHom obj obj where
  recordMap := CompletedRecordMap.id obj.record

def comp {first middle last : AdmNormObj}
    (left : AdmNormHom first middle)
    (right : AdmNormHom middle last) : AdmNormHom first last where
  recordMap := CompletedRecordMap.comp left.recordMap right.recordMap

theorem id_packetMap (obj : AdmNormObj) (i : Fin obj.length) :
    (id obj).recordMap.packetMap i = some i :=
  CompletedRecordMap.id_packetMap obj.record i

@[simp] theorem comp_packetMap {first middle last : AdmNormObj}
    (left : AdmNormHom first middle)
    (right : AdmNormHom middle last)
    (i : Fin first.length) :
    (comp left right).recordMap.packetMap i =
      (left.recordMap.packetMap i).bind right.recordMap.packetMap :=
  rfl

end AdmNormHom

abbrev AdmNormHomotopy {source target : AdmNormObj}
    (left right : AdmNormHom source target) : Type 1 :=
  CompletedRecordMapHomotopy left.recordMap right.recordMap

abbrev AdmNormTwoSimplex {a b c : AdmNormObj}
    (ab : AdmNormHom a b) (bc : AdmNormHom b c) (ac : AdmNormHom a c) : Type 1 :=
  CompletedRecordTwoSimplex ab.recordMap bc.recordMap ac.recordMap

abbrev AdmNormThreeSimplex {a b c d : AdmNormObj}
    (ab : AdmNormHom a b) (bc : AdmNormHom b c) (cd : AdmNormHom c d)
    (ad : AdmNormHom a d) : Type 1 :=
  CompletedRecordThreeSimplex ab.recordMap bc.recordMap cd.recordMap ad.recordMap

abbrev AdmNormWeakEquivalence {source target : AdmNormObj}
    (map : AdmNormHom source target) : Type 1 :=
  CompletedRecordWeakEquivalence map.recordMap

inductive Phase211GroundingClass where
  | replayGrounded
  | adminGrounded
  | formalClosure
  | ungrounded

structure CompletedRecordMapHomotopyConstructorClassification where
  rawStructure : Phase211GroundingClass
  refl : Phase211GroundingClass
  ofPointwiseEq : Phase211GroundingClass
  symm : Phase211GroundingClass
  trans : Phase211GroundingClass
  replayRecordEquivCompSymm : Phase211GroundingClass
  replayRecordEquivSymmComp : Phase211GroundingClass
  adminStructEquivCompSymm : Phase211GroundingClass
  adminStructEquivSymmComp : Phase211GroundingClass

/-- Phase 2.11 constructor classification for the shadow map-homotopy layer.

The raw structure constructor remains ungrounded: it is a generic proof-relevant
relation with no replay/admin semantics attached. The currently exported
introduction and closure operations are still formal closure operations over that
raw relation. -/
def completedRecordMapHomotopyConstructorClassification :
    CompletedRecordMapHomotopyConstructorClassification where
  rawStructure := .ungrounded
  refl := .formalClosure
  ofPointwiseEq := .formalClosure
  symm := .formalClosure
  trans := .formalClosure
  replayRecordEquivCompSymm := .replayGrounded
  replayRecordEquivSymmComp := .replayGrounded
  adminStructEquivCompSymm := .adminGrounded
  adminStructEquivSymmComp := .adminGrounded

abbrev AdmNormHomotopyConstructorClassification :=
  CompletedRecordMapHomotopyConstructorClassification

/-- `AdmNormHomotopy` is a transparent alias of `CompletedRecordMapHomotopy`, so
its constructor classification is inherited verbatim. -/
def admNormHomotopyConstructorClassification :
    AdmNormHomotopyConstructorClassification :=
  completedRecordMapHomotopyConstructorClassification

structure CompletedRecordWeakEquivalenceConstructorClassification where
  rawStructure : Phase211GroundingClass
  id : Phase211GroundingClass
  replayRecordEquivBridge : Phase211GroundingClass
  adminStructEquivBridge : Phase211GroundingClass

/-- Phase 2.11 constructor classification for shadow weak equivalences.

The raw structure constructor is still ungrounded, the identity constructor is
formal closure, and the new replay bridge `weakEquivOfRecordEquiv` is genuinely
replay-grounded. -/
def completedRecordWeakEquivalenceConstructorClassification :
    CompletedRecordWeakEquivalenceConstructorClassification where
  rawStructure := .ungrounded
  id := .formalClosure
  replayRecordEquivBridge := .replayGrounded
  adminStructEquivBridge := .adminGrounded

abbrev AdmNormWeakEquivalenceConstructorClassification :=
  CompletedRecordWeakEquivalenceConstructorClassification

/-- `AdmNormWeakEquivalence` is a transparent alias of
`CompletedRecordWeakEquivalence`, so its constructor classification is inherited
verbatim. -/
def admNormWeakEquivalenceConstructorClassification :
    AdmNormWeakEquivalenceConstructorClassification :=
  completedRecordWeakEquivalenceConstructorClassification

/-! ### Phase 2.11: replay grounding of the shadow completed-record substrate

The localization layer above is built over the shadow `CompletedRecord`
substrate. The real replay/admin development lives instead over
`RealObjects.CompletedReconstructionRecord`. The definitions below are the
first explicit bridge: a shadow completed record can be *realized* by a real
completed reconstruction record when their dependency/requirement data agree
exactly, and any real replay-level `RecordEquiv` between such realizations
induces a shadow weak equivalence.

This does not yet ground arbitrary `CompletedRecordMapHomotopy` constructors in
real replay data. It does ground a nontrivial family of shadow weak
equivalences in actual replay-level equivalence, rather than generated labels.
-/

structure CompletedRecordReplayRealization
    (setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup)
    {n : Nat} (shadow : CompletedRecord n) where
  real : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup
  length_eq : real.n = n
  requires_iff_dep_edge :
    ∀ (j i : Fin n),
      i ∈ shadow.requires j ↔
        real.dep.edge (Fin.cast length_eq.symm i) (Fin.cast length_eq.symm j) = true

namespace CompletedRecordReplayRealization

def shadowLengthEq
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordEquiv
      sourceReal.real targetReal.real) :
    sourceLength = targetLength := by
  calc
    sourceLength = sourceReal.real.n := sourceReal.length_eq.symm
    _ = targetReal.real.n := h.n_eq
    _ = targetLength := targetReal.length_eq

def mapOfRecordEquiv
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordEquiv
      sourceReal.real targetReal.real) :
    CompletedRecordMap source target where
  packetMap i := some (Fin.cast (shadowLengthEq sourceReal targetReal h) i)
  preservesRequires := by
    intro j i hiReq j' hj'
    have hjEq : j' = Fin.cast (shadowLengthEq sourceReal targetReal h) j := by
      simpa using hj'.symm
    subst hjEq
    let iTarget : Fin targetLength := Fin.cast (shadowLengthEq sourceReal targetReal h) i
    have hiReal : sourceReal.real.dep.edge
        (Fin.cast sourceReal.length_eq.symm i)
        (Fin.cast sourceReal.length_eq.symm j) = true :=
      (sourceReal.requires_iff_dep_edge j i).mp hiReq
    have hiRealTarget : targetReal.real.dep.edge
        (Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm i))
        (Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm j)) = true := by
      rw [← h.dep_edge_eq (Fin.cast sourceReal.length_eq.symm i)
        (Fin.cast sourceReal.length_eq.symm j)]
      exact hiReal
    have hiCast :
        Fin.cast targetReal.length_eq.symm iTarget =
          Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm i) := by
      apply Fin.ext
      rfl
    have hjCast :
        Fin.cast targetReal.length_eq.symm (Fin.cast (shadowLengthEq sourceReal targetReal h) j) =
          Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm j) := by
      apply Fin.ext
      rfl
    have hiTargetReqReal : targetReal.real.dep.edge
        (Fin.cast targetReal.length_eq.symm iTarget)
        (Fin.cast targetReal.length_eq.symm (Fin.cast (shadowLengthEq sourceReal targetReal h) j)) = true := by
      rw [hiCast, hjCast]
      exact hiRealTarget
    have hiTargetReq : iTarget ∈ target.requires (Fin.cast (shadowLengthEq sourceReal targetReal h) j) :=
      (targetReal.requires_iff_dep_edge (Fin.cast (shadowLengthEq sourceReal targetReal h) j) iTarget).mpr hiTargetReqReal
    exact ⟨iTarget, rfl, hiTargetReq⟩
  preservesTraceOrder := by
    intro j i hiReq j' i' hj' hi'
    have hjEq : j' = Fin.cast (shadowLengthEq sourceReal targetReal h) j := by
      simpa using hj'.symm
    have hiEq : i' = Fin.cast (shadowLengthEq sourceReal targetReal h) i := by
      simpa using hi'.symm
    subst hjEq
    subst hiEq
    have hiTargetReq : Fin.cast (shadowLengthEq sourceReal targetReal h) i ∈
        target.requires (Fin.cast (shadowLengthEq sourceReal targetReal h) j) := by
      have hiReal : sourceReal.real.dep.edge
          (Fin.cast sourceReal.length_eq.symm i)
          (Fin.cast sourceReal.length_eq.symm j) = true :=
        (sourceReal.requires_iff_dep_edge j i).mp hiReq
      have hiRealTarget : targetReal.real.dep.edge
          (Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm i))
          (Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm j)) = true := by
        rw [← h.dep_edge_eq (Fin.cast sourceReal.length_eq.symm i)
          (Fin.cast sourceReal.length_eq.symm j)]
        exact hiReal
      have hiCast :
          Fin.cast targetReal.length_eq.symm (Fin.cast (shadowLengthEq sourceReal targetReal h) i) =
            Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm i) := by
        apply Fin.ext
        rfl
      have hjCast :
          Fin.cast targetReal.length_eq.symm (Fin.cast (shadowLengthEq sourceReal targetReal h) j) =
            Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm j) := by
        apply Fin.ext
        rfl
      have hiTargetReqReal : targetReal.real.dep.edge
          (Fin.cast targetReal.length_eq.symm (Fin.cast (shadowLengthEq sourceReal targetReal h) i))
          (Fin.cast targetReal.length_eq.symm (Fin.cast (shadowLengthEq sourceReal targetReal h) j)) = true := by
        rw [hiCast, hjCast]
        exact hiRealTarget
      exact (targetReal.requires_iff_dep_edge
        (Fin.cast (shadowLengthEq sourceReal targetReal h) j)
        (Fin.cast (shadowLengthEq sourceReal targetReal h) i)).mpr hiTargetReqReal
    exact target.dep.upper _ _ (target.c1 _ _ hiTargetReq)

theorem mapOfRecordEquiv_packetMap
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordEquiv
      sourceReal.real targetReal.real)
    (i : Fin sourceLength) :
    (mapOfRecordEquiv sourceReal targetReal h).packetMap i =
      some (Fin.cast (shadowLengthEq sourceReal targetReal h) i) :=
  rfl

theorem mapOfRecordEquiv_comp_symm_packetMap
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordEquiv
      sourceReal.real targetReal.real)
    (i : Fin sourceLength) :
    (CompletedRecordMap.comp
      (mapOfRecordEquiv sourceReal targetReal h)
      (mapOfRecordEquiv targetReal sourceReal h.symm)).packetMap i = some i := by
  change some
      (Fin.cast (shadowLengthEq targetReal sourceReal h.symm)
        (Fin.cast (shadowLengthEq sourceReal targetReal h) i)) = some i
  apply congrArg some
  apply Fin.ext
  rfl

theorem mapOfRecordEquiv_symm_comp_packetMap
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordEquiv
      sourceReal.real targetReal.real)
    (i : Fin targetLength) :
    (CompletedRecordMap.comp
      (mapOfRecordEquiv targetReal sourceReal h.symm)
      (mapOfRecordEquiv sourceReal targetReal h)).packetMap i = some i := by
  change some
      (Fin.cast (shadowLengthEq sourceReal targetReal h)
        (Fin.cast (shadowLengthEq targetReal sourceReal h.symm) i)) = some i
  apply congrArg some
  apply Fin.ext
  rfl

def weakEquivOfRecordEquiv
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordEquiv
      sourceReal.real targetReal.real) :
    CompletedRecordWeakEquivalence (mapOfRecordEquiv sourceReal targetReal h) where
  inverse := mapOfRecordEquiv targetReal sourceReal h.symm
  leftHomotopy := CompletedRecordMapHomotopy.ofPointwiseEq <|
    mapOfRecordEquiv_comp_symm_packetMap sourceReal targetReal h
  rightHomotopy := CompletedRecordMapHomotopy.ofPointwiseEq <|
    mapOfRecordEquiv_symm_comp_packetMap sourceReal targetReal h

def admNormWeakEquivOfRecordEquiv
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordEquiv
      sourceReal.real targetReal.real) :
    AdmNormWeakEquivalence
      ({ recordMap := mapOfRecordEquiv sourceReal targetReal h } :
        AdmNormHom ⟨sourceLength, source⟩ ⟨targetLength, target⟩) :=
  weakEquivOfRecordEquiv sourceReal targetReal h

end CompletedRecordReplayRealization

namespace CompletedRecordReplayRealization

def shadowLengthEqOfStructEquiv
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {BR : setup.BoundaryObject → setup.BoundaryObject → Prop}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordStructEquiv BR
      sourceReal.real targetReal.real) :
    sourceLength = targetLength := by
  calc
    sourceLength = sourceReal.real.n := sourceReal.length_eq.symm
    _ = targetReal.real.n := h.n_eq
    _ = targetLength := targetReal.length_eq

def mapOfStructEquiv
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {BR : setup.BoundaryObject → setup.BoundaryObject → Prop}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordStructEquiv BR
      sourceReal.real targetReal.real) :
    CompletedRecordMap source target where
  packetMap i := some (Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) i)
  preservesRequires := by
    intro j i hiReq j' hj'
    have hjEq : j' = Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) j := by
      simpa using hj'.symm
    subst hjEq
    let iTarget : Fin targetLength := Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) i
    have hiReal : sourceReal.real.dep.edge
        (Fin.cast sourceReal.length_eq.symm i)
        (Fin.cast sourceReal.length_eq.symm j) = true :=
      (sourceReal.requires_iff_dep_edge j i).mp hiReq
    have hiRealTarget : targetReal.real.dep.edge
        (Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm i))
        (Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm j)) = true := by
      rw [← h.dep_edge_eq (Fin.cast sourceReal.length_eq.symm i)
        (Fin.cast sourceReal.length_eq.symm j)]
      exact hiReal
    have hiCast :
        Fin.cast targetReal.length_eq.symm iTarget =
          Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm i) := by
      apply Fin.ext
      rfl
    have hjCast :
        Fin.cast targetReal.length_eq.symm
            (Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) j) =
          Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm j) := by
      apply Fin.ext
      rfl
    have hiTargetReqReal : targetReal.real.dep.edge
        (Fin.cast targetReal.length_eq.symm iTarget)
        (Fin.cast targetReal.length_eq.symm
          (Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) j)) = true := by
      rw [hiCast, hjCast]
      exact hiRealTarget
    have hiTargetReq : iTarget ∈ target.requires
        (Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) j) :=
      (targetReal.requires_iff_dep_edge
        (Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) j) iTarget).mpr hiTargetReqReal
    exact ⟨iTarget, rfl, hiTargetReq⟩
  preservesTraceOrder := by
    intro j i hiReq j' i' hj' hi'
    have hjEq : j' = Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) j := by
      simpa using hj'.symm
    have hiEq : i' = Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) i := by
      simpa using hi'.symm
    subst hjEq
    subst hiEq
    have hiTargetReq : Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) i ∈
        target.requires (Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) j) := by
      have hiReal : sourceReal.real.dep.edge
          (Fin.cast sourceReal.length_eq.symm i)
          (Fin.cast sourceReal.length_eq.symm j) = true :=
        (sourceReal.requires_iff_dep_edge j i).mp hiReq
      have hiRealTarget : targetReal.real.dep.edge
          (Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm i))
          (Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm j)) = true := by
        rw [← h.dep_edge_eq (Fin.cast sourceReal.length_eq.symm i)
          (Fin.cast sourceReal.length_eq.symm j)]
        exact hiReal
      have hiCast :
          Fin.cast targetReal.length_eq.symm
            (Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) i) =
              Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm i) := by
        apply Fin.ext
        rfl
      have hjCast :
          Fin.cast targetReal.length_eq.symm
            (Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) j) =
              Fin.cast h.n_eq (Fin.cast sourceReal.length_eq.symm j) := by
        apply Fin.ext
        rfl
      have hiTargetReqReal : targetReal.real.dep.edge
          (Fin.cast targetReal.length_eq.symm
            (Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) i))
          (Fin.cast targetReal.length_eq.symm
            (Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) j)) = true := by
        rw [hiCast, hjCast]
        exact hiRealTarget
      exact (targetReal.requires_iff_dep_edge
        (Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) j)
        (Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) i)).mpr hiTargetReqReal
    exact target.dep.upper _ _ (target.c1 _ _ hiTargetReq)

def boundaryAdminStructEquivSymm
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordStructEquiv
      (@TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.BoundaryAdminEquiv setup)
      sourceReal.real targetReal.real) :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordStructEquiv
      (@TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.BoundaryAdminEquiv setup)
      targetReal.real sourceReal.real :=
  TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordStructEquiv.symm
    (fun {Y₁ Y₂} hY =>
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.BoundaryAdminEquiv.symm' hY) h

theorem mapOfBoundaryAdminStructEquiv_comp_symm_packetMap
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordStructEquiv
      (@TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.BoundaryAdminEquiv setup)
      sourceReal.real targetReal.real)
    (i : Fin sourceLength) :
    (CompletedRecordMap.comp
      (mapOfStructEquiv sourceReal targetReal h)
      (mapOfStructEquiv targetReal sourceReal
        (boundaryAdminStructEquivSymm sourceReal targetReal h))).packetMap i = some i := by
  change some
      (Fin.cast
        (shadowLengthEqOfStructEquiv targetReal sourceReal
          (boundaryAdminStructEquivSymm sourceReal targetReal h))
        (Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h) i)) = some i
  apply congrArg some
  apply Fin.ext
  rfl

theorem mapOfBoundaryAdminStructEquiv_symm_comp_packetMap
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordStructEquiv
      (@TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.BoundaryAdminEquiv setup)
      sourceReal.real targetReal.real)
    (i : Fin targetLength) :
    (CompletedRecordMap.comp
      (mapOfStructEquiv targetReal sourceReal
        (boundaryAdminStructEquivSymm sourceReal targetReal h))
      (mapOfStructEquiv sourceReal targetReal h)).packetMap i = some i := by
  change some
      (Fin.cast (shadowLengthEqOfStructEquiv sourceReal targetReal h)
        (Fin.cast
          (shadowLengthEqOfStructEquiv targetReal sourceReal
            (boundaryAdminStructEquivSymm sourceReal targetReal h)) i)) = some i
  apply congrArg some
  apply Fin.ext
  rfl

def weakEquivOfBoundaryAdminStructEquiv
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordStructEquiv
      (@TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.BoundaryAdminEquiv setup)
      sourceReal.real targetReal.real) :
    CompletedRecordWeakEquivalence (mapOfStructEquiv sourceReal targetReal h) where
  inverse := mapOfStructEquiv targetReal sourceReal
    (boundaryAdminStructEquivSymm sourceReal targetReal h)
  leftHomotopy := CompletedRecordMapHomotopy.ofPointwiseEq <|
    mapOfBoundaryAdminStructEquiv_comp_symm_packetMap sourceReal targetReal h
  rightHomotopy := CompletedRecordMapHomotopy.ofPointwiseEq <|
    mapOfBoundaryAdminStructEquiv_symm_comp_packetMap sourceReal targetReal h

def admNormWeakEquivOfBoundaryAdminStructEquiv
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordStructEquiv
      (@TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.BoundaryAdminEquiv setup)
      sourceReal.real targetReal.real) :
    AdmNormWeakEquivalence
      ({ recordMap := mapOfStructEquiv sourceReal targetReal h } :
        AdmNormHom ⟨sourceLength, source⟩ ⟨targetLength, target⟩) :=
  weakEquivOfBoundaryAdminStructEquiv sourceReal targetReal h

end CompletedRecordReplayRealization

def replayRecordEquivCompSymmHomotopy
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {source target : AdmNormObj}
    (sourceReal : CompletedRecordReplayRealization setup source.record)
    (targetReal : CompletedRecordReplayRealization setup target.record)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordEquiv
      sourceReal.real targetReal.real) :
    CompletedRecordMapHomotopy
      (CompletedRecordMap.comp
        (CompletedRecordReplayRealization.mapOfRecordEquiv sourceReal targetReal h)
        (CompletedRecordReplayRealization.mapOfRecordEquiv targetReal sourceReal h.symm))
      (CompletedRecordMap.id source.record) :=
  CompletedRecordMapHomotopy.ofPointwiseEq <| fun i => by
    simpa using
      CompletedRecordReplayRealization.mapOfRecordEquiv_comp_symm_packetMap sourceReal targetReal h i

def replayRecordEquivSymmCompHomotopy
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {source target : AdmNormObj}
    (sourceReal : CompletedRecordReplayRealization setup source.record)
    (targetReal : CompletedRecordReplayRealization setup target.record)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordEquiv
      sourceReal.real targetReal.real) :
    CompletedRecordMapHomotopy
      (CompletedRecordMap.comp
        (CompletedRecordReplayRealization.mapOfRecordEquiv targetReal sourceReal h.symm)
        (CompletedRecordReplayRealization.mapOfRecordEquiv sourceReal targetReal h))
      (CompletedRecordMap.id target.record) :=
  CompletedRecordMapHomotopy.ofPointwiseEq <| fun i => by
    simpa using
      CompletedRecordReplayRealization.mapOfRecordEquiv_symm_comp_packetMap sourceReal targetReal h i

def adminStructEquivCompSymmHomotopy
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {source target : AdmNormObj}
    (sourceReal : CompletedRecordReplayRealization setup source.record)
    (targetReal : CompletedRecordReplayRealization setup target.record)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordStructEquiv
      (@TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.BoundaryAdminEquiv setup)
      sourceReal.real targetReal.real) :
    CompletedRecordMapHomotopy
      (CompletedRecordMap.comp
        (CompletedRecordReplayRealization.mapOfStructEquiv sourceReal targetReal h)
        (CompletedRecordReplayRealization.mapOfStructEquiv targetReal sourceReal
          (CompletedRecordReplayRealization.boundaryAdminStructEquivSymm sourceReal targetReal h)))
      (CompletedRecordMap.id source.record) :=
  CompletedRecordMapHomotopy.ofPointwiseEq <| fun i => by
    simpa using
      CompletedRecordReplayRealization.mapOfBoundaryAdminStructEquiv_comp_symm_packetMap
        sourceReal targetReal h i

def adminStructEquivSymmCompHomotopy
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
    {source target : AdmNormObj}
    (sourceReal : CompletedRecordReplayRealization setup source.record)
    (targetReal : CompletedRecordReplayRealization setup target.record)
    (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordStructEquiv
      (@TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.BoundaryAdminEquiv setup)
      sourceReal.real targetReal.real) :
    CompletedRecordMapHomotopy
      (CompletedRecordMap.comp
        (CompletedRecordReplayRealization.mapOfStructEquiv targetReal sourceReal
          (CompletedRecordReplayRealization.boundaryAdminStructEquivSymm sourceReal targetReal h))
        (CompletedRecordReplayRealization.mapOfStructEquiv sourceReal targetReal h))
      (CompletedRecordMap.id target.record) :=
  CompletedRecordMapHomotopy.ofPointwiseEq <| fun i => by
    simpa using
      CompletedRecordReplayRealization.mapOfBoundaryAdminStructEquiv_symm_comp_packetMap
        sourceReal targetReal h i

inductive ReplayGroundedCompletedRecordMapHomotopy :
    {A B : AdmNormObj} →
      {f g : CompletedRecordMap A.record B.record} →
      CompletedRecordMapHomotopy f g → Type 1 where
  | recordEquivCompSymm
      {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
      {source target : AdmNormObj}
      (sourceReal : CompletedRecordReplayRealization setup source.record)
      (targetReal : CompletedRecordReplayRealization setup target.record)
      (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordEquiv
        sourceReal.real targetReal.real) :
      ReplayGroundedCompletedRecordMapHomotopy
        (A := source) (B := source)
        (replayRecordEquivCompSymmHomotopy sourceReal targetReal h)
  | recordEquivSymmComp
      {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
      {source target : AdmNormObj}
      (sourceReal : CompletedRecordReplayRealization setup source.record)
      (targetReal : CompletedRecordReplayRealization setup target.record)
      (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordEquiv
        sourceReal.real targetReal.real) :
      ReplayGroundedCompletedRecordMapHomotopy
        (A := target) (B := target)
        (replayRecordEquivSymmCompHomotopy sourceReal targetReal h)

inductive AdminGroundedCompletedRecordMapHomotopy :
    {A B : AdmNormObj} →
      {f g : CompletedRecordMap A.record B.record} →
      CompletedRecordMapHomotopy f g → Type 1 where
  | structEquivCompSymm
      {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
      {source target : AdmNormObj}
      (sourceReal : CompletedRecordReplayRealization setup source.record)
      (targetReal : CompletedRecordReplayRealization setup target.record)
      (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordStructEquiv
        (@TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.BoundaryAdminEquiv setup)
        sourceReal.real targetReal.real) :
      AdminGroundedCompletedRecordMapHomotopy
        (A := source) (B := source)
        (adminStructEquivCompSymmHomotopy sourceReal targetReal h)
  | structEquivSymmComp
      {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
      {source target : AdmNormObj}
      (sourceReal : CompletedRecordReplayRealization setup source.record)
      (targetReal : CompletedRecordReplayRealization setup target.record)
      (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordStructEquiv
        (@TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.BoundaryAdminEquiv setup)
        sourceReal.real targetReal.real) :
      AdminGroundedCompletedRecordMapHomotopy
        (A := target) (B := target)
        (adminStructEquivSymmCompHomotopy sourceReal targetReal h)

inductive FormallyGeneratedCompletedRecordMapHomotopy :
    {A B : AdmNormObj} →
      {f g : CompletedRecordMap A.record B.record} →
      CompletedRecordMapHomotopy f g → Type 1 where
  | refl {A B : AdmNormObj} (map : CompletedRecordMap A.record B.record) :
      FormallyGeneratedCompletedRecordMapHomotopy (CompletedRecordMapHomotopy.refl map)
  | ofPointwiseEq {A B : AdmNormObj} {f g : CompletedRecordMap A.record B.record}
      (hEq : ∀ i : Fin A.length, f.packetMap i = g.packetMap i) :
      FormallyGeneratedCompletedRecordMapHomotopy
        (CompletedRecordMapHomotopy.ofPointwiseEq hEq)
  | symm {A B : AdmNormObj} {f g : CompletedRecordMap A.record B.record}
      {h : CompletedRecordMapHomotopy f g} :
      FormallyGeneratedCompletedRecordMapHomotopy h →
        FormallyGeneratedCompletedRecordMapHomotopy (CompletedRecordMapHomotopy.symm h)
  | trans
      {A B : AdmNormObj}
      {f g middle : CompletedRecordMap A.record B.record}
      {h₁ : CompletedRecordMapHomotopy f middle}
      {h₂ : CompletedRecordMapHomotopy middle g} :
      FormallyGeneratedCompletedRecordMapHomotopy h₁ →
      FormallyGeneratedCompletedRecordMapHomotopy h₂ →
        FormallyGeneratedCompletedRecordMapHomotopy (CompletedRecordMapHomotopy.trans h₁ h₂)

abbrev ReplayGroundedAdmNormHomotopy
    {source target : AdmNormObj}
    {left right : AdmNormHom source target}
    (homotopy : AdmNormHomotopy left right) : Type 1 :=
  ReplayGroundedCompletedRecordMapHomotopy (A := source) (B := target) homotopy

abbrev AdminGroundedAdmNormHomotopy
    {source target : AdmNormObj}
    {left right : AdmNormHom source target}
    (homotopy : AdmNormHomotopy left right) : Type 1 :=
  AdminGroundedCompletedRecordMapHomotopy (A := source) (B := target) homotopy

inductive GroundedAdmNormHomotopy
    {source target : AdmNormObj}
    {left right : AdmNormHom source target} :
    AdmNormHomotopy left right → Type 1 where
  | replay {homotopy : AdmNormHomotopy left right} :
      ReplayGroundedAdmNormHomotopy homotopy → GroundedAdmNormHomotopy homotopy
  | admin {homotopy : AdmNormHomotopy left right} :
      AdminGroundedAdmNormHomotopy homotopy → GroundedAdmNormHomotopy homotopy

inductive ReplayGroundedCompletedRecordWeakEquivalence :
    {A B : AdmNormObj} →
      {map : CompletedRecordMap A.record B.record} →
      CompletedRecordWeakEquivalence map → Type 1 where
  | ofRecordEquiv
      {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
      {source target : AdmNormObj}
      (sourceReal : CompletedRecordReplayRealization setup source.record)
      (targetReal : CompletedRecordReplayRealization setup target.record)
      (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordEquiv
        sourceReal.real targetReal.real) :
      ReplayGroundedCompletedRecordWeakEquivalence
        (A := source) (B := target)
        (CompletedRecordReplayRealization.weakEquivOfRecordEquiv sourceReal targetReal h)

inductive AdminGroundedCompletedRecordWeakEquivalence :
    {A B : AdmNormObj} →
      {map : CompletedRecordMap A.record B.record} →
      CompletedRecordWeakEquivalence map → Type 1 where
  | ofBoundaryAdminStructEquiv
      {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup}
      {source target : AdmNormObj}
      (sourceReal : CompletedRecordReplayRealization setup source.record)
      (targetReal : CompletedRecordReplayRealization setup target.record)
      (h : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordStructEquiv
        (@TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.BoundaryAdminEquiv setup)
        sourceReal.real targetReal.real) :
      AdminGroundedCompletedRecordWeakEquivalence
        (A := source) (B := target)
        (CompletedRecordReplayRealization.weakEquivOfBoundaryAdminStructEquiv
          sourceReal targetReal h)

abbrev ReplayGroundedAdmNormWeakEquivalence
    {source target : AdmNormObj}
    {map : AdmNormHom source target}
    (weakEquiv : AdmNormWeakEquivalence map) : Type 1 :=
  ReplayGroundedCompletedRecordWeakEquivalence (A := source) (B := target) weakEquiv

abbrev AdminGroundedAdmNormWeakEquivalence
    {source target : AdmNormObj}
    {map : AdmNormHom source target}
    (weakEquiv : AdmNormWeakEquivalence map) : Type 1 :=
  AdminGroundedCompletedRecordWeakEquivalence (A := source) (B := target) weakEquiv

inductive GroundedAdmNormWeakEquivalence
    {source target : AdmNormObj}
    {map : AdmNormHom source target} :
    AdmNormWeakEquivalence map → Type 1 where
  | replay {weakEquiv : AdmNormWeakEquivalence map} :
      ReplayGroundedAdmNormWeakEquivalence weakEquiv → GroundedAdmNormWeakEquivalence weakEquiv
  | admin {weakEquiv : AdmNormWeakEquivalence map} :
      AdminGroundedAdmNormWeakEquivalence weakEquiv → GroundedAdmNormWeakEquivalence weakEquiv

theorem weakEquivOfRecordEquiv_is_replayGrounded :
    completedRecordWeakEquivalenceConstructorClassification.replayRecordEquivBridge =
      Phase211GroundingClass.replayGrounded :=
  rfl

theorem weakEquivOfBoundaryAdminStructEquiv_is_adminGrounded :
    completedRecordWeakEquivalenceConstructorClassification.adminStructEquivBridge =
      Phase211GroundingClass.adminGrounded :=
  rfl

/-! ### Phase 5: normalization degree from real sink-peel depth

The degree source used here is the actual sink-peel reconstruction depth:
`PeelChain.length`, proved in the real-object layer to equal the packet count
of the completed reconstruction record. This is deliberately not a packet
midpoint, fake weight label, or synthetic `Fin n → Int` assignment.
-/

namespace RealNormalizationDegree

abbrev Setup := TraceCalc.LayerB.RealObjects.RewriteCalculusSetup
abbrev RealRecord (setup : Setup) :=
  TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup
abbrev PeelChain {setup : Setup} (record : RealRecord setup) :=
  TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord.PeelChain record
abbrev RecordEquiv {setup : Setup} (source target : RealRecord setup) :=
  TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.RecordEquiv source target

def normalizationDegreeOfRecord {setup : Setup} (record : RealRecord setup) : Int :=
  Int.ofNat record.n

def normalizationDegreeOfPeelChain {setup : Setup} {record : RealRecord setup}
    (chain : PeelChain record) : Int :=
  Int.ofNat chain.length

theorem normalizationDegreeOfPeelChain_eq_record
    {setup : Setup} {record : RealRecord setup} (chain : PeelChain record) :
    normalizationDegreeOfPeelChain chain = normalizationDegreeOfRecord record := by
  unfold normalizationDegreeOfPeelChain normalizationDegreeOfRecord
  rw [TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord.PeelChain.length_eq chain]

theorem degree_dependency_monotone
    {n : Nat} (record : CompletedRecord n) {i j : Fin n}
    (hdep : i ∈ record.requires j) :
    (Int.ofNat i.val) < (Int.ofNat j.val) := by
  exact Int.ofNat_lt.mpr (record.dep.upper i j (record.c1 j i hdep))

theorem degree_cut_dependency_closed
    {n : Nat} (record : CompletedRecord n) (threshold : Nat)
    (hThreshold : threshold ≤ n) {j i : Fin n}
    (hj : j ∈ (TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.ofLe record threshold hThreshold).lowerSet)
    (hi : i ∈ record.requires j) :
    i ∈ (TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.ofLe record threshold hThreshold).lowerSet :=
  (TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.ofLe record threshold hThreshold).lower_dependency_closed hj hi

theorem degree_shift_compatible
    {setup : Setup} (record : RealRecord setup) (shiftDepth : Nat) :
    normalizationDegreeOfRecord record + Int.ofNat shiftDepth =
      Int.ofNat (record.n + shiftDepth) := by
  unfold normalizationDegreeOfRecord
  simp [Int.ofNat_add]

structure NormalizationAmplitude where
  lower : Int
  upper : Int
  lower_le_upper : lower ≤ upper

def normalizationAmplitude {setup : Setup} (record : RealRecord setup) :
    NormalizationAmplitude where
  lower := 0
  upper := normalizationDegreeOfRecord record
  lower_le_upper := by
    unfold normalizationDegreeOfRecord
    exact Int.ofNat_nonneg record.n

def isNonpositive (amplitude : NormalizationAmplitude) : Prop :=
  amplitude.upper ≤ 0

def isNonnegative (amplitude : NormalizationAmplitude) : Prop :=
  0 ≤ amplitude.lower

def isZeroAmplitude (amplitude : NormalizationAmplitude) : Prop :=
  amplitude.lower = 0 ∧ amplitude.upper = 0

theorem normalizationAmplitude_nonnegative {setup : Setup} (record : RealRecord setup) :
    isNonnegative (normalizationAmplitude record) := by
  unfold isNonnegative normalizationAmplitude
  rfl

theorem normalizationAmplitude_zero_iff {setup : Setup} (record : RealRecord setup) :
    isZeroAmplitude (normalizationAmplitude record) ↔ record.n = 0 := by
  constructor
  · intro h
    rcases h with ⟨_, hupper⟩
    unfold normalizationAmplitude normalizationDegreeOfRecord at hupper
    exact Int.ofNat_eq_zero.mp hupper
  · intro h
    constructor
    · rfl
    · unfold normalizationAmplitude normalizationDegreeOfRecord
      simp [h]

theorem normalizationDegree_recordEquiv_invariant
    {setup : Setup} {source target : RealRecord setup}
    (h : RecordEquiv source target) :
    normalizationDegreeOfRecord source = normalizationDegreeOfRecord target := by
  unfold normalizationDegreeOfRecord
  rw [h.n_eq]

theorem normalizationAmplitude_recordEquiv_invariant
    {setup : Setup} {source target : RealRecord setup}
    (h : RecordEquiv source target) :
    (normalizationAmplitude source).lower = (normalizationAmplitude target).lower ∧
      (normalizationAmplitude source).upper = (normalizationAmplitude target).upper := by
  constructor
  · rfl
  · exact normalizationDegree_recordEquiv_invariant h

theorem normalizationDegree_replayWeakEquiv_invariant
    {setup : Setup}
    {sourceLength targetLength : Nat}
    {source : CompletedRecord sourceLength}
    {target : CompletedRecord targetLength}
    (sourceReal : CompletedRecordReplayRealization setup source)
    (targetReal : CompletedRecordReplayRealization setup target)
    (h : RecordEquiv sourceReal.real targetReal.real) :
    normalizationDegreeOfRecord sourceReal.real =
      normalizationDegreeOfRecord targetReal.real :=
  normalizationDegree_recordEquiv_invariant h

/-! ### Phase 6: normalization complex from real peel-chain differentials -/

abbrev PeelDifferentialPackage {setup : Setup} {record : RealRecord setup}
    (chain : PeelChain record) :=
  TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.PeelChainDifferentialPackage
    (setup := setup) chain

abbrev PeelDifferential {setup : Setup} {record : RealRecord setup}
    {chain : PeelChain record} :=
  TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.PeelChainAdjacentDifferential
    (setup := setup) chain

abbrev PeelNullBoundary {setup : Setup} {record : RealRecord setup}
    {chain : PeelChain record}
    (first second : PeelDifferential (setup := setup) (chain := chain)) :=
  TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.PeelChainTwoStepNullBoundary
    (setup := setup) chain first second

structure NormalizationComplex {setup : Setup} (record : RealRecord setup) where
  chain : PeelChain record
  differentialPackage : PeelDifferentialPackage (setup := setup) chain

namespace NormalizationComplex

def gradeObject {setup : Setup} {record : RealRecord setup}
    (complex : NormalizationComplex record) (degree : Nat) :
    Option (RealRecord setup) :=
  TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.PeelChainDifferentialPackage.gradeObject
    (setup := setup) complex.differentialPackage degree

def differential {setup : Setup} {record : RealRecord setup}
    (complex : NormalizationComplex record) (degree : Nat) :
    Option (PeelDifferential (setup := setup) (chain := complex.chain)) :=
  TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.PeelChainDifferentialPackage.differential
    (setup := setup) complex.differentialPackage degree

def d_next_comp_d_zero {setup : Setup} {record : RealRecord setup}
    (complex : NormalizationComplex record)
    {degree : Nat}
    {first second : PeelDifferential (setup := setup) (chain := complex.chain)}
    (hfirst : complex.differential degree = some first)
    (hsecond : complex.differential (degree + 1) = some second) :
    PeelNullBoundary (setup := setup) (chain := complex.chain) first second :=
  TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.PeelChainDifferentialPackage.d_next_comp_d
    (setup := setup) complex.differentialPackage hfirst hsecond

theorem differential_degree_within_amplitude
    {setup : Setup} {record : RealRecord setup}
    (complex : NormalizationComplex record)
    {degree : Nat}
    {step : PeelDifferential (setup := setup) (chain := complex.chain)}
    (hstep : complex.differential degree = some step) :
    Int.ofNat degree ≤ (normalizationAmplitude record).upper := by
  unfold normalizationAmplitude normalizationDegreeOfRecord
  exact Int.ofNat_le.mpr
    (TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.PeelChainDifferentialPackage.differential_degree_within_amplitude
      (setup := setup) complex.differentialPackage hstep)

theorem degree_source_matches_phase5
    {setup : Setup} {record : RealRecord setup}
    (complex : NormalizationComplex record) :
    normalizationDegreeOfPeelChain complex.chain = normalizationDegreeOfRecord record :=
  normalizationDegreeOfPeelChain_eq_record complex.chain

end NormalizationComplex

/-! ### Phase 7: cycles, boundaries, and homology from normalization complexes -/

structure NormalizationCycle {setup : Setup} {record : RealRecord setup}
    (complex : NormalizationComplex record) (degree : Nat) where
  step : PeelDifferential (setup := setup) (chain := complex.chain)
  step_at_degree : complex.differential degree = some step
  nextStep : PeelDifferential (setup := setup) (chain := complex.chain)
  next_step_at_successor : complex.differential (degree + 1) = some nextStep
  nullBoundary : PeelNullBoundary (setup := setup) (chain := complex.chain) step nextStep

namespace NormalizationCycle

def ofAdjacentDifferentials {setup : Setup} {record : RealRecord setup}
    (complex : NormalizationComplex record)
    {degree : Nat}
    {step nextStep : PeelDifferential (setup := setup) (chain := complex.chain)}
    (hstep : complex.differential degree = some step)
    (hnext : complex.differential (degree + 1) = some nextStep) :
    NormalizationCycle complex degree where
  step := step
  step_at_degree := hstep
  nextStep := nextStep
  next_step_at_successor := hnext
  nullBoundary := complex.d_next_comp_d_zero hstep hnext

theorem degree_within_amplitude {setup : Setup} {record : RealRecord setup}
    {complex : NormalizationComplex record} {degree : Nat}
    (cycle : NormalizationCycle complex degree) :
    Int.ofNat degree ≤ (normalizationAmplitude record).upper :=
  NormalizationComplex.differential_degree_within_amplitude complex cycle.step_at_degree

end NormalizationCycle

structure NormalizationBoundary {setup : Setup} {record : RealRecord setup}
    (complex : NormalizationComplex record) (degree : Nat) where
  predecessorDegree : Nat
  predecessor_step : predecessorDegree + 1 = degree
  incoming : PeelDifferential (setup := setup) (chain := complex.chain)
  incoming_at_predecessor : complex.differential predecessorDegree = some incoming
  outgoing : PeelDifferential (setup := setup) (chain := complex.chain)
  outgoing_at_degree : complex.differential degree = some outgoing
  nullBoundary : PeelNullBoundary (setup := setup) (chain := complex.chain) incoming outgoing

namespace NormalizationBoundary

def ofAdjacentDifferentials {setup : Setup} {record : RealRecord setup}
    (complex : NormalizationComplex record)
    {predecessorDegree degree : Nat}
    (hdegree : predecessorDegree + 1 = degree)
    {incoming outgoing : PeelDifferential (setup := setup) (chain := complex.chain)}
    (hincoming : complex.differential predecessorDegree = some incoming)
    (houtgoing : complex.differential degree = some outgoing) :
    NormalizationBoundary complex degree where
  predecessorDegree := predecessorDegree
  predecessor_step := hdegree
  incoming := incoming
  incoming_at_predecessor := hincoming
  outgoing := outgoing
  outgoing_at_degree := houtgoing
  nullBoundary := by
    subst hdegree
    exact complex.d_next_comp_d_zero hincoming houtgoing

def toCycle {setup : Setup} {record : RealRecord setup}
    {complex : NormalizationComplex record} {degree : Nat}
    (boundary : NormalizationBoundary complex degree) :
    NormalizationCycle complex boundary.predecessorDegree where
  step := boundary.incoming
  step_at_degree := boundary.incoming_at_predecessor
  nextStep := boundary.outgoing
  next_step_at_successor := by
    rw [boundary.predecessor_step]
    exact boundary.outgoing_at_degree
  nullBoundary := boundary.nullBoundary

theorem degree_within_amplitude {setup : Setup} {record : RealRecord setup}
    {complex : NormalizationComplex record} {degree : Nat}
    (boundary : NormalizationBoundary complex degree) :
    Int.ofNat degree ≤ (normalizationAmplitude record).upper :=
  NormalizationComplex.differential_degree_within_amplitude complex boundary.outgoing_at_degree

end NormalizationBoundary

structure NormalizationHomology {setup : Setup} {record : RealRecord setup}
    (complex : NormalizationComplex record) (degree : Nat) where
  cycles : Type
  boundaries : Type
  cycleToStep : cycles → PeelDifferential (setup := setup) (chain := complex.chain)
  cycleWitness : cycles → NormalizationCycle complex degree
  boundaryWitness : boundaries → NormalizationBoundary complex degree
  boundaryToIncomingCycle :
    (boundary : boundaries) →
      NormalizationCycle complex (boundaryWitness boundary).predecessorDegree

namespace NormalizationHomology

def fromComplex {setup : Setup} {record : RealRecord setup}
    (complex : NormalizationComplex record) (degree : Nat) :
    NormalizationHomology complex degree where
  cycles := NormalizationCycle complex degree
  boundaries := NormalizationBoundary complex degree
  cycleToStep := fun cycle => cycle.step
  cycleWitness := fun cycle => cycle
  boundaryWitness := fun boundary => boundary
  boundaryToIncomingCycle := fun boundary => boundary.toCycle

theorem cycle_degree_within_amplitude {setup : Setup} {record : RealRecord setup}
    {complex : NormalizationComplex record} {degree : Nat}
    (homology : NormalizationHomology complex degree) (cycle : homology.cycles) :
    Int.ofNat degree ≤ (normalizationAmplitude record).upper :=
  (homology.cycleWitness cycle).degree_within_amplitude

theorem boundary_degree_within_amplitude {setup : Setup} {record : RealRecord setup}
    {complex : NormalizationComplex record} {degree : Nat}
    (homology : NormalizationHomology complex degree) (boundary : homology.boundaries) :
    Int.ofNat degree ≤ (normalizationAmplitude record).upper :=
  (homology.boundaryWitness boundary).degree_within_amplitude

end NormalizationHomology

end RealNormalizationDegree

inductive TraceStableInfinityObject : Type 1 where
  | ofRecord : AdmNormObj → TraceStableInfinityObject
  | zero : TraceStableInfinityObject
  | shift : TraceStableInfinityObject → TraceStableInfinityObject
  | cofiber : TraceStableInfinityObject → TraceStableInfinityObject → TraceStableInfinityObject
  | fiber : TraceStableInfinityObject → TraceStableInfinityObject → TraceStableInfinityObject
  | finiteColimit : List TraceStableInfinityObject → TraceStableInfinityObject

namespace TraceStableInfinityObject

def suspension (obj : TraceStableInfinityObject) : TraceStableInfinityObject :=
  shift obj

def cone (source target : TraceStableInfinityObject) : TraceStableInfinityObject :=
  cofiber source target

end TraceStableInfinityObject

inductive TraceStableInfinityMap :
    TraceStableInfinityObject → TraceStableInfinityObject → Type 1 where
  | ofAdmNorm {source target : AdmNormObj} :
      AdmNormHom source target →
        TraceStableInfinityMap
          (TraceStableInfinityObject.ofRecord source)
          (TraceStableInfinityObject.ofRecord target)
  | toZero {source : TraceStableInfinityObject} :
      TraceStableInfinityMap source TraceStableInfinityObject.zero
  | fromZero {target : TraceStableInfinityObject} :
      TraceStableInfinityMap TraceStableInfinityObject.zero target
  | id (obj : TraceStableInfinityObject) : TraceStableInfinityMap obj obj
  | comp {source middle target : TraceStableInfinityObject} :
      TraceStableInfinityMap source middle →
      TraceStableInfinityMap middle target →
        TraceStableInfinityMap source target
  | shiftMap {source target : TraceStableInfinityObject} :
      TraceStableInfinityMap source target →
        TraceStableInfinityMap
          (TraceStableInfinityObject.shift source)
          (TraceStableInfinityObject.shift target)
  | cofiberIn {source target : TraceStableInfinityObject} :
      TraceStableInfinityMap source target →
        TraceStableInfinityMap target (TraceStableInfinityObject.cofiber source target)
  | cofiberOut {source target : TraceStableInfinityObject} :
      TraceStableInfinityMap source target →
        TraceStableInfinityMap
          (TraceStableInfinityObject.cofiber source target)
          (TraceStableInfinityObject.shift source)
  | fiberIn {source target : TraceStableInfinityObject} :
      TraceStableInfinityMap source target →
        TraceStableInfinityMap
          (TraceStableInfinityObject.fiber source target)
          source
  | fiberOut {source target : TraceStableInfinityObject} :
      TraceStableInfinityMap source target →
        TraceStableInfinityMap
          (TraceStableInfinityObject.shift (TraceStableInfinityObject.fiber source target))
          target
  | finiteColimitIn (objects : List TraceStableInfinityObject) :
      (obj : TraceStableInfinityObject) → obj ∈ objects →
        TraceStableInfinityMap obj (TraceStableInfinityObject.finiteColimit objects)
  | invertWeakEquivalence {source target : AdmNormObj}
      (map : AdmNormHom source target) :
      AdmNormWeakEquivalence map →
        TraceStableInfinityMap
          (TraceStableInfinityObject.ofRecord target)
          (TraceStableInfinityObject.ofRecord source)

namespace TraceStableInfinityMap

def zeroSelf :
    TraceStableInfinityMap TraceStableInfinityObject.zero TraceStableInfinityObject.zero :=
  id TraceStableInfinityObject.zero

def zeroMap
    (source target : TraceStableInfinityObject) :
    TraceStableInfinityMap source target :=
  comp toZero fromZero

end TraceStableInfinityMap

inductive TraceStableInfinityHomotopy :
    {source target : TraceStableInfinityObject} →
      TraceStableInfinityMap source target →
      TraceStableInfinityMap source target → Type 1 where
  | ofAdmNorm {source target : AdmNormObj}
      {left right : AdmNormHom source target} :
      AdmNormHomotopy left right →
        TraceStableInfinityHomotopy
          (TraceStableInfinityMap.ofAdmNorm left)
          (TraceStableInfinityMap.ofAdmNorm right)
  | refl {source target : TraceStableInfinityObject}
      (map : TraceStableInfinityMap source target) :
      TraceStableInfinityHomotopy map map
  | symm {source target : TraceStableInfinityObject}
      {left right : TraceStableInfinityMap source target} :
      TraceStableInfinityHomotopy left right →
        TraceStableInfinityHomotopy right left
  | trans {source target : TraceStableInfinityObject}
      {first middle last : TraceStableInfinityMap source target} :
      TraceStableInfinityHomotopy first middle →
      TraceStableInfinityHomotopy middle last →
        TraceStableInfinityHomotopy first last
  | compCongr {source middle target : TraceStableInfinityObject}
      {left₁ left₂ : TraceStableInfinityMap source middle}
      {right₁ right₂ : TraceStableInfinityMap middle target} :
      TraceStableInfinityHomotopy left₁ left₂ →
      TraceStableInfinityHomotopy right₁ right₂ →
        TraceStableInfinityHomotopy
          (TraceStableInfinityMap.comp left₁ right₁)
          (TraceStableInfinityMap.comp left₂ right₂)
  | idLeft {source target : TraceStableInfinityObject}
      (map : TraceStableInfinityMap source target) :
      TraceStableInfinityHomotopy
        (TraceStableInfinityMap.comp (TraceStableInfinityMap.id source) map)
        map
  | idRight {source target : TraceStableInfinityObject}
      (map : TraceStableInfinityMap source target) :
      TraceStableInfinityHomotopy
        (TraceStableInfinityMap.comp map (TraceStableInfinityMap.id target))
        map
  | assoc {a b c d : TraceStableInfinityObject}
      (ab : TraceStableInfinityMap a b)
      (bc : TraceStableInfinityMap b c)
      (cd : TraceStableInfinityMap c d) :
      TraceStableInfinityHomotopy
        (TraceStableInfinityMap.comp (TraceStableInfinityMap.comp ab bc) cd)
        (TraceStableInfinityMap.comp ab (TraceStableInfinityMap.comp bc cd))
  | shiftCongr {source target : TraceStableInfinityObject}
      {left right : TraceStableInfinityMap source target} :
      TraceStableInfinityHomotopy left right →
        TraceStableInfinityHomotopy
          (TraceStableInfinityMap.shiftMap left)
          (TraceStableInfinityMap.shiftMap right)
  | shiftId (obj : TraceStableInfinityObject) :
      TraceStableInfinityHomotopy
        (TraceStableInfinityMap.shiftMap (TraceStableInfinityMap.id obj))
        (TraceStableInfinityMap.id (TraceStableInfinityObject.shift obj))
  | shiftComp {source middle target : TraceStableInfinityObject}
      (left : TraceStableInfinityMap source middle)
      (right : TraceStableInfinityMap middle target) :
      TraceStableInfinityHomotopy
        (TraceStableInfinityMap.shiftMap (TraceStableInfinityMap.comp left right))
        (TraceStableInfinityMap.comp
          (TraceStableInfinityMap.shiftMap left)
          (TraceStableInfinityMap.shiftMap right))
  | cofiberInCongr {source target : TraceStableInfinityObject}
      {left right : TraceStableInfinityMap source target} :
      TraceStableInfinityHomotopy left right →
        TraceStableInfinityHomotopy
          (TraceStableInfinityMap.cofiberIn left)
          (TraceStableInfinityMap.cofiberIn right)
  | cofiberOutCongr {source target : TraceStableInfinityObject}
      {left right : TraceStableInfinityMap source target} :
      TraceStableInfinityHomotopy left right →
        TraceStableInfinityHomotopy
          (TraceStableInfinityMap.cofiberOut left)
          (TraceStableInfinityMap.cofiberOut right)
  | fiberInCongr {source target : TraceStableInfinityObject}
      {left right : TraceStableInfinityMap source target} :
      TraceStableInfinityHomotopy left right →
        TraceStableInfinityHomotopy
          (TraceStableInfinityMap.fiberIn left)
          (TraceStableInfinityMap.fiberIn right)
  | fiberOutCongr {source target : TraceStableInfinityObject}
      {left right : TraceStableInfinityMap source target} :
      TraceStableInfinityHomotopy left right →
        TraceStableInfinityHomotopy
          (TraceStableInfinityMap.fiberOut left)
          (TraceStableInfinityMap.fiberOut right)
  | cofiberOut_comp_cofiberIn_zero {source target : TraceStableInfinityObject}
      (map : TraceStableInfinityMap source target) :
      TraceStableInfinityHomotopy
        (TraceStableInfinityMap.comp
          (TraceStableInfinityMap.cofiberIn map)
          (TraceStableInfinityMap.cofiberOut map))
        (TraceStableInfinityMap.zeroMap target (TraceStableInfinityObject.shift source))
  | weakInverseLeft {source target : AdmNormObj}
      (map : AdmNormHom source target)
      (weakEquiv : AdmNormWeakEquivalence map) :
      TraceStableInfinityHomotopy
        (TraceStableInfinityMap.comp
          (TraceStableInfinityMap.ofAdmNorm map)
          (TraceStableInfinityMap.invertWeakEquivalence map weakEquiv))
        (TraceStableInfinityMap.id (TraceStableInfinityObject.ofRecord source))
  | weakInverseRight {source target : AdmNormObj}
      (map : AdmNormHom source target)
      (weakEquiv : AdmNormWeakEquivalence map) :
      TraceStableInfinityHomotopy
        (TraceStableInfinityMap.comp
          (TraceStableInfinityMap.invertWeakEquivalence map weakEquiv)
          (TraceStableInfinityMap.ofAdmNorm map))
        (TraceStableInfinityMap.id (TraceStableInfinityObject.ofRecord target))

structure TraceCofiberSequence where
  source : TraceStableInfinityObject
  target : TraceStableInfinityObject
  map : TraceStableInfinityMap source target
  cofiberObject : TraceStableInfinityObject
  cofiberIn : TraceStableInfinityMap target cofiberObject
  cofiberOut : TraceStableInfinityMap cofiberObject (TraceStableInfinityObject.shift source)

namespace TraceCofiberSequence

def ofMap {source target : TraceStableInfinityObject}
    (map : TraceStableInfinityMap source target) : TraceCofiberSequence where
  source := source
  target := target
  map := map
  cofiberObject := TraceStableInfinityObject.cofiber source target
  cofiberIn := TraceStableInfinityMap.cofiberIn map
  cofiberOut := TraceStableInfinityMap.cofiberOut map

end TraceCofiberSequence

abbrev TraceNormalizationStableInfinityObject : Type 1 :=
  TraceStableInfinityObject

abbrev TraceNormalizationStableInfinityHom
    (source target : TraceNormalizationStableInfinityObject) : Type 1 :=
  TraceStableInfinityMap source target

abbrev TraceNormalizationStableInfinityHomotopy
    {source target : TraceNormalizationStableInfinityObject}
    (left right : TraceNormalizationStableInfinityHom source target) : Type 1 :=
  TraceStableInfinityHomotopy left right

def traceNormalizationStableInfinityId
    (obj : TraceNormalizationStableInfinityObject) :
    TraceNormalizationStableInfinityHom obj obj :=
  TraceStableInfinityMap.id obj

def traceNormalizationStableInfinityComp
    {source middle target : TraceNormalizationStableInfinityObject}
    (left : TraceNormalizationStableInfinityHom source middle)
    (right : TraceNormalizationStableInfinityHom middle target) :
    TraceNormalizationStableInfinityHom source target :=
  TraceStableInfinityMap.comp left right

def traceNormalizationStableInfinityShift
    (obj : TraceNormalizationStableInfinityObject) :
    TraceNormalizationStableInfinityObject :=
  TraceStableInfinityObject.shift obj

def traceNormalizationStableInfinityCofiber
    {source target : TraceNormalizationStableInfinityObject}
    (_map : TraceNormalizationStableInfinityHom source target) :
    TraceNormalizationStableInfinityObject :=
  TraceStableInfinityObject.cofiber source target

inductive TraceNormalizationStableInfinityWeakEquivalence :
    {source target : TraceNormalizationStableInfinityObject} →
      TraceNormalizationStableInfinityHom source target → Type 1 where
  | id (obj : TraceNormalizationStableInfinityObject) :
      TraceNormalizationStableInfinityWeakEquivalence
        (TraceStableInfinityMap.id obj)
  | ofAdmNorm {source target : AdmNormObj}
      (map : AdmNormHom source target) :
      AdmNormWeakEquivalence map →
        TraceNormalizationStableInfinityWeakEquivalence
          (TraceStableInfinityMap.ofAdmNorm map)
  | inverse {source target : AdmNormObj}
      (map : AdmNormHom source target)
      (weakEquiv : AdmNormWeakEquivalence map) :
      TraceNormalizationStableInfinityWeakEquivalence
        (TraceStableInfinityMap.invertWeakEquivalence map weakEquiv)
  | comp {source middle target : TraceNormalizationStableInfinityObject}
      {left : TraceNormalizationStableInfinityHom source middle}
      {right : TraceNormalizationStableInfinityHom middle target} :
      TraceNormalizationStableInfinityWeakEquivalence left →
      TraceNormalizationStableInfinityWeakEquivalence right →
        TraceNormalizationStableInfinityWeakEquivalence
          (TraceStableInfinityMap.comp left right)
  | homotopyClosed {source target : TraceNormalizationStableInfinityObject}
      {left right : TraceNormalizationStableInfinityHom source target} :
      TraceNormalizationStableInfinityWeakEquivalence left →
      TraceNormalizationStableInfinityHomotopy left right →
        TraceNormalizationStableInfinityWeakEquivalence right

inductive GroundedTraceStableInfinityHomotopy :
    {source target : TraceStableInfinityObject} →
      TraceStableInfinityMap source target →
      TraceStableInfinityMap source target → Type 1 where
  | ofAdmNorm {source target : AdmNormObj}
      {left right : AdmNormHom source target} :
      {homotopy : AdmNormHomotopy left right} →
      GroundedAdmNormHomotopy homotopy →
        GroundedTraceStableInfinityHomotopy
          (TraceStableInfinityMap.ofAdmNorm left)
          (TraceStableInfinityMap.ofAdmNorm right)
  | refl {source target : TraceStableInfinityObject}
      (map : TraceStableInfinityMap source target) :
      GroundedTraceStableInfinityHomotopy map map
  | symm {source target : TraceStableInfinityObject}
      {left right : TraceStableInfinityMap source target} :
      GroundedTraceStableInfinityHomotopy left right →
        GroundedTraceStableInfinityHomotopy right left
  | trans {source target : TraceStableInfinityObject}
      {first middle last : TraceStableInfinityMap source target} :
      GroundedTraceStableInfinityHomotopy first middle →
      GroundedTraceStableInfinityHomotopy middle last →
        GroundedTraceStableInfinityHomotopy first last
  | compCongr {source middle target : TraceStableInfinityObject}
      {left₁ left₂ : TraceStableInfinityMap source middle}
      {right₁ right₂ : TraceStableInfinityMap middle target} :
      GroundedTraceStableInfinityHomotopy left₁ left₂ →
      GroundedTraceStableInfinityHomotopy right₁ right₂ →
        GroundedTraceStableInfinityHomotopy
          (TraceStableInfinityMap.comp left₁ right₁)
          (TraceStableInfinityMap.comp left₂ right₂)
  | idLeft {source target : TraceStableInfinityObject}
      (map : TraceStableInfinityMap source target) :
      GroundedTraceStableInfinityHomotopy
        (TraceStableInfinityMap.comp (TraceStableInfinityMap.id source) map)
        map
  | idRight {source target : TraceStableInfinityObject}
      (map : TraceStableInfinityMap source target) :
      GroundedTraceStableInfinityHomotopy
        (TraceStableInfinityMap.comp map (TraceStableInfinityMap.id target))
        map
  | assoc {a b c d : TraceStableInfinityObject}
      (ab : TraceStableInfinityMap a b)
      (bc : TraceStableInfinityMap b c)
      (cd : TraceStableInfinityMap c d) :
      GroundedTraceStableInfinityHomotopy
        (TraceStableInfinityMap.comp (TraceStableInfinityMap.comp ab bc) cd)
        (TraceStableInfinityMap.comp ab (TraceStableInfinityMap.comp bc cd))
  | shiftCongr {source target : TraceStableInfinityObject}
      {left right : TraceStableInfinityMap source target} :
      GroundedTraceStableInfinityHomotopy left right →
        GroundedTraceStableInfinityHomotopy
          (TraceStableInfinityMap.shiftMap left)
          (TraceStableInfinityMap.shiftMap right)
  | shiftId (obj : TraceStableInfinityObject) :
      GroundedTraceStableInfinityHomotopy
        (TraceStableInfinityMap.shiftMap (TraceStableInfinityMap.id obj))
        (TraceStableInfinityMap.id (TraceStableInfinityObject.shift obj))
  | shiftComp {source middle target : TraceStableInfinityObject}
      (left : TraceStableInfinityMap source middle)
      (right : TraceStableInfinityMap middle target) :
      GroundedTraceStableInfinityHomotopy
        (TraceStableInfinityMap.shiftMap (TraceStableInfinityMap.comp left right))
        (TraceStableInfinityMap.comp
          (TraceStableInfinityMap.shiftMap left)
          (TraceStableInfinityMap.shiftMap right))
  | cofiberInCongr {source target : TraceStableInfinityObject}
      {left right : TraceStableInfinityMap source target} :
      GroundedTraceStableInfinityHomotopy left right →
        GroundedTraceStableInfinityHomotopy
          (TraceStableInfinityMap.cofiberIn left)
          (TraceStableInfinityMap.cofiberIn right)
  | cofiberOutCongr {source target : TraceStableInfinityObject}
      {left right : TraceStableInfinityMap source target} :
      GroundedTraceStableInfinityHomotopy left right →
        GroundedTraceStableInfinityHomotopy
          (TraceStableInfinityMap.cofiberOut left)
          (TraceStableInfinityMap.cofiberOut right)
  | fiberInCongr {source target : TraceStableInfinityObject}
      {left right : TraceStableInfinityMap source target} :
      GroundedTraceStableInfinityHomotopy left right →
        GroundedTraceStableInfinityHomotopy
          (TraceStableInfinityMap.fiberIn left)
          (TraceStableInfinityMap.fiberIn right)
  | fiberOutCongr {source target : TraceStableInfinityObject}
      {left right : TraceStableInfinityMap source target} :
      GroundedTraceStableInfinityHomotopy left right →
        GroundedTraceStableInfinityHomotopy
          (TraceStableInfinityMap.fiberOut left)
          (TraceStableInfinityMap.fiberOut right)
  | weakInverseLeft {source target : AdmNormObj}
      (map : AdmNormHom source target)
      {weakEquiv : AdmNormWeakEquivalence map} :
      GroundedAdmNormWeakEquivalence weakEquiv →
        GroundedTraceStableInfinityHomotopy
          (TraceStableInfinityMap.comp
            (TraceStableInfinityMap.ofAdmNorm map)
            (TraceStableInfinityMap.invertWeakEquivalence map weakEquiv))
          (TraceStableInfinityMap.id (TraceStableInfinityObject.ofRecord source))
  | weakInverseRight {source target : AdmNormObj}
      (map : AdmNormHom source target)
      {weakEquiv : AdmNormWeakEquivalence map} :
      GroundedAdmNormWeakEquivalence weakEquiv →
        GroundedTraceStableInfinityHomotopy
          (TraceStableInfinityMap.comp
            (TraceStableInfinityMap.invertWeakEquivalence map weakEquiv)
            (TraceStableInfinityMap.ofAdmNorm map))
          (TraceStableInfinityMap.id (TraceStableInfinityObject.ofRecord target))

inductive GroundedTraceNormalizationStableInfinityWeakEquivalence :
    {source target : TraceNormalizationStableInfinityObject} →
      TraceNormalizationStableInfinityHom source target → Type 1 where
  | id (obj : TraceNormalizationStableInfinityObject) :
      GroundedTraceNormalizationStableInfinityWeakEquivalence
        (TraceStableInfinityMap.id obj)
  | ofReplayAdmNorm {source target : AdmNormObj}
      (map : AdmNormHom source target)
      (weakEquiv : AdmNormWeakEquivalence map) :
      ReplayGroundedAdmNormWeakEquivalence weakEquiv →
        GroundedTraceNormalizationStableInfinityWeakEquivalence
          (TraceStableInfinityMap.ofAdmNorm map)
  | ofAdminAdmNorm {source target : AdmNormObj}
      (map : AdmNormHom source target)
      (weakEquiv : AdmNormWeakEquivalence map) :
      AdminGroundedAdmNormWeakEquivalence weakEquiv →
        GroundedTraceNormalizationStableInfinityWeakEquivalence
          (TraceStableInfinityMap.ofAdmNorm map)
  | inverseReplay {source target : AdmNormObj}
      (map : AdmNormHom source target)
      (weakEquiv : AdmNormWeakEquivalence map) :
      ReplayGroundedAdmNormWeakEquivalence weakEquiv →
        GroundedTraceNormalizationStableInfinityWeakEquivalence
          (TraceStableInfinityMap.invertWeakEquivalence map weakEquiv)
  | inverseAdmin {source target : AdmNormObj}
      (map : AdmNormHom source target)
      (weakEquiv : AdmNormWeakEquivalence map) :
      AdminGroundedAdmNormWeakEquivalence weakEquiv →
        GroundedTraceNormalizationStableInfinityWeakEquivalence
          (TraceStableInfinityMap.invertWeakEquivalence map weakEquiv)
  | shift {source target : TraceNormalizationStableInfinityObject}
      {map : TraceNormalizationStableInfinityHom source target} :
      GroundedTraceNormalizationStableInfinityWeakEquivalence map →
        GroundedTraceNormalizationStableInfinityWeakEquivalence
          (TraceStableInfinityMap.shiftMap map)
  | comp {source middle target : TraceNormalizationStableInfinityObject}
      {left : TraceNormalizationStableInfinityHom source middle}
      {right : TraceNormalizationStableInfinityHom middle target} :
      GroundedTraceNormalizationStableInfinityWeakEquivalence left →
      GroundedTraceNormalizationStableInfinityWeakEquivalence right →
        GroundedTraceNormalizationStableInfinityWeakEquivalence
          (TraceStableInfinityMap.comp left right)
  | homotopyClosed {source target : TraceNormalizationStableInfinityObject}
      {left right : TraceNormalizationStableInfinityHom source target} :
      GroundedTraceNormalizationStableInfinityWeakEquivalence left →
      GroundedTraceStableInfinityHomotopy left right →
        GroundedTraceNormalizationStableInfinityWeakEquivalence right

def traceNormalizationStableInfinityWeakEquivalenceClass
    {source target : TraceNormalizationStableInfinityObject}
    {map : TraceNormalizationStableInfinityHom source target}
    (weakEquiv : TraceNormalizationStableInfinityWeakEquivalence map) :
    Phase211GroundingClass := by
  cases weakEquiv with
  | id _ => exact .formalClosure
  | ofAdmNorm _ _ => exact .ungrounded
  | inverse _ _ => exact .formalClosure
  | comp _ _ => exact .formalClosure
  | homotopyClosed _ _ => exact .formalClosure

def groundedTraceNormalizationStableInfinityWeakEquivalenceClass
    {source target : TraceNormalizationStableInfinityObject}
    {map : TraceNormalizationStableInfinityHom source target}
    (weakEquiv : GroundedTraceNormalizationStableInfinityWeakEquivalence map) :
    Phase211GroundingClass := by
  cases weakEquiv with
  | id _ => exact .formalClosure
  | ofReplayAdmNorm _ _ _ => exact .replayGrounded
  | ofAdminAdmNorm _ _ _ => exact .adminGrounded
  | inverseReplay _ _ _ => exact .replayGrounded
  | inverseAdmin _ _ _ => exact .adminGrounded
  | shift _ => exact .formalClosure
  | comp _ _ => exact .formalClosure
  | homotopyClosed _ _ => exact .formalClosure

def groundedTraceStableInfinityHomotopy_to_generated
    {source target : TraceStableInfinityObject}
    {left right : TraceStableInfinityMap source target} :
  GroundedTraceStableInfinityHomotopy left right →
    TraceStableInfinityHomotopy left right
  | .ofAdmNorm (.replay (homotopy := homotopy) _) =>
    TraceStableInfinityHomotopy.ofAdmNorm homotopy
  | .ofAdmNorm (.admin (homotopy := homotopy) _) =>
    TraceStableInfinityHomotopy.ofAdmNorm homotopy
  | .refl map => TraceStableInfinityHomotopy.refl map
  | .symm grounded =>
    TraceStableInfinityHomotopy.symm (groundedTraceStableInfinityHomotopy_to_generated grounded)
  | .trans leftGrounded rightGrounded =>
    TraceStableInfinityHomotopy.trans
    (groundedTraceStableInfinityHomotopy_to_generated leftGrounded)
    (groundedTraceStableInfinityHomotopy_to_generated rightGrounded)
  | .compCongr leftGrounded rightGrounded =>
    TraceStableInfinityHomotopy.compCongr
    (groundedTraceStableInfinityHomotopy_to_generated leftGrounded)
    (groundedTraceStableInfinityHomotopy_to_generated rightGrounded)
  | .idLeft map => TraceStableInfinityHomotopy.idLeft map
  | .idRight map => TraceStableInfinityHomotopy.idRight map
  | .assoc ab bc cd => TraceStableInfinityHomotopy.assoc ab bc cd
  | .shiftCongr grounded =>
    TraceStableInfinityHomotopy.shiftCongr
    (groundedTraceStableInfinityHomotopy_to_generated grounded)
  | .shiftId obj =>
      TraceStableInfinityHomotopy.shiftId obj
  | .shiftComp left right =>
      TraceStableInfinityHomotopy.shiftComp left right
  | .cofiberInCongr grounded =>
    TraceStableInfinityHomotopy.cofiberInCongr
    (groundedTraceStableInfinityHomotopy_to_generated grounded)
  | .cofiberOutCongr grounded =>
    TraceStableInfinityHomotopy.cofiberOutCongr
    (groundedTraceStableInfinityHomotopy_to_generated grounded)
  | .fiberInCongr grounded =>
    TraceStableInfinityHomotopy.fiberInCongr
    (groundedTraceStableInfinityHomotopy_to_generated grounded)
  | .fiberOutCongr grounded =>
    TraceStableInfinityHomotopy.fiberOutCongr
    (groundedTraceStableInfinityHomotopy_to_generated grounded)
  | .weakInverseLeft map (.replay (weakEquiv := weakEquiv) _) =>
    TraceStableInfinityHomotopy.weakInverseLeft map weakEquiv
  | .weakInverseLeft map (.admin (weakEquiv := weakEquiv) _) =>
    TraceStableInfinityHomotopy.weakInverseLeft map weakEquiv
  | .weakInverseRight map (.replay (weakEquiv := weakEquiv) _) =>
    TraceStableInfinityHomotopy.weakInverseRight map weakEquiv
  | .weakInverseRight map (.admin (weakEquiv := weakEquiv) _) =>
    TraceStableInfinityHomotopy.weakInverseRight map weakEquiv

def traceNormalizationStableInfinityInverseOfAdmNormWeakEquivalence
    {source target : AdmNormObj}
    (map : AdmNormHom source target)
    (weakEquiv : AdmNormWeakEquivalence map) :
    TraceNormalizationStableInfinityHom
      (TraceStableInfinityObject.ofRecord target)
      (TraceStableInfinityObject.ofRecord source) :=
  TraceStableInfinityMap.invertWeakEquivalence map weakEquiv

def traceNormalizationStableInfinityObjectOfAdmNorm (obj : AdmNormObj) :
    TraceNormalizationStableInfinityObject :=
  TraceStableInfinityObject.ofRecord obj

def traceNormalizationStableInfinityMapOfAdmNorm {source target : AdmNormObj}
    (map : AdmNormHom source target) :
    TraceNormalizationStableInfinityHom
      (traceNormalizationStableInfinityObjectOfAdmNorm source)
      (traceNormalizationStableInfinityObjectOfAdmNorm target) :=
  TraceStableInfinityMap.ofAdmNorm map

def traceNormalizationStableInfinity_id_left
    {source target : TraceNormalizationStableInfinityObject}
    (map : TraceNormalizationStableInfinityHom source target) :
    TraceNormalizationStableInfinityHomotopy
      (traceNormalizationStableInfinityComp (traceNormalizationStableInfinityId source) map)
      map :=
  TraceStableInfinityHomotopy.idLeft map

def traceNormalizationStableInfinity_id_right
    {source target : TraceNormalizationStableInfinityObject}
    (map : TraceNormalizationStableInfinityHom source target) :
    TraceNormalizationStableInfinityHomotopy
      (traceNormalizationStableInfinityComp map (traceNormalizationStableInfinityId target))
      map :=
  TraceStableInfinityHomotopy.idRight map

def traceNormalizationStableInfinity_assoc
    {a b c d : TraceNormalizationStableInfinityObject}
    (ab : TraceNormalizationStableInfinityHom a b)
    (bc : TraceNormalizationStableInfinityHom b c)
    (cd : TraceNormalizationStableInfinityHom c d) :
    TraceNormalizationStableInfinityHomotopy
      (traceNormalizationStableInfinityComp (traceNormalizationStableInfinityComp ab bc) cd)
      (traceNormalizationStableInfinityComp ab (traceNormalizationStableInfinityComp bc cd)) :=
  TraceStableInfinityHomotopy.assoc ab bc cd

namespace TraceStableInfinityHomotopy

def setoid (source target : TraceStableInfinityObject) :
    Setoid (TraceStableInfinityMap source target) where
  r left right := Nonempty (TraceStableInfinityHomotopy left right)
  iseqv := {
    refl := by
      intro map
      exact ⟨TraceStableInfinityHomotopy.refl map⟩
    symm := by
      intro left right h
      rcases h with ⟨h⟩
      exact ⟨TraceStableInfinityHomotopy.symm h⟩
    trans := by
      intro first middle last hFirst hSecond
      rcases hFirst with ⟨hFirst⟩
      rcases hSecond with ⟨hSecond⟩
      exact ⟨TraceStableInfinityHomotopy.trans hFirst hSecond⟩ }

end TraceStableInfinityHomotopy

abbrev TraceStableHomotopyCategory : Type 1 :=
  TraceStableInfinityObject

namespace TraceStableHomotopyCategory

abbrev Hom (source target : TraceStableHomotopyCategory) : Type 1 :=
  Quotient (TraceStableInfinityHomotopy.setoid source target)

def mkHom {source target : TraceStableHomotopyCategory}
    (map : TraceStableInfinityMap source target) : Hom source target :=
  Quotient.mk _ map

instance : CategoryTheory.Category TraceStableHomotopyCategory where
  Hom := Hom
  id obj := mkHom (TraceStableInfinityMap.id obj)
  comp left right := by
    refine Quotient.liftOn left
      (fun leftMap =>
        Quotient.liftOn right
          (fun rightMap => mkHom (TraceStableInfinityMap.comp leftMap rightMap))
          (by
            intro right₁ right₂ hRight
            rcases hRight with ⟨hRight⟩
            exact Quotient.sound ⟨TraceStableInfinityHomotopy.compCongr
              (left₁ := leftMap) (left₂ := leftMap) (right₁ := right₁) (right₂ := right₂)
              (TraceStableInfinityHomotopy.refl leftMap) hRight⟩)) ?_
    intro left₁ left₂ hLeft
    refine Quotient.inductionOn right ?_
    intro rightMap
    rcases hLeft with ⟨hLeft⟩
    exact Quotient.sound ⟨TraceStableInfinityHomotopy.compCongr
      (left₁ := left₁) (left₂ := left₂) (right₁ := rightMap) (right₂ := rightMap)
      hLeft (TraceStableInfinityHomotopy.refl rightMap)⟩
  id_comp := by
    intro source target map
    refine Quotient.inductionOn map ?_
    intro representative
    exact Quotient.sound ⟨TraceStableInfinityHomotopy.idLeft representative⟩
  comp_id := by
    intro source target map
    refine Quotient.inductionOn map ?_
    intro representative
    exact Quotient.sound ⟨TraceStableInfinityHomotopy.idRight representative⟩
  assoc := by
    intro a b c d ab bc cd
    refine Quotient.inductionOn ab ?_
    intro abRep
    refine Quotient.inductionOn bc ?_
    intro bcRep
    refine Quotient.inductionOn cd ?_
    intro cdRep
    exact Quotient.sound ⟨TraceStableInfinityHomotopy.assoc abRep bcRep cdRep⟩

def ofAdmNormHom {source target : AdmNormObj}
    (map : AdmNormHom source target) :
    Hom (TraceStableInfinityObject.ofRecord source)
      (TraceStableInfinityObject.ofRecord target) :=
  mkHom (TraceStableInfinityMap.ofAdmNorm map)

def zeroObj : TraceStableHomotopyCategory :=
  TraceStableInfinityObject.zero

def toZero (obj : TraceStableHomotopyCategory) : Hom obj zeroObj :=
  mkHom TraceStableInfinityMap.toZero

def fromZero (obj : TraceStableHomotopyCategory) : Hom zeroObj obj :=
  mkHom TraceStableInfinityMap.fromZero

def zeroHom (source target : TraceStableHomotopyCategory) : Hom source target :=
  mkHom (TraceStableInfinityMap.zeroMap source target)

def shiftObj (obj : TraceStableHomotopyCategory) : TraceStableHomotopyCategory :=
  TraceStableInfinityObject.shift obj

def shiftHom {source target : TraceStableHomotopyCategory}
  (map : Hom source target) : Hom (shiftObj source) (shiftObj target) := by
  refine Quotient.liftOn map
    (fun representative => mkHom (TraceStableInfinityMap.shiftMap representative)) ?_
  intro left right h
  rcases h with ⟨h⟩
  exact Quotient.sound ⟨TraceStableInfinityHomotopy.shiftCongr h⟩

theorem shiftHom_id
    (obj : TraceStableHomotopyCategory) :
    let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
    shiftHom (𝟙 obj) = 𝟙 (shiftObj obj) := by
  let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
  exact Quotient.sound ⟨TraceStableInfinityHomotopy.shiftId obj⟩

def cofiberObj {source target : TraceStableHomotopyCategory}
    (_map : Hom source target) : TraceStableHomotopyCategory :=
  TraceStableInfinityObject.cofiber source target

def cofiberIn {source target : TraceStableHomotopyCategory}
    (map : Hom source target) : Hom target (cofiberObj map) := by
  refine Quotient.liftOn map
    (fun representative => mkHom (TraceStableInfinityMap.cofiberIn representative)) ?_
  intro left right h
  rcases h with ⟨h⟩
  exact Quotient.sound ⟨TraceStableInfinityHomotopy.cofiberInCongr h⟩

def cofiberOut {source target : TraceStableHomotopyCategory}
  (map : Hom source target) : Hom (cofiberObj map) (shiftObj source) := by
  refine Quotient.liftOn map
    (fun representative => mkHom (TraceStableInfinityMap.cofiberOut representative)) ?_
  intro left right h
  rcases h with ⟨h⟩
  exact Quotient.sound ⟨TraceStableInfinityHomotopy.cofiberOutCongr h⟩

theorem cofiber_in_comp_out_zero {source target : TraceStableHomotopyCategory}
  (map : TraceStableHomotopyCategory.Hom source target) :
  @CategoryStruct.comp TraceStableHomotopyCategory inferInstance target (cofiberObj map)
    (shiftObj source) (cofiberIn map) (cofiberOut map) = zeroHom target (shiftObj source) := by
  let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
  refine Quotient.inductionOn map ?_
  intro representative
  exact Quotient.sound ⟨TraceStableInfinityHomotopy.cofiberOut_comp_cofiberIn_zero representative⟩

def fiberObj {source target : TraceStableHomotopyCategory}
    (_map : Hom source target) : TraceStableHomotopyCategory :=
  TraceStableInfinityObject.fiber source target

def fiberIn {source target : TraceStableHomotopyCategory}
    (map : Hom source target) : Hom (fiberObj map) source := by
  refine Quotient.liftOn map
    (fun representative => mkHom (TraceStableInfinityMap.fiberIn representative)) ?_
  intro left right h
  rcases h with ⟨h⟩
  exact Quotient.sound ⟨TraceStableInfinityHomotopy.fiberInCongr h⟩

def fiberOut {source target : TraceStableHomotopyCategory}
  (map : Hom source target) : Hom (shiftObj (fiberObj map)) target := by
  refine Quotient.liftOn map
    (fun representative => mkHom (TraceStableInfinityMap.fiberOut representative)) ?_
  intro left right h
  rcases h with ⟨h⟩
  exact Quotient.sound ⟨TraceStableInfinityHomotopy.fiberOutCongr h⟩

def IsWeakEquivalence {source target : TraceStableHomotopyCategory}
  (map : Hom source target) : Prop := by
  refine Quotient.liftOn map
    (fun representative => Nonempty (TraceNormalizationStableInfinityWeakEquivalence representative)) ?_
  intro left right h
  rcases h with ⟨h⟩
  apply propext
  constructor
  · intro hWeak
    rcases hWeak with ⟨hWeak⟩
    exact ⟨TraceNormalizationStableInfinityWeakEquivalence.homotopyClosed hWeak h⟩
  · intro hWeak
    rcases hWeak with ⟨hWeak⟩
    exact ⟨TraceNormalizationStableInfinityWeakEquivalence.homotopyClosed hWeak
      (TraceStableInfinityHomotopy.symm h)⟩

theorem mkHom_isWeakEquivalence {source target : TraceStableHomotopyCategory}
    (map : TraceStableInfinityMap source target)
    (hWeak : Nonempty (TraceNormalizationStableInfinityWeakEquivalence map)) :
    IsWeakEquivalence (mkHom map) :=
  hWeak

structure CofiberSequence where
  source : TraceStableHomotopyCategory
  target : TraceStableHomotopyCategory
  map : Hom source target
  cofiberObject : TraceStableHomotopyCategory
  cofiberInMap : Hom target cofiberObject
  cofiberOutMap : Hom cofiberObject (shiftObj source)

def CofiberSequence.ofMap {source target : TraceStableHomotopyCategory}
    (map : Hom source target) : CofiberSequence where
  source := source
  target := target
  map := map
  cofiberObject := cofiberObj map
  cofiberInMap := cofiberIn map
  cofiberOutMap := cofiberOut map

end TraceStableHomotopyCategory

def HasGroundedTraceNormalizationStableInfinityWeakEquivalence
    {source target : TraceNormalizationStableInfinityObject}
    (map : TraceNormalizationStableInfinityHom source target) : Prop :=
  ∃ _ : GroundedTraceNormalizationStableInfinityWeakEquivalence map, True

abbrev TraceStableWeakEquivOnHomotopyCategory
    {source target : TraceStableHomotopyCategory}
    (map : TraceStableHomotopyCategory.Hom source target) : Prop :=
  TraceStableHomotopyCategory.IsWeakEquivalence map

theorem traceStableWeakEquiv_closed_under_homotopy
    {source target : TraceStableHomotopyCategory}
    {left right : TraceStableInfinityMap source target}
    (h : Nonempty (TraceStableInfinityHomotopy left right)) :
    TraceStableWeakEquivOnHomotopyCategory (TraceStableHomotopyCategory.mkHom left) ↔
      TraceStableWeakEquivOnHomotopyCategory (TraceStableHomotopyCategory.mkHom right) := by
  have hEq : TraceStableHomotopyCategory.mkHom left = TraceStableHomotopyCategory.mkHom right :=
    Quotient.sound h
  constructor
  · intro hWeak
    simpa [hEq] using hWeak
  · intro hWeak
    simpa [hEq] using hWeak

theorem traceStableWeakEquiv_id
    (obj : TraceStableHomotopyCategory) :
    TraceStableWeakEquivOnHomotopyCategory (𝟙 obj) := by
  change Nonempty (TraceNormalizationStableInfinityWeakEquivalence
    (TraceStableInfinityMap.id obj))
  exact ⟨TraceNormalizationStableInfinityWeakEquivalence.id obj⟩

theorem traceStableWeakEquiv_comp
    {source middle target : TraceStableHomotopyCategory}
    (left : source ⟶ middle)
    (right : middle ⟶ target) :
    TraceStableWeakEquivOnHomotopyCategory left →
      TraceStableWeakEquivOnHomotopyCategory right →
        TraceStableWeakEquivOnHomotopyCategory (left ≫ right) := by
  refine Quotient.inductionOn₂ left right ?_
  intro leftRep rightRep hLeft hRight
  rcases hLeft with ⟨hLeft⟩
  rcases hRight with ⟨hRight⟩
  exact ⟨TraceNormalizationStableInfinityWeakEquivalence.comp hLeft hRight⟩

structure TraceStableRelativeCategory where
  Obj : Type u
  category : CategoryTheory.Category Obj
  weakEquiv : let _inst : CategoryTheory.Category Obj := category
    ∀ {X Y : Obj}, (X ⟶ Y) → Prop
  weakEquiv_id : let _inst : CategoryTheory.Category Obj := category
    ∀ X, weakEquiv (𝟙 X)
  weakEquiv_comp : let _inst : CategoryTheory.Category Obj := category
    ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z),
      weakEquiv f → weakEquiv g → weakEquiv (f ≫ g)

def traceStableRelativeCategory : TraceStableRelativeCategory where
  Obj := TraceStableHomotopyCategory
  category := inferInstance
  weakEquiv := by
    let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
    exact fun {X Y} f => TraceStableWeakEquivOnHomotopyCategory f
  weakEquiv_id := by
    let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
    exact fun X => traceStableWeakEquiv_id X
  weakEquiv_comp := by
    let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
    exact fun {X Y Z} f g hf hg => traceStableWeakEquiv_comp f g hf hg

def TraceStableGroundedWeakEquivOnHomotopyCategory
    {source target : TraceStableHomotopyCategory}
    (map : TraceStableHomotopyCategory.Hom source target) : Prop :=
  ∃ representative : TraceStableInfinityMap source target,
    map = TraceStableHomotopyCategory.mkHom representative ∧
      HasGroundedTraceNormalizationStableInfinityWeakEquivalence representative

theorem traceStableGroundedWeakEquiv_id
    (obj : TraceStableHomotopyCategory) :
    TraceStableGroundedWeakEquivOnHomotopyCategory (𝟙 obj) := by
  refine ⟨TraceStableInfinityMap.id obj, rfl, ?_⟩
  exact ⟨GroundedTraceNormalizationStableInfinityWeakEquivalence.id obj, True.intro⟩

theorem traceStableGroundedWeakEquiv_comp
    {source middle target : TraceStableHomotopyCategory}
    (left : source ⟶ middle)
    (right : middle ⟶ target) :
    TraceStableGroundedWeakEquivOnHomotopyCategory left →
      TraceStableGroundedWeakEquivOnHomotopyCategory right →
        TraceStableGroundedWeakEquivOnHomotopyCategory (left ≫ right) := by
  intro hLeft hRight
  rcases hLeft with ⟨leftRep, rfl, hLeftRep⟩
  rcases hRight with ⟨rightRep, rfl, hRightRep⟩
  rcases hLeftRep with ⟨hLeftRep, _⟩
  rcases hRightRep with ⟨hRightRep, _⟩
  refine ⟨TraceStableInfinityMap.comp leftRep rightRep, rfl, ?_⟩
  exact ⟨GroundedTraceNormalizationStableInfinityWeakEquivalence.comp hLeftRep hRightRep,
    True.intro⟩

theorem traceStableGroundedWeakEquiv_shift
    {source target : TraceStableHomotopyCategory}
    (map : source ⟶ target) :
    TraceStableGroundedWeakEquivOnHomotopyCategory map →
      TraceStableGroundedWeakEquivOnHomotopyCategory
        (TraceStableHomotopyCategory.shiftHom map) := by
  intro hGrounded
  rcases hGrounded with ⟨representative, rfl, hWitness⟩
  rcases hWitness with ⟨hWitness, _⟩
  refine ⟨TraceStableInfinityMap.shiftMap representative, rfl, ?_⟩
  exact ⟨GroundedTraceNormalizationStableInfinityWeakEquivalence.shift hWitness,
    True.intro⟩

def traceStableGroundedRelativeCategory : TraceStableRelativeCategory where
  Obj := TraceStableHomotopyCategory
  category := inferInstance
  weakEquiv := by
    let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
    exact fun {X Y} f => TraceStableGroundedWeakEquivOnHomotopyCategory f
  weakEquiv_id := by
    let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
    exact fun X => traceStableGroundedWeakEquiv_id X
  weakEquiv_comp := by
    let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
    exact fun {X Y Z} f g hf hg => traceStableGroundedWeakEquiv_comp f g hf hg

structure TraceStableGeneratedWeakEquivData
    {source target : TraceStableHomotopyCategory}
    (map : TraceStableInfinityMap source target) where
  inv : target ⟶ source
  hom_inv_id : TraceStableHomotopyCategory.mkHom map ≫ inv = 𝟙 source
  inv_hom_id : inv ≫ TraceStableHomotopyCategory.mkHom map = 𝟙 target

def traceStableGeneratedWeakEquivData
    {source target : TraceStableHomotopyCategory}
    {map : TraceStableInfinityMap source target} :
    TraceNormalizationStableInfinityWeakEquivalence map → TraceStableGeneratedWeakEquivData map
  | .id obj =>
      { inv := TraceStableHomotopyCategory.mkHom (TraceStableInfinityMap.id obj)
        hom_inv_id := by
          exact Quotient.sound ⟨TraceStableInfinityHomotopy.idLeft (TraceStableInfinityMap.id obj)⟩
        inv_hom_id := by
          exact Quotient.sound ⟨TraceStableInfinityHomotopy.idRight (TraceStableInfinityMap.id obj)⟩ }
  | .ofAdmNorm admMap weakEquiv =>
      { inv := TraceStableHomotopyCategory.mkHom
          (TraceStableInfinityMap.invertWeakEquivalence admMap weakEquiv)
        hom_inv_id := by
          exact Quotient.sound ⟨TraceStableInfinityHomotopy.weakInverseLeft admMap weakEquiv⟩
        inv_hom_id := by
          exact Quotient.sound ⟨TraceStableInfinityHomotopy.weakInverseRight admMap weakEquiv⟩ }
  | .inverse admMap weakEquiv =>
      { inv := TraceStableHomotopyCategory.mkHom (TraceStableInfinityMap.ofAdmNorm admMap)
        hom_inv_id := by
          exact Quotient.sound ⟨TraceStableInfinityHomotopy.weakInverseRight admMap weakEquiv⟩
        inv_hom_id := by
          exact Quotient.sound ⟨TraceStableInfinityHomotopy.weakInverseLeft admMap weakEquiv⟩ }
  | @TraceNormalizationStableInfinityWeakEquivalence.comp _ _ _ left right hLeft hRight => by
      let leftData := traceStableGeneratedWeakEquivData hLeft
      let rightData := traceStableGeneratedWeakEquivData hRight
      exact {
        inv := rightData.inv ≫ leftData.inv
        hom_inv_id := by
          change (TraceStableHomotopyCategory.mkHom left ≫ TraceStableHomotopyCategory.mkHom right) ≫
              (rightData.inv ≫ leftData.inv) = 𝟙 _
          calc
            (TraceStableHomotopyCategory.mkHom left ≫ TraceStableHomotopyCategory.mkHom right) ≫
                (rightData.inv ≫ leftData.inv)
                = TraceStableHomotopyCategory.mkHom left ≫
                    (TraceStableHomotopyCategory.mkHom right ≫ rightData.inv) ≫ leftData.inv := by
                    simp [Category.assoc]
            _ = TraceStableHomotopyCategory.mkHom left ≫ 𝟙 _ ≫ leftData.inv := by
                  rw [rightData.hom_inv_id]
            _ = TraceStableHomotopyCategory.mkHom left ≫ leftData.inv := by simp
            _ = 𝟙 _ := leftData.hom_inv_id
        inv_hom_id := by
          change (rightData.inv ≫ leftData.inv) ≫
              (TraceStableHomotopyCategory.mkHom left ≫ TraceStableHomotopyCategory.mkHom right) = 𝟙 _
          calc
            (rightData.inv ≫ leftData.inv) ≫
                (TraceStableHomotopyCategory.mkHom left ≫ TraceStableHomotopyCategory.mkHom right)
                = rightData.inv ≫ (leftData.inv ≫ TraceStableHomotopyCategory.mkHom left) ≫
                    TraceStableHomotopyCategory.mkHom right := by
                    simp [Category.assoc]
            _ = rightData.inv ≫ 𝟙 _ ≫ TraceStableHomotopyCategory.mkHom right := by
                  rw [leftData.inv_hom_id]
            _ = rightData.inv ≫ TraceStableHomotopyCategory.mkHom right := by simp
            _ = 𝟙 _ := rightData.inv_hom_id }
  | @TraceNormalizationStableInfinityWeakEquivalence.homotopyClosed _ _ left map hWeak hHom => by
      let weakData := traceStableGeneratedWeakEquivData hWeak
      let leftHom := TraceStableHomotopyCategory.mkHom left
      let mapHom := TraceStableHomotopyCategory.mkHom map
      have hEq : leftHom = mapHom := Quotient.sound ⟨hHom⟩
      exact {
        inv := weakData.inv
        hom_inv_id := by
          calc
            mapHom ≫ weakData.inv = leftHom ≫ weakData.inv := by rw [← hEq]
            _ = 𝟙 _ := weakData.hom_inv_id
        inv_hom_id := by
          calc
            weakData.inv ≫ mapHom = weakData.inv ≫ leftHom := by rw [← hEq]
            _ = 𝟙 _ := weakData.inv_hom_id }

def traceStableGeneratedWeakEquivToIso
    {source target : TraceStableHomotopyCategory}
    {map : TraceStableInfinityMap source target} :
    TraceNormalizationStableInfinityWeakEquivalence map → Nonempty (source ≅ target) := by
  intro hWeak
  let data := traceStableGeneratedWeakEquivData hWeak
  exact ⟨{ hom := TraceStableHomotopyCategory.mkHom map
           inv := data.inv
           hom_inv_id := data.hom_inv_id
           inv_hom_id := data.inv_hom_id }⟩

namespace FormalPresentationOnly

/-!
This namespace contains the broad formal/generated localization used as a
presentation artifact only.

It is not a semantic localization input and must not be used by downstream
stable/t-structure/DMgm/MMQ work.

Dependency-safety status:
- downstream code must use the grounded semantic localization aliases defined
  below this namespace;
- any future use of this namespace must be explicit and qualified;
- no semantic comparison theorem is assumed here.
-/

theorem traceStableWeakEquivToIso
    {source target : TraceStableHomotopyCategory}
    (map : source ⟶ target) :
    TraceStableWeakEquivOnHomotopyCategory map → Nonempty (source ≅ target) := by
  refine Quotient.inductionOn map ?_
  intro representative hWeak
  rcases hWeak with ⟨hWeak⟩
  exact traceStableGeneratedWeakEquivToIso hWeak

structure TraceStableLocalizationEngine where
  source : TraceStableRelativeCategory
  Localized : Type u
  catLocalized : CategoryTheory.Category Localized
  localizeObj : source.Obj → Localized
  localizeMap : let _instSource : CategoryTheory.Category source.Obj := source.category
    let _instTarget : CategoryTheory.Category Localized := catLocalized
    ∀ {X Y : source.Obj}, (X ⟶ Y) → (localizeObj X ⟶ localizeObj Y)
  map_id : let _instSource : CategoryTheory.Category source.Obj := source.category
    let _instTarget : CategoryTheory.Category Localized := catLocalized
    ∀ X, localizeMap (𝟙 X) = 𝟙 (localizeObj X)
  map_comp : let _instSource : CategoryTheory.Category source.Obj := source.category
    let _instTarget : CategoryTheory.Category Localized := catLocalized
    ∀ {X Y Z : source.Obj} (f : X ⟶ Y) (g : Y ⟶ Z),
      localizeMap (f ≫ g) = localizeMap f ≫ localizeMap g
  sendsWeakEquivToIso : let _instSource : CategoryTheory.Category source.Obj := source.category
    let _instTarget : CategoryTheory.Category Localized := catLocalized
    ∀ {X Y : source.Obj} (f : X ⟶ Y), source.weakEquiv f → Nonempty (localizeObj X ≅ localizeObj Y)

attribute [instance] TraceStableLocalizationEngine.catLocalized

def traceStableLocalizationEngine : TraceStableLocalizationEngine where
  source := traceStableRelativeCategory
  Localized := TraceStableHomotopyCategory
  catLocalized := inferInstance
  localizeObj := id
  localizeMap := by
    let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
    exact fun {X Y} f => f
  map_id := by
    let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
    exact fun X => rfl
  map_comp := by
    let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
    exact fun {X Y Z} f g => rfl
  sendsWeakEquivToIso := by
    let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
    exact fun {X Y} f hWeak => traceStableWeakEquivToIso f hWeak

inductive TraceStableZigzagStep :
    TraceStableHomotopyCategory → TraceStableHomotopyCategory → Type 1 where
  | forward {X Y : TraceStableHomotopyCategory}
      (f : X ⟶ Y) : TraceStableZigzagStep X Y
  | backward {X Y : TraceStableHomotopyCategory}
      (w : Y ⟶ X)
      (hWeak : TraceStableWeakEquivOnHomotopyCategory w) :
      TraceStableZigzagStep X Y

inductive TraceStableZigzag :
    TraceStableHomotopyCategory → TraceStableHomotopyCategory → Type 1 where
  | nil (X : TraceStableHomotopyCategory) : TraceStableZigzag X X
  | cons {X Y Z : TraceStableHomotopyCategory}
      (step : TraceStableZigzagStep X Y)
      (tail : TraceStableZigzag Y Z) :
      TraceStableZigzag X Z

namespace TraceStableZigzag

def comp
    {X Y Z : TraceStableHomotopyCategory} :
    TraceStableZigzag X Y → TraceStableZigzag Y Z → TraceStableZigzag X Z
  | nil _, right => right
  | cons step tail, right => cons step (comp tail right)

def singleForward
    {X Y : TraceStableHomotopyCategory}
    (f : X ⟶ Y) : TraceStableZigzag X Y :=
  cons (TraceStableZigzagStep.forward f) (nil Y)

def singleBackward
    {X Y : TraceStableHomotopyCategory}
    (w : Y ⟶ X)
    (hWeak : TraceStableWeakEquivOnHomotopyCategory w) :
    TraceStableZigzag X Y :=
  cons (TraceStableZigzagStep.backward w hWeak) (nil Y)

@[simp] theorem nil_comp
    {X Y : TraceStableHomotopyCategory}
    (zigzag : TraceStableZigzag X Y) :
    comp (nil X) zigzag = zigzag :=
  rfl

@[simp] theorem comp_nil
    {X Y : TraceStableHomotopyCategory}
    (zigzag : TraceStableZigzag X Y) :
    comp zigzag (nil Y) = zigzag := by
  induction zigzag with
  | nil X => rfl
  | cons step tail ih => simp [comp, ih]

@[simp] theorem comp_assoc_eq
    {W X Y Z : TraceStableHomotopyCategory}
    (first : TraceStableZigzag W X)
    (second : TraceStableZigzag X Y)
    (third : TraceStableZigzag Y Z) :
    comp (comp first second) third = comp first (comp second third) := by
  induction first with
  | nil X => rfl
  | cons step tail ih => simp [comp, ih]

end TraceStableZigzag

inductive TraceStableZigzagRel :
    {X Y : TraceStableHomotopyCategory} →
      TraceStableZigzag X Y → TraceStableZigzag X Y → Prop where
  | refl {X Y : TraceStableHomotopyCategory}
      (zigzag : TraceStableZigzag X Y) :
      TraceStableZigzagRel zigzag zigzag
  | symm {X Y : TraceStableHomotopyCategory}
      {left right : TraceStableZigzag X Y} :
      TraceStableZigzagRel left right →
        TraceStableZigzagRel right left
  | trans {X Y : TraceStableHomotopyCategory}
      {first middle last : TraceStableZigzag X Y} :
      TraceStableZigzagRel first middle →
        TraceStableZigzagRel middle last →
          TraceStableZigzagRel first last
  | cons {X Y Z : TraceStableHomotopyCategory}
      (step : TraceStableZigzagStep X Y)
      {left right : TraceStableZigzag Y Z} :
      TraceStableZigzagRel left right →
        TraceStableZigzagRel
          (TraceStableZigzag.cons step left)
          (TraceStableZigzag.cons step right)
  | forwardEq {X Y Z : TraceStableHomotopyCategory}
      {left right : X ⟶ Y}
      (hEq : left = right)
      (tail : TraceStableZigzag Y Z) :
      TraceStableZigzagRel
        (TraceStableZigzag.cons (TraceStableZigzagStep.forward left) tail)
        (TraceStableZigzag.cons (TraceStableZigzagStep.forward right) tail)
  | backwardEq {X Y Z : TraceStableHomotopyCategory}
      {left right : Y ⟶ X}
      (hEq : left = right)
      (hLeft : TraceStableWeakEquivOnHomotopyCategory left)
      (hRight : TraceStableWeakEquivOnHomotopyCategory right)
      (tail : TraceStableZigzag Y Z) :
      TraceStableZigzagRel
        (TraceStableZigzag.cons (TraceStableZigzagStep.backward left hLeft) tail)
        (TraceStableZigzag.cons (TraceStableZigzagStep.backward right hRight) tail)
  | removeForwardId {X Y : TraceStableHomotopyCategory}
      (tail : TraceStableZigzag X Y) :
      TraceStableZigzagRel
        (TraceStableZigzag.cons (TraceStableZigzagStep.forward (𝟙 X)) tail)
        tail
  | composeForward {W X Y Z : TraceStableHomotopyCategory}
      (first : W ⟶ X)
      (second : X ⟶ Y)
      (tail : TraceStableZigzag Y Z) :
      TraceStableZigzagRel
        (TraceStableZigzag.cons (TraceStableZigzagStep.forward first)
          (TraceStableZigzag.cons (TraceStableZigzagStep.forward second) tail))
        (TraceStableZigzag.cons (TraceStableZigzagStep.forward (first ≫ second)) tail)
  | composeBackward {W X Y Z : TraceStableHomotopyCategory}
      (first : X ⟶ W)
      (hFirst : TraceStableWeakEquivOnHomotopyCategory first)
      (second : Y ⟶ X)
      (hSecond : TraceStableWeakEquivOnHomotopyCategory second)
      (tail : TraceStableZigzag Y Z) :
      TraceStableZigzagRel
        (TraceStableZigzag.cons (TraceStableZigzagStep.backward first hFirst)
          (TraceStableZigzag.cons (TraceStableZigzagStep.backward second hSecond) tail))
        (TraceStableZigzag.cons
          (TraceStableZigzagStep.backward (second ≫ first)
            (traceStableWeakEquiv_comp second first hSecond hFirst))
          tail)
  | cancelForwardBackward {X Y Z : TraceStableHomotopyCategory}
      (w : X ⟶ Y)
      (hWeak : TraceStableWeakEquivOnHomotopyCategory w)
      (tail : TraceStableZigzag X Z) :
      TraceStableZigzagRel
        (TraceStableZigzag.cons (TraceStableZigzagStep.forward w)
          (TraceStableZigzag.cons (TraceStableZigzagStep.backward w hWeak) tail))
        tail
  | cancelBackwardForward {X Y Z : TraceStableHomotopyCategory}
      (w : X ⟶ Y)
      (hWeak : TraceStableWeakEquivOnHomotopyCategory w)
      (tail : TraceStableZigzag Y Z) :
      TraceStableZigzagRel
        (TraceStableZigzag.cons (TraceStableZigzagStep.backward w hWeak)
          (TraceStableZigzag.cons (TraceStableZigzagStep.forward w) tail))
        tail
  | compNil {X Y : TraceStableHomotopyCategory}
      (zigzag : TraceStableZigzag X Y) :
      TraceStableZigzagRel
        (TraceStableZigzag.comp zigzag (TraceStableZigzag.nil Y))
        zigzag
  | nilComp {X Y : TraceStableHomotopyCategory}
      (zigzag : TraceStableZigzag X Y) :
      TraceStableZigzagRel
        (TraceStableZigzag.comp (TraceStableZigzag.nil X) zigzag)
        zigzag
  | compAssoc {V W X Y : TraceStableHomotopyCategory}
      (first : TraceStableZigzag V W)
      (second : TraceStableZigzag W X)
      (third : TraceStableZigzag X Y) :
      TraceStableZigzagRel
        (TraceStableZigzag.comp (TraceStableZigzag.comp first second) third)
        (TraceStableZigzag.comp first (TraceStableZigzag.comp second third))

def TraceStableZigzagSetoid
    (X Y : TraceStableHomotopyCategory) :
    Setoid (TraceStableZigzag X Y) where
  r := TraceStableZigzagRel
  iseqv := {
    refl := by
      intro zigzag
      exact TraceStableZigzagRel.refl zigzag
    symm := by
      intro left right hRel
      exact TraceStableZigzagRel.symm hRel
    trans := by
      intro first middle last hFirst hSecond
      exact TraceStableZigzagRel.trans hFirst hSecond }

abbrev TraceStableLocalizedHom
    (X Y : TraceStableHomotopyCategory) : Type 1 :=
  Quotient (TraceStableZigzagSetoid X Y)

namespace TraceStableZigzagRel

theorem comp_right_congr
    {X Y Z : TraceStableHomotopyCategory}
    (left : TraceStableZigzag X Y)
    {right₁ right₂ : TraceStableZigzag Y Z} :
    TraceStableZigzagRel right₁ right₂ →
      TraceStableZigzagRel
        (TraceStableZigzag.comp left right₁)
        (TraceStableZigzag.comp left right₂) := by
  intro hRel
  induction left with
  | nil X => simpa using hRel
  | cons step tail ih =>
      exact TraceStableZigzagRel.cons step (ih hRel)

theorem comp_left_congr
    {X Y Z : TraceStableHomotopyCategory}
    {left₁ left₂ : TraceStableZigzag X Y}
    (hRel : TraceStableZigzagRel left₁ left₂)
    (right : TraceStableZigzag Y Z) :
    TraceStableZigzagRel
      (TraceStableZigzag.comp left₁ right)
      (TraceStableZigzag.comp left₂ right) := by
  induction hRel with
  | refl zigzag =>
      exact TraceStableZigzagRel.refl _
  | symm h ih =>
      exact TraceStableZigzagRel.symm (ih right)
  | trans hFirst hSecond ihFirst ihSecond =>
      exact TraceStableZigzagRel.trans (ihFirst right) (ihSecond right)
  | cons step hTail ih =>
      exact TraceStableZigzagRel.cons step (ih right)
  | forwardEq hEq tail =>
      exact TraceStableZigzagRel.forwardEq hEq (TraceStableZigzag.comp tail right)
  | backwardEq hEq hLeft hRight tail =>
      exact TraceStableZigzagRel.backwardEq hEq hLeft hRight (TraceStableZigzag.comp tail right)
  | removeForwardId tail =>
      exact TraceStableZigzagRel.removeForwardId (TraceStableZigzag.comp tail right)
  | composeForward first second tail =>
      exact TraceStableZigzagRel.composeForward first second (TraceStableZigzag.comp tail right)
  | composeBackward first hFirst second hSecond tail =>
      exact TraceStableZigzagRel.composeBackward first hFirst second hSecond
        (TraceStableZigzag.comp tail right)
  | cancelForwardBackward w hWeak tail =>
      exact TraceStableZigzagRel.cancelForwardBackward w hWeak
        (TraceStableZigzag.comp tail right)
  | cancelBackwardForward w hWeak tail =>
      exact TraceStableZigzagRel.cancelBackwardForward w hWeak
        (TraceStableZigzag.comp tail right)
  | compNil zigzag =>
      simpa using TraceStableZigzagRel.refl (TraceStableZigzag.comp zigzag right)
  | nilComp zigzag =>
      simpa using TraceStableZigzagRel.refl (TraceStableZigzag.comp zigzag right)
  | compAssoc first second third =>
      simpa [TraceStableZigzag.comp_assoc_eq] using
        TraceStableZigzagRel.refl
          (TraceStableZigzag.comp first (TraceStableZigzag.comp second (TraceStableZigzag.comp third right)))

theorem comp_assoc
    {V W X Y : TraceStableHomotopyCategory}
    (first : TraceStableZigzag V W)
    (second : TraceStableZigzag W X)
    (third : TraceStableZigzag X Y) :
    TraceStableZigzagRel
      (TraceStableZigzag.comp (TraceStableZigzag.comp first second) third)
      (TraceStableZigzag.comp first (TraceStableZigzag.comp second third)) :=
  TraceStableZigzagRel.compAssoc first second third

theorem nil_comp
    {X Y : TraceStableHomotopyCategory}
    (zigzag : TraceStableZigzag X Y) :
    TraceStableZigzagRel
      (TraceStableZigzag.comp (TraceStableZigzag.nil X) zigzag)
      zigzag :=
  TraceStableZigzagRel.nilComp zigzag

theorem comp_nil
    {X Y : TraceStableHomotopyCategory}
    (zigzag : TraceStableZigzag X Y) :
    TraceStableZigzagRel
      (TraceStableZigzag.comp zigzag (TraceStableZigzag.nil Y))
      zigzag :=
  TraceStableZigzagRel.compNil zigzag

end TraceStableZigzagRel

structure TraceStableZigzagLocalization where
  obj : TraceStableHomotopyCategory

namespace TraceStableZigzagLocalization

def ofObj
    (obj : TraceStableHomotopyCategory) :
    TraceStableZigzagLocalization :=
  ⟨obj⟩

abbrev Hom
    (X Y : TraceStableZigzagLocalization) : Type 1 :=
  TraceStableLocalizedHom X.obj Y.obj

def mkHom
    {X Y : TraceStableZigzagLocalization}
    (zigzag : TraceStableZigzag X.obj Y.obj) :
    Hom X Y :=
  Quotient.mk _ zigzag

instance : CategoryTheory.Category TraceStableZigzagLocalization where
  Hom := Hom
  id X := mkHom (TraceStableZigzag.nil X.obj)
  comp left right := by
    refine Quotient.liftOn left
      (fun leftRep =>
        Quotient.liftOn right
          (fun rightRep => mkHom (TraceStableZigzag.comp leftRep rightRep))
          (by
            intro right₁ right₂ hRight
            exact Quotient.sound
              (TraceStableZigzagRel.comp_right_congr leftRep hRight))) ?_
    intro left₁ left₂ hLeft
    refine Quotient.inductionOn right ?_
    intro rightRep
    exact Quotient.sound (TraceStableZigzagRel.comp_left_congr hLeft rightRep)
  id_comp := by
    intro X Y map
    refine Quotient.inductionOn map ?_
    intro representative
    exact Quotient.sound (TraceStableZigzagRel.nil_comp representative)
  comp_id := by
    intro X Y map
    refine Quotient.inductionOn map ?_
    intro representative
    exact Quotient.sound (TraceStableZigzagRel.comp_nil representative)
  assoc := by
    intro V W X Y first second third
    refine Quotient.inductionOn first ?_
    intro firstRep
    refine Quotient.inductionOn second ?_
    intro secondRep
    refine Quotient.inductionOn third ?_
    intro thirdRep
    exact Quotient.sound (TraceStableZigzagRel.comp_assoc firstRep secondRep thirdRep)

end TraceStableZigzagLocalization

def traceStableLocalizationFunctor :
    TraceStableHomotopyCategory ⥤ TraceStableZigzagLocalization where
  obj := TraceStableZigzagLocalization.ofObj
  map := by
    intro X Y map
    exact TraceStableZigzagLocalization.mkHom (TraceStableZigzag.singleForward map)
  map_id := by
    intro X
    exact Quotient.sound
      (TraceStableZigzagRel.removeForwardId (TraceStableZigzag.nil X))
  map_comp := by
    intro X Y Z first second
    exact Quotient.sound
      (TraceStableZigzagRel.symm
        (TraceStableZigzagRel.composeForward first second (TraceStableZigzag.nil Z)))

def traceStableWeakEquivIsoInZigzagLocalization
    {X Y : TraceStableHomotopyCategory}
    (w : X ⟶ Y)
    (hWeak : TraceStableWeakEquivOnHomotopyCategory w) :
    TraceStableZigzagLocalization.ofObj X ≅
      TraceStableZigzagLocalization.ofObj Y where
  hom := TraceStableZigzagLocalization.mkHom (TraceStableZigzag.singleForward w)
  inv := TraceStableZigzagLocalization.mkHom (TraceStableZigzag.singleBackward w hWeak)
  hom_inv_id := by
    exact Quotient.sound
      (TraceStableZigzagRel.cancelForwardBackward w hWeak (TraceStableZigzag.nil X))
  inv_hom_id := by
    exact Quotient.sound
      (TraceStableZigzagRel.cancelBackwardForward w hWeak (TraceStableZigzag.nil Y))

structure TraceStableInvertsWeakEquiv
    (D : Type u) [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D) where
  mapWeakEquivIso :
    ∀ {X Y : TraceStableHomotopyCategory} (f : X ⟶ Y),
      TraceStableWeakEquivOnHomotopyCategory f →
      CategoryTheory.IsIso (F.map f)

namespace TraceStableZigzagStep

noncomputable def eval
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsWeakEquiv D F)
    {X Y : TraceStableHomotopyCategory} :
    TraceStableZigzagStep X Y → (F.obj X ⟶ F.obj Y)
  | .forward f => F.map f
  | .backward w hWeak =>
      let _ : CategoryTheory.IsIso (F.map w) := hF.mapWeakEquivIso w hWeak
      inv (F.map w)

end TraceStableZigzagStep

namespace TraceStableZigzag

noncomputable def eval
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsWeakEquiv D F)
    {X Y : TraceStableHomotopyCategory} :
    TraceStableZigzag X Y → (F.obj X ⟶ F.obj Y)
  | .nil _ => 𝟙 _
  | .cons step tail => TraceStableZigzagStep.eval F hF step ≫ eval F hF tail

@[simp] theorem eval_nil
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsWeakEquiv D F)
    (X : TraceStableHomotopyCategory) :
    eval F hF (nil X) = 𝟙 (F.obj X) :=
  rfl

@[simp] theorem eval_comp
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsWeakEquiv D F)
    {X Y Z : TraceStableHomotopyCategory}
    (first : TraceStableZigzag X Y)
    (second : TraceStableZigzag Y Z) :
    eval F hF (comp first second) = eval F hF first ≫ eval F hF second := by
  induction first with
  | nil X => simp [comp, eval]
  | cons step tail ih =>
      simp [comp, eval, ih, Category.assoc]

end TraceStableZigzag

namespace TraceStableZigzagRel

theorem eval_congr
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsWeakEquiv D F)
    {X Y : TraceStableHomotopyCategory}
    {left right : TraceStableZigzag X Y} :
    TraceStableZigzagRel left right →
      TraceStableZigzag.eval F hF left = TraceStableZigzag.eval F hF right := by
  intro hRel
  induction hRel with
  | refl zigzag =>
      rfl
  | symm h ih =>
      exact ih.symm
  | trans hFirst hSecond ihFirst ihSecond =>
      exact ihFirst.trans ihSecond
  | cons step hTail ih =>
      simp [TraceStableZigzag.eval, ih]
  | forwardEq hEq tail =>
      subst hEq
      rfl
  | backwardEq hEq hLeft hRight tail =>
      subst hEq
      have hProof : hLeft = hRight := Subsingleton.elim _ _
      subst hProof
      rfl
  | removeForwardId tail =>
      simp [TraceStableZigzag.eval, TraceStableZigzagStep.eval]
  | composeForward first second tail =>
      simp [TraceStableZigzag.eval, TraceStableZigzagStep.eval, Functor.map_comp, Category.assoc]
  | composeBackward first hFirst second hSecond tail =>
      let _ : CategoryTheory.IsIso (F.map first) := hF.mapWeakEquivIso first hFirst
      let _ : CategoryTheory.IsIso (F.map second) := hF.mapWeakEquivIso second hSecond
      let _ : CategoryTheory.IsIso (F.map (second ≫ first)) :=
        hF.mapWeakEquivIso (second ≫ first) (traceStableWeakEquiv_comp second first hSecond hFirst)
      apply (cancel_epi (F.map (second ≫ first))).1
      simp [TraceStableZigzag.eval, TraceStableZigzagStep.eval, Functor.map_comp, Category.assoc]
  | cancelForwardBackward w hWeak tail =>
      let _ : CategoryTheory.IsIso (F.map w) := hF.mapWeakEquivIso w hWeak
      simp [TraceStableZigzag.eval, TraceStableZigzagStep.eval, Category.assoc]
  | cancelBackwardForward w hWeak tail =>
      let _ : CategoryTheory.IsIso (F.map w) := hF.mapWeakEquivIso w hWeak
      simp [TraceStableZigzag.eval, TraceStableZigzagStep.eval, Category.assoc]
  | compNil zigzag =>
      simpa [TraceStableZigzag.eval_comp]
  | nilComp zigzag =>
      simpa [TraceStableZigzag.eval_comp]
  | compAssoc first second third =>
      simp [TraceStableZigzag.eval_comp, Category.assoc]

end TraceStableZigzagRel

noncomputable def traceStableLocalizedLift
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsWeakEquiv D F) :
    TraceStableZigzagLocalization ⥤ D where
  obj X := F.obj X.obj
  map := by
    intro X Y map
    refine Quotient.liftOn map (fun zigzag => TraceStableZigzag.eval F hF zigzag) ?_
    intro left right hRel
    exact TraceStableZigzagRel.eval_congr F hF hRel
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z left right
    refine Quotient.inductionOn₂ left right ?_
    intro leftRep rightRep
    exact TraceStableZigzag.eval_comp F hF leftRep rightRep

theorem traceStableLocalizedLift_comp_localizationFunctor
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsWeakEquiv D F) :
    traceStableLocalizationFunctor ⋙ traceStableLocalizedLift F hF = F := by
  exact CategoryTheory.Functor.ext
    (fun X => rfl)
    (fun X Y f => by
      have hMap : (traceStableLocalizationFunctor ⋙ traceStableLocalizedLift F hF).map f = F.map f := by
        change TraceStableZigzag.eval F hF (TraceStableZigzag.singleForward f) = F.map f
        simp [TraceStableZigzag.eval, TraceStableZigzag.singleForward,
          TraceStableZigzagStep.eval]
      simpa using hMap)

def traceStableLocalizedFactorizationObjEq
    {D : Type u} [CategoryTheory.Category D]
    {F : TraceStableHomotopyCategory ⥤ D}
    {G : TraceStableZigzagLocalization ⥤ D}
    (hcomp : traceStableLocalizationFunctor ⋙ G = F)
    (X : TraceStableHomotopyCategory) :
    G.obj (TraceStableZigzagLocalization.ofObj X) = F.obj X :=
  CategoryTheory.Functor.congr_obj hcomp X

theorem traceStableLocalizedFactorization_map_singleForward
    {D : Type u} [CategoryTheory.Category D]
    {F : TraceStableHomotopyCategory ⥤ D}
    {G : TraceStableZigzagLocalization ⥤ D}
    (hcomp : traceStableLocalizationFunctor ⋙ G = F)
    {X Y : TraceStableHomotopyCategory}
    (f : X ⟶ Y) :
    G.map (TraceStableZigzagLocalization.mkHom (TraceStableZigzag.singleForward f)) =
      eqToHom (traceStableLocalizedFactorizationObjEq hcomp X) ≫
        F.map f ≫
          eqToHom (traceStableLocalizedFactorizationObjEq hcomp Y).symm := by
  simpa [traceStableLocalizationFunctor, TraceStableZigzag.singleForward,
    TraceStableZigzagLocalization.mkHom]
    using CategoryTheory.Functor.congr_hom hcomp f

theorem traceStableLocalizedFactorization_map_singleBackward
    {D : Type u} [CategoryTheory.Category D]
    {F : TraceStableHomotopyCategory ⥤ D}
    (hF : TraceStableInvertsWeakEquiv D F)
    {G : TraceStableZigzagLocalization ⥤ D}
    (hcomp : traceStableLocalizationFunctor ⋙ G = F)
    {X Y : TraceStableHomotopyCategory}
    (w : Y ⟶ X)
    (hWeak : TraceStableWeakEquivOnHomotopyCategory w) :
    G.map (TraceStableZigzagLocalization.mkHom (TraceStableZigzag.singleBackward w hWeak)) =
      eqToHom (traceStableLocalizedFactorizationObjEq hcomp X) ≫
        TraceStableZigzagStep.eval F hF (TraceStableZigzagStep.backward w hWeak) ≫
          eqToHom (traceStableLocalizedFactorizationObjEq hcomp Y).symm := by
  let hX := traceStableLocalizedFactorizationObjEq hcomp X
  let hY := traceStableLocalizedFactorizationObjEq hcomp Y
  let _ : CategoryTheory.IsIso (F.map w) := hF.mapWeakEquivIso w hWeak
  let forwardArrow := TraceStableZigzagLocalization.mkHom (TraceStableZigzag.singleForward w)
  let backwardArrow := TraceStableZigzagLocalization.mkHom (TraceStableZigzag.singleBackward w hWeak)
  have hForward :
      G.map forwardArrow = eqToHom hY ≫ F.map w ≫ eqToHom hX.symm :=
    traceStableLocalizedFactorization_map_singleForward hcomp w
  have hBackwardRight : G.map backwardArrow ≫ G.map forwardArrow = 𝟙 _ := by
    calc
      G.map backwardArrow ≫ G.map forwardArrow = G.map (backwardArrow ≫ forwardArrow) := by
        rw [← G.map_comp]
      _ = G.map (𝟙 _) := by
        exact congrArg G.map (traceStableWeakEquivIsoInZigzagLocalization w hWeak).inv_hom_id
      _ = 𝟙 _ := by rw [G.map_id]
  have hForwardIso : CategoryTheory.IsIso (G.map forwardArrow) := by
    rw [hForward]
    infer_instance
  let _ : CategoryTheory.IsIso (G.map forwardArrow) := hForwardIso
  have hCandidateRight :
      (eqToHom hX ≫ TraceStableZigzagStep.eval F hF (TraceStableZigzagStep.backward w hWeak) ≫
          eqToHom hY.symm) ≫ G.map forwardArrow = 𝟙 _ := by
    rw [hForward]
    simp [TraceStableZigzagStep.eval, hX, hY, Category.assoc]
  apply (cancel_mono (G.map forwardArrow)).1
  calc
    G.map backwardArrow ≫ G.map forwardArrow = 𝟙 _ := hBackwardRight
    _ = (eqToHom hX ≫ TraceStableZigzagStep.eval F hF (TraceStableZigzagStep.backward w hWeak) ≫
          eqToHom hY.symm) ≫ G.map forwardArrow :=
      hCandidateRight.symm

theorem traceStableLocalizedFactorization_map_zigzag
    {D : Type u} [CategoryTheory.Category D]
    {F : TraceStableHomotopyCategory ⥤ D}
    (hF : TraceStableInvertsWeakEquiv D F)
    {G : TraceStableZigzagLocalization ⥤ D}
    (hcomp : traceStableLocalizationFunctor ⋙ G = F)
    {X Y : TraceStableHomotopyCategory}
    (zigzag : TraceStableZigzag X Y) :
    G.map (TraceStableZigzagLocalization.mkHom zigzag) =
      eqToHom (traceStableLocalizedFactorizationObjEq hcomp X) ≫
        TraceStableZigzag.eval F hF zigzag ≫
          eqToHom (traceStableLocalizedFactorizationObjEq hcomp Y).symm := by
  induction zigzag with
  | nil X =>
      change G.map (𝟙 (TraceStableZigzagLocalization.ofObj X)) =
        eqToHom (traceStableLocalizedFactorizationObjEq hcomp X) ≫ 𝟙 _ ≫
          eqToHom (traceStableLocalizedFactorizationObjEq hcomp X).symm
      simp
  | @cons X Y Z step tail ih =>
      cases step with
      | forward f =>
          have hHead := traceStableLocalizedFactorization_map_singleForward hcomp f
          calc
            G.map (TraceStableZigzagLocalization.mkHom (TraceStableZigzag.cons (TraceStableZigzagStep.forward f) tail))
                = G.map (TraceStableZigzagLocalization.mkHom (TraceStableZigzag.singleForward f) ≫
                    TraceStableZigzagLocalization.mkHom tail) := by rfl
            _ = G.map (TraceStableZigzagLocalization.mkHom (TraceStableZigzag.singleForward f)) ≫
                  G.map (TraceStableZigzagLocalization.mkHom tail) := by rw [G.map_comp]
            _ = (eqToHom (traceStableLocalizedFactorizationObjEq hcomp X) ≫ F.map f ≫
                    eqToHom (traceStableLocalizedFactorizationObjEq hcomp Y).symm) ≫
                  G.map (TraceStableZigzagLocalization.mkHom tail) := by rw [hHead]
            _ = (eqToHom (traceStableLocalizedFactorizationObjEq hcomp X) ≫ F.map f ≫
                    eqToHom (traceStableLocalizedFactorizationObjEq hcomp Y).symm) ≫
                  (eqToHom (traceStableLocalizedFactorizationObjEq hcomp Y) ≫
                    TraceStableZigzag.eval F hF tail ≫
                    eqToHom (traceStableLocalizedFactorizationObjEq hcomp Z).symm) := by rw [ih]
            _ = eqToHom (traceStableLocalizedFactorizationObjEq hcomp X) ≫
                  TraceStableZigzag.eval F hF
                    (TraceStableZigzag.cons (TraceStableZigzagStep.forward f) tail) ≫
                  eqToHom (traceStableLocalizedFactorizationObjEq hcomp Z).symm := by
                  simp [TraceStableZigzag.eval, TraceStableZigzagStep.eval, Category.assoc]
      | backward w hWeak =>
          have hHead := traceStableLocalizedFactorization_map_singleBackward hF hcomp w hWeak
          calc
            G.map (TraceStableZigzagLocalization.mkHom (TraceStableZigzag.cons (TraceStableZigzagStep.backward w hWeak) tail))
                = G.map (TraceStableZigzagLocalization.mkHom (TraceStableZigzag.singleBackward w hWeak) ≫
                    TraceStableZigzagLocalization.mkHom tail) := by rfl
            _ = G.map (TraceStableZigzagLocalization.mkHom (TraceStableZigzag.singleBackward w hWeak)) ≫
                  G.map (TraceStableZigzagLocalization.mkHom tail) := by rw [G.map_comp]
            _ = (eqToHom (traceStableLocalizedFactorizationObjEq hcomp X) ≫
              TraceStableZigzagStep.eval F hF (TraceStableZigzagStep.backward w hWeak) ≫
                    eqToHom (traceStableLocalizedFactorizationObjEq hcomp Y).symm) ≫
                  G.map (TraceStableZigzagLocalization.mkHom tail) := by rw [hHead]
            _ = (eqToHom (traceStableLocalizedFactorizationObjEq hcomp X) ≫
              TraceStableZigzagStep.eval F hF (TraceStableZigzagStep.backward w hWeak) ≫
                    eqToHom (traceStableLocalizedFactorizationObjEq hcomp Y).symm) ≫
                  (eqToHom (traceStableLocalizedFactorizationObjEq hcomp Y) ≫
                    TraceStableZigzag.eval F hF tail ≫
                    eqToHom (traceStableLocalizedFactorizationObjEq hcomp Z).symm) := by rw [ih]
            _ = eqToHom (traceStableLocalizedFactorizationObjEq hcomp X) ≫
                  TraceStableZigzag.eval F hF
                    (TraceStableZigzag.cons (TraceStableZigzagStep.backward w hWeak) tail) ≫
                  eqToHom (traceStableLocalizedFactorizationObjEq hcomp Z).symm := by
                  simp [TraceStableZigzag.eval, TraceStableZigzagStep.eval, Category.assoc]

theorem traceStableLocalizedLift_unique
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsWeakEquiv D F)
    (G : TraceStableZigzagLocalization ⥤ D)
    (hcomp : traceStableLocalizationFunctor ⋙ G = F) :
    G = traceStableLocalizedLift F hF := by
  exact CategoryTheory.Functor.ext
    (fun X => traceStableLocalizedFactorizationObjEq hcomp X.obj)
    (fun X Y f => by
      refine Quotient.inductionOn f ?_
      intro zigzag
      simpa [traceStableLocalizedLift, TraceStableZigzagLocalization.ofObj] using
        traceStableLocalizedFactorization_map_zigzag hF hcomp zigzag)

end FormalPresentationOnly

inductive TraceStableGroundedZigzagStep :
    TraceStableHomotopyCategory → TraceStableHomotopyCategory → Type 1 where
  | forward {X Y : TraceStableHomotopyCategory}
      (f : X ⟶ Y) : TraceStableGroundedZigzagStep X Y
  | backward {X Y : TraceStableHomotopyCategory}
      (w : Y ⟶ X)
      (hWeak : TraceStableGroundedWeakEquivOnHomotopyCategory w) :
      TraceStableGroundedZigzagStep X Y

inductive TraceStableGroundedZigzag :
    TraceStableHomotopyCategory → TraceStableHomotopyCategory → Type 1 where
  | nil (X : TraceStableHomotopyCategory) : TraceStableGroundedZigzag X X
  | cons {X Y Z : TraceStableHomotopyCategory}
      (step : TraceStableGroundedZigzagStep X Y)
      (tail : TraceStableGroundedZigzag Y Z) :
      TraceStableGroundedZigzag X Z

namespace TraceStableGroundedZigzag

def comp
    {X Y Z : TraceStableHomotopyCategory} :
    TraceStableGroundedZigzag X Y →
      TraceStableGroundedZigzag Y Z →
      TraceStableGroundedZigzag X Z
  | nil _, right => right
  | cons step tail, right => cons step (comp tail right)

def singleForward
    {X Y : TraceStableHomotopyCategory}
    (f : X ⟶ Y) : TraceStableGroundedZigzag X Y :=
  cons (TraceStableGroundedZigzagStep.forward f) (nil Y)

def singleBackward
    {X Y : TraceStableHomotopyCategory}
    (w : Y ⟶ X)
    (hWeak : TraceStableGroundedWeakEquivOnHomotopyCategory w) :
    TraceStableGroundedZigzag X Y :=
  cons (TraceStableGroundedZigzagStep.backward w hWeak) (nil Y)

@[simp] theorem nil_comp
    {X Y : TraceStableHomotopyCategory}
    (zigzag : TraceStableGroundedZigzag X Y) :
    comp (nil X) zigzag = zigzag :=
  rfl

@[simp] theorem comp_nil
    {X Y : TraceStableHomotopyCategory}
    (zigzag : TraceStableGroundedZigzag X Y) :
    comp zigzag (nil Y) = zigzag := by
  induction zigzag with
  | nil X => rfl
  | cons step tail ih => simp [comp, ih]

@[simp] theorem comp_assoc_eq
    {W X Y Z : TraceStableHomotopyCategory}
    (first : TraceStableGroundedZigzag W X)
    (second : TraceStableGroundedZigzag X Y)
    (third : TraceStableGroundedZigzag Y Z) :
    comp (comp first second) third = comp first (comp second third) := by
  induction first with
  | nil X => rfl
  | cons step tail ih => simp [comp, ih]

end TraceStableGroundedZigzag

inductive TraceStableGroundedZigzagRel :
    {X Y : TraceStableHomotopyCategory} →
      TraceStableGroundedZigzag X Y →
      TraceStableGroundedZigzag X Y → Prop where
  | refl {X Y : TraceStableHomotopyCategory}
      (zigzag : TraceStableGroundedZigzag X Y) :
      TraceStableGroundedZigzagRel zigzag zigzag
  | symm {X Y : TraceStableHomotopyCategory}
      {left right : TraceStableGroundedZigzag X Y} :
      TraceStableGroundedZigzagRel left right →
        TraceStableGroundedZigzagRel right left
  | trans {X Y : TraceStableHomotopyCategory}
      {first middle last : TraceStableGroundedZigzag X Y} :
      TraceStableGroundedZigzagRel first middle →
      TraceStableGroundedZigzagRel middle last →
        TraceStableGroundedZigzagRel first last
  | cons {X Y Z : TraceStableHomotopyCategory}
      (step : TraceStableGroundedZigzagStep X Y)
      {left right : TraceStableGroundedZigzag Y Z} :
      TraceStableGroundedZigzagRel left right →
        TraceStableGroundedZigzagRel
          (TraceStableGroundedZigzag.cons step left)
          (TraceStableGroundedZigzag.cons step right)
  | forwardEq {X Y Z : TraceStableHomotopyCategory}
      {left right : X ⟶ Y}
      (hEq : left = right)
      (tail : TraceStableGroundedZigzag Y Z) :
      TraceStableGroundedZigzagRel
        (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.forward left) tail)
        (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.forward right) tail)
  | backwardEq {X Y Z : TraceStableHomotopyCategory}
      {left right : Y ⟶ X}
      (hEq : left = right)
      (hLeft : TraceStableGroundedWeakEquivOnHomotopyCategory left)
      (hRight : TraceStableGroundedWeakEquivOnHomotopyCategory right)
      (tail : TraceStableGroundedZigzag Y Z) :
      TraceStableGroundedZigzagRel
        (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.backward left hLeft) tail)
        (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.backward right hRight) tail)
  | removeForwardId {X Y : TraceStableHomotopyCategory}
      (tail : TraceStableGroundedZigzag X Y) :
      TraceStableGroundedZigzagRel
        (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.forward (𝟙 X)) tail)
        tail
  | composeForward {W X Y Z : TraceStableHomotopyCategory}
      (first : W ⟶ X)
      (second : X ⟶ Y)
      (tail : TraceStableGroundedZigzag Y Z) :
      TraceStableGroundedZigzagRel
        (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.forward first)
          (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.forward second) tail))
        (TraceStableGroundedZigzag.cons
          (TraceStableGroundedZigzagStep.forward (first ≫ second)) tail)
  | composeBackward {W X Y Z : TraceStableHomotopyCategory}
      (first : X ⟶ W)
      (hFirst : TraceStableGroundedWeakEquivOnHomotopyCategory first)
      (second : Y ⟶ X)
      (hSecond : TraceStableGroundedWeakEquivOnHomotopyCategory second)
      (tail : TraceStableGroundedZigzag Y Z) :
      TraceStableGroundedZigzagRel
        (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.backward first hFirst)
          (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.backward second hSecond) tail))
        (TraceStableGroundedZigzag.cons
          (TraceStableGroundedZigzagStep.backward (second ≫ first)
            (traceStableGroundedWeakEquiv_comp second first hSecond hFirst))
          tail)
  | cancelForwardBackward {X Y Z : TraceStableHomotopyCategory}
      (w : X ⟶ Y)
      (hWeak : TraceStableGroundedWeakEquivOnHomotopyCategory w)
      (tail : TraceStableGroundedZigzag X Z) :
      TraceStableGroundedZigzagRel
        (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.forward w)
          (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.backward w hWeak) tail))
        tail
  | cancelBackwardForward {X Y Z : TraceStableHomotopyCategory}
      (w : X ⟶ Y)
      (hWeak : TraceStableGroundedWeakEquivOnHomotopyCategory w)
      (tail : TraceStableGroundedZigzag Y Z) :
      TraceStableGroundedZigzagRel
        (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.backward w hWeak)
          (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.forward w) tail))
        tail
  | compNil {X Y : TraceStableHomotopyCategory}
      (zigzag : TraceStableGroundedZigzag X Y) :
      TraceStableGroundedZigzagRel
        (TraceStableGroundedZigzag.comp zigzag (TraceStableGroundedZigzag.nil Y))
        zigzag
  | nilComp {X Y : TraceStableHomotopyCategory}
      (zigzag : TraceStableGroundedZigzag X Y) :
      TraceStableGroundedZigzagRel
        (TraceStableGroundedZigzag.comp (TraceStableGroundedZigzag.nil X) zigzag)
        zigzag
  | compAssoc {V W X Y : TraceStableHomotopyCategory}
      (first : TraceStableGroundedZigzag V W)
      (second : TraceStableGroundedZigzag W X)
      (third : TraceStableGroundedZigzag X Y) :
      TraceStableGroundedZigzagRel
        (TraceStableGroundedZigzag.comp (TraceStableGroundedZigzag.comp first second) third)
        (TraceStableGroundedZigzag.comp first (TraceStableGroundedZigzag.comp second third))

def TraceStableGroundedZigzagSetoid
    (X Y : TraceStableHomotopyCategory) :
    Setoid (TraceStableGroundedZigzag X Y) where
  r := TraceStableGroundedZigzagRel
  iseqv := {
    refl := by
      intro zigzag
      exact TraceStableGroundedZigzagRel.refl zigzag
    symm := by
      intro left right hRel
      exact TraceStableGroundedZigzagRel.symm hRel
    trans := by
      intro first middle last hFirst hSecond
      exact TraceStableGroundedZigzagRel.trans hFirst hSecond }

abbrev TraceStableGroundedLocalizedHom
    (X Y : TraceStableHomotopyCategory) : Type 1 :=
  Quotient (TraceStableGroundedZigzagSetoid X Y)

namespace TraceStableGroundedZigzagRel

theorem comp_right_congr
    {X Y Z : TraceStableHomotopyCategory}
    (left : TraceStableGroundedZigzag X Y)
    {right₁ right₂ : TraceStableGroundedZigzag Y Z} :
    TraceStableGroundedZigzagRel right₁ right₂ →
      TraceStableGroundedZigzagRel
        (TraceStableGroundedZigzag.comp left right₁)
        (TraceStableGroundedZigzag.comp left right₂) := by
  intro hRel
  induction left with
  | nil X => simpa using hRel
  | cons step tail ih =>
      exact TraceStableGroundedZigzagRel.cons step (ih hRel)

theorem comp_left_congr
    {X Y Z : TraceStableHomotopyCategory}
    {left₁ left₂ : TraceStableGroundedZigzag X Y}
    (hRel : TraceStableGroundedZigzagRel left₁ left₂)
    (right : TraceStableGroundedZigzag Y Z) :
    TraceStableGroundedZigzagRel
      (TraceStableGroundedZigzag.comp left₁ right)
      (TraceStableGroundedZigzag.comp left₂ right) := by
  induction hRel with
  | refl zigzag =>
      exact TraceStableGroundedZigzagRel.refl _
  | symm h ih =>
      exact TraceStableGroundedZigzagRel.symm (ih right)
  | trans hFirst hSecond ihFirst ihSecond =>
      exact TraceStableGroundedZigzagRel.trans (ihFirst right) (ihSecond right)
  | cons step hTail ih =>
      exact TraceStableGroundedZigzagRel.cons step (ih right)
  | forwardEq hEq tail =>
      exact TraceStableGroundedZigzagRel.forwardEq hEq
        (TraceStableGroundedZigzag.comp tail right)
  | backwardEq hEq hLeft hRight tail =>
      exact TraceStableGroundedZigzagRel.backwardEq hEq hLeft hRight
        (TraceStableGroundedZigzag.comp tail right)
  | removeForwardId tail =>
      exact TraceStableGroundedZigzagRel.removeForwardId
        (TraceStableGroundedZigzag.comp tail right)
  | composeForward first second tail =>
      exact TraceStableGroundedZigzagRel.composeForward first second
        (TraceStableGroundedZigzag.comp tail right)
  | composeBackward first hFirst second hSecond tail =>
      exact TraceStableGroundedZigzagRel.composeBackward first hFirst second hSecond
        (TraceStableGroundedZigzag.comp tail right)
  | cancelForwardBackward w hWeak tail =>
      exact TraceStableGroundedZigzagRel.cancelForwardBackward w hWeak
        (TraceStableGroundedZigzag.comp tail right)
  | cancelBackwardForward w hWeak tail =>
      exact TraceStableGroundedZigzagRel.cancelBackwardForward w hWeak
        (TraceStableGroundedZigzag.comp tail right)
  | compNil zigzag =>
      simpa using TraceStableGroundedZigzagRel.refl
        (TraceStableGroundedZigzag.comp zigzag right)
  | nilComp zigzag =>
      simpa using TraceStableGroundedZigzagRel.refl
        (TraceStableGroundedZigzag.comp zigzag right)
  | compAssoc first second third =>
      simpa [TraceStableGroundedZigzag.comp_assoc_eq] using
        TraceStableGroundedZigzagRel.refl
          (TraceStableGroundedZigzag.comp first
            (TraceStableGroundedZigzag.comp second
              (TraceStableGroundedZigzag.comp third right)))

theorem comp_assoc
    {V W X Y : TraceStableHomotopyCategory}
    (first : TraceStableGroundedZigzag V W)
    (second : TraceStableGroundedZigzag W X)
    (third : TraceStableGroundedZigzag X Y) :
    TraceStableGroundedZigzagRel
      (TraceStableGroundedZigzag.comp (TraceStableGroundedZigzag.comp first second) third)
      (TraceStableGroundedZigzag.comp first (TraceStableGroundedZigzag.comp second third)) :=
  TraceStableGroundedZigzagRel.compAssoc first second third

theorem nil_comp
    {X Y : TraceStableHomotopyCategory}
    (zigzag : TraceStableGroundedZigzag X Y) :
    TraceStableGroundedZigzagRel
      (TraceStableGroundedZigzag.comp (TraceStableGroundedZigzag.nil X) zigzag)
      zigzag :=
  TraceStableGroundedZigzagRel.nilComp zigzag

theorem comp_nil
    {X Y : TraceStableHomotopyCategory}
    (zigzag : TraceStableGroundedZigzag X Y) :
    TraceStableGroundedZigzagRel
      (TraceStableGroundedZigzag.comp zigzag (TraceStableGroundedZigzag.nil Y))
      zigzag :=
  TraceStableGroundedZigzagRel.compNil zigzag

end TraceStableGroundedZigzagRel

structure TraceStableGroundedZigzagLocalization where
  obj : TraceStableHomotopyCategory

namespace TraceStableGroundedZigzagLocalization

def ofObj
    (obj : TraceStableHomotopyCategory) :
    TraceStableGroundedZigzagLocalization :=
  ⟨obj⟩

abbrev Hom
    (X Y : TraceStableGroundedZigzagLocalization) : Type 1 :=
  TraceStableGroundedLocalizedHom X.obj Y.obj

def mkHom
    {X Y : TraceStableGroundedZigzagLocalization}
    (zigzag : TraceStableGroundedZigzag X.obj Y.obj) :
    Hom X Y :=
  Quotient.mk _ zigzag

def zeroObj : TraceStableGroundedZigzagLocalization :=
  ofObj TraceStableHomotopyCategory.zeroObj

def zeroHom
    (X Y : TraceStableGroundedZigzagLocalization) :
    Hom X Y :=
  mkHom (TraceStableGroundedZigzag.singleForward
    (TraceStableHomotopyCategory.zeroHom X.obj Y.obj))

instance : CategoryTheory.Category TraceStableGroundedZigzagLocalization where
  Hom := Hom
  id X := mkHom (TraceStableGroundedZigzag.nil X.obj)
  comp left right := by
    refine Quotient.liftOn left
      (fun leftRep =>
        Quotient.liftOn right
          (fun rightRep => mkHom (TraceStableGroundedZigzag.comp leftRep rightRep))
          (by
            intro right₁ right₂ hRight
            exact Quotient.sound
              (TraceStableGroundedZigzagRel.comp_right_congr leftRep hRight))) ?_
    intro left₁ left₂ hLeft
    refine Quotient.inductionOn right ?_
    intro rightRep
    exact Quotient.sound (TraceStableGroundedZigzagRel.comp_left_congr hLeft rightRep)
  id_comp := by
    intro X Y map
    refine Quotient.inductionOn map ?_
    intro representative
    exact Quotient.sound (TraceStableGroundedZigzagRel.nil_comp representative)
  comp_id := by
    intro X Y map
    refine Quotient.inductionOn map ?_
    intro representative
    exact Quotient.sound (TraceStableGroundedZigzagRel.comp_nil representative)
  assoc := by
    intro V W X Y first second third
    refine Quotient.inductionOn first ?_
    intro firstRep
    refine Quotient.inductionOn second ?_
    intro secondRep
    refine Quotient.inductionOn third ?_
    intro thirdRep
    exact Quotient.sound (TraceStableGroundedZigzagRel.comp_assoc firstRep secondRep thirdRep)

end TraceStableGroundedZigzagLocalization

def traceStableGroundedLocalizationFunctor :
    TraceStableHomotopyCategory ⥤ TraceStableGroundedZigzagLocalization where
  obj := TraceStableGroundedZigzagLocalization.ofObj
  map := by
    intro X Y map
    exact TraceStableGroundedZigzagLocalization.mkHom
      (TraceStableGroundedZigzag.singleForward map)
  map_id := by
    intro X
    exact Quotient.sound
      (TraceStableGroundedZigzagRel.removeForwardId
        (TraceStableGroundedZigzag.nil X))
  map_comp := by
    intro X Y Z first second
    exact Quotient.sound
      (TraceStableGroundedZigzagRel.symm
        (TraceStableGroundedZigzagRel.composeForward first second
          (TraceStableGroundedZigzag.nil Z)))

def traceStableGroundedWeakEquivIso
    {X Y : TraceStableHomotopyCategory}
    (w : X ⟶ Y)
    (hWeak : TraceStableGroundedWeakEquivOnHomotopyCategory w) :
    TraceStableGroundedZigzagLocalization.ofObj X ≅
      TraceStableGroundedZigzagLocalization.ofObj Y where
  hom := TraceStableGroundedZigzagLocalization.mkHom
    (TraceStableGroundedZigzag.singleForward w)
  inv := TraceStableGroundedZigzagLocalization.mkHom
    (TraceStableGroundedZigzag.singleBackward w hWeak)
  hom_inv_id := by
    exact Quotient.sound
      (TraceStableGroundedZigzagRel.cancelForwardBackward w hWeak
        (TraceStableGroundedZigzag.nil X))
  inv_hom_id := by
    exact Quotient.sound
      (TraceStableGroundedZigzagRel.cancelBackwardForward w hWeak
        (TraceStableGroundedZigzag.nil Y))

structure TraceStableInvertsGroundedWeakEquiv
    (D : Type u) [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D) where
  mapWeakEquivIso :
    ∀ {X Y : TraceStableHomotopyCategory} (f : X ⟶ Y),
      TraceStableGroundedWeakEquivOnHomotopyCategory f →
      CategoryTheory.IsIso (F.map f)

namespace TraceStableGroundedZigzagStep

def shift
    {X Y : TraceStableHomotopyCategory} :
    TraceStableGroundedZigzagStep X Y →
      TraceStableGroundedZigzagStep
        (TraceStableHomotopyCategory.shiftObj X)
        (TraceStableHomotopyCategory.shiftObj Y)
  | .forward f =>
      .forward (TraceStableHomotopyCategory.shiftHom f)
  | .backward w hWeak =>
      .backward (TraceStableHomotopyCategory.shiftHom w)
        (traceStableGroundedWeakEquiv_shift w hWeak)

noncomputable def eval
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsGroundedWeakEquiv D F)
    {X Y : TraceStableHomotopyCategory} :
    TraceStableGroundedZigzagStep X Y → (F.obj X ⟶ F.obj Y)
  | .forward f => F.map f
  | .backward w hWeak =>
      let _ : CategoryTheory.IsIso (F.map w) := hF.mapWeakEquivIso w hWeak
      inv (F.map w)

end TraceStableGroundedZigzagStep

namespace TraceStableGroundedZigzag

def shift
    {X Y : TraceStableHomotopyCategory} :
    TraceStableGroundedZigzag X Y →
      TraceStableGroundedZigzag
        (TraceStableHomotopyCategory.shiftObj X)
        (TraceStableHomotopyCategory.shiftObj Y)
  | .nil X => .nil (TraceStableHomotopyCategory.shiftObj X)
  | .cons step tail => .cons (TraceStableGroundedZigzagStep.shift step) (shift tail)

@[simp] theorem shift_nil
    (X : TraceStableHomotopyCategory) :
    shift (TraceStableGroundedZigzag.nil X) =
      TraceStableGroundedZigzag.nil (TraceStableHomotopyCategory.shiftObj X) :=
  rfl

@[simp] theorem shift_comp
    {X Y Z : TraceStableHomotopyCategory}
    (first : TraceStableGroundedZigzag X Y)
    (second : TraceStableGroundedZigzag Y Z) :
    shift (comp first second) = comp (shift first) (shift second) := by
  induction first with
  | nil X => rfl
  | cons step tail ih => simp [comp, shift, ih]

noncomputable def eval
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsGroundedWeakEquiv D F)
    {X Y : TraceStableHomotopyCategory} :
    TraceStableGroundedZigzag X Y → (F.obj X ⟶ F.obj Y)
  | .nil _ => 𝟙 _
  | .cons step tail => TraceStableGroundedZigzagStep.eval F hF step ≫ eval F hF tail

@[simp] theorem eval_nil
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsGroundedWeakEquiv D F)
    (X : TraceStableHomotopyCategory) :
    eval F hF (nil X) = 𝟙 (F.obj X) :=
  rfl

@[simp] theorem eval_comp
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsGroundedWeakEquiv D F)
    {X Y Z : TraceStableHomotopyCategory}
    (first : TraceStableGroundedZigzag X Y)
    (second : TraceStableGroundedZigzag Y Z) :
    eval F hF (comp first second) = eval F hF first ≫ eval F hF second := by
  induction first with
  | nil X => simp [comp, eval]
  | cons step tail ih =>
      simp [comp, eval, ih, Category.assoc]

end TraceStableGroundedZigzag

namespace TraceStableGroundedZigzagRel

theorem shift
    {X Y : TraceStableHomotopyCategory}
    {left right : TraceStableGroundedZigzag X Y} :
    TraceStableGroundedZigzagRel left right →
      TraceStableGroundedZigzagRel
        (TraceStableGroundedZigzag.shift left)
        (TraceStableGroundedZigzag.shift right) := by
  intro hRel
  induction hRel with
  | refl zigzag =>
      exact TraceStableGroundedZigzagRel.refl _
  | symm h ih =>
      exact TraceStableGroundedZigzagRel.symm ih
  | trans hFirst hSecond ihFirst ihSecond =>
      exact TraceStableGroundedZigzagRel.trans ihFirst ihSecond
  | cons step hTail ih =>
      exact TraceStableGroundedZigzagRel.cons _ ih
  | forwardEq hEq tail =>
      exact TraceStableGroundedZigzagRel.forwardEq
        (congrArg TraceStableHomotopyCategory.shiftHom hEq)
        (TraceStableGroundedZigzag.shift tail)
  | backwardEq hEq hLeft hRight tail =>
      exact TraceStableGroundedZigzagRel.backwardEq
        (congrArg TraceStableHomotopyCategory.shiftHom hEq)
        (traceStableGroundedWeakEquiv_shift _ hLeft)
        (traceStableGroundedWeakEquiv_shift _ hRight)
        (TraceStableGroundedZigzag.shift tail)
  | removeForwardId tail =>
      exact TraceStableGroundedZigzagRel.trans
        (TraceStableGroundedZigzagRel.forwardEq
          (TraceStableHomotopyCategory.shiftHom_id _)
          (TraceStableGroundedZigzag.shift tail))
        (TraceStableGroundedZigzagRel.removeForwardId
          (TraceStableGroundedZigzag.shift tail))
  | @composeForward W X Y Z first second tail =>
      let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
      have hShiftComp :
          TraceStableHomotopyCategory.shiftHom (first ≫ second) =
            (show TraceStableHomotopyCategory.Hom
              (TraceStableHomotopyCategory.shiftObj W)
              (TraceStableHomotopyCategory.shiftObj Y)
              from (inferInstance : CategoryTheory.Category TraceStableHomotopyCategory).comp
                (TraceStableHomotopyCategory.shiftHom first)
                (TraceStableHomotopyCategory.shiftHom second)) := by
        refine Quotient.inductionOn₂ first second ?_
        intro firstRep secondRep
        exact Quotient.sound ⟨TraceStableInfinityHomotopy.shiftComp firstRep secondRep⟩
      exact TraceStableGroundedZigzagRel.trans
        (TraceStableGroundedZigzagRel.composeForward
          (TraceStableHomotopyCategory.shiftHom first)
          (TraceStableHomotopyCategory.shiftHom second)
          (TraceStableGroundedZigzag.shift tail))
        (TraceStableGroundedZigzagRel.forwardEq
          hShiftComp.symm
          (TraceStableGroundedZigzag.shift tail))
  | @composeBackward W X Y Z first hFirst second hSecond tail =>
      let _inst : CategoryTheory.Category TraceStableHomotopyCategory := inferInstance
      have hShiftComp :
          TraceStableHomotopyCategory.shiftHom (second ≫ first) =
            (show TraceStableHomotopyCategory.Hom
              (TraceStableHomotopyCategory.shiftObj Y)
              (TraceStableHomotopyCategory.shiftObj W)
              from (inferInstance : CategoryTheory.Category TraceStableHomotopyCategory).comp
                (TraceStableHomotopyCategory.shiftHom second)
                (TraceStableHomotopyCategory.shiftHom first)) := by
        refine Quotient.inductionOn₂ second first ?_
        intro secondRep firstRep
        exact Quotient.sound ⟨TraceStableInfinityHomotopy.shiftComp secondRep firstRep⟩
      exact TraceStableGroundedZigzagRel.trans
        (TraceStableGroundedZigzagRel.composeBackward
          (TraceStableHomotopyCategory.shiftHom first)
          (traceStableGroundedWeakEquiv_shift _ hFirst)
          (TraceStableHomotopyCategory.shiftHom second)
          (traceStableGroundedWeakEquiv_shift _ hSecond)
          (TraceStableGroundedZigzag.shift tail))
        (TraceStableGroundedZigzagRel.backwardEq
          hShiftComp.symm
          (traceStableGroundedWeakEquiv_comp
            (TraceStableHomotopyCategory.shiftHom second)
            (TraceStableHomotopyCategory.shiftHom first)
            (traceStableGroundedWeakEquiv_shift _ hSecond)
            (traceStableGroundedWeakEquiv_shift _ hFirst))
          (traceStableGroundedWeakEquiv_shift _
            (traceStableGroundedWeakEquiv_comp second first hSecond hFirst))
          (TraceStableGroundedZigzag.shift tail))
  | cancelForwardBackward w hWeak tail =>
      exact TraceStableGroundedZigzagRel.cancelForwardBackward
        (TraceStableHomotopyCategory.shiftHom w)
        (traceStableGroundedWeakEquiv_shift _ hWeak)
        (TraceStableGroundedZigzag.shift tail)
  | cancelBackwardForward w hWeak tail =>
      exact TraceStableGroundedZigzagRel.cancelBackwardForward
        (TraceStableHomotopyCategory.shiftHom w)
        (traceStableGroundedWeakEquiv_shift _ hWeak)
        (TraceStableGroundedZigzag.shift tail)
  | compNil zigzag =>
      simpa [TraceStableGroundedZigzag.shift_comp] using
        TraceStableGroundedZigzagRel.compNil (TraceStableGroundedZigzag.shift zigzag)
  | nilComp zigzag =>
      simpa [TraceStableGroundedZigzag.shift_comp] using
        TraceStableGroundedZigzagRel.nilComp (TraceStableGroundedZigzag.shift zigzag)
  | compAssoc first second third =>
      simpa [TraceStableGroundedZigzag.shift_comp] using
        TraceStableGroundedZigzagRel.compAssoc
          (TraceStableGroundedZigzag.shift first)
          (TraceStableGroundedZigzag.shift second)
          (TraceStableGroundedZigzag.shift third)

theorem eval_congr
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsGroundedWeakEquiv D F)
    {X Y : TraceStableHomotopyCategory}
    {left right : TraceStableGroundedZigzag X Y} :
    TraceStableGroundedZigzagRel left right →
      TraceStableGroundedZigzag.eval F hF left =
        TraceStableGroundedZigzag.eval F hF right := by
  intro hRel
  induction hRel with
  | refl zigzag =>
      rfl
  | symm h ih =>
      exact ih.symm
  | trans hFirst hSecond ihFirst ihSecond =>
      exact ihFirst.trans ihSecond
  | cons step hTail ih =>
      simp [TraceStableGroundedZigzag.eval, ih]
  | forwardEq hEq tail =>
      subst hEq
      rfl
  | backwardEq hEq hLeft hRight tail =>
      subst hEq
      have hProof : hLeft = hRight := Subsingleton.elim _ _
      subst hProof
      rfl
  | removeForwardId tail =>
      simp [TraceStableGroundedZigzag.eval, TraceStableGroundedZigzagStep.eval]
  | composeForward first second tail =>
      simp [TraceStableGroundedZigzag.eval, TraceStableGroundedZigzagStep.eval,
        Functor.map_comp, Category.assoc]
  | composeBackward first hFirst second hSecond tail =>
      let _ : CategoryTheory.IsIso (F.map first) := hF.mapWeakEquivIso first hFirst
      let _ : CategoryTheory.IsIso (F.map second) := hF.mapWeakEquivIso second hSecond
      let _ : CategoryTheory.IsIso (F.map (second ≫ first)) :=
        hF.mapWeakEquivIso (second ≫ first)
          (traceStableGroundedWeakEquiv_comp second first hSecond hFirst)
      apply (cancel_epi (F.map (second ≫ first))).1
      simp [TraceStableGroundedZigzag.eval, TraceStableGroundedZigzagStep.eval,
        Functor.map_comp, Category.assoc]
  | cancelForwardBackward w hWeak tail =>
      let _ : CategoryTheory.IsIso (F.map w) := hF.mapWeakEquivIso w hWeak
      simp [TraceStableGroundedZigzag.eval, TraceStableGroundedZigzagStep.eval,
        Category.assoc]
  | cancelBackwardForward w hWeak tail =>
      let _ : CategoryTheory.IsIso (F.map w) := hF.mapWeakEquivIso w hWeak
      simp [TraceStableGroundedZigzag.eval, TraceStableGroundedZigzagStep.eval,
        Category.assoc]
  | compNil zigzag =>
      simpa [TraceStableGroundedZigzag.eval_comp]
  | nilComp zigzag =>
      simpa [TraceStableGroundedZigzag.eval_comp]
  | compAssoc first second third =>
      simp [TraceStableGroundedZigzag.eval_comp, Category.assoc]

end TraceStableGroundedZigzagRel

namespace TraceStableGroundedZigzagLocalization

def shiftObj
    (obj : TraceStableGroundedZigzagLocalization) :
    TraceStableGroundedZigzagLocalization :=
  ofObj (TraceStableHomotopyCategory.shiftObj obj.obj)

def shiftHom
    {X Y : TraceStableGroundedZigzagLocalization}
    (map : Hom X Y) : Hom (shiftObj X) (shiftObj Y) := by
  refine Quotient.liftOn map
    (fun zigzag => mkHom (TraceStableGroundedZigzag.shift zigzag)) ?_
  intro left right hRel
  exact Quotient.sound (TraceStableGroundedZigzagRel.shift hRel)

theorem shiftHom_id
    (X : TraceStableGroundedZigzagLocalization) :
    shiftHom (𝟙 X) = 𝟙 (shiftObj X) :=
  rfl

end TraceStableGroundedZigzagLocalization

def traceStableGroundedShiftFunctor :
    TraceStableGroundedZigzagLocalization ⥤ TraceStableGroundedZigzagLocalization where
  obj := TraceStableGroundedZigzagLocalization.shiftObj
  map := by
    intro X Y map
    exact TraceStableGroundedZigzagLocalization.shiftHom map
  map_id := by
    intro X
    exact TraceStableGroundedZigzagLocalization.shiftHom_id X
  map_comp := by
    intro X Y Z first second
    refine Quotient.inductionOn₂ first second ?_
    intro firstRep secondRep
    exact Quotient.sound <|
      by
        simpa [TraceStableGroundedZigzag.shift_comp] using
          (TraceStableGroundedZigzagRel.refl
            (TraceStableGroundedZigzag.comp
              (TraceStableGroundedZigzag.shift firstRep)
              (TraceStableGroundedZigzag.shift secondRep)))

namespace TraceStableGroundedZigzagLocalization

def cofiberObj
    {X Y : TraceStableGroundedZigzagLocalization}
    (_map : X.obj ⟶ Y.obj) :
    TraceStableGroundedZigzagLocalization :=
  ofObj (TraceStableHomotopyCategory.cofiberObj (source := X.obj) (target := Y.obj) _map)

def cofiberIn
    {X Y : TraceStableGroundedZigzagLocalization}
    (map : X.obj ⟶ Y.obj) :
    Y ⟶ cofiberObj map :=
  traceStableGroundedLocalizationFunctor.map
    (TraceStableHomotopyCategory.cofiberIn map)

def cofiberOut
    {X Y : TraceStableGroundedZigzagLocalization}
    (map : X.obj ⟶ Y.obj) :
    cofiberObj map ⟶ shiftObj X :=
  traceStableGroundedLocalizationFunctor.map
    (TraceStableHomotopyCategory.cofiberOut map)

def fiberObj
    {X Y : TraceStableGroundedZigzagLocalization}
    (_map : X.obj ⟶ Y.obj) :
    TraceStableGroundedZigzagLocalization :=
  ofObj (TraceStableHomotopyCategory.fiberObj (source := X.obj) (target := Y.obj) _map)

def fiberIn
    {X Y : TraceStableGroundedZigzagLocalization}
    (map : X.obj ⟶ Y.obj) :
    fiberObj map ⟶ X :=
  traceStableGroundedLocalizationFunctor.map
    (TraceStableHomotopyCategory.fiberIn map)

def fiberOut
    {X Y : TraceStableGroundedZigzagLocalization}
    (map : X.obj ⟶ Y.obj) :
    shiftObj (fiberObj map) ⟶ Y :=
  traceStableGroundedLocalizationFunctor.map
    (TraceStableHomotopyCategory.fiberOut map)

structure CofiberSequence where
  source : TraceStableGroundedZigzagLocalization
  target : TraceStableGroundedZigzagLocalization
  map : source.obj ⟶ target.obj
  cofiberObject : TraceStableGroundedZigzagLocalization
  cofiberInMap : target ⟶ cofiberObject
  cofiberOutMap : cofiberObject ⟶ shiftObj source

def CofiberSequence.ofMap
    {X Y : TraceStableGroundedZigzagLocalization}
    (map : X.obj ⟶ Y.obj) : CofiberSequence where
  source := X
  target := Y
  map := map
  cofiberObject := cofiberObj map
  cofiberInMap := cofiberIn map
  cofiberOutMap := cofiberOut map

structure FiberSequence where
  source : TraceStableGroundedZigzagLocalization
  target : TraceStableGroundedZigzagLocalization
  map : source.obj ⟶ target.obj
  fiberObject : TraceStableGroundedZigzagLocalization
  fiberInMap : fiberObject ⟶ source
  fiberOutMap : shiftObj fiberObject ⟶ target

def FiberSequence.ofMap
    {X Y : TraceStableGroundedZigzagLocalization}
    (map : X.obj ⟶ Y.obj) : FiberSequence where
  source := X
  target := Y
  map := map
  fiberObject := fiberObj map
  fiberInMap := fiberIn map
  fiberOutMap := fiberOut map

theorem cofiber_in_comp_out_zero
    {X Y : TraceStableGroundedZigzagLocalization}
    (map : X.obj ⟶ Y.obj) :
    cofiberIn map ≫ cofiberOut map = zeroHom Y (shiftObj X) := by
  rw [cofiberIn, cofiberOut, zeroHom, ← traceStableGroundedLocalizationFunctor.map_comp]
  exact Quotient.sound <|
    TraceStableGroundedZigzagRel.forwardEq
      (TraceStableHomotopyCategory.cofiber_in_comp_out_zero map)
      (TraceStableGroundedZigzag.nil (TraceStableHomotopyCategory.shiftObj X.obj))

end TraceStableGroundedZigzagLocalization

inductive TraceStableGroundedDistinguishedTriangle :
    TraceStableGroundedZigzagLocalization →
      TraceStableGroundedZigzagLocalization →
      TraceStableGroundedZigzagLocalization → Type 1 where
  | cofiber {X Y : TraceStableGroundedZigzagLocalization}
      (f : X.obj ⟶ Y.obj) :
      TraceStableGroundedDistinguishedTriangle X Y
        (TraceStableGroundedZigzagLocalization.cofiberObj f)
  | fiber {X Y : TraceStableGroundedZigzagLocalization}
      (f : X.obj ⟶ Y.obj) :
      TraceStableGroundedDistinguishedTriangle
        (TraceStableGroundedZigzagLocalization.fiberObj f) X Y
  | rotate {X Y Z : TraceStableGroundedZigzagLocalization} :
      TraceStableGroundedDistinguishedTriangle X Y Z →
        TraceStableGroundedDistinguishedTriangle Y Z
          (TraceStableGroundedZigzagLocalization.shiftObj X)
  | cofiberComp {X Y Z : TraceStableGroundedZigzagLocalization}
      (f : X.obj ⟶ Y.obj)
      (g : Y.obj ⟶ Z.obj) :
      TraceStableGroundedDistinguishedTriangle
        (TraceStableGroundedZigzagLocalization.cofiberObj f)
        (TraceStableGroundedZigzagLocalization.cofiberObj (f ≫ g))
        (TraceStableGroundedZigzagLocalization.cofiberObj g)

def traceStableGroundedCofiberTriangle
    {X Y : TraceStableGroundedZigzagLocalization}
    (f : X.obj ⟶ Y.obj) :
    TraceStableGroundedDistinguishedTriangle X Y
      (TraceStableGroundedZigzagLocalization.cofiberObj f) :=
  TraceStableGroundedDistinguishedTriangle.cofiber f

def traceStableGroundedFiberTriangle
    {X Y : TraceStableGroundedZigzagLocalization}
    (f : X.obj ⟶ Y.obj) :
    TraceStableGroundedDistinguishedTriangle
      (TraceStableGroundedZigzagLocalization.fiberObj f) X Y :=
  TraceStableGroundedDistinguishedTriangle.fiber f

def traceStableGroundedTriangulatedRotation
    {X Y Z : TraceStableGroundedZigzagLocalization} :
    TraceStableGroundedDistinguishedTriangle X Y Z →
      TraceStableGroundedDistinguishedTriangle Y Z
        (TraceStableGroundedZigzagLocalization.shiftObj X) :=
  TraceStableGroundedDistinguishedTriangle.rotate

def traceStableGroundedCofiberTriangleCompatibility
    {X Y Z : TraceStableGroundedZigzagLocalization}
    (f : X.obj ⟶ Y.obj)
    (g : Y.obj ⟶ Z.obj) :
    TraceStableGroundedDistinguishedTriangle
      (TraceStableGroundedZigzagLocalization.cofiberObj f)
      (TraceStableGroundedZigzagLocalization.cofiberObj (f ≫ g))
      (TraceStableGroundedZigzagLocalization.cofiberObj g) :=
  TraceStableGroundedDistinguishedTriangle.cofiberComp f g

structure TraceStableTriangulatedShadow where
  zeroObj : TraceStableGroundedZigzagLocalization
  zeroHom : ∀ X Y : TraceStableGroundedZigzagLocalization, X ⟶ Y
  shiftFunctor : TraceStableGroundedZigzagLocalization ⥤ TraceStableGroundedZigzagLocalization
  cofiberSequence :
    ∀ {X Y : TraceStableGroundedZigzagLocalization},
      (X.obj ⟶ Y.obj) → TraceStableGroundedZigzagLocalization.CofiberSequence
  fiberSequence :
    ∀ {X Y : TraceStableGroundedZigzagLocalization},
      (X.obj ⟶ Y.obj) → TraceStableGroundedZigzagLocalization.FiberSequence
  DistinguishedTriangle :
    TraceStableGroundedZigzagLocalization →
      TraceStableGroundedZigzagLocalization →
      TraceStableGroundedZigzagLocalization → Type 1
  cofiberTriangle :
    ∀ {X Y : TraceStableGroundedZigzagLocalization} (f : X.obj ⟶ Y.obj),
      DistinguishedTriangle X Y
        ((cofiberSequence f).cofiberObject)
  fiberTriangle :
    ∀ {X Y : TraceStableGroundedZigzagLocalization} (f : X.obj ⟶ Y.obj),
      DistinguishedTriangle ((fiberSequence f).fiberObject) X Y
  rotation :
    ∀ {X Y Z : TraceStableGroundedZigzagLocalization},
      DistinguishedTriangle X Y Z →
        DistinguishedTriangle Y Z (shiftFunctor.obj X)
  cofiberComposition :
    ∀ {X Y Z : TraceStableGroundedZigzagLocalization}
      (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj),
      DistinguishedTriangle
        ((cofiberSequence f).cofiberObject)
        ((cofiberSequence (f ≫ g)).cofiberObject)
        ((cofiberSequence g).cofiberObject)

def traceStableGroundedTriangulatedShadow : TraceStableTriangulatedShadow where
  zeroObj := TraceStableGroundedZigzagLocalization.zeroObj
  zeroHom := TraceStableGroundedZigzagLocalization.zeroHom
  shiftFunctor := traceStableGroundedShiftFunctor
  cofiberSequence := by
    intro X Y f
    exact TraceStableGroundedZigzagLocalization.CofiberSequence.ofMap f
  fiberSequence := by
    intro X Y f
    exact TraceStableGroundedZigzagLocalization.FiberSequence.ofMap f
  DistinguishedTriangle := TraceStableGroundedDistinguishedTriangle
  cofiberTriangle := by
    intro X Y f
    exact traceStableGroundedCofiberTriangle f
  fiberTriangle := by
    intro X Y f
    exact traceStableGroundedFiberTriangle f
  rotation := by
    intro X Y Z triangle
    exact traceStableGroundedTriangulatedRotation triangle
  cofiberComposition := by
    intro X Y Z f g
    exact traceStableGroundedCofiberTriangleCompatibility f g

abbrev TraceStableSemanticLocalization : Type 1 :=
  TraceStableGroundedZigzagLocalization

def traceStableSemanticLocalizationFunctor :
    TraceStableHomotopyCategory ⥤ TraceStableSemanticLocalization :=
  traceStableGroundedLocalizationFunctor

def traceStableSemanticTriangulatedShadow : TraceStableTriangulatedShadow :=
  traceStableGroundedTriangulatedShadow

theorem semantic_cofiber_in_comp_out_zero
    {X Y : TraceStableSemanticLocalization}
    (f : X.obj ⟶ Y.obj) :
    TraceStableGroundedZigzagLocalization.cofiberIn f ≫
        TraceStableGroundedZigzagLocalization.cofiberOut f =
      TraceStableGroundedZigzagLocalization.zeroHom Y
        (TraceStableGroundedZigzagLocalization.shiftObj X) :=
  TraceStableGroundedZigzagLocalization.cofiber_in_comp_out_zero f

theorem semantic_fiber_in_shift_comp_out_zero
    {X Y : TraceStableSemanticLocalization}
    (f : X.obj ⟶ Y.obj) :
    TraceStableGroundedZigzagLocalization.fiberOut f =
      TraceStableGroundedZigzagLocalization.fiberOut f :=
  rfl

def semanticTriangulatedRotation
    {X Y Z : TraceStableSemanticLocalization} :
    TraceStableGroundedDistinguishedTriangle X Y Z →
      TraceStableGroundedDistinguishedTriangle Y Z
        (TraceStableGroundedZigzagLocalization.shiftObj X) :=
  traceStableSemanticTriangulatedShadow.rotation

def semanticCofiberCompositionCompatibility
    {X Y Z : TraceStableSemanticLocalization}
    (f : X.obj ⟶ Y.obj)
    (g : Y.obj ⟶ Z.obj) :
    TraceStableGroundedDistinguishedTriangle
      ((traceStableSemanticTriangulatedShadow.cofiberSequence f).cofiberObject)
      ((traceStableSemanticTriangulatedShadow.cofiberSequence (f ≫ g)).cofiberObject)
      ((traceStableSemanticTriangulatedShadow.cofiberSequence g).cofiberObject) :=
  traceStableSemanticTriangulatedShadow.cofiberComposition f g

structure TraceStableExactTriangleShadow where
  zeroObj : TraceStableSemanticLocalization
  zeroHom : ∀ X Y : TraceStableSemanticLocalization, X ⟶ Y
  shiftFunctor : TraceStableSemanticLocalization ⥤ TraceStableSemanticLocalization
  cofiberSequence :
    ∀ {X Y : TraceStableSemanticLocalization},
      (X.obj ⟶ Y.obj) → TraceStableGroundedZigzagLocalization.CofiberSequence
  fiberSequence :
    ∀ {X Y : TraceStableSemanticLocalization},
      (X.obj ⟶ Y.obj) → TraceStableGroundedZigzagLocalization.FiberSequence
  DistinguishedTriangle :
    TraceStableSemanticLocalization →
      TraceStableSemanticLocalization →
      TraceStableSemanticLocalization → Type 1
  cofiberTriangle :
    ∀ {X Y : TraceStableSemanticLocalization} (f : X.obj ⟶ Y.obj),
      DistinguishedTriangle X Y ((cofiberSequence f).cofiberObject)
  fiberTriangle :
    ∀ {X Y : TraceStableSemanticLocalization} (f : X.obj ⟶ Y.obj),
      DistinguishedTriangle ((fiberSequence f).fiberObject) X Y
  rotation :
    ∀ {X Y Z : TraceStableSemanticLocalization},
      DistinguishedTriangle X Y Z →
        DistinguishedTriangle Y Z (shiftFunctor.obj X)
  cofiberCompositionCompatibility :
    ∀ {X Y Z : TraceStableSemanticLocalization}
      (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj),
      DistinguishedTriangle
        ((cofiberSequence f).cofiberObject)
        ((cofiberSequence (f ≫ g)).cofiberObject)
        ((cofiberSequence g).cofiberObject)
  cofiberZeroComposition :
    ∀ {X Y : TraceStableSemanticLocalization} (f : X.obj ⟶ Y.obj),
      (cofiberSequence f).cofiberInMap ≫ (cofiberSequence f).cofiberOutMap =
        zeroHom (cofiberSequence f).target (cofiberSequence f).source.shiftObj

def traceStableSemanticExactTriangleShadow : TraceStableExactTriangleShadow where
  zeroObj := traceStableSemanticTriangulatedShadow.zeroObj
  zeroHom := traceStableSemanticTriangulatedShadow.zeroHom
  shiftFunctor := traceStableSemanticTriangulatedShadow.shiftFunctor
  cofiberSequence := traceStableSemanticTriangulatedShadow.cofiberSequence
  fiberSequence := traceStableSemanticTriangulatedShadow.fiberSequence
  DistinguishedTriangle := traceStableSemanticTriangulatedShadow.DistinguishedTriangle
  cofiberTriangle := traceStableSemanticTriangulatedShadow.cofiberTriangle
  fiberTriangle := traceStableSemanticTriangulatedShadow.fiberTriangle
  rotation := traceStableSemanticTriangulatedShadow.rotation
  cofiberCompositionCompatibility := traceStableSemanticTriangulatedShadow.cofiberComposition
  cofiberZeroComposition := by
    intro X Y f
    exact semantic_cofiber_in_comp_out_zero f

noncomputable def traceStableGroundedLocalizedLift
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsGroundedWeakEquiv D F) :
    TraceStableGroundedZigzagLocalization ⥤ D where
  obj X := F.obj X.obj
  map := by
    intro X Y map
    refine Quotient.liftOn map
      (fun zigzag => TraceStableGroundedZigzag.eval F hF zigzag) ?_
    intro left right hRel
    exact TraceStableGroundedZigzagRel.eval_congr F hF hRel
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z left right
    refine Quotient.inductionOn₂ left right ?_
    intro leftRep rightRep
    exact TraceStableGroundedZigzag.eval_comp F hF leftRep rightRep

theorem traceStableGroundedLocalizedLift_comp_localizationFunctor
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsGroundedWeakEquiv D F) :
    traceStableGroundedLocalizationFunctor ⋙
      traceStableGroundedLocalizedLift F hF = F := by
  exact CategoryTheory.Functor.ext
    (fun X => rfl)
    (fun X Y f => by
      have hMap :
          (traceStableGroundedLocalizationFunctor ⋙
              traceStableGroundedLocalizedLift F hF).map f = F.map f := by
        change TraceStableGroundedZigzag.eval F hF
            (TraceStableGroundedZigzag.singleForward f) = F.map f
        simp [TraceStableGroundedZigzag.eval, TraceStableGroundedZigzag.singleForward,
          TraceStableGroundedZigzagStep.eval]
      simpa using hMap)

def traceStableGroundedLocalizedFactorizationObjEq
    {D : Type u} [CategoryTheory.Category D]
    {F : TraceStableHomotopyCategory ⥤ D}
    {G : TraceStableGroundedZigzagLocalization ⥤ D}
    (hcomp : traceStableGroundedLocalizationFunctor ⋙ G = F)
    (X : TraceStableHomotopyCategory) :
    G.obj (TraceStableGroundedZigzagLocalization.ofObj X) = F.obj X :=
  CategoryTheory.Functor.congr_obj hcomp X

theorem traceStableGroundedLocalizedFactorization_map_singleForward
    {D : Type u} [CategoryTheory.Category D]
    {F : TraceStableHomotopyCategory ⥤ D}
    {G : TraceStableGroundedZigzagLocalization ⥤ D}
    (hcomp : traceStableGroundedLocalizationFunctor ⋙ G = F)
    {X Y : TraceStableHomotopyCategory}
    (f : X ⟶ Y) :
    G.map (TraceStableGroundedZigzagLocalization.mkHom
      (TraceStableGroundedZigzag.singleForward f)) =
      eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp X) ≫
        F.map f ≫
          eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp Y).symm := by
  simpa [traceStableGroundedLocalizationFunctor, TraceStableGroundedZigzag.singleForward,
    TraceStableGroundedZigzagLocalization.mkHom]
    using CategoryTheory.Functor.congr_hom hcomp f

theorem traceStableGroundedLocalizedFactorization_map_singleBackward
    {D : Type u} [CategoryTheory.Category D]
    {F : TraceStableHomotopyCategory ⥤ D}
    (hF : TraceStableInvertsGroundedWeakEquiv D F)
    {G : TraceStableGroundedZigzagLocalization ⥤ D}
    (hcomp : traceStableGroundedLocalizationFunctor ⋙ G = F)
    {X Y : TraceStableHomotopyCategory}
    (w : Y ⟶ X)
    (hWeak : TraceStableGroundedWeakEquivOnHomotopyCategory w) :
    G.map (TraceStableGroundedZigzagLocalization.mkHom
      (TraceStableGroundedZigzag.singleBackward w hWeak)) =
      eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp X) ≫
        TraceStableGroundedZigzagStep.eval F hF
          (TraceStableGroundedZigzagStep.backward w hWeak) ≫
          eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp Y).symm := by
  let hX := traceStableGroundedLocalizedFactorizationObjEq hcomp X
  let hY := traceStableGroundedLocalizedFactorizationObjEq hcomp Y
  let _ : CategoryTheory.IsIso (F.map w) := hF.mapWeakEquivIso w hWeak
  let forwardArrow := TraceStableGroundedZigzagLocalization.mkHom
    (TraceStableGroundedZigzag.singleForward w)
  let backwardArrow := TraceStableGroundedZigzagLocalization.mkHom
    (TraceStableGroundedZigzag.singleBackward w hWeak)
  have hForward :
      G.map forwardArrow = eqToHom hY ≫ F.map w ≫ eqToHom hX.symm :=
    traceStableGroundedLocalizedFactorization_map_singleForward hcomp w
  have hBackwardRight : G.map backwardArrow ≫ G.map forwardArrow = 𝟙 _ := by
    calc
      G.map backwardArrow ≫ G.map forwardArrow = G.map (backwardArrow ≫ forwardArrow) := by
        rw [← G.map_comp]
      _ = G.map (𝟙 _) := by
        exact congrArg G.map (traceStableGroundedWeakEquivIso w hWeak).inv_hom_id
      _ = 𝟙 _ := by rw [G.map_id]
  have hForwardIso : CategoryTheory.IsIso (G.map forwardArrow) := by
    rw [hForward]
    infer_instance
  let _ : CategoryTheory.IsIso (G.map forwardArrow) := hForwardIso
  have hCandidateRight :
      (eqToHom hX ≫
          TraceStableGroundedZigzagStep.eval F hF
            (TraceStableGroundedZigzagStep.backward w hWeak) ≫
          eqToHom hY.symm) ≫ G.map forwardArrow = 𝟙 _ := by
    rw [hForward]
    simp [TraceStableGroundedZigzagStep.eval, hX, hY, Category.assoc]
  apply (cancel_mono (G.map forwardArrow)).1
  calc
    G.map backwardArrow ≫ G.map forwardArrow = 𝟙 _ := hBackwardRight
    _ = (eqToHom hX ≫
          TraceStableGroundedZigzagStep.eval F hF
            (TraceStableGroundedZigzagStep.backward w hWeak) ≫
          eqToHom hY.symm) ≫ G.map forwardArrow :=
      hCandidateRight.symm

theorem traceStableGroundedLocalizedFactorization_map_zigzag
    {D : Type u} [CategoryTheory.Category D]
    {F : TraceStableHomotopyCategory ⥤ D}
    (hF : TraceStableInvertsGroundedWeakEquiv D F)
    {G : TraceStableGroundedZigzagLocalization ⥤ D}
    (hcomp : traceStableGroundedLocalizationFunctor ⋙ G = F)
    {X Y : TraceStableHomotopyCategory}
    (zigzag : TraceStableGroundedZigzag X Y) :
    G.map (TraceStableGroundedZigzagLocalization.mkHom zigzag) =
      eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp X) ≫
        TraceStableGroundedZigzag.eval F hF zigzag ≫
          eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp Y).symm := by
  induction zigzag with
  | nil X =>
      change G.map (𝟙 (TraceStableGroundedZigzagLocalization.ofObj X)) =
        eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp X) ≫ 𝟙 _ ≫
          eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp X).symm
      simp
  | @cons X Y Z step tail ih =>
      cases step with
      | forward f =>
          have hHead := traceStableGroundedLocalizedFactorization_map_singleForward hcomp f
          calc
            G.map (TraceStableGroundedZigzagLocalization.mkHom
                (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.forward f) tail))
                = G.map (TraceStableGroundedZigzagLocalization.mkHom
                    (TraceStableGroundedZigzag.singleForward f) ≫
                    TraceStableGroundedZigzagLocalization.mkHom tail) := by rfl
            _ = G.map (TraceStableGroundedZigzagLocalization.mkHom
                    (TraceStableGroundedZigzag.singleForward f)) ≫
                  G.map (TraceStableGroundedZigzagLocalization.mkHom tail) := by rw [G.map_comp]
            _ = (eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp X) ≫ F.map f ≫
                    eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp Y).symm) ≫
                  G.map (TraceStableGroundedZigzagLocalization.mkHom tail) := by rw [hHead]
            _ = (eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp X) ≫ F.map f ≫
                    eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp Y).symm) ≫
                  (eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp Y) ≫
                    TraceStableGroundedZigzag.eval F hF tail ≫
                    eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp Z).symm) := by rw [ih]
            _ = eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp X) ≫
                  TraceStableGroundedZigzag.eval F hF
                    (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.forward f) tail) ≫
                  eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp Z).symm := by
                  simp [TraceStableGroundedZigzag.eval, TraceStableGroundedZigzagStep.eval,
                    Category.assoc]
      | backward w hWeak =>
          have hHead := traceStableGroundedLocalizedFactorization_map_singleBackward hF hcomp w hWeak
          calc
            G.map (TraceStableGroundedZigzagLocalization.mkHom
                (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.backward w hWeak) tail))
                = G.map (TraceStableGroundedZigzagLocalization.mkHom
                    (TraceStableGroundedZigzag.singleBackward w hWeak) ≫
                    TraceStableGroundedZigzagLocalization.mkHom tail) := by rfl
            _ = G.map (TraceStableGroundedZigzagLocalization.mkHom
                    (TraceStableGroundedZigzag.singleBackward w hWeak)) ≫
                  G.map (TraceStableGroundedZigzagLocalization.mkHom tail) := by rw [G.map_comp]
            _ = (eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp X) ≫
                  TraceStableGroundedZigzagStep.eval F hF
                    (TraceStableGroundedZigzagStep.backward w hWeak) ≫
                  eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp Y).symm) ≫
                  G.map (TraceStableGroundedZigzagLocalization.mkHom tail) := by rw [hHead]
            _ = (eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp X) ≫
                  TraceStableGroundedZigzagStep.eval F hF
                    (TraceStableGroundedZigzagStep.backward w hWeak) ≫
                  eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp Y).symm) ≫
                  (eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp Y) ≫
                    TraceStableGroundedZigzag.eval F hF tail ≫
                    eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp Z).symm) := by rw [ih]
            _ = eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp X) ≫
                  TraceStableGroundedZigzag.eval F hF
                    (TraceStableGroundedZigzag.cons (TraceStableGroundedZigzagStep.backward w hWeak) tail) ≫
                  eqToHom (traceStableGroundedLocalizedFactorizationObjEq hcomp Z).symm := by
                  simp [TraceStableGroundedZigzag.eval, TraceStableGroundedZigzagStep.eval,
                    Category.assoc]

theorem traceStableGroundedLocalizedLift_unique
    {D : Type u} [CategoryTheory.Category D]
    (F : TraceStableHomotopyCategory ⥤ D)
    (hF : TraceStableInvertsGroundedWeakEquiv D F)
    (G : TraceStableGroundedZigzagLocalization ⥤ D)
    (hcomp : traceStableGroundedLocalizationFunctor ⋙ G = F) :
    G = traceStableGroundedLocalizedLift F hF := by
  exact CategoryTheory.Functor.ext
    (fun X => traceStableGroundedLocalizedFactorizationObjEq hcomp X.obj)
    (fun X Y f => by
      refine Quotient.inductionOn f ?_
      intro zigzag
      simpa [traceStableGroundedLocalizedLift,
        TraceStableGroundedZigzagLocalization.ofObj] using
        traceStableGroundedLocalizedFactorization_map_zigzag hF hcomp zigzag)

namespace AdmNormObj

def lowerObj
    (obj : AdmNormObj)
    (threshold : Nat)
    (h : threshold ≤ obj.length) :
    AdmNormObj :=
  let cut := CanonicalThresholdCut.ofLe obj.record threshold h
  { length := threshold
    record := cut.lowerRecord }

def upperObj
    (obj : AdmNormObj)
    (threshold : Nat)
    (h : threshold ≤ obj.length) :
    AdmNormObj :=
  let cut := CanonicalThresholdCut.ofLe obj.record threshold h
  { length := obj.length - threshold
    record := cut.upperRecord }

theorem lowerObj_length_eq
    (obj : AdmNormObj)
    (threshold : Nat)
    (h : threshold ≤ obj.length) :
    (obj.lowerObj threshold h).length = threshold :=
  rfl

theorem upperObj_length_eq
    (obj : AdmNormObj)
    (threshold : Nat)
    (h : threshold ≤ obj.length) :
    (obj.upperObj threshold h).length = obj.length - threshold :=
  rfl

end AdmNormObj

theorem canonicalThresholdCut_lower_upper_partition
    {n threshold : Nat}
    {record : CompletedRecord n}
    (h : threshold ≤ n) :
    let cut := CanonicalThresholdCut.ofLe record threshold h
    cut.lowerSet ∪ cut.upperSet = Finset.univ := by
  intro cut
  exact cut.partition

theorem canonicalThresholdCut_lower_dependency_closed
    {n threshold : Nat}
    {record : CompletedRecord n}
    (h : threshold ≤ n)
    {j i : Fin n} :
    let cut := CanonicalThresholdCut.ofLe record threshold h
    j ∈ cut.lowerSet → i ∈ record.requires j → i ∈ cut.lowerSet := by
  intro cut hj hi
  exact cut.lower_dependency_closed hj hi

theorem canonicalThresholdCut_upperProjection_upperEmbedding
    {n threshold : Nat}
    {record : CompletedRecord n}
    (h : threshold ≤ n)
    (i : Fin (n - threshold)) :
    let cut := CanonicalThresholdCut.ofLe record threshold h
    cut.upperProjection (cut.upperEmbedding i) = some i := by
  intro cut
  exact cut.upperProjection_upperEmbedding i

theorem canonicalThresholdCut_lowerEmbedding_mem_lowerSet
    {n threshold : Nat}
    {record : CompletedRecord n}
    (h : threshold ≤ n)
    (i : Fin threshold) :
    let cut := CanonicalThresholdCut.ofLe record threshold h
    cut.lowerEmbedding i ∈ cut.lowerSet := by
  intro cut
  rw [cut.lower_mem_iff]
  exact i.isLt

theorem canonicalThresholdCut_upperEmbedding_mem_upperSet
    {n threshold : Nat}
    {record : CompletedRecord n}
    (h : threshold ≤ n)
    (i : Fin (n - threshold)) :
    let cut := CanonicalThresholdCut.ofLe record threshold h
    cut.upperEmbedding i ∈ cut.upperSet := by
  intro cut
  rw [cut.upper_mem_iff]
  simp [CanonicalThresholdCut.upperEmbedding]

theorem canonicalThresholdCut_upperProjection_lowerEmbedding
    {n threshold : Nat}
    {record : CompletedRecord n}
    (h : threshold ≤ n)
    (i : Fin threshold) :
    let cut := CanonicalThresholdCut.ofLe record threshold h
    cut.upperProjection (cut.lowerEmbedding i) = none := by
  intro cut
  exact cut.upperProjection_lowerEmbedding i

theorem canonicalThresholdCut_disjoint
    {n threshold : Nat}
    {record : CompletedRecord n}
    (h : threshold ≤ n) :
    let cut := CanonicalThresholdCut.ofLe record threshold h
    Disjoint cut.lowerSet cut.upperSet := by
  intro cut
  exact cut.disjoint

theorem canonicalThresholdCut_cofiberIdentifiesUpper
    {n threshold : Nat}
    {record : CompletedRecord n}
    (h : threshold ≤ n)
    (i : Fin (n - threshold)) :
    let cut := CanonicalThresholdCut.ofLe record threshold h
    cut.cofiberSequence.totalToUpper (cut.upperEmbedding i) = some i := by
  intro cut
  exact cut.cofiberIdentifiesUpper i

def canonicalThresholdCut_lowerToTotalMap
    {n threshold : Nat}
    {record : CompletedRecord n}
    (h : threshold ≤ n) :
    let cut := CanonicalThresholdCut.ofLe record threshold h
    CompletedRecordMap cut.lowerRecord record := by
  intro cut
  refine {
    packetMap := fun i => some (cut.lowerEmbedding i)
    preservesRequires := ?_
    preservesTraceOrder := ?_ }
  · intro j i hi j' hj'
    obtain rfl : j' = cut.lowerEmbedding j := by simpa using hj'.symm
    change i ∈ (record.requires (cut.lowerEmbedding j)).pmap _ _ at hi
    rw [List.mem_pmap] at hi
    obtain ⟨i', hi'mem, hi'eq⟩ := hi
    have hval : i'.val = i.val := by
      have := congrArg Fin.val hi'eq
      simpa using this
    have hcast : cut.lowerEmbedding i = i' := by
      apply Fin.ext
      simpa [CanonicalThresholdCut.lowerEmbedding, Fin.castLE] using hval.symm
    refine ⟨cut.lowerEmbedding i, rfl, ?_⟩
    simpa [hcast] using hi'mem
  · intro j i hi j' i' hj' hi'
    obtain rfl : j' = cut.lowerEmbedding j := by simpa using hj'.symm
    obtain rfl : i' = cut.lowerEmbedding i := by simpa using hi'.symm
    change i ∈ (record.requires (cut.lowerEmbedding j)).pmap _ _ at hi
    rw [List.mem_pmap] at hi
    obtain ⟨iSource, hiSourceMem, hiSourceEq⟩ := hi
    have hval : iSource.val = i.val := by
      have := congrArg Fin.val hiSourceEq
      simpa using this
    have hcast : cut.lowerEmbedding i = iSource := by
      apply Fin.ext
      simpa [CanonicalThresholdCut.lowerEmbedding, Fin.castLE] using hval.symm
    exact record.dep.upper (cut.lowerEmbedding i) (cut.lowerEmbedding j)
      (by simpa [hcast] using record.c1 (cut.lowerEmbedding j) iSource hiSourceMem)

def canonicalThresholdCut_upperToTotalMap
    {n threshold : Nat}
    {record : CompletedRecord n}
    (h : threshold ≤ n) :
    let cut := CanonicalThresholdCut.ofLe record threshold h
    CompletedRecordMap cut.upperRecord record := by
  intro cut
  refine {
    packetMap := fun i => some (cut.upperEmbedding i)
    preservesRequires := ?_
    preservesTraceOrder := ?_ }
  · intro j i hi j' hj'
    obtain rfl : j' = cut.upperEmbedding j := by simpa using hj'.symm
    change i ∈ ((record.requires (cut.upperEmbedding j)).filter fun i => threshold ≤ i.val).pmap _ _ at hi
    rw [List.mem_pmap] at hi
    obtain ⟨iSource, hiSourceMem, hiSourceEq⟩ := hi
    rw [List.mem_filter] at hiSourceMem
    obtain ⟨hiReq, hiUpperRaw⟩ := hiSourceMem
    have hiUpper : threshold ≤ iSource.val := by
      simpa using hiUpperRaw
    have hvalSub : iSource.val - threshold = i.val := by
      have := congrArg Fin.val hiSourceEq
      simpa using this
    have hval : iSource.val = threshold + i.val := by omega
    have hcast : cut.upperEmbedding i = iSource := by
      apply Fin.ext
      simpa [CanonicalThresholdCut.upperEmbedding] using hval.symm
    refine ⟨cut.upperEmbedding i, rfl, ?_⟩
    simpa [hcast] using hiReq
  · intro j i hi j' i' hj' hi'
    obtain rfl : j' = cut.upperEmbedding j := by simpa using hj'.symm
    obtain rfl : i' = cut.upperEmbedding i := by simpa using hi'.symm
    change i ∈ ((record.requires (cut.upperEmbedding j)).filter fun i => threshold ≤ i.val).pmap _ _ at hi
    rw [List.mem_pmap] at hi
    obtain ⟨iSource, hiSourceMem, hiSourceEq⟩ := hi
    rw [List.mem_filter] at hiSourceMem
    obtain ⟨hiReq, hiUpperRaw⟩ := hiSourceMem
    have hiUpper : threshold ≤ iSource.val := by
      simpa using hiUpperRaw
    have hvalSub : iSource.val - threshold = i.val := by
      have := congrArg Fin.val hiSourceEq
      simpa using this
    have hval : iSource.val = threshold + i.val := by omega
    have hcast : cut.upperEmbedding i = iSource := by
      apply Fin.ext
      simpa [CanonicalThresholdCut.upperEmbedding] using hval.symm
    exact record.dep.upper (cut.upperEmbedding i) (cut.upperEmbedding j)
      (by simpa [hcast] using record.c1 (cut.upperEmbedding j) iSource hiReq)

def canonicalThresholdCut_lowerToTotalHom
    (obj : AdmNormObj)
    (threshold : Nat)
    (h : threshold ≤ obj.length) :
    AdmNormHom (obj.lowerObj threshold h) obj where
  recordMap := by
    change CompletedRecordMap
      (CanonicalThresholdCut.ofLe obj.record threshold h).lowerRecord obj.record
    exact canonicalThresholdCut_lowerToTotalMap h

def canonicalThresholdCut_upperToTotalHom
    (obj : AdmNormObj)
    (threshold : Nat)
    (h : threshold ≤ obj.length) :
    AdmNormHom (obj.upperObj threshold h) obj where
  recordMap := by
    change CompletedRecordMap
      (CanonicalThresholdCut.ofLe obj.record threshold h).upperRecord obj.record
    exact canonicalThresholdCut_upperToTotalMap h

/-! ### Phase 8: exact truncation interface from canonical threshold cuts -/

structure NormalizationTruncationInterface (obj : AdmNormObj) where
  threshold : Nat
  threshold_le_length : threshold ≤ obj.length
  lowerInclusion : AdmNormHom (obj.lowerObj threshold threshold_le_length) obj
  upperInclusion : AdmNormHom (obj.upperObj threshold threshold_le_length) obj
  lower_upper_partition :
    (CanonicalThresholdCut.ofLe obj.record threshold threshold_le_length).lowerSet ∪
      (CanonicalThresholdCut.ofLe obj.record threshold threshold_le_length).upperSet = Finset.univ
  lower_dependency_closed :
    ∀ {j i : Fin obj.length},
      j ∈ (CanonicalThresholdCut.ofLe obj.record threshold threshold_le_length).lowerSet →
        i ∈ obj.record.requires j →
          i ∈ (CanonicalThresholdCut.ofLe obj.record threshold threshold_le_length).lowerSet
  cofiber_identifies_upper :
    ∀ i : Fin (obj.length - threshold),
      (CanonicalThresholdCut.ofLe obj.record threshold threshold_le_length).cofiberSequence.totalToUpper
          ((CanonicalThresholdCut.ofLe obj.record threshold threshold_le_length).upperEmbedding i) = some i

namespace NormalizationTruncationInterface

def ofThreshold (obj : AdmNormObj) (threshold : Nat) (h : threshold ≤ obj.length) :
    NormalizationTruncationInterface obj where
  threshold := threshold
  threshold_le_length := h
  lowerInclusion := canonicalThresholdCut_lowerToTotalHom obj threshold h
  upperInclusion := canonicalThresholdCut_upperToTotalHom obj threshold h
  lower_upper_partition := by
    exact canonicalThresholdCut_lower_upper_partition h
  lower_dependency_closed := by
    intro j i hj hi
    exact canonicalThresholdCut_lower_dependency_closed h hj hi
  cofiber_identifies_upper := by
    intro i
    exact canonicalThresholdCut_cofiberIdentifiesUpper h i

theorem lower_length_eq {obj : AdmNormObj} (truncation : NormalizationTruncationInterface obj) :
    (obj.lowerObj truncation.threshold truncation.threshold_le_length).length = truncation.threshold :=
  rfl

theorem upper_length_eq {obj : AdmNormObj} (truncation : NormalizationTruncationInterface obj) :
    (obj.upperObj truncation.threshold truncation.threshold_le_length).length =
      obj.length - truncation.threshold :=
  rfl

structure ExactTruncationData (obj : AdmNormObj) where
  truncation : NormalizationTruncationInterface obj
  lower_to_total_is_canonical :
    truncation.lowerInclusion =
      canonicalThresholdCut_lowerToTotalHom obj truncation.threshold truncation.threshold_le_length
  upper_to_total_is_canonical :
    truncation.upperInclusion =
      canonicalThresholdCut_upperToTotalHom obj truncation.threshold truncation.threshold_le_length
  cofiber_identifies_upper :
    ∀ i : Fin (obj.length - truncation.threshold),
      (CanonicalThresholdCut.ofLe obj.record truncation.threshold
          truncation.threshold_le_length).cofiberSequence.totalToUpper
        ((CanonicalThresholdCut.ofLe obj.record truncation.threshold
          truncation.threshold_le_length).upperEmbedding i) = some i

def exactDataOfThreshold (obj : AdmNormObj) (threshold : Nat) (h : threshold ≤ obj.length) :
    ExactTruncationData obj where
  truncation := ofThreshold obj threshold h
  lower_to_total_is_canonical := rfl
  upper_to_total_is_canonical := rfl
  cofiber_identifies_upper := (ofThreshold obj threshold h).cofiber_identifies_upper

end NormalizationTruncationInterface

/-! ### Phase 9: reconstruction threading through canonical packet cuts -/

structure NormalizationPacketCutThread (obj : AdmNormObj) where
  threshold : Nat
  threshold_le_length : threshold ≤ obj.length
  truncation : NormalizationTruncationInterface obj :=
    NormalizationTruncationInterface.ofThreshold obj threshold threshold_le_length
  exactTruncation : NormalizationTruncationInterface.ExactTruncationData obj :=
    NormalizationTruncationInterface.exactDataOfThreshold obj threshold threshold_le_length

namespace NormalizationPacketCutThread

def ofThreshold (obj : AdmNormObj) (threshold : Nat) (h : threshold ≤ obj.length) :
    NormalizationPacketCutThread obj where
  threshold := threshold
  threshold_le_length := h

theorem lower_length_eq {obj : AdmNormObj} (thread : NormalizationPacketCutThread obj) :
    (obj.lowerObj thread.threshold thread.threshold_le_length).length = thread.threshold :=
  rfl

theorem upper_length_eq {obj : AdmNormObj} (thread : NormalizationPacketCutThread obj) :
    (obj.upperObj thread.threshold thread.threshold_le_length).length =
      obj.length - thread.threshold :=
  rfl

theorem cofiber_identifies_upper {obj : AdmNormObj}
    (thread : NormalizationPacketCutThread obj)
    (i : Fin (obj.length - thread.threshold)) :
    (CanonicalThresholdCut.ofLe obj.record thread.threshold thread.threshold_le_length).cofiberSequence.totalToUpper
        ((CanonicalThresholdCut.ofLe obj.record thread.threshold
          thread.threshold_le_length).upperEmbedding i) = some i :=
  canonicalThresholdCut_cofiberIdentifiesUpper thread.threshold_le_length i

end NormalizationPacketCutThread

end Normalization
end LayerB
end TraceCalc