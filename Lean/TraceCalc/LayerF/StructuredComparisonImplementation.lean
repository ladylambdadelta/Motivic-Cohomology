import TraceCalc.LayerF.RealizationPackage

universe u v w x y z

namespace TraceCalc
namespace LayerF

/-- Reusable comparison-isomorphism core data for Lane J.1. This isolates the carrier, relation,
and comparison-isomorphism proof from the functoriality and package-compatibility side data. -/
structure StructuredComparisonIsoCore where
  BettiLikeCarrier : Type w
  DeRhamLikeCarrier : Type x
  comparisonMap : BettiLikeCarrier → DeRhamLikeCarrier → Prop
  comparisonIsomorphism : Prop
  comparisonIsomorphism_holds : comparisonIsomorphism

/-- Relation-with-witness theorem object for J.1. The comparison relation itself is abstract, but
the data includes maps and witness theorems showing that it is the graph of an equivalence. -/
structure StructuredComparisonRelationCore where
  BettiLikeCarrier : Type w
  DeRhamLikeCarrier : Type x
  comparisonRel : BettiLikeCarrier → DeRhamLikeCarrier → Prop
  toDeRham : BettiLikeCarrier → DeRhamLikeCarrier
  toBetti : DeRhamLikeCarrier → BettiLikeCarrier
  leftInverse : ∀ b : BettiLikeCarrier, toBetti (toDeRham b) = b
  rightInverse : ∀ d : DeRhamLikeCarrier, toDeRham (toBetti d) = d
  relation_graph_toDeRham : ∀ b : BettiLikeCarrier, ∀ d : DeRhamLikeCarrier,
    comparisonRel b d ↔ toDeRham b = d

namespace StructuredComparisonRelationCore

/-- Identity relation-with-witness core. This is the relation-core analogue of the existing
identity comparison-isomorphism core. -/
def identity (V : Type w) : StructuredComparisonRelationCore.{w, w} where
  BettiLikeCarrier := V
  DeRhamLikeCarrier := V
  comparisonRel := fun b d => b = d
  toDeRham := id
  toBetti := id
  leftInverse := by
    intro b
    rfl
  rightInverse := by
    intro d
    rfl
  relation_graph_toDeRham := by
    intro b d
    rfl

/-- Composition of compatible relation-with-witness cores. The middle carrier alignment is carried
explicitly as equality data rather than treated as definitional for free. -/
def compose
    (coreAB : StructuredComparisonRelationCore.{w, x})
    (coreBC : StructuredComparisonRelationCore.{x, y})
    (middleEq : coreAB.DeRhamLikeCarrier = coreBC.BettiLikeCarrier) :
    StructuredComparisonRelationCore.{w, y} := by
  exact
    { BettiLikeCarrier := coreAB.BettiLikeCarrier
      DeRhamLikeCarrier := coreBC.DeRhamLikeCarrier
      comparisonRel := fun b e =>
        ∃ d : coreAB.DeRhamLikeCarrier,
          coreAB.comparisonRel b d ∧ coreBC.comparisonRel (Eq.mp middleEq d) e
      toDeRham := fun b => coreBC.toDeRham (Eq.mp middleEq (coreAB.toDeRham b))
      toBetti := fun e => coreAB.toBetti (Eq.mp middleEq.symm (coreBC.toBetti e))
      leftInverse := by
        intro b
        have hmid :
            Eq.mp middleEq.symm
              (coreBC.toBetti (coreBC.toDeRham (Eq.mp middleEq (coreAB.toDeRham b)))) =
              coreAB.toDeRham b := by
          simpa using congrArg (Eq.mp middleEq.symm)
            (coreBC.leftInverse (Eq.mp middleEq (coreAB.toDeRham b)))
        calc
          coreAB.toBetti
              (Eq.mp middleEq.symm
                (coreBC.toBetti (coreBC.toDeRham (Eq.mp middleEq (coreAB.toDeRham b))))) =
              coreAB.toBetti (coreAB.toDeRham b) := by rw [hmid]
          _ = b := coreAB.leftInverse b
      rightInverse := by
        intro e
        have hmid :
            Eq.mp middleEq
              (coreAB.toDeRham (coreAB.toBetti (Eq.mp middleEq.symm (coreBC.toBetti e)))) =
              coreBC.toBetti e := by
          simpa using congrArg (Eq.mp middleEq)
            (coreAB.rightInverse (Eq.mp middleEq.symm (coreBC.toBetti e)))
        calc
          coreBC.toDeRham
              (Eq.mp middleEq
                (coreAB.toDeRham (coreAB.toBetti (Eq.mp middleEq.symm (coreBC.toBetti e))))) =
              coreBC.toDeRham (coreBC.toBetti e) := by rw [hmid]
          _ = e := coreBC.rightInverse e
      relation_graph_toDeRham := by
        intro b e
        constructor
        · intro h
          rcases h with ⟨d, hab, hbc⟩
          have hab' : coreAB.toDeRham b = d :=
            (coreAB.relation_graph_toDeRham b d).1 hab
          have hbc' : coreBC.toDeRham (Eq.mp middleEq d) = e :=
            (coreBC.relation_graph_toDeRham (Eq.mp middleEq d) e).1 hbc
          simpa [hab'] using hbc'
        · intro h
          refine ⟨coreAB.toDeRham b, ?_, ?_⟩
          · exact (coreAB.relation_graph_toDeRham b (coreAB.toDeRham b)).2 rfl
          · exact (coreBC.relation_graph_toDeRham
              (Eq.mp middleEq (coreAB.toDeRham b)) e).2 h }

/-- Derived comparison-isomorphism witness for a relation core. -/
def comparisonIsoWitness (core : StructuredComparisonRelationCore.{w, x}) : Prop :=
  (∀ b : core.BettiLikeCarrier, core.toBetti (core.toDeRham b) = b) ∧
    (∀ d : core.DeRhamLikeCarrier, core.toDeRham (core.toBetti d) = d) ∧
    (∀ b : core.BettiLikeCarrier, ∀ d : core.DeRhamLikeCarrier,
      core.comparisonRel b d ↔ core.toDeRham b = d)

theorem comparisonIsoWitness_holds (core : StructuredComparisonRelationCore.{w, x}) :
    core.comparisonIsoWitness := by
  exact ⟨core.leftInverse, core.rightInverse, core.relation_graph_toDeRham⟩

/-- Proposition-level agreement for comparison relations with fixed endpoint carrier surfaces. This
is the right theorem surface for the calculus laws when definitional equality is too strong. -/
def RelationAgreement
    {B : Type w}
    {D : Type x}
    (rel₁ rel₂ : B → D → Prop) : Prop :=
  ∀ b : B, ∀ d : D, rel₁ b d ↔ rel₂ b d

theorem relationAgreement_refl
    {B : Type w}
    {D : Type x}
    (rel : B → D → Prop) :
    RelationAgreement rel rel := by
  intro b d
  rfl

theorem relationAgreement_symm
    {B : Type w}
    {D : Type x}
    {rel₁ rel₂ : B → D → Prop}
    (h : RelationAgreement rel₁ rel₂) :
    RelationAgreement rel₂ rel₁ := by
  intro b d
  exact (h b d).symm

theorem relationAgreement_trans
    {B : Type w}
    {D : Type x}
    {rel₁ rel₂ rel₃ : B → D → Prop}
    (h₁₂ : RelationAgreement rel₁ rel₂)
    (h₂₃ : RelationAgreement rel₂ rel₃) :
    RelationAgreement rel₁ rel₃ := by
  intro b d
  exact (h₁₂ b d).trans (h₂₃ b d)

/-- Relation agreement is a congruence for existential composition of comparison relations. This
is the relation-level core of composition congruence for the J.1 witness calculus. -/
theorem relationAgreement_compose_congr
    {B : Type w}
    {C : Type x}
    {D : Type y}
    {relAB₁ relAB₂ : B → C → Prop}
    {relBC₁ relBC₂ : C → D → Prop}
    (hAB : RelationAgreement relAB₁ relAB₂)
    (hBC : RelationAgreement relBC₁ relBC₂) :
    RelationAgreement
      (fun b d => ∃ c : C, relAB₁ b c ∧ relBC₁ c d)
      (fun b d => ∃ c : C, relAB₂ b c ∧ relBC₂ c d) := by
  intro b d
  constructor
  · rintro ⟨c, hab, hbc⟩
    exact ⟨c, (hAB b c).1 hab, (hBC c d).1 hbc⟩
  · rintro ⟨c, hab, hbc⟩
    exact ⟨c, (hAB b c).2 hab, (hBC c d).2 hbc⟩

/-- Category-like theorem bundle for the relation-core comparison calculus. -/
structure CalculusLaws where
  leftIdentity :
    ∀ (core : StructuredComparisonRelationCore.{w, x}),
      RelationAgreement
        (compose (identity core.BettiLikeCarrier) core rfl).comparisonRel
        core.comparisonRel
  rightIdentity :
    ∀ (core : StructuredComparisonRelationCore.{w, x}),
      RelationAgreement
        (compose core (identity core.DeRhamLikeCarrier) rfl).comparisonRel
        core.comparisonRel
  associativity :
    ∀ (coreAB : StructuredComparisonRelationCore.{w, x})
      (coreBC : StructuredComparisonRelationCore.{x, y})
      (coreCD : StructuredComparisonRelationCore.{y, z})
      (hAB_BC : coreAB.DeRhamLikeCarrier = coreBC.BettiLikeCarrier)
      (hBC_CD : coreBC.DeRhamLikeCarrier = coreCD.BettiLikeCarrier),
        RelationAgreement
          (compose (compose coreAB coreBC hAB_BC) coreCD hBC_CD).comparisonRel
          (compose coreAB (compose coreBC coreCD hBC_CD) hAB_BC).comparisonRel

/-- Generic left identity law for the relation-core calculus. -/
theorem compose_leftIdentity
    (core : StructuredComparisonRelationCore.{w, x}) :
    RelationAgreement
      (compose (identity core.BettiLikeCarrier) core rfl).comparisonRel
      core.comparisonRel := by
  intro b d
  constructor
  · rintro ⟨b', hb', hcore⟩
    cases hb'
    exact hcore
  · intro hcore
    refine ⟨b, rfl, hcore⟩

/-- Generic right identity law for the relation-core calculus. -/
theorem compose_rightIdentity
    (core : StructuredComparisonRelationCore.{w, x}) :
    RelationAgreement
      (compose core (identity core.DeRhamLikeCarrier) rfl).comparisonRel
      core.comparisonRel := by
  intro b d
  constructor
  · rintro ⟨d', hcore, hd'⟩
    cases hd'
    exact hcore
  · intro hcore
    refine ⟨d, hcore, rfl⟩

/-- Generic associativity law for the relation-core calculus. -/
theorem compose_associativity
    (coreAB : StructuredComparisonRelationCore.{w, x})
    (coreBC : StructuredComparisonRelationCore.{x, y})
    (coreCD : StructuredComparisonRelationCore.{y, z})
    (hAB_BC : coreAB.DeRhamLikeCarrier = coreBC.BettiLikeCarrier)
    (hBC_CD : coreBC.DeRhamLikeCarrier = coreCD.BettiLikeCarrier) :
    RelationAgreement
      (compose (compose coreAB coreBC hAB_BC) coreCD hBC_CD).comparisonRel
      (compose coreAB (compose coreBC coreCD hBC_CD) hAB_BC).comparisonRel := by
  intro b f
  have hleft :=
    (compose (compose coreAB coreBC hAB_BC) coreCD hBC_CD).relation_graph_toDeRham b f
  have hright :=
    (compose coreAB (compose coreBC coreCD hBC_CD) hAB_BC).relation_graph_toDeRham b f
  exact ⟨fun h => hright.2 (hleft.1 h), fun h => hleft.2 (hright.1 h)⟩

/-- The generic relation-core calculus laws are available as a bundled theorem object. -/
def calculusLaws : CalculusLaws :=
  { leftIdentity := compose_leftIdentity
    rightIdentity := compose_rightIdentity
    associativity := compose_associativity }

end StructuredComparisonRelationCore

namespace StructuredComparisonIsoCore

/-- Constructor from a relation-with-witness theorem object. -/
def ofRelationCore (core : StructuredComparisonRelationCore.{w, x}) : StructuredComparisonIsoCore.{w, x} where
  BettiLikeCarrier := core.BettiLikeCarrier
  DeRhamLikeCarrier := core.DeRhamLikeCarrier
  comparisonMap := core.comparisonRel
  comparisonIsomorphism := core.comparisonIsoWitness
  comparisonIsomorphism_holds := core.comparisonIsoWitness_holds

/-- Generic identity-style comparison core. This is the first reusable non-mock family for J.1:
the two carrier surfaces agree, the comparison relation is equality, and the comparison theorem is
the reflexive self-comparison statement. -/
def identity (V : Type w) : StructuredComparisonIsoCore.{w, w} where
  BettiLikeCarrier := V
  DeRhamLikeCarrier := V
  comparisonMap := fun b d => b = d
  comparisonIsomorphism := ∀ v : V, (v = v)
  comparisonIsomorphism_holds := by
    intro v
    rfl

/-- Generic asymmetric comparison core induced by an explicit equivalence between the Betti-like
and de Rham-like carrier surfaces. The comparison relation is the graph of the forward map. -/
def ofEquiv
    (B : Type w)
    (D : Type x)
    (equivBD : B ≃ D) : StructuredComparisonIsoCore.{w, x} where
  BettiLikeCarrier := B
  DeRhamLikeCarrier := D
  comparisonMap := fun b d => equivBD b = d
  comparisonIsomorphism :=
    (∀ b : B, equivBD b = equivBD b) ∧
      (∀ d : D, equivBD (equivBD.symm d) = d)
  comparisonIsomorphism_holds := by
    constructor
    · intro b
      rfl
    · intro d
      exact equivBD.apply_symm_apply d

end StructuredComparisonIsoCore

namespace StructuredComparisonFunctorialityData

/-- Implementation-facing constructor for the subordinate J.1 functoriality data. -/
def ofBasicFunctoriality
    {BettiLikeCarrier : Type w}
    {DeRhamLikeCarrier : Type x}
    {comparisonMap : BettiLikeCarrier → DeRhamLikeCarrier → Prop}
    (bettiLikeFunctoriality : Prop)
    (bettiLikeFunctoriality_holds : bettiLikeFunctoriality)
    (deRhamLikeFunctoriality : Prop)
    (deRhamLikeFunctoriality_holds : deRhamLikeFunctoriality)
    (comparisonMapFunctorial : Prop)
    (comparisonMapFunctorial_holds : comparisonMapFunctorial)
    (realizationFunctorsInfinity : Prop)
    (realizationFunctorsInfinity_holds : realizationFunctorsInfinity)
    (realizationFunctorsPiZero : Prop)
    (realizationFunctorsPiZero_holds : realizationFunctorsPiZero) :
    StructuredComparisonFunctorialityData BettiLikeCarrier DeRhamLikeCarrier comparisonMap where
  bettiLikeFunctoriality := bettiLikeFunctoriality
  bettiLikeFunctoriality_holds := bettiLikeFunctoriality_holds
  deRhamLikeFunctoriality := deRhamLikeFunctoriality
  deRhamLikeFunctoriality_holds := deRhamLikeFunctoriality_holds
  comparisonMapFunctorial := comparisonMapFunctorial
  comparisonMapFunctorial_holds := comparisonMapFunctorial_holds
  realizationFunctorsInfinity := realizationFunctorsInfinity
  realizationFunctorsInfinity_holds := realizationFunctorsInfinity_holds
  realizationFunctorsPiZero := realizationFunctorsPiZero
  realizationFunctorsPiZero_holds := realizationFunctorsPiZero_holds

end StructuredComparisonFunctorialityData

namespace StructuredComparisonCompatibilityData

/-- Implementation-facing constructor for the subordinate J.1 compatibility data. -/
def ofBasicCompatibility
    (compatibleWithSourcePackage : Prop)
    (compatibleWithSourcePackage_holds : compatibleWithSourcePackage)
    (compatibleWithTargetPackage : Prop)
    (compatibleWithTargetPackage_holds : compatibleWithTargetPackage)
    (compatibleWithComparisonPackage : Prop)
    (compatibleWithComparisonPackage_holds : compatibleWithComparisonPackage)
    (structuredFaithfulness : Prop)
    (structuredFaithfulness_holds : structuredFaithfulness) :
    StructuredComparisonCompatibilityData where
  compatibleWithSourcePackage := compatibleWithSourcePackage
  compatibleWithSourcePackage_holds := compatibleWithSourcePackage_holds
  compatibleWithTargetPackage := compatibleWithTargetPackage
  compatibleWithTargetPackage_holds := compatibleWithTargetPackage_holds
  compatibleWithComparisonPackage := compatibleWithComparisonPackage
  compatibleWithComparisonPackage_holds := compatibleWithComparisonPackage_holds
  structuredFaithfulness := structuredFaithfulness
  structuredFaithfulness_holds := structuredFaithfulness_holds

end StructuredComparisonCompatibilityData

namespace StructuredComparisonImplementationTicket

/-- Thin J.1 wrapper from an explicit comparison-isomorphism core object plus the subordinate
functoriality and compatibility theorem data. -/
def ofIsoCore
    (core : StructuredComparisonIsoCore.{w, x})
    (functorialityData : StructuredComparisonFunctorialityData
      core.BettiLikeCarrier core.DeRhamLikeCarrier core.comparisonMap)
    (compatibilityData : StructuredComparisonCompatibilityData) :
    StructuredComparisonImplementationTicket.{w, x} :=
  ofComparisonIsoData
    core.BettiLikeCarrier
    core.DeRhamLikeCarrier
    core.comparisonMap
    core.comparisonIsomorphism
    core.comparisonIsomorphism_holds
    functorialityData
    compatibilityData

theorem ofIsoCore_supplies_ticket
    (core : StructuredComparisonIsoCore.{w, x})
    (functorialityData : StructuredComparisonFunctorialityData
      core.BettiLikeCarrier core.DeRhamLikeCarrier core.comparisonMap)
    (compatibilityData : StructuredComparisonCompatibilityData) :
    (ofIsoCore core functorialityData compatibilityData).theoremTarget := by
  simpa [ofIsoCore] using
    ofComparisonIsoData_supplies_ticket
      core.BettiLikeCarrier
      core.DeRhamLikeCarrier
      core.comparisonMap
      core.comparisonIsomorphism
      core.comparisonIsomorphism_holds
      functorialityData
      compatibilityData

theorem ofIsoCore_supplies_structuredRealizationPackage
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms)
    (core : StructuredComparisonIsoCore.{w, x})
    (functorialityData : StructuredComparisonFunctorialityData
      core.BettiLikeCarrier core.DeRhamLikeCarrier core.comparisonMap)
    (compatibilityData : StructuredComparisonCompatibilityData) :
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((ofIsoCore core functorialityData compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).structuredRealizationConsequence =
        compatibilityData.structuredFaithfulness ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((ofIsoCore core functorialityData compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).realizationFunctorsInfinity =
        functorialityData.realizationFunctorsInfinity ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((ofIsoCore core functorialityData compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).realizationFunctorsPiZero =
        functorialityData.realizationFunctorsPiZero := by
  simpa [ofIsoCore] using
    supplies_structuredRealizationPackage targetData comparisonData
      (ofComparisonIsoData
        core.BettiLikeCarrier
        core.DeRhamLikeCarrier
        core.comparisonMap
        core.comparisonIsomorphism
        core.comparisonIsomorphism_holds
        functorialityData
        compatibilityData)

end StructuredComparisonImplementationTicket

/-- Generic identity-style comparison core family for J.1. This keeps the core shape fixed while
providing the first reusable abstract comparison relation beyond a one-off mock record literal. -/
def identityStructuredComparisonIsoCore (V : Type w) : StructuredComparisonIsoCore.{w, w} :=
  StructuredComparisonIsoCore.identity V

/-- Generic asymmetric comparison-core family induced by an explicit equivalence. This is the
first reusable J.1 family where the Betti-like and de Rham-like carriers are allowed to differ. -/
def equivStructuredComparisonIsoCore
    (B : Type w)
    (D : Type x)
    (equivBD : B ≃ D) : StructuredComparisonIsoCore.{w, x} :=
  StructuredComparisonIsoCore.ofEquiv B D equivBD

/-- Conversion from a relation-with-witness theorem object into the sharpened J.1 core surface. -/
def relationStructuredComparisonIsoCore
    (core : StructuredComparisonRelationCore.{w, x}) : StructuredComparisonIsoCore.{w, x} :=
  StructuredComparisonIsoCore.ofRelationCore core

/-- On the comparison-map surface, the relation-core identity object converts to the same equality
relation used by the existing identity comparison-isomorphism core. -/
theorem relationStructuredComparisonIsoCore_identity_map_eq (V : Type w) :
    (relationStructuredComparisonIsoCore
      (StructuredComparisonRelationCore.identity V)).comparisonMap =
        (identityStructuredComparisonIsoCore V).comparisonMap := by
  rfl

/-- Conversion of a composed relation core preserves the explicit comparison witness as the
comparison-isomorphism theorem surface. -/
theorem relationStructuredComparisonIsoCore_compose_witness_eq
    (coreAB : StructuredComparisonRelationCore.{w, x})
    (coreBC : StructuredComparisonRelationCore.{x, y})
    (middleEq : coreAB.DeRhamLikeCarrier = coreBC.BettiLikeCarrier) :
    (relationStructuredComparisonIsoCore
      (StructuredComparisonRelationCore.compose coreAB coreBC middleEq)).comparisonIsomorphism =
        (StructuredComparisonRelationCore.compose coreAB coreBC middleEq).comparisonIsoWitness := by
  rfl

/-- Conversion of left identity into the sharpened J.1 comparison core preserves the comparison-map
surface. -/
theorem relationStructuredComparisonIsoCore_leftIdentity_map_eq
    (core : StructuredComparisonRelationCore.{w, x}) :
    (relationStructuredComparisonIsoCore
      (StructuredComparisonRelationCore.compose
        (StructuredComparisonRelationCore.identity core.BettiLikeCarrier)
        core rfl)).comparisonMap =
      (relationStructuredComparisonIsoCore core).comparisonMap := by
  funext b d
  exact propext (StructuredComparisonRelationCore.compose_leftIdentity core b d)

/-- Conversion of right identity into the sharpened J.1 comparison core preserves the
comparison-map surface. -/
theorem relationStructuredComparisonIsoCore_rightIdentity_map_eq
    (core : StructuredComparisonRelationCore.{w, x}) :
    (relationStructuredComparisonIsoCore
      (StructuredComparisonRelationCore.compose
        core
        (StructuredComparisonRelationCore.identity core.DeRhamLikeCarrier) rfl)).comparisonMap =
      (relationStructuredComparisonIsoCore core).comparisonMap := by
  funext b d
  exact propext (StructuredComparisonRelationCore.compose_rightIdentity core b d)

/-- Conversion of associative relation-core composites into the sharpened J.1 comparison core
preserves the comparison-map surface. -/
theorem relationStructuredComparisonIsoCore_compose_associativity_map_eq
    (coreAB : StructuredComparisonRelationCore.{w, x})
    (coreBC : StructuredComparisonRelationCore.{x, y})
    (coreCD : StructuredComparisonRelationCore.{y, z})
    (hAB_BC : coreAB.DeRhamLikeCarrier = coreBC.BettiLikeCarrier)
    (hBC_CD : coreBC.DeRhamLikeCarrier = coreCD.BettiLikeCarrier) :
    (relationStructuredComparisonIsoCore
      (StructuredComparisonRelationCore.compose
        (StructuredComparisonRelationCore.compose coreAB coreBC hAB_BC)
        coreCD hBC_CD)).comparisonMap =
      (relationStructuredComparisonIsoCore
        (StructuredComparisonRelationCore.compose
          coreAB
          (StructuredComparisonRelationCore.compose coreBC coreCD hBC_CD)
          hAB_BC)).comparisonMap := by
  funext b f
  exact propext
    (StructuredComparisonRelationCore.compose_associativity
      coreAB coreBC coreCD hAB_BC hBC_CD b f)

/-- Relation agreement for a relation core is preserved by conversion into the sharpened J.1
comparison-map surface. -/
theorem relationAgreement_toIsoCore_comparisonMap_agreement
    (core : StructuredComparisonRelationCore.{w, x})
    {rel : core.BettiLikeCarrier → core.DeRhamLikeCarrier → Prop}
    (h : StructuredComparisonRelationCore.RelationAgreement core.comparisonRel rel) :
    StructuredComparisonRelationCore.RelationAgreement
      (relationStructuredComparisonIsoCore core).comparisonMap
      rel := h

/-- Proposition-level relation agreement yields equality of the comparison-map surface after
conversion into `StructuredComparisonIsoCore`. -/
theorem relationAgreement_ofRelationCore_respects_comparisonMap
    (core : StructuredComparisonRelationCore.{w, x})
    {rel : core.BettiLikeCarrier → core.DeRhamLikeCarrier → Prop}
    (h : StructuredComparisonRelationCore.RelationAgreement core.comparisonRel rel) :
    (relationStructuredComparisonIsoCore core).comparisonMap = rel := by
  funext b d
  exact propext (h b d)

/-- Ticket-level substitution on the structured-comparison comparison-map surface. When a relation
core agrees propositionally with an expected relation on the same endpoint carriers, the ticket
produced from that core exposes the same comparison-map surface. -/
theorem relationAgreement_supplies_same_structuredComparisonMap
    (core : StructuredComparisonRelationCore.{w, x})
    {rel : core.BettiLikeCarrier → core.DeRhamLikeCarrier → Prop}
    (h : StructuredComparisonRelationCore.RelationAgreement core.comparisonRel rel)
    (functorialityData : StructuredComparisonFunctorialityData
      core.BettiLikeCarrier core.DeRhamLikeCarrier core.comparisonRel)
    (compatibilityData : StructuredComparisonCompatibilityData) :
    (StructuredComparisonImplementationTicket.ofIsoCore
      (relationStructuredComparisonIsoCore core)
      functorialityData
      compatibilityData).comparisonMap = rel := by
  exact relationAgreement_ofRelationCore_respects_comparisonMap core h

/-- Transport shared functoriality data from an expected comparison relation back to the relation
core surface using proposition-level relation agreement. -/
def relationAgreement_transportFunctorialityData
    (core : StructuredComparisonRelationCore.{w, x})
    {rel : core.BettiLikeCarrier → core.DeRhamLikeCarrier → Prop}
    (h : StructuredComparisonRelationCore.RelationAgreement core.comparisonRel rel)
    (functorialityData : StructuredComparisonFunctorialityData
      core.BettiLikeCarrier core.DeRhamLikeCarrier rel) :
    StructuredComparisonFunctorialityData
      core.BettiLikeCarrier core.DeRhamLikeCarrier core.comparisonRel :=
  Eq.mp
    (by
      simpa [relationStructuredComparisonIsoCore, StructuredComparisonIsoCore.ofRelationCore] using
        congrArg
          (fun comparisonMap =>
            StructuredComparisonFunctorialityData
              core.BettiLikeCarrier
              core.DeRhamLikeCarrier
              comparisonMap)
          (relationAgreement_ofRelationCore_respects_comparisonMap core h).symm)
    functorialityData

/-- In the narrow shared-data case, relation agreement is enough to substitute one relation-core
ticket for any expected comparison relation at the structured-comparison theorem-package surface.
The comparison-isomorphism proposition itself may differ; that field is intentionally omitted from
this package surface. -/
theorem relationAgreement_supplies_same_structuredComparisonTheoremPackage
    (core : StructuredComparisonRelationCore.{w, x})
    {rel : core.BettiLikeCarrier → core.DeRhamLikeCarrier → Prop}
    (h : StructuredComparisonRelationCore.RelationAgreement core.comparisonRel rel)
    (comparisonIsomorphism : Prop)
    (comparisonIsomorphism_holds : comparisonIsomorphism)
    (functorialityData : StructuredComparisonFunctorialityData
      core.BettiLikeCarrier core.DeRhamLikeCarrier rel)
    (compatibilityData : StructuredComparisonCompatibilityData) :
    (StructuredComparisonImplementationTicket.ofIsoCore
      (relationStructuredComparisonIsoCore core)
      (relationAgreement_transportFunctorialityData core h functorialityData)
      compatibilityData).toStructuredComparisonTheoremPackage =
    (StructuredComparisonImplementationTicket.ofComparisonIsoData
      core.BettiLikeCarrier
      core.DeRhamLikeCarrier
      rel
      comparisonIsomorphism
      comparisonIsomorphism_holds
      functorialityData
      compatibilityData).toStructuredComparisonTheoremPackage := by
  have hmap :=
    relationAgreement_supplies_same_structuredComparisonMap
      core h
      (relationAgreement_transportFunctorialityData core h functorialityData)
      compatibilityData
  have hrel : core.comparisonRel = rel := by
    simpa [StructuredComparisonImplementationTicket.ofIsoCore,
      relationStructuredComparisonIsoCore,
      StructuredComparisonIsoCore.ofRelationCore] using hmap
  cases functorialityData
  cases compatibilityData
  cases hrel
  rfl

/-- In the same shared-data situation, relation agreement is enough to substitute one relation-core
ticket for another all the way down to the Layer D structured-realization package surface. -/
theorem relationAgreement_supplies_same_structuredPackageSurface
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms)
    (core : StructuredComparisonRelationCore.{w, x})
    {rel : core.BettiLikeCarrier → core.DeRhamLikeCarrier → Prop}
    (h : StructuredComparisonRelationCore.RelationAgreement core.comparisonRel rel)
    (comparisonIsomorphism : Prop)
    (comparisonIsomorphism_holds : comparisonIsomorphism)
    (functorialityData : StructuredComparisonFunctorialityData
      core.BettiLikeCarrier core.DeRhamLikeCarrier rel)
    (compatibilityData : StructuredComparisonCompatibilityData) :
    LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofIsoCore
          (relationStructuredComparisonIsoCore core)
          (relationAgreement_transportFunctorialityData core h functorialityData)
          compatibilityData).toStructuredRealizationInputData targetData comparisonData) =
    LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofComparisonIsoData
          core.BettiLikeCarrier
          core.DeRhamLikeCarrier
          rel
          comparisonIsomorphism
          comparisonIsomorphism_holds
          functorialityData
          compatibilityData).toStructuredRealizationInputData targetData comparisonData) := by
  have hmap :=
    relationAgreement_supplies_same_structuredComparisonMap
      core h
      (relationAgreement_transportFunctorialityData core h functorialityData)
      compatibilityData
  have hrel : core.comparisonRel = rel := by
    simpa [StructuredComparisonImplementationTicket.ofIsoCore,
      relationStructuredComparisonIsoCore,
      StructuredComparisonIsoCore.ofRelationCore] using hmap
  cases functorialityData
  cases compatibilityData
  cases hrel
  rfl

/-- The generic identity-style core already lands in the sharpened J.1 ticket surface once the
remaining subordinate theorem data are supplied. -/
theorem identityStructuredComparisonIsoCore_supplies_ticket
    (V : Type w)
    (functorialityData : StructuredComparisonFunctorialityData
      V V (fun b d => b = d))
    (compatibilityData : StructuredComparisonCompatibilityData) :
    (StructuredComparisonImplementationTicket.ofIsoCore
      (identityStructuredComparisonIsoCore V)
      functorialityData
      compatibilityData).theoremTarget := by
  simpa [identityStructuredComparisonIsoCore, StructuredComparisonIsoCore.identity] using
    StructuredComparisonImplementationTicket.ofIsoCore_supplies_ticket
      (identityStructuredComparisonIsoCore V)
      functorialityData
      compatibilityData

/-- The generic identity-style core also reaches the existing structured realization package path
once the subordinate theorem data are supplied. -/
theorem identityStructuredComparisonIsoCore_supplies_structuredPackage
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms)
    (V : Type w)
    (functorialityData : StructuredComparisonFunctorialityData
      V V (fun b d => b = d))
    (compatibilityData : StructuredComparisonCompatibilityData) :
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofIsoCore
          (identityStructuredComparisonIsoCore V)
          functorialityData
          compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).structuredRealizationConsequence =
        compatibilityData.structuredFaithfulness ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofIsoCore
          (identityStructuredComparisonIsoCore V)
          functorialityData
          compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).realizationFunctorsInfinity =
        functorialityData.realizationFunctorsInfinity ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofIsoCore
          (identityStructuredComparisonIsoCore V)
          functorialityData
          compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).realizationFunctorsPiZero =
        functorialityData.realizationFunctorsPiZero := by
  simpa [identityStructuredComparisonIsoCore, StructuredComparisonIsoCore.identity] using
    StructuredComparisonImplementationTicket.ofIsoCore_supplies_structuredRealizationPackage
      targetData comparisonData
      (identityStructuredComparisonIsoCore V)
      functorialityData
      compatibilityData

/-- The generic asymmetric equivalence-induced core lands in the sharpened J.1 ticket surface once
the remaining subordinate theorem data are supplied. -/
theorem equivStructuredComparisonIsoCore_supplies_ticket
    (B : Type w)
    (D : Type x)
    (equivBD : B ≃ D)
    (functorialityData : StructuredComparisonFunctorialityData
      B D (fun b d => equivBD b = d))
    (compatibilityData : StructuredComparisonCompatibilityData) :
    (StructuredComparisonImplementationTicket.ofIsoCore
      (equivStructuredComparisonIsoCore B D equivBD)
      functorialityData
      compatibilityData).theoremTarget := by
  simpa [equivStructuredComparisonIsoCore, StructuredComparisonIsoCore.ofEquiv] using
    StructuredComparisonImplementationTicket.ofIsoCore_supplies_ticket
      (equivStructuredComparisonIsoCore B D equivBD)
      functorialityData
      compatibilityData

/-- The generic asymmetric equivalence-induced core reaches the existing structured realization
package path once the subordinate theorem data are supplied. -/
theorem equivStructuredComparisonIsoCore_supplies_structuredPackage
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms)
    (B : Type w)
    (D : Type x)
    (equivBD : B ≃ D)
    (functorialityData : StructuredComparisonFunctorialityData
      B D (fun b d => equivBD b = d))
    (compatibilityData : StructuredComparisonCompatibilityData) :
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofIsoCore
          (equivStructuredComparisonIsoCore B D equivBD)
          functorialityData
          compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).structuredRealizationConsequence =
        compatibilityData.structuredFaithfulness ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofIsoCore
          (equivStructuredComparisonIsoCore B D equivBD)
          functorialityData
          compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).realizationFunctorsInfinity =
        functorialityData.realizationFunctorsInfinity ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofIsoCore
          (equivStructuredComparisonIsoCore B D equivBD)
          functorialityData
          compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).realizationFunctorsPiZero =
        functorialityData.realizationFunctorsPiZero := by
  simpa [equivStructuredComparisonIsoCore, StructuredComparisonIsoCore.ofEquiv] using
    StructuredComparisonImplementationTicket.ofIsoCore_supplies_structuredRealizationPackage
      targetData comparisonData
      (equivStructuredComparisonIsoCore B D equivBD)
      functorialityData
      compatibilityData

/-- A relation-with-witness theorem object already lands in the sharpened J.1 ticket surface once
the remaining subordinate theorem data are supplied. -/
theorem relationCore_supplies_ticket
    (core : StructuredComparisonRelationCore.{w, x})
    (functorialityData : StructuredComparisonFunctorialityData
      core.BettiLikeCarrier core.DeRhamLikeCarrier core.comparisonRel)
    (compatibilityData : StructuredComparisonCompatibilityData) :
    (StructuredComparisonImplementationTicket.ofIsoCore
      (relationStructuredComparisonIsoCore core)
      functorialityData
      compatibilityData).theoremTarget := by
  simpa [relationStructuredComparisonIsoCore, StructuredComparisonIsoCore.ofRelationCore,
    StructuredComparisonRelationCore.comparisonIsoWitness] using
    StructuredComparisonImplementationTicket.ofIsoCore_supplies_ticket
      (relationStructuredComparisonIsoCore core)
      functorialityData
      compatibilityData

/-- A relation-with-witness theorem object reaches the existing structured realization package path
once the remaining subordinate theorem data are supplied. -/
theorem relationCore_supplies_structuredPackage
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms)
    (core : StructuredComparisonRelationCore.{w, x})
    (functorialityData : StructuredComparisonFunctorialityData
      core.BettiLikeCarrier core.DeRhamLikeCarrier core.comparisonRel)
    (compatibilityData : StructuredComparisonCompatibilityData) :
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofIsoCore
          (relationStructuredComparisonIsoCore core)
          functorialityData
          compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).structuredRealizationConsequence =
        compatibilityData.structuredFaithfulness ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofIsoCore
          (relationStructuredComparisonIsoCore core)
          functorialityData
          compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).realizationFunctorsInfinity =
        functorialityData.realizationFunctorsInfinity ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofIsoCore
          (relationStructuredComparisonIsoCore core)
          functorialityData
          compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).realizationFunctorsPiZero =
        functorialityData.realizationFunctorsPiZero := by
  simpa [relationStructuredComparisonIsoCore, StructuredComparisonIsoCore.ofRelationCore,
    StructuredComparisonRelationCore.comparisonIsoWitness] using
    StructuredComparisonImplementationTicket.ofIsoCore_supplies_structuredRealizationPackage
      targetData comparisonData
      (relationStructuredComparisonIsoCore core)
      functorialityData
      compatibilityData

/-- A composed relation-with-witness theorem object lands in the sharpened J.1 ticket surface
once the remaining subordinate theorem data are supplied. -/
theorem composedRelationCore_supplies_ticket
    (coreAB : StructuredComparisonRelationCore.{w, x})
  (coreBC : StructuredComparisonRelationCore.{x, y})
    (middleEq : coreAB.DeRhamLikeCarrier = coreBC.BettiLikeCarrier)
    (functorialityData : StructuredComparisonFunctorialityData
      (StructuredComparisonRelationCore.compose coreAB coreBC middleEq).BettiLikeCarrier
      (StructuredComparisonRelationCore.compose coreAB coreBC middleEq).DeRhamLikeCarrier
      (StructuredComparisonRelationCore.compose coreAB coreBC middleEq).comparisonRel)
    (compatibilityData : StructuredComparisonCompatibilityData) :
    (StructuredComparisonImplementationTicket.ofIsoCore
      (relationStructuredComparisonIsoCore
        (StructuredComparisonRelationCore.compose coreAB coreBC middleEq))
      functorialityData
      compatibilityData).theoremTarget := by
  simpa using relationCore_supplies_ticket
    (StructuredComparisonRelationCore.compose coreAB coreBC middleEq)
    functorialityData
    compatibilityData

/-- A composed relation-with-witness theorem object reaches the structured realization package
path once the remaining subordinate theorem data are supplied. -/
theorem composedRelationCore_supplies_structuredPackage
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms)
    (coreAB : StructuredComparisonRelationCore.{w, x})
  (coreBC : StructuredComparisonRelationCore.{x, y})
    (middleEq : coreAB.DeRhamLikeCarrier = coreBC.BettiLikeCarrier)
    (functorialityData : StructuredComparisonFunctorialityData
      (StructuredComparisonRelationCore.compose coreAB coreBC middleEq).BettiLikeCarrier
      (StructuredComparisonRelationCore.compose coreAB coreBC middleEq).DeRhamLikeCarrier
      (StructuredComparisonRelationCore.compose coreAB coreBC middleEq).comparisonRel)
    (compatibilityData : StructuredComparisonCompatibilityData) :
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofIsoCore
          (relationStructuredComparisonIsoCore
            (StructuredComparisonRelationCore.compose coreAB coreBC middleEq))
          functorialityData
          compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).structuredRealizationConsequence =
        compatibilityData.structuredFaithfulness ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofIsoCore
          (relationStructuredComparisonIsoCore
            (StructuredComparisonRelationCore.compose coreAB coreBC middleEq))
          functorialityData
          compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).realizationFunctorsInfinity =
        functorialityData.realizationFunctorsInfinity ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofIsoCore
          (relationStructuredComparisonIsoCore
            (StructuredComparisonRelationCore.compose coreAB coreBC middleEq))
          functorialityData
          compatibilityData).toStructuredRealizationInputData
        targetData comparisonData)).realizationFunctorsPiZero =
        functorialityData.realizationFunctorsPiZero := by
  simpa using relationCore_supplies_structuredPackage
    targetData comparisonData
    (StructuredComparisonRelationCore.compose coreAB coreBC middleEq)
    functorialityData
    compatibilityData

/-- Cheap finite identity-core example for J.1. This stays non-motivic but uses a genuinely small
finite carrier rather than a bespoke record literal. -/
def boolIdentityStructuredComparisonIsoCore : StructuredComparisonIsoCore.{0, 0} :=
  identityStructuredComparisonIsoCore Bool

/-- Cheap finite identity-core example on `Fin 2`. -/
def finTwoIdentityStructuredComparisonIsoCore : StructuredComparisonIsoCore.{0, 0} :=
  identityStructuredComparisonIsoCore (Fin 2)

/-- Forward map for the finite asymmetric Bool/Fin 2 sanity core. -/
def boolToFinTwo : Bool → Fin 2
  | false => ⟨0, by decide⟩
  | true => ⟨1, by decide⟩

/-- Inverse map for the finite asymmetric Bool/Fin 2 sanity core. -/
def finTwoToBool (i : Fin 2) : Bool :=
  if i.1 = 0 then false else true

/-- The Bool-to-Fin-2 map is left-inverted by the chosen Fin-2-to-Bool map. -/
theorem finTwoToBool_boolToFinTwo (b : Bool) :
    finTwoToBool (boolToFinTwo b) = b := by
  cases b <;> simp [boolToFinTwo, finTwoToBool]

/-- The chosen Fin-2-to-Bool map is right-inverse to the Bool-to-Fin-2 map. -/
theorem boolToFinTwo_finTwoToBool (i : Fin 2) :
    boolToFinTwo (finTwoToBool i) = i := by
  apply Fin.ext
  have hi : i.1 = 0 ∨ i.1 = 1 := by
    omega
  cases hi with
  | inl h0 =>
      simp [boolToFinTwo, finTwoToBool, h0]
  | inr h1 =>
      simp [boolToFinTwo, finTwoToBool, h1]

/-- Standard finite asymmetric equivalence between `Bool` and `Fin 2`. -/
def boolFinTwoEquiv : Bool ≃ Fin 2 :=
  { toFun := boolToFinTwo
    invFun := finTwoToBool
    left_inv := finTwoToBool_boolToFinTwo
    right_inv := boolToFinTwo_finTwoToBool }

/-- Finite relation-with-witness theorem object for the Bool/Fin 2 sanity comparison. The
comparison relation is written as a value-level condition rather than definitionally as the graph
of the equivalence map. -/
def boolFinTwoRelationCore : StructuredComparisonRelationCore.{0, 0} where
  BettiLikeCarrier := Bool
  DeRhamLikeCarrier := Fin 2
  comparisonRel := fun b d => d.1 = (if b then 1 else 0)
  toDeRham := boolToFinTwo
  toBetti := finTwoToBool
  leftInverse := finTwoToBool_boolToFinTwo
  rightInverse := boolToFinTwo_finTwoToBool
  relation_graph_toDeRham := by
    intro b d
    cases b <;> constructor
    · intro h
      apply Fin.ext
      simpa [boolToFinTwo] using h.symm
    · intro h
      have hval := congrArg Fin.val h
      simpa [boolToFinTwo] using hval.symm
    · intro h
      apply Fin.ext
      simpa [boolToFinTwo] using h.symm
    · intro h
      have hval := congrArg Fin.val h
      simpa [boolToFinTwo] using hval.symm

/-- Finite reverse relation-with-witness core for the Fin 2/Bool leg. The comparison relation is
again presented propositionally rather than by definitional graph reduction. -/
def finTwoBoolRelationCore : StructuredComparisonRelationCore.{0, 0} where
  BettiLikeCarrier := Fin 2
  DeRhamLikeCarrier := Bool
  comparisonRel := fun i b => finTwoToBool i = b
  toDeRham := finTwoToBool
  toBetti := boolToFinTwo
  leftInverse := boolToFinTwo_finTwoToBool
  rightInverse := finTwoToBool_boolToFinTwo
  relation_graph_toDeRham := by
    intro i b
    rfl

/-- Finite composed relation core witnessing Bool -> Fin 2 -> Bool. The resulting relation is not
definitionally equality, but it remains a witnessed comparison core. -/
def boolFinTwoBoolComposedRelationCore : StructuredComparisonRelationCore.{0, 0} :=
  StructuredComparisonRelationCore.compose
    boolFinTwoRelationCore
    finTwoBoolRelationCore
    rfl

/-- The composed Bool -> Fin 2 -> Bool relation agrees propositionally with equality, even though
the relation itself is presented as an explicit existential composite. -/
theorem boolFinTwoBoolComposedRelation_agrees_with_equality
    (b₁ b₂ : Bool) :
    (∃ d : Fin 2, boolFinTwoRelationCore.comparisonRel b₁ d ∧ finTwoBoolRelationCore.comparisonRel d b₂) ↔
      b₁ = b₂ := by
  constructor
  · rintro ⟨d, hab, hbc⟩
    have hd : boolToFinTwo b₁ = d :=
      (boolFinTwoRelationCore.relation_graph_toDeRham b₁ d).1 hab
    have hb : finTwoToBool (boolToFinTwo b₁) = b₂ := by
      simpa [hd] using hbc
    simpa [finTwoToBool_boolToFinTwo b₁] using hb
  · intro h
    refine ⟨boolToFinTwo b₁, ?_, ?_⟩
    · exact (boolFinTwoRelationCore.relation_graph_toDeRham b₁ (boolToFinTwo b₁)).2 rfl
    · simpa [h] using finTwoToBool_boolToFinTwo b₁

/-- The finite composed Bool -> Fin 2 -> Bool comparison relation agrees with the expected Bool
equality relation at the proposition level. -/
theorem boolFinTwoBoolComposedRelationCore_agrees_with_identityRelation :
    StructuredComparisonRelationCore.RelationAgreement
      boolFinTwoBoolComposedRelationCore.comparisonRel
      (fun b₁ b₂ : Bool => b₁ = b₂) := by
  intro b₁ b₂
  simpa [boolFinTwoBoolComposedRelationCore, StructuredComparisonRelationCore.compose] using
    boolFinTwoBoolComposedRelation_agrees_with_equality b₁ b₂

/-- Finite left identity law for the Bool -> Fin 2 relation core. -/
theorem boolFinTwoRelationCore_leftIdentity :
    StructuredComparisonRelationCore.RelationAgreement
      (StructuredComparisonRelationCore.compose
        (StructuredComparisonRelationCore.identity Bool)
        boolFinTwoRelationCore rfl).comparisonRel
      boolFinTwoRelationCore.comparisonRel :=
  StructuredComparisonRelationCore.compose_leftIdentity boolFinTwoRelationCore

/-- Finite right identity law for the Bool -> Fin 2 relation core. -/
theorem boolFinTwoRelationCore_rightIdentity :
    StructuredComparisonRelationCore.RelationAgreement
      (StructuredComparisonRelationCore.compose
        boolFinTwoRelationCore
        (StructuredComparisonRelationCore.identity (Fin 2)) rfl).comparisonRel
      boolFinTwoRelationCore.comparisonRel :=
  StructuredComparisonRelationCore.compose_rightIdentity boolFinTwoRelationCore

/-- Finite left identity law for the Fin 2 -> Bool relation core. -/
theorem finTwoBoolRelationCore_leftIdentity :
    StructuredComparisonRelationCore.RelationAgreement
      (StructuredComparisonRelationCore.compose
        (StructuredComparisonRelationCore.identity (Fin 2))
        finTwoBoolRelationCore rfl).comparisonRel
      finTwoBoolRelationCore.comparisonRel :=
  StructuredComparisonRelationCore.compose_leftIdentity finTwoBoolRelationCore

/-- Finite right identity law for the Fin 2 -> Bool relation core. -/
theorem finTwoBoolRelationCore_rightIdentity :
    StructuredComparisonRelationCore.RelationAgreement
      (StructuredComparisonRelationCore.compose
        finTwoBoolRelationCore
        (StructuredComparisonRelationCore.identity Bool) rfl).comparisonRel
      finTwoBoolRelationCore.comparisonRel :=
  StructuredComparisonRelationCore.compose_rightIdentity finTwoBoolRelationCore

/-- Finite associativity law for the chain Bool -> Fin 2 -> Bool -> Fin 2. -/
theorem boolFinTwoBoolFinTwoRelationCore_associativity :
    StructuredComparisonRelationCore.RelationAgreement
      (StructuredComparisonRelationCore.compose
        (StructuredComparisonRelationCore.compose
          boolFinTwoRelationCore finTwoBoolRelationCore rfl)
        boolFinTwoRelationCore rfl).comparisonRel
      (StructuredComparisonRelationCore.compose
        boolFinTwoRelationCore
        (StructuredComparisonRelationCore.compose
          finTwoBoolRelationCore boolFinTwoRelationCore rfl) rfl).comparisonRel :=
  StructuredComparisonRelationCore.compose_associativity
    boolFinTwoRelationCore
    finTwoBoolRelationCore
    boolFinTwoRelationCore
    rfl rfl

/-- First finite asymmetric sanity core for J.1: Bool on the Betti-like side and Fin 2 on the
de Rham-like side, related by the standard equivalence. -/
def boolFinTwoStructuredComparisonIsoCore : StructuredComparisonIsoCore.{0, 0} :=
  equivStructuredComparisonIsoCore Bool (Fin 2) boolFinTwoEquiv

/-- Minimal non-motivic comparison-isomorphism core for the J.1 interface. This is a sanity model
only; it gives a named core object without asserting any mathematical comparison theorem. -/
def mockStructuredComparisonIsoCore : StructuredComparisonIsoCore.{0, 0} where
  BettiLikeCarrier := boolIdentityStructuredComparisonIsoCore.BettiLikeCarrier
  DeRhamLikeCarrier := boolIdentityStructuredComparisonIsoCore.DeRhamLikeCarrier
  comparisonMap := boolIdentityStructuredComparisonIsoCore.comparisonMap
  comparisonIsomorphism := boolIdentityStructuredComparisonIsoCore.comparisonIsomorphism
  comparisonIsomorphism_holds := boolIdentityStructuredComparisonIsoCore.comparisonIsomorphism_holds

/-- Minimal sanity functoriality data for the J.1 implementation interface. This is only a local
interface check, not a mathematical realization construction. -/
def mockStructuredComparisonFunctorialityData :
  StructuredComparisonFunctorialityData.{0, 0} Bool Bool (fun b d => b = d) :=
  StructuredComparisonFunctorialityData.ofBasicFunctoriality
    True trivial
    True trivial
    True trivial
    True trivial
    True trivial

/-- Minimal sanity compatibility data for the J.1 implementation interface. This is only a local
interface check, not a mathematical realization construction. -/
def mockStructuredComparisonCompatibilityData : StructuredComparisonCompatibilityData :=
  StructuredComparisonCompatibilityData.ofBasicCompatibility
    True trivial
    True trivial
    True trivial
    True trivial

/-- Minimal sanity functoriality data for the finite asymmetric Bool/Fin 2 core. -/
def boolFinTwoStructuredComparisonFunctorialityData :
    StructuredComparisonFunctorialityData.{0, 0} Bool (Fin 2)
      (fun b d => boolFinTwoEquiv b = d) :=
  StructuredComparisonFunctorialityData.ofBasicFunctoriality
    True trivial
    True trivial
    True trivial
    True trivial
    True trivial

/-- Minimal sanity ticket induced by the finite asymmetric Bool/Fin 2 core. -/
def boolFinTwoStructuredComparisonTicket : StructuredComparisonImplementationTicket.{0, 0} :=
  StructuredComparisonImplementationTicket.ofIsoCore
    boolFinTwoStructuredComparisonIsoCore
    boolFinTwoStructuredComparisonFunctorialityData
    mockStructuredComparisonCompatibilityData

/-- The finite asymmetric Bool/Fin 2 core already lands in the sharpened J.1 ticket surface. -/
theorem boolFinTwoStructuredComparisonIsoCore_supplies_ticket :
    boolFinTwoStructuredComparisonTicket.theoremTarget := by
  simpa [boolFinTwoStructuredComparisonTicket,
    boolFinTwoStructuredComparisonIsoCore,
    boolFinTwoStructuredComparisonFunctorialityData,
    boolFinTwoEquiv,
    equivStructuredComparisonIsoCore,
    StructuredComparisonIsoCore.ofEquiv,
    StructuredComparisonImplementationTicket.ofIsoCore,
    StructuredComparisonFunctorialityData.ofBasicFunctoriality] using
    equivStructuredComparisonIsoCore_supplies_ticket
      Bool (Fin 2) boolFinTwoEquiv
      boolFinTwoStructuredComparisonFunctorialityData
      mockStructuredComparisonCompatibilityData

/-- Minimal sanity functoriality data for the finite Bool/Fin 2 relation-with-witness core. -/
def boolFinTwoRelationFunctorialityData :
    StructuredComparisonFunctorialityData.{0, 0} Bool (Fin 2)
      (fun b d => d.1 = (if b then 1 else 0)) :=
  StructuredComparisonFunctorialityData.ofBasicFunctoriality
    True trivial
    True trivial
    True trivial
    True trivial
    True trivial

/-- Minimal sanity functoriality data for the finite composed Bool -> Fin 2 -> Bool relation
core. -/
def boolFinTwoBoolComposedRelationFunctorialityData :
    StructuredComparisonFunctorialityData.{0, 0}
      boolFinTwoBoolComposedRelationCore.BettiLikeCarrier
      boolFinTwoBoolComposedRelationCore.DeRhamLikeCarrier
      boolFinTwoBoolComposedRelationCore.comparisonRel :=
  StructuredComparisonFunctorialityData.ofBasicFunctoriality
    True trivial
    True trivial
    True trivial
    True trivial
    True trivial

/-- Minimal sanity ticket induced by the finite Bool/Fin 2 relation-with-witness core. -/
def boolFinTwoRelationTicket : StructuredComparisonImplementationTicket.{0, 0} :=
  StructuredComparisonImplementationTicket.ofIsoCore
    (relationStructuredComparisonIsoCore boolFinTwoRelationCore)
    boolFinTwoRelationFunctorialityData
    mockStructuredComparisonCompatibilityData

/-- Minimal sanity ticket induced by the finite composed Bool -> Fin 2 -> Bool relation core. -/
def boolFinTwoBoolComposedRelationTicket : StructuredComparisonImplementationTicket.{0, 0} :=
  StructuredComparisonImplementationTicket.ofIsoCore
    (relationStructuredComparisonIsoCore boolFinTwoBoolComposedRelationCore)
    boolFinTwoBoolComposedRelationFunctorialityData
    mockStructuredComparisonCompatibilityData

/-- The finite Bool/Fin 2 relation-with-witness core already lands in the sharpened J.1 ticket
surface. -/
theorem boolFinTwoRelationCore_supplies_ticket :
    boolFinTwoRelationTicket.theoremTarget := by
  simpa [boolFinTwoRelationTicket, relationStructuredComparisonIsoCore,
    StructuredComparisonIsoCore.ofRelationCore,
    StructuredComparisonRelationCore.comparisonIsoWitness,
    boolFinTwoRelationFunctorialityData,
    boolFinTwoRelationCore,
    StructuredComparisonFunctorialityData.ofBasicFunctoriality,
    boolToFinTwo, finTwoToBool] using
    relationCore_supplies_ticket
      boolFinTwoRelationCore
      boolFinTwoRelationFunctorialityData
      mockStructuredComparisonCompatibilityData

/-- The finite Bool/Fin 2 relation-with-witness core reaches the existing structured realization
package path. -/
theorem boolFinTwoRelationCore_supplies_structuredPackage
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms) :
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      (boolFinTwoRelationTicket.toStructuredRealizationInputData targetData comparisonData)).structuredRealizationConsequence =
        mockStructuredComparisonCompatibilityData.structuredFaithfulness ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      (boolFinTwoRelationTicket.toStructuredRealizationInputData targetData comparisonData)).realizationFunctorsInfinity =
        boolFinTwoRelationFunctorialityData.realizationFunctorsInfinity ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      (boolFinTwoRelationTicket.toStructuredRealizationInputData targetData comparisonData)).realizationFunctorsPiZero =
        boolFinTwoRelationFunctorialityData.realizationFunctorsPiZero := by
  simpa [boolFinTwoRelationTicket, relationStructuredComparisonIsoCore,
    StructuredComparisonIsoCore.ofRelationCore,
    StructuredComparisonRelationCore.comparisonIsoWitness,
    boolFinTwoRelationFunctorialityData,
    boolFinTwoRelationCore,
    StructuredComparisonFunctorialityData.ofBasicFunctoriality,
    boolToFinTwo, finTwoToBool] using
    relationCore_supplies_structuredPackage
      targetData comparisonData
      boolFinTwoRelationCore
      boolFinTwoRelationFunctorialityData
      mockStructuredComparisonCompatibilityData

/-- The finite composed Bool -> Fin 2 -> Bool relation core lands in the sharpened J.1 ticket
surface. -/
theorem boolFinTwoBoolComposedRelationCore_supplies_ticket :
    boolFinTwoBoolComposedRelationTicket.theoremTarget := by
  simpa [boolFinTwoBoolComposedRelationTicket, relationStructuredComparisonIsoCore,
    StructuredComparisonIsoCore.ofRelationCore,
    StructuredComparisonRelationCore.comparisonIsoWitness,
    boolFinTwoBoolComposedRelationCore,
    finTwoBoolRelationCore,
    boolFinTwoRelationCore,
    StructuredComparisonRelationCore.compose,
    boolFinTwoBoolComposedRelationFunctorialityData,
    StructuredComparisonFunctorialityData.ofBasicFunctoriality,
    boolToFinTwo, finTwoToBool] using
    composedRelationCore_supplies_ticket
      boolFinTwoRelationCore
      finTwoBoolRelationCore
      rfl
      boolFinTwoBoolComposedRelationFunctorialityData
      mockStructuredComparisonCompatibilityData

/-- The finite composed Bool -> Fin 2 -> Bool relation core reaches the existing structured
realization package path. -/
theorem boolFinTwoBoolComposedRelationCore_supplies_structuredPackage
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms) :
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      (boolFinTwoBoolComposedRelationTicket.toStructuredRealizationInputData
        targetData comparisonData)).structuredRealizationConsequence =
        mockStructuredComparisonCompatibilityData.structuredFaithfulness ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      (boolFinTwoBoolComposedRelationTicket.toStructuredRealizationInputData
        targetData comparisonData)).realizationFunctorsInfinity =
        boolFinTwoBoolComposedRelationFunctorialityData.realizationFunctorsInfinity ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      (boolFinTwoBoolComposedRelationTicket.toStructuredRealizationInputData
        targetData comparisonData)).realizationFunctorsPiZero =
        boolFinTwoBoolComposedRelationFunctorialityData.realizationFunctorsPiZero := by
  simpa [boolFinTwoBoolComposedRelationTicket, relationStructuredComparisonIsoCore,
    StructuredComparisonIsoCore.ofRelationCore,
    StructuredComparisonRelationCore.comparisonIsoWitness,
    boolFinTwoBoolComposedRelationCore,
    finTwoBoolRelationCore,
    boolFinTwoRelationCore,
    StructuredComparisonRelationCore.compose,
    boolFinTwoBoolComposedRelationFunctorialityData,
    StructuredComparisonFunctorialityData.ofBasicFunctoriality,
    boolToFinTwo, finTwoToBool] using
    composedRelationCore_supplies_structuredPackage
      targetData comparisonData
      boolFinTwoRelationCore
      finTwoBoolRelationCore
      rfl
      boolFinTwoBoolComposedRelationFunctorialityData
      mockStructuredComparisonCompatibilityData

/-- The finite composed Bool -> Fin 2 -> Bool relation is accepted by the downstream J.1 ticket
surface as the same comparison-map surface as the expected Bool identity relation. -/
theorem boolFinTwoBoolComposedRelationTicket_supplies_identityComparisonMap :
    boolFinTwoBoolComposedRelationTicket.comparisonMap =
      (identityStructuredComparisonIsoCore Bool).comparisonMap := by
  calc
    boolFinTwoBoolComposedRelationTicket.comparisonMap =
        (relationStructuredComparisonIsoCore boolFinTwoBoolComposedRelationCore).comparisonMap := rfl
    _ = (fun b₁ b₂ : Bool => b₁ = b₂) :=
      relationAgreement_ofRelationCore_respects_comparisonMap
        boolFinTwoBoolComposedRelationCore
        boolFinTwoBoolComposedRelationCore_agrees_with_identityRelation
    _ = (identityStructuredComparisonIsoCore Bool).comparisonMap := rfl

/-- The finite composed Bool -> Fin 2 -> Bool ticket can be substituted for the Bool identity
ticket at the Layer D structured-realization package surface. -/
theorem boolFinTwoBoolComposedRelationTicket_supplies_identityStructuredPackageSurface
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms) :
    LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      (boolFinTwoBoolComposedRelationTicket.toStructuredRealizationInputData
        targetData comparisonData) =
    LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      ((StructuredComparisonImplementationTicket.ofIsoCore
          (identityStructuredComparisonIsoCore Bool)
          mockStructuredComparisonFunctorialityData
          mockStructuredComparisonCompatibilityData).toStructuredRealizationInputData
        targetData comparisonData) := by
  rfl

/-- Minimal sanity instantiation of the J.1 implementation ticket. This demonstrates that the
comparison-isomorphism constructor is usable end-to-end without asserting any motivic content. -/
def mockStructuredComparisonTicket : StructuredComparisonImplementationTicket.{0, 0} :=
  StructuredComparisonImplementationTicket.ofIsoCore
    mockStructuredComparisonIsoCore
    mockStructuredComparisonFunctorialityData
    mockStructuredComparisonCompatibilityData

/-- The structured realization package induced by the minimal J.1 sanity ticket. -/
def mockStructuredComparisonStructuredPackage
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms) :
    LayerD.StructuredRealizationPackage :=
  LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
    (StructuredComparisonImplementationTicket.toStructuredRealizationInputData
      targetData comparisonData mockStructuredComparisonTicket)

/-- The minimal J.1 sanity ticket reaches the existing structured realization package path. -/
theorem mockStructuredComparisonTicket_supplies_structuredPackage
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms) :
    (mockStructuredComparisonStructuredPackage targetData comparisonData).structuredRealizationConsequence =
      True ∧
    (mockStructuredComparisonStructuredPackage targetData comparisonData).realizationFunctorsInfinity =
      True ∧
    (mockStructuredComparisonStructuredPackage targetData comparisonData).realizationFunctorsPiZero =
      True := by
  simpa [mockStructuredComparisonStructuredPackage, mockStructuredComparisonTicket,
    mockStructuredComparisonIsoCore, mockStructuredComparisonFunctorialityData,
    boolIdentityStructuredComparisonIsoCore,
    identityStructuredComparisonIsoCore,
    StructuredComparisonIsoCore.identity,
    mockStructuredComparisonCompatibilityData,
    StructuredComparisonFunctorialityData.ofBasicFunctoriality,
    StructuredComparisonCompatibilityData.ofBasicCompatibility,
    StructuredComparisonImplementationTicket.ofIsoCore] using
    StructuredComparisonImplementationTicket.ofIsoCore_supplies_structuredRealizationPackage
      targetData comparisonData
      mockStructuredComparisonIsoCore
      mockStructuredComparisonFunctorialityData
      mockStructuredComparisonCompatibilityData

end LayerF
end TraceCalc