import Mathlib.RingTheory.Smooth.StandardSmooth

universe u

namespace Boundary

noncomputable section

namespace _root_.Algebra
namespace PreSubmersivePresentation

/-- In a finite zero-dimensional presubmersive presentation, the distinguished
relation-to-variable map is bijective. The proof is finite cardinal arithmetic:
presubmersiveness gives injectivity and `#rels ≤ #vars`; dimension zero gives
`#vars - #rels = 0`, hence equal cardinalities, and injectivity is equivalent
to surjectivity for finite types of equal size. -/
lemma map_bijective_of_dimension_zero
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    [P.IsFinite]
    (hDim : P.dimension = 0) :
    Function.Bijective P.map := by
  have hle := P.card_relations_le_card_vars_of_isFinite
  have hEqCard : Nat.card P.vars = Nat.card P.rels := by
    have hZero : Nat.card P.vars - Nat.card P.rels = 0 := by
      rw [Algebra.Presentation.dimension] at hDim
      exact hDim
    exact le_antisymm (Nat.sub_eq_zero_iff_le.mp hZero) hle
  letI : Fintype P.vars := Fintype.ofFinite P.vars
  letI : Fintype P.rels := Fintype.ofFinite P.rels
  have hEqFintype : Fintype.card P.rels = Fintype.card P.vars := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hEqCard.symm
  let eCard : P.rels ≃ P.vars := Fintype.equivOfCardEq hEqFintype
  have hsurj : Function.Surjective P.map :=
    (Finite.injective_iff_surjective_of_equiv (f := P.map) eCard).mp P.map_inj
  exact ⟨P.map_inj, hsurj⟩

/-- The canonical equivalence in relative dimension zero is the actual
relation-to-variable map, equipped with the bijectivity proof above. -/
noncomputable def mapEquivOfDimensionZero
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    [P.IsFinite]
    (hDim : P.dimension = 0) :
    P.rels ≃ P.vars :=
  Equiv.ofBijective P.map
    (Algebra.PreSubmersivePresentation.map_bijective_of_dimension_zero P hDim)

/-- The canonical variable split of a presubmersive presentation is the split
into the range of the relation-to-variable map and its complement, with the
range identified with the relation type by the map embedding. -/
noncomputable def varsEquivRelationsSumComplement
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    [Fintype P.rels] :
    P.vars ≃ P.rels ⊕ { v : P.vars // v ∉ Set.range P.map } := by
  classical
  let f : P.rels ↪ P.vars := ⟨P.map, P.map_inj⟩
  let eRange : P.rels ≃ { v : P.vars // v ∈ Set.range P.map } :=
    f.toEquivRange
  refine (Equiv.sumCompl fun v : P.vars => v ∈ Set.range P.map).symm.trans ?_
  exact Equiv.sumCongr eRange.symm (Equiv.refl _)

/-- Under the canonical range-complement split, the variable selected by a
relation lies in the relation summand as that relation. -/
theorem varsEquivRelationsSumComplement_apply_map
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    [Fintype P.rels]
    (r : P.rels) :
    Algebra.PreSubmersivePresentation.varsEquivRelationsSumComplement
      (R := R) (S := S) P (P.map r) = Sum.inl r := by
  classical
  let f : P.rels ↪ P.vars := ⟨P.map, P.map_inj⟩
  let eRange : P.rels ≃ { v : P.vars // v ∈ Set.range P.map } :=
    f.toEquivRange
  change
    (Equiv.sumCongr eRange.symm (Equiv.refl _))
        ((Equiv.sumCompl fun v : P.vars => v ∈ Set.range P.map).symm (P.map r))
      = Sum.inl r
  rw [Equiv.sumCompl_apply_symm_of_pos]
  · have hsub :
        (⟨P.map r, ⟨r, rfl⟩⟩ : Set.range P.map) =
          ⟨P.map r, Set.mem_range_self r⟩ := Subtype.ext rfl
    rw [hsub]
    exact congrArg Sum.inl
      (Function.Embedding.toEquivRange_symm_apply_self f r)

/-- The complement in the canonical range-complement split has cardinality
equal to the presentation dimension. -/
theorem card_complement_eq_dimension
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S) [P.IsFinite] :
    Nat.card { v : P.vars // v ∉ Set.range P.map } = P.toPresentation.dimension := by
  letI : Finite P.vars := ‹P.IsFinite›.finite_vars
  letI : Finite P.rels := ‹P.IsFinite›.finite_rels
  letI : Fintype P.rels := Fintype.ofFinite P.rels
  let e := Algebra.PreSubmersivePresentation.varsEquivRelationsSumComplement
    (R := R) (S := S) P
  have hcard :
      Nat.card P.vars =
        Nat.card P.rels + Nat.card { v : P.vars // v ∉ Set.range P.map } := by
    rw [← Nat.card_sum]
    exact Nat.card_congr e
  rw [Algebra.Presentation.dimension, hcard]
  exact
    (Nat.add_sub_cancel_left
      (Nat.card P.rels)
      (Nat.card { v : P.vars // v ∉ Set.range P.map })).symm

/-- In dimension zero, the complementary-variable type in the canonical split
is empty. -/
theorem complement_isEmpty_of_dimension_zero
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S) [P.IsFinite]
    (hDim : P.dimension = 0) :
    IsEmpty { v : P.vars // v ∉ Set.range P.map } := by
  have hcard : Nat.card { v : P.vars // v ∉ Set.range P.map } = 0 := by
    rw [Algebra.PreSubmersivePresentation.card_complement_eq_dimension P, hDim]
  letI : Finite { v : P.vars // v ∉ Set.range P.map } := inferInstance
  exact Finite.card_eq_zero_iff.mp hcard

end PreSubmersivePresentation
end _root_.Algebra

end

end Boundary
