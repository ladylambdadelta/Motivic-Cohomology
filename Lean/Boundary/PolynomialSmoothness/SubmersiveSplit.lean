import Boundary.PolynomialSmoothness.PresentationCombinatorics

universe u w

namespace Boundary

noncomputable section

namespace _root_.Algebra
namespace IsStandardSmoothOfRelativeDimension

/-- The canonical splitting attached to a submersive presentation: variables
are the image of the relation-to-variable map, hence the relations themselves,
together with the complementary variables. -/
noncomputable def submersivePresentationSplit
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.SubmersivePresentation.{u, w} R S) :
    P.vars ≃ P.rels ⊕
      { v : P.vars // v ∉ Set.range P.toPreSubmersivePresentation.map } :=
  by
    let PP : Algebra.PreSubmersivePresentation R S := P.toPreSubmersivePresentation
    letI : Fintype PP.rels := Fintype.ofFinite PP.rels
    exact Algebra.PreSubmersivePresentation.varsEquivRelationsSumComplement
      (R := R) (S := S) PP

/-- The canonical splitting sends the variable attached to a relation to the
left summand. -/
theorem submersivePresentationSplit_apply_map
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.SubmersivePresentation.{u, w} R S) (r : P.rels) :
    submersivePresentationSplit P (P.toPreSubmersivePresentation.map r) = Sum.inl r := by
  let PP : Algebra.PreSubmersivePresentation R S := P.toPreSubmersivePresentation
  letI : Fintype PP.rels := Fintype.ofFinite PP.rels
  change
    Algebra.PreSubmersivePresentation.varsEquivRelationsSumComplement
        (R := R) (S := S) PP (PP.map r) = Sum.inl r
  exact Algebra.PreSubmersivePresentation.varsEquivRelationsSumComplement_apply_map
    (R := R) (S := S) PP r

/-- The complementary variables in the canonical splitting have cardinality
equal to the relative dimension of the presentation. -/
theorem submersivePresentationSplit_complement_card
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.SubmersivePresentation.{u, w} R S) :
    Nat.card { v : P.vars // v ∉ Set.range P.toPreSubmersivePresentation.map } =
      P.dimension := by
  exact Algebra.PreSubmersivePresentation.card_complement_eq_dimension
    (R := R) (S := S) P.toPreSubmersivePresentation

/-- In relative dimension zero the canonical complement is empty. -/
theorem submersivePresentationSplit_complement_isEmpty_of_dimension_zero
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.SubmersivePresentation.{u, w} R S)
    (hP : P.dimension = 0) :
    IsEmpty { v : P.vars // v ∉ Set.range P.toPreSubmersivePresentation.map } := by
  letI : Finite { v : P.vars // v ∉ Set.range P.toPreSubmersivePresentation.map } :=
    inferInstance
  have hcard :
      Nat.card { v : P.vars // v ∉ Set.range P.toPreSubmersivePresentation.map } = 0 := by
    rw [submersivePresentationSplit_complement_card P, hP]
  exact Finite.card_eq_zero_iff.mp hcard

/-- A standard-smooth algebra of relative dimension `n` admits a submersive
presentation whose variable type splits as relations together with `n` free
variables, and the relation-to-variable map identifies with the left summand
under the canonical range-complement splitting. -/
theorem exists_submersivePresentation_split
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension.{u, w} n R S] :
    ∃ (P : Algebra.SubmersivePresentation.{u, w} R S)
      (τ : Type w)
      (_ : Finite τ)
      (e : P.vars ≃ P.rels ⊕ τ),
      (∀ r, e (P.toPreSubmersivePresentation.map r) = Sum.inl r) ∧ Nat.card τ = n := by
  obtain ⟨P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension n R S›.out
  let τ : Type w := { v : P.vars // v ∉ Set.range P.toPreSubmersivePresentation.map }
  let e : P.vars ≃ P.rels ⊕ τ := submersivePresentationSplit P
  letI : Finite τ := inferInstance
  refine ⟨P, τ, inferInstance, e, ?_, ?_⟩
  · intro r
    exact submersivePresentationSplit_apply_map P r
  · calc
      Nat.card τ = P.dimension := submersivePresentationSplit_complement_card P
      _ = n := hP

/-- A standard-smooth algebra of relative dimension `0` admits a submersive
presentation whose relation-to-variable map is bijective. -/
theorem exists_submersivePresentation_map_bijective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmoothOfRelativeDimension.{u, w} 0 R S] :
    ∃ P : Algebra.SubmersivePresentation.{u, w} R S,
      Function.Bijective P.toPreSubmersivePresentation.map := by
  obtain ⟨P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension.{u, w} 0 R S›.out
  refine ⟨P, ?_⟩
  letI : P.toPreSubmersivePresentation.IsFinite := P.isFinite
  exact Algebra.PreSubmersivePresentation.map_bijective_of_dimension_zero
    P.toPreSubmersivePresentation hP

/-- A zero-dimensional submersive presentation has canonically equivalent
relation and variable index types. -/
noncomputable def submersivePresentationMapEquiv
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.SubmersivePresentation.{u, w} R S)
    (hP : P.dimension = 0) :
    P.rels ≃ P.vars := by
  letI : P.toPreSubmersivePresentation.IsFinite := P.isFinite
  exact Algebra.PreSubmersivePresentation.mapEquivOfDimensionZero
    P.toPreSubmersivePresentation hP

end IsStandardSmoothOfRelativeDimension

end _root_.Algebra

end

end Boundary
