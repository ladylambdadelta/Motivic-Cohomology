import Boundary.PolynomialSmoothness.JacobianTransport
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.MvPolynomial.Equiv

universe u

-- Root-level extensions of the mathlib algebra owner namespaces.

noncomputable section

-- No `Boundary` namespace is opened in this file.

namespace Algebra.Generators

/-- Given a split of the generator variables into `σ ⊕ τ`, the `τ`-variables
induce the polynomial-base algebra map `R[τ] -> S`. -/
noncomputable def splitBaseAlgHom
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Generators R S)
    {σ τ : Type u}
    (e : P.vars ≃ σ ⊕ τ) :
    MvPolynomial τ R →ₐ[R] S :=
  MvPolynomial.aeval (fun t => P.val (e.symm (Sum.inr t)))

/-- Given a split of the generator variables into `σ ⊕ τ`, rewrite the
section as a polynomial in the `σ`-variables with coefficients in `R[τ]`. -/
noncomputable def splitSection
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Generators R S)
    {σ τ : Type u}
    (e : P.vars ≃ σ ⊕ τ) :
    S → MvPolynomial σ (MvPolynomial τ R) :=
  fun s =>
    MvPolynomial.sumAlgEquiv R σ τ
      (MvPolynomial.renameEquiv R e (P.σ s))

/-- The ring of polynomials in the original variables is canonically
identified with polynomials in the left variables with coefficients in the
polynomial ring on the right variables. -/
noncomputable def splitRingEquiv
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Generators R S)
    {σ τ : Type u}
    (e : P.vars ≃ σ ⊕ τ) :
    P.Ring ≃ₐ[R] MvPolynomial σ (MvPolynomial τ R) :=
  (MvPolynomial.renameEquiv R e).trans (MvPolynomial.sumAlgEquiv R σ τ)

/-- Evaluating the transformed section against the left variables and the base
algebra map coming from the right variables recovers the original element. -/
theorem aeval_splitSection
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Generators R S)
    {σ τ : Type u}
    (e : P.vars ≃ σ ⊕ τ) :
    letI : Algebra (MvPolynomial τ R) S := (P.splitBaseAlgHom e).toAlgebra
    ∀ s, MvPolynomial.aeval (fun i => P.val (e.symm (Sum.inl i))) (P.splitSection e s) = s := by
  classical
  let leftVal : σ → S := fun i => P.val (e.symm (Sum.inl i))
  let rightVal : τ → S := fun j => P.val (e.symm (Sum.inr j))
  let base : MvPolynomial τ R →ₐ[R] S := MvPolynomial.aeval rightVal
  letI : Algebra (MvPolynomial τ R) S := base.toAlgebra
  letI : IsScalarTower R (MvPolynomial τ R) S := IsScalarTower.of_algHom base
  have hcomp :
      ((MvPolynomial.aeval leftVal).restrictScalars R).comp
          (MvPolynomial.sumAlgEquiv R σ τ).toAlgHom =
      MvPolynomial.aeval (Sum.elim leftVal rightVal) := by
      apply MvPolynomial.algHom_ext
      intro x
      cases x with
      | inl i =>
          rw [AlgHom.comp_apply]
          change MvPolynomial.aeval leftVal
              (MvPolynomial.sumToIter R σ τ (MvPolynomial.X (Sum.inl i))) =
            MvPolynomial.aeval (Sum.elim leftVal rightVal) (MvPolynomial.X (Sum.inl i))
          rw [MvPolynomial.sumToIter_Xl, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
          rfl
      | inr j =>
          rw [AlgHom.comp_apply]
          change MvPolynomial.aeval leftVal
              (MvPolynomial.sumToIter R σ τ (MvPolynomial.X (Sum.inr j))) =
            MvPolynomial.aeval (Sum.elim leftVal rightVal) (MvPolynomial.X (Sum.inr j))
          rw [MvPolynomial.sumToIter_Xr, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
          change (algebraMap (MvPolynomial τ R) S) (MvPolynomial.X j) = rightVal j
          rw [RingHom.algebraMap_toAlgebra]
          exact MvPolynomial.aeval_X rightVal j
  intro s
  calc
    MvPolynomial.aeval leftVal (P.splitSection e s)
        = MvPolynomial.aeval (Sum.elim leftVal rightVal) (MvPolynomial.renameEquiv R e (P.σ s)) := by
            exact AlgHom.congr_fun hcomp (MvPolynomial.renameEquiv R e (P.σ s))
    _ = MvPolynomial.aeval (fun v => P.val v) (P.σ s) := by
          have hrename :
              (MvPolynomial.aeval (R := R) (Sum.elim leftVal rightVal)).comp
                  (MvPolynomial.rename e) =
                MvPolynomial.aeval (R := R) (fun v => P.val v) := by
            apply MvPolynomial.algHom_ext
            intro v
            rw [AlgHom.comp_apply, MvPolynomial.rename_X, MvPolynomial.aeval_X,
              MvPolynomial.aeval_X]
            rcases h : e v with i | j
            · change P.val (e.symm (Sum.inl i)) = P.val v
              rw [← h, e.symm_apply_apply]
            · change P.val (e.symm (Sum.inr j)) = P.val v
              rw [← h, e.symm_apply_apply]
          exact AlgHom.congr_fun hrename (P.σ s)
    _ = s := P.aeval_val_σ s

/-- Evaluating after transporting polynomials through the split ring
equivalence agrees with the original evaluation map. -/
theorem aeval_splitRingEquiv
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Generators R S)
    {σ τ : Type u}
    (e : P.vars ≃ σ ⊕ τ) :
    letI : Algebra (MvPolynomial τ R) S := (P.splitBaseAlgHom e).toAlgebra
    ((MvPolynomial.aeval (fun i => P.val (e.symm (Sum.inl i)))).restrictScalars R).comp
        (P.splitRingEquiv e).toAlgHom =
      MvPolynomial.aeval P.val := by
  classical
  let leftVal : σ → S := fun i => P.val (e.symm (Sum.inl i))
  let rightVal : τ → S := fun j => P.val (e.symm (Sum.inr j))
  letI : Algebra (MvPolynomial τ R) S := (P.splitBaseAlgHom e).toAlgebra
  letI : IsScalarTower R (MvPolynomial τ R) S := IsScalarTower.of_algHom (P.splitBaseAlgHom e)
  apply MvPolynomial.algHom_ext
  intro v
  rw [AlgHom.comp_apply, MvPolynomial.aeval_X]
  change ((MvPolynomial.aeval leftVal).restrictScalars R)
      (((MvPolynomial.renameEquiv R e).trans (MvPolynomial.sumAlgEquiv R σ τ))
        (MvPolynomial.X v)) = P.val v
  rw [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  rcases h : e v with i | j
  · change ((MvPolynomial.aeval leftVal).restrictScalars R)
        ((MvPolynomial.sumAlgEquiv R σ τ) (MvPolynomial.X (Sum.inl i))) = P.val v
    change MvPolynomial.aeval leftVal
        (MvPolynomial.sumToIter R σ τ (MvPolynomial.X (Sum.inl i))) = P.val v
    rw [MvPolynomial.sumToIter_Xl, MvPolynomial.aeval_X]
    change P.val (e.symm (Sum.inl i)) = P.val v
    rw [← h, e.symm_apply_apply]
  · change ((MvPolynomial.aeval leftVal).restrictScalars R)
        ((MvPolynomial.sumAlgEquiv R σ τ) (MvPolynomial.X (Sum.inr j))) = P.val v
    change MvPolynomial.aeval leftVal
        (MvPolynomial.sumToIter R σ τ (MvPolynomial.X (Sum.inr j))) = P.val v
    rw [MvPolynomial.sumToIter_Xr, MvPolynomial.aeval_C]
    change (algebraMap (MvPolynomial τ R) S) (MvPolynomial.X j) = P.val v
    rw [RingHom.algebraMap_toAlgebra]
    change MvPolynomial.aeval rightVal (MvPolynomial.X j) = P.val v
    rw [MvPolynomial.aeval_X]
    change P.val (e.symm (Sum.inr j)) = P.val v
    rw [← h, e.symm_apply_apply]

/-- After splitting the variables as `σ ⊕ τ`, the left variables form a
generator family of `S` over the polynomial base `R[τ]`. -/
noncomputable def splitGenerators
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Generators R S)
    {σ τ : Type u}
    (e : P.vars ≃ σ ⊕ τ) :
    letI : Algebra (MvPolynomial τ R) S := (P.splitBaseAlgHom e).toAlgebra
    Algebra.Generators (MvPolynomial τ R) S := by
  classical
  letI : Algebra (MvPolynomial τ R) S := (P.splitBaseAlgHom e).toAlgebra
  refine Algebra.Generators.ofSurjective (fun i => P.val (e.symm (Sum.inl i))) ?_
  intro s
  exact ⟨P.splitSection e s, P.aeval_splitSection e s⟩

theorem splitGenerators_val
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Generators R S)
    {σ τ : Type u}
    (e : P.vars ≃ σ ⊕ τ)
    (i : σ) :
    letI : Algebra (MvPolynomial τ R) S := (P.splitBaseAlgHom e).toAlgebra
    (P.splitGenerators e).val i = P.val (e.symm (Sum.inl i)) :=
  rfl

end Algebra.Generators

namespace MvPolynomial

/-- `sumAlgEquiv` commutes with partial derivatives in the left variables. -/
  theorem pderiv_sumAlgEquiv_inl
      {R σ τ : Type u} [CommRing R]
      (i : σ) (p : MvPolynomial (σ ⊕ τ) R) :
      MvPolynomial.pderiv i ((MvPolynomial.sumAlgEquiv R σ τ) p) =
        (MvPolynomial.sumAlgEquiv R σ τ) (MvPolynomial.pderiv (Sum.inl i) p) := by
    change
      MvPolynomial.pderiv i
          (MvPolynomial.sumToIter R σ τ p) =
        MvPolynomial.sumToIter R σ τ (MvPolynomial.pderiv (Sum.inl i) p)
    exact
      (MvPolynomial.aeval_sum_elim_pderiv_inl
        (S := MvPolynomial τ R) (p := p)
        (f := fun j => (MvPolynomial.X j : MvPolynomial τ R)) (j := i)).symm

end MvPolynomial

namespace Algebra.Presentation

/-- Transport a presentation across a split of its variable type into
`σ ⊕ τ`, reinterpreting it as a presentation over the polynomial base
`R[τ]` on the left variables `σ`. -/
noncomputable def split
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Presentation R S)
    {σ τ : Type u}
    (e : P.vars ≃ σ ⊕ τ) :
    letI : Algebra (MvPolynomial τ R) S := (P.toGenerators.splitBaseAlgHom e).toAlgebra
    Algebra.Presentation (MvPolynomial τ R) S := by
  letI : Algebra (MvPolynomial τ R) S := (P.toGenerators.splitBaseAlgHom e).toAlgebra
  letI : IsScalarTower R (MvPolynomial τ R) S :=
    IsScalarTower.of_algHom (P.toGenerators.splitBaseAlgHom e)
  refine {
  toGenerators := P.toGenerators.splitGenerators e
  rels := P.rels
  relation := fun r => P.toGenerators.splitRingEquiv e (P.relation r)
  span_range_relation_eq_ker := ?_ }
  ·
    classical
    let φ := (P.toGenerators.splitRingEquiv e).toAlgHom
    let newVal : σ → S := fun i => P.val (e.symm (Sum.inl i))
    letI : Algebra (MvPolynomial τ R) S := (P.toGenerators.splitBaseAlgHom e).toAlgebra
    letI : IsScalarTower R (MvPolynomial τ R) S :=
      IsScalarTower.of_algHom (P.toGenerators.splitBaseAlgHom e)
    have hcomp :
        ((MvPolynomial.aeval newVal).restrictScalars R).comp φ = MvPolynomial.aeval P.val :=
      P.toGenerators.aeval_splitRingEquiv e
    calc
      Ideal.span (Set.range fun r => φ (P.relation r))
          = Ideal.map φ.toRingHom (Ideal.span (Set.range P.relation)) := by
              rw [Ideal.map_span]
              congr
              ext x
              constructor
              · rintro ⟨r, rfl⟩
                exact ⟨P.relation r, ⟨r, rfl⟩, rfl⟩
              · rintro ⟨x, ⟨r, rfl⟩, rfl⟩
                exact ⟨r, rfl⟩
      _ = Ideal.map φ.toRingHom P.toGenerators.ker := by
            rw [P.span_range_relation_eq_ker]
      _ = RingHom.ker (((MvPolynomial.aeval newVal).restrictScalars R).toRingHom) := by
            rw [Generators.ker_eq_ker_aeval_val]
            have hk :
                Ideal.comap φ.toRingHom
                    (RingHom.ker (((MvPolynomial.aeval newVal).restrictScalars R).toRingHom)) =
                  RingHom.ker (MvPolynomial.aeval P.val) := by
              change Ideal.comap φ.toRingHom
                  (RingHom.ker (((MvPolynomial.aeval newVal).restrictScalars R).toRingHom)) =
                RingHom.ker (MvPolynomial.aeval P.val)
              rw [RingHom.comap_ker]
              exact congrArg RingHom.ker (congrArg AlgHom.toRingHom hcomp)
            rw [← hk, Ideal.map_comap_of_surjective φ.toRingHom
              (AlgEquiv.surjective (P.toGenerators.splitRingEquiv e))]
      _ = RingHom.ker (MvPolynomial.aeval newVal) := rfl

end Algebra.Presentation

namespace Algebra.PreSubmersivePresentation

/-- If a presubmersive presentation has its variables split as
`rels ⊕ τ`, with the distinguished map landing in the left summand, then it
may be reinterpreted as a presubmersive presentation over the polynomial base
`R[τ]` whose relation-to-variable map is the identity. -/
noncomputable def split
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    {τ : Type u}
    (e : P.vars ≃ P.rels ⊕ τ)
    (he : ∀ r, e (P.map r) = Sum.inl r) :
    letI : Algebra (MvPolynomial τ R) S := (P.toGenerators.splitBaseAlgHom e).toAlgebra
    Algebra.PreSubmersivePresentation (MvPolynomial τ R) S := by
  letI : Algebra (MvPolynomial τ R) S := (P.toGenerators.splitBaseAlgHom e).toAlgebra
  letI : IsScalarTower R (MvPolynomial τ R) S :=
    IsScalarTower.of_algHom (P.toGenerators.splitBaseAlgHom e)
  exact {
    toPresentation := P.toPresentation.split e
    map := fun r => r
    map_inj := fun _ _ h => h
    relations_finite := P.relations_finite }

/-- The split presubmersive presentation has relative dimension `0`. -/
theorem split_dimension_zero
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    [P.IsFinite]
    {τ : Type u}
    (e : P.vars ≃ P.rels ⊕ τ)
    (he : ∀ r, e (P.map r) = Sum.inl r) :
    letI : Algebra (MvPolynomial τ R) S := (P.toGenerators.splitBaseAlgHom e).toAlgebra
    (P.split e he).dimension = 0 := by
  classical
  letI : Algebra (MvPolynomial τ R) S := (P.toGenerators.splitBaseAlgHom e).toAlgebra
  letI : IsScalarTower R (MvPolynomial τ R) S :=
    IsScalarTower.of_algHom (P.toGenerators.splitBaseAlgHom e)
  change Nat.card P.rels - Nat.card P.rels = 0
  rw [Nat.sub_self]

theorem split_jacobiMatrix_apply
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    {τ : Type u}
    (e : P.vars ≃ P.rels ⊕ τ)
    (he : ∀ r, e (P.map r) = Sum.inl r)
    [Fintype P.rels] [DecidableEq P.rels]
    (i j : P.rels) :
    letI : Algebra (MvPolynomial τ R) S := (P.toGenerators.splitBaseAlgHom e).toAlgebra
    letI : Fintype (P.split e he).rels := inferInstanceAs (Fintype P.rels)
    algebraMap (P.split e he).Ring S ((P.split e he).jacobiMatrix i j) =
      algebraMap P.Ring S (P.jacobiMatrix i j) := by
  classical
  let leftVal : P.rels → S := fun r => P.val (e.symm (Sum.inl r))
  let rightVal : τ → S := fun t => P.val (e.symm (Sum.inr t))
  letI : Algebra (MvPolynomial τ R) S := (P.toGenerators.splitBaseAlgHom e).toAlgebra
  letI : IsScalarTower R (MvPolynomial τ R) S :=
    IsScalarTower.of_algHom (P.toGenerators.splitBaseAlgHom e)
  have hsum :
      ((MvPolynomial.aeval leftVal).restrictScalars R).comp
          (MvPolynomial.sumAlgEquiv R P.rels τ).toAlgHom =
        MvPolynomial.aeval (Sum.elim leftVal rightVal) := by
      apply MvPolynomial.algHom_ext
      intro x
      cases x with
      | inl r =>
          rw [AlgHom.comp_apply]
          change MvPolynomial.aeval leftVal
              (MvPolynomial.sumToIter R P.rels τ (MvPolynomial.X (Sum.inl r))) =
            MvPolynomial.aeval (Sum.elim leftVal rightVal) (MvPolynomial.X (Sum.inl r))
          rw [MvPolynomial.sumToIter_Xl, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
          rfl
      | inr t =>
          rw [AlgHom.comp_apply]
          change MvPolynomial.aeval leftVal
              (MvPolynomial.sumToIter R P.rels τ (MvPolynomial.X (Sum.inr t))) =
            MvPolynomial.aeval (Sum.elim leftVal rightVal) (MvPolynomial.X (Sum.inr t))
          rw [MvPolynomial.sumToIter_Xr, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
          change (algebraMap (MvPolynomial τ R) S) (MvPolynomial.X t) = rightVal t
          rw [RingHom.algebraMap_toAlgebra]
          exact MvPolynomial.aeval_X rightVal t
  have hrename :
      (MvPolynomial.aeval (R := R) (Sum.elim leftVal rightVal)).comp (MvPolynomial.rename e) =
        MvPolynomial.aeval (R := R) P.val := by
    apply MvPolynomial.algHom_ext
    intro v
    rcases hv : e v with r | t
    · rw [AlgHom.comp_apply, MvPolynomial.rename_X, MvPolynomial.aeval_X,
        MvPolynomial.aeval_X]
      rw [hv]
      change P.val (e.symm (Sum.inl r)) = P.val v
      rw [← hv, e.symm_apply_apply]
    · rw [AlgHom.comp_apply, MvPolynomial.rename_X, MvPolynomial.aeval_X,
        MvPolynomial.aeval_X]
      rw [hv]
      change P.val (e.symm (Sum.inr t)) = P.val v
      rw [← hv, e.symm_apply_apply]
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
    Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  change MvPolynomial.aeval leftVal (MvPolynomial.pderiv i
      ((P.toGenerators.splitRingEquiv e) (P.relation j))) =
    MvPolynomial.aeval P.val (MvPolynomial.pderiv (P.map i) (P.relation j))
  rw [Algebra.Generators.splitRingEquiv]
  change MvPolynomial.aeval leftVal
      (MvPolynomial.pderiv i
        ((MvPolynomial.sumAlgEquiv R P.rels τ)
          ((MvPolynomial.renameEquiv R e) (P.relation j)))) =
    MvPolynomial.aeval P.val (MvPolynomial.pderiv (P.map i) (P.relation j))
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.pderiv_sumAlgEquiv_inl]
  have hcomp :
      (((MvPolynomial.aeval leftVal).restrictScalars R).comp
          (MvPolynomial.sumAlgEquiv R P.rels τ).toAlgHom)
        (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.rename e (P.relation j))) =
      MvPolynomial.aeval (Sum.elim leftVal rightVal)
        (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.rename e (P.relation j))) :=
    AlgHom.congr_fun hsum
      (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.rename e (P.relation j)))
  change (((MvPolynomial.aeval leftVal).restrictScalars R).comp
      (MvPolynomial.sumAlgEquiv R P.rels τ).toAlgHom)
          (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.rename e (P.relation j))) =
      MvPolynomial.aeval P.val (MvPolynomial.pderiv (P.map i) (P.relation j))
  rw [hcomp]
  have hpderivRename :
      MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.rename e (P.relation j)) =
        MvPolynomial.rename e (MvPolynomial.pderiv (P.map i) (P.relation j)) := by
    rw [← he i]
    exact MvPolynomial.pderiv_rename e.injective (P.map i) (P.relation j)
  rw [hpderivRename]
  exact AlgHom.congr_fun hrename (MvPolynomial.pderiv (P.map i) (P.relation j))

theorem split_jacobian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    {τ : Type u}
    (e : P.vars ≃ P.rels ⊕ τ)
    (he : ∀ r, e (P.map r) = Sum.inl r)
    [Fintype P.rels] [DecidableEq P.rels] :
    letI : Algebra (MvPolynomial τ R) S := (P.toGenerators.splitBaseAlgHom e).toAlgebra
    letI : Fintype (P.split e he).rels := inferInstanceAs (Fintype P.rels)
    (P.split e he).jacobian = P.jacobian := by
  classical
  letI : Algebra (MvPolynomial τ R) S := (P.toGenerators.splitBaseAlgHom e).toAlgebra
  letI : Fintype (P.split e he).rels := inferInstanceAs (Fintype P.rels)
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have hM :
      (algebraMap (P.split e he).Ring S).mapMatrix (P.split e he).jacobiMatrix =
        (algebraMap P.Ring S).mapMatrix P.jacobiMatrix := by
    ext i j
    exact P.split_jacobiMatrix_apply e he i j
  rw [RingHom.map_det, RingHom.map_det, hM]
  rfl

end Algebra.PreSubmersivePresentation

end

-- The `Boundary` namespace is closed before the root-level algebra extensions.
