import Boundary.PolynomialReduction
import Boundary.PolynomialReductionRelation
import Boundary.PolynomialNormalForm

noncomputable section

open scoped MonomialOrder

namespace Boundary
namespace PolynomialGroebnerBasis

variable {σ : Type*} [Fintype σ]
variable [DecidableEq σ]
variable {k : Type*} [Field k]

/-- The least common multiple of two monomials, defined pointwise by `max`. -/
noncomputable def monomialLcm (a b : σ →₀ ℕ) : σ →₀ ℕ :=
  { toFun := fun i => max (a i) (b i)
    support := a.support ∪ b.support
    mem_support_toFun := by
      intro i
      by_cases ha : a i = 0 <;> by_cases hb : b i = 0 <;> simp [ha, hb] }

theorem monomialLcm_left (a b : σ →₀ ℕ) :
    Boundary.PolynomialReduction.monomialDivides a (monomialLcm (σ := σ) a b) := by
  intro i
  simp [monomialLcm]

theorem monomialLcm_right (a b : σ →₀ ℕ) :
    Boundary.PolynomialReduction.monomialDivides b (monomialLcm (σ := σ) a b) := by
  intro i
  simp [monomialLcm]

/-- The `S`-polynomial attached to two polynomials with respect to a fixed monomial order. -/
noncomputable def sPolynomial (m : MonomialOrder σ) (f g : MvPolynomial σ k) :
    MvPolynomial σ k :=
  MvPolynomial.monomial
      (Boundary.PolynomialReduction.monomialQuotient
        (PolynomialGroebnerBasics.leadingMonomial m f)
        (monomialLcm (σ := σ)
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (PolynomialGroebnerBasics.leadingMonomial m g))
        (monomialLcm_left (σ := σ)
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (PolynomialGroebnerBasics.leadingMonomial m g)))
      (PolynomialGroebnerBasics.leadingCoeff m g) * f
    - MvPolynomial.monomial
      (Boundary.PolynomialReduction.monomialQuotient
        (PolynomialGroebnerBasics.leadingMonomial m g)
        (monomialLcm (σ := σ)
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (PolynomialGroebnerBasics.leadingMonomial m g))
        (monomialLcm_right (σ := σ)
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (PolynomialGroebnerBasics.leadingMonomial m g)))
      (PolynomialGroebnerBasics.leadingCoeff m f) * g

theorem sPolynomial_apply
    (m : MonomialOrder σ) (f g : MvPolynomial σ k) :
    sPolynomial (σ := σ) (k := k) m f g =
      MvPolynomial.monomial
        (Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (monomialLcm_left (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g)))
        (PolynomialGroebnerBasics.leadingCoeff m g) * f
        - MvPolynomial.monomial
          (Boundary.PolynomialReduction.monomialQuotient
            (PolynomialGroebnerBasics.leadingMonomial m g)
            (monomialLcm (σ := σ)
              (PolynomialGroebnerBasics.leadingMonomial m f)
              (PolynomialGroebnerBasics.leadingMonomial m g))
            (monomialLcm_right (σ := σ)
              (PolynomialGroebnerBasics.leadingMonomial m f)
              (PolynomialGroebnerBasics.leadingMonomial m g)))
          (PolynomialGroebnerBasics.leadingCoeff m f) * g := by
  rfl

/-- The `S`-polynomial cancels the coefficient at the least common multiple monomial. -/
theorem coeff_sPolynomial_monomialLcm_zero
    (m : MonomialOrder σ) (f g : MvPolynomial σ k) :
    MvPolynomial.coeff
        (monomialLcm (σ := σ)
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (PolynomialGroebnerBasics.leadingMonomial m g))
        (sPolynomial (σ := σ) (k := k) m f g) = 0 := by
  classical
  have hle_f :
      Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (monomialLcm_left (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
        ≤
      monomialLcm (σ := σ)
        (PolynomialGroebnerBasics.leadingMonomial m f)
        (PolynomialGroebnerBasics.leadingMonomial m g) := by
    intro i
    simp [Boundary.PolynomialReduction.monomialQuotient, monomialLcm]
  have hsub_f :
      monomialLcm (σ := σ)
        (PolynomialGroebnerBasics.leadingMonomial m f)
        (PolynomialGroebnerBasics.leadingMonomial m g) -
        Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (monomialLcm_left (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
      =
      PolynomialGroebnerBasics.leadingMonomial m f := by
    simpa [Boundary.PolynomialReduction.monomialQuotient, monomialLcm] using
      (Boundary.PolynomialReduction.monomialQuotient_sub
        (a := PolynomialGroebnerBasics.leadingMonomial m f)
        (b := monomialLcm (σ := σ)
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (PolynomialGroebnerBasics.leadingMonomial m g))
        (monomialLcm_left (σ := σ)
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (PolynomialGroebnerBasics.leadingMonomial m g))
      )
  have hle_g :
      Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m g)
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (monomialLcm_right (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
        ≤
      monomialLcm (σ := σ)
        (PolynomialGroebnerBasics.leadingMonomial m f)
        (PolynomialGroebnerBasics.leadingMonomial m g) := by
    intro i
    simp [Boundary.PolynomialReduction.monomialQuotient, monomialLcm]
  have hsub_g :
      monomialLcm (σ := σ)
        (PolynomialGroebnerBasics.leadingMonomial m f)
        (PolynomialGroebnerBasics.leadingMonomial m g) -
        Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m g)
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (monomialLcm_right (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
      =
      PolynomialGroebnerBasics.leadingMonomial m g := by
    simpa [Boundary.PolynomialReduction.monomialQuotient, monomialLcm] using
      (Boundary.PolynomialReduction.monomialQuotient_sub
        (a := PolynomialGroebnerBasics.leadingMonomial m g)
        (b := monomialLcm (σ := σ)
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (PolynomialGroebnerBasics.leadingMonomial m g))
        (monomialLcm_right (σ := σ)
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (PolynomialGroebnerBasics.leadingMonomial m g))
      )
  have hleft :
      MvPolynomial.coeff
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (MvPolynomial.monomial
            (Boundary.PolynomialReduction.monomialQuotient
              (PolynomialGroebnerBasics.leadingMonomial m f)
              (monomialLcm (σ := σ)
                (PolynomialGroebnerBasics.leadingMonomial m f)
                (PolynomialGroebnerBasics.leadingMonomial m g))
              (monomialLcm_left (σ := σ)
                (PolynomialGroebnerBasics.leadingMonomial m f)
                (PolynomialGroebnerBasics.leadingMonomial m g)))
            (PolynomialGroebnerBasics.leadingCoeff m g) * f)
        = PolynomialGroebnerBasics.leadingCoeff m g *
            PolynomialGroebnerBasics.leadingCoeff m f := by
    have htmp :=
      (MvPolynomial.coeff_monomial_mul'
        (m := monomialLcm (σ := σ)
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (PolynomialGroebnerBasics.leadingMonomial m g))
        (s := Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (monomialLcm_left (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g)))
        (r := PolynomialGroebnerBasics.leadingCoeff m g)
        (p := f))
    rw [if_pos hle_f, hsub_f] at htmp
    simpa [PolynomialGroebnerBasics.leadingCoeff, monomialLcm, mul_comm, mul_left_comm,
      mul_assoc] using htmp
  have hright :
      MvPolynomial.coeff
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (MvPolynomial.monomial
            (Boundary.PolynomialReduction.monomialQuotient
              (PolynomialGroebnerBasics.leadingMonomial m g)
              (monomialLcm (σ := σ)
                (PolynomialGroebnerBasics.leadingMonomial m f)
                (PolynomialGroebnerBasics.leadingMonomial m g))
              (monomialLcm_right (σ := σ)
                (PolynomialGroebnerBasics.leadingMonomial m f)
                (PolynomialGroebnerBasics.leadingMonomial m g)))
            (PolynomialGroebnerBasics.leadingCoeff m f) * g)
        = PolynomialGroebnerBasics.leadingCoeff m f *
            PolynomialGroebnerBasics.leadingCoeff m g := by
    have htmp :=
      (MvPolynomial.coeff_monomial_mul'
        (m := monomialLcm (σ := σ)
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (PolynomialGroebnerBasics.leadingMonomial m g))
        (s := Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m g)
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (monomialLcm_right (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g)))
        (r := PolynomialGroebnerBasics.leadingCoeff m f)
        (p := g))
    rw [if_pos hle_g, hsub_g] at htmp
    simpa [PolynomialGroebnerBasics.leadingCoeff, monomialLcm, mul_comm, mul_left_comm,
      mul_assoc] using htmp
  have hcoeff :
      MvPolynomial.coeff
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (sPolynomial (σ := σ) (k := k) m f g)
      = PolynomialGroebnerBasics.leadingCoeff m g *
          PolynomialGroebnerBasics.leadingCoeff m f -
          PolynomialGroebnerBasics.leadingCoeff m f *
            PolynomialGroebnerBasics.leadingCoeff m g := by
    rw [sPolynomial_apply, MvPolynomial.coeff_sub, hleft, hright]
  rw [hcoeff]
  rw [mul_comm]
  rw [sub_self]

/-!
A finite family is a Gröbner basis if every pairwise `S`-polynomial is not reducible
by the family. This is the self-contained predicate used in the upstream Gröbner layer.
-/
def reducibleByList (m : MonomialOrder σ) (G : List (MvPolynomial σ k))
    (f : MvPolynomial σ k) : Prop :=
  f ≠ 0 ∧ ∃ g ∈ G, Boundary.PolynomialReduction.reducibleByLeadingTerm (m := m) g f

/-- A finite family is a Gröbner basis if every pairwise `S`-polynomial is not reducible
by the family. -/
def IsGroebnerBasis (m : MonomialOrder σ) (G : List (MvPolynomial σ k)) : Prop :=
  ∀ f ∈ G, ∀ g ∈ G, ¬ reducibleByList (σ := σ) (k := k) m G (sPolynomial (σ := σ) (k := k) m f g)

theorem isGroebnerBasis_nil (m : MonomialOrder σ) :
    IsGroebnerBasis (σ := σ) (k := k) m [] := by
  intro f hf
  cases hf

theorem isGroebnerBasis_of_forall_mem
    (m : MonomialOrder σ) (G : List (MvPolynomial σ k))
    (h : ∀ f ∈ G, ∀ g ∈ G,
      ¬ reducibleByList (σ := σ) (k := k) m G (sPolynomial (σ := σ) (k := k) m f g)) :
    IsGroebnerBasis (σ := σ) (k := k) m G := by
  simpa [IsGroebnerBasis] using h

/-- A finite family is a Gröbner basis exactly when all pairwise `S`-polynomials are
not reducible by the family. -/
theorem isGroebnerBasis_iff
    (m : MonomialOrder σ) (G : List (MvPolynomial σ k)) :
    IsGroebnerBasis (σ := σ) (k := k) m G ↔
      ∀ f ∈ G, ∀ g ∈ G, ¬ reducibleByList (σ := σ) (k := k) m G (sPolynomial (σ := σ) (k := k) m f g) := by
  rfl

/-- A reduction criterion: if a family is a Gröbner basis, then every `S`-polynomial is not
reducible by the family. -/
theorem not_reducible_sPolynomial_of_isGroebnerBasis
    (m : MonomialOrder σ) (G : List (MvPolynomial σ k))
    (hG : IsGroebnerBasis (σ := σ) (k := k) m G)
    (f g : MvPolynomial σ k) (hf : f ∈ G) (hg : g ∈ G) :
    ¬ reducibleByList (σ := σ) (k := k) m G (sPolynomial (σ := σ) (k := k) m f g) := by
  intro hred
  exact hG f hf g hg hred

/-- If some pairwise `S`-polynomial is reducible, the family is not a Gröbner basis. -/
theorem not_isGroebnerBasis_of_reducible_sPolynomial
    (m : MonomialOrder σ) (G : List (MvPolynomial σ k))
    (f g : MvPolynomial σ k) (hf : f ∈ G) (hg : g ∈ G)
    (hred : reducibleByList (σ := σ) (k := k) m G (sPolynomial (σ := σ) (k := k) m f g)) :
    ¬ IsGroebnerBasis (σ := σ) (k := k) m G := by
  intro hG
  exact (hG f hf g hg hred)

/-- The `S`-polynomial lies in the ideal generated by the pair `f, g`. -/
theorem sPolynomial_mem_span_pair
    (m : MonomialOrder σ) (f g : MvPolynomial σ k) :
    sPolynomial (σ := σ) (k := k) m f g ∈
      Ideal.span ({f, g} : Set (MvPolynomial σ k)) := by
  classical
  rw [sPolynomial_apply]
  have hf : f ∈ Ideal.span ({f, g} : Set (MvPolynomial σ k)) := by
    exact Ideal.subset_span (by simp)
  have hg : g ∈ Ideal.span ({f, g} : Set (MvPolynomial σ k)) := by
    exact Ideal.subset_span (by simp)
  have hmul_f :
      MvPolynomial.monomial
        (Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (monomialLcm_left (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g)))
        (PolynomialGroebnerBasics.leadingCoeff m g) * f ∈
      Ideal.span ({f, g} : Set (MvPolynomial σ k)) := by
    exact Ideal.mul_mem_left (Ideal.span ({f, g} : Set (MvPolynomial σ k)))
      (MvPolynomial.monomial
        (Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (monomialLcm_left (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g)))
        (PolynomialGroebnerBasics.leadingCoeff m g))
      hf
  have hmul_g :
      MvPolynomial.monomial
        (Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m g)
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (monomialLcm_right (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g)))
        (PolynomialGroebnerBasics.leadingCoeff m f) * g ∈
      Ideal.span ({f, g} : Set (MvPolynomial σ k)) := by
    exact Ideal.mul_mem_left (Ideal.span ({f, g} : Set (MvPolynomial σ k)))
      (MvPolynomial.monomial
        (Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m g)
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (monomialLcm_right (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g)))
        (PolynomialGroebnerBasics.leadingCoeff m f))
      hg
  change
      MvPolynomial.monomial
        (Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (monomialLcm_left (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g)))
        (PolynomialGroebnerBasics.leadingCoeff m g) * f -
      MvPolynomial.monomial
        (Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m g)
          (monomialLcm (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g))
          (monomialLcm_right (σ := σ)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (PolynomialGroebnerBasics.leadingMonomial m g)))
        (PolynomialGroebnerBasics.leadingCoeff m f) * g ∈
      Ideal.span ({f, g} : Set (MvPolynomial σ k))
  exact (Ideal.sub_mem (I := Ideal.span ({f, g} : Set (MvPolynomial σ k))) hmul_f hmul_g)

/-- The `S`-polynomial of a pair lies in the ideal generated by that pair. -/
theorem sPolynomial_mem_pair_span
    (m : MonomialOrder σ) (f g : MvPolynomial σ k) :
    sPolynomial (σ := σ) (k := k) m f g ∈
      Ideal.span ({f, g} : Set (MvPolynomial σ k)) :=
  sPolynomial_mem_span_pair (σ := σ) (k := k) m f g

/-- The `S`-polynomial of two elements of an ideal lies in that ideal. -/
theorem sPolynomial_mem_ideal
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ k))
    {f g : MvPolynomial σ k} (hf : f ∈ I) (hg : g ∈ I) :
    sPolynomial (σ := σ) (k := k) m f g ∈ I := by
  have hspan : Ideal.span ({f, g} : Set (MvPolynomial σ k)) ≤ I := by
    refine Ideal.span_le.mpr ?_
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact hf
    · exact hg
  exact hspan (sPolynomial_mem_pair_span (σ := σ) (k := k) m f g)

/-- Any ideal containing a finite family contains all `S`-polynomials of pairs from that family. -/
theorem sPolynomial_mem_ideal_of_mem
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ k))
    {f g : MvPolynomial σ k} (hf : f ∈ I) (hg : g ∈ I) :
    sPolynomial (σ := σ) (k := k) m f g ∈ I :=
  sPolynomial_mem_ideal (σ := σ) (k := k) m I hf hg

/-- The `S`-polynomial of two members of a finite list lies in the finite list span. -/
theorem sPolynomial_mem_listSpan
    (m : MonomialOrder σ) (G : List (MvPolynomial σ k))
    {f g : MvPolynomial σ k} (hf : f ∈ G) (hg : g ∈ G) :
    sPolynomial (σ := σ) (k := k) m f g ∈
      Boundary.PolynomialNormalForm.listSpan (σ := σ) (k := k) G := by
  have hspan :
      Ideal.span ({f, g} : Set (MvPolynomial σ k)) ≤
        Boundary.PolynomialNormalForm.listSpan (σ := σ) (k := k) G := by
    refine Ideal.span_le.mpr ?_
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact Boundary.PolynomialNormalForm.mem_listSpan_of_mem_list
        (σ := σ) (k := k) (G := G) hf
    · exact Boundary.PolynomialNormalForm.mem_listSpan_of_mem_list
        (σ := σ) (k := k) (G := G) hg
  exact hspan (sPolynomial_mem_span_pair (σ := σ) (k := k) m f g)

/-- The finite list span is closed under `S`-polynomials of its own elements. -/
theorem sPolynomial_mem_listSpan_of_mem
    (m : MonomialOrder σ) (G : List (MvPolynomial σ k))
    {f g : MvPolynomial σ k}
    (hf : f ∈ Boundary.PolynomialNormalForm.listSpan (σ := σ) (k := k) G)
    (hg : g ∈ Boundary.PolynomialNormalForm.listSpan (σ := σ) (k := k) G) :
    sPolynomial (σ := σ) (k := k) m f g ∈
      Boundary.PolynomialNormalForm.listSpan (σ := σ) (k := k) G :=
  sPolynomial_mem_ideal_of_mem (σ := σ) (k := k) m
    (Boundary.PolynomialNormalForm.listSpan (σ := σ) (k := k) G) hf hg

/-- A pairwise `S`-polynomial from a finite list has a division witness with zero remainder. -/
theorem sPolynomial_exists_zero_remainder_of_mem_list
    (m : MonomialOrder σ) (G : List (MvPolynomial σ k))
    {f g : MvPolynomial σ k} (hf : f ∈ G) (hg : g ∈ G) :
    ∃ q : Fin G.length →₀ MvPolynomial σ k,
      ¬ Boundary.PolynomialNormalForm.reducibleByList (m := m) G (0 : MvPolynomial σ k) ∧
      sPolynomial (σ := σ) (k := k) m f g =
        (0 : MvPolynomial σ k) +
          q.sum (fun i a => a * Boundary.PolynomialNormalForm.listGenerators
            (σ := σ) (k := k) G i) := by
  have hmem :
      sPolynomial (σ := σ) (k := k) m f g ∈
        Boundary.PolynomialNormalForm.listSpan (σ := σ) (k := k) G :=
    sPolynomial_mem_listSpan (σ := σ) (k := k) m G hf hg
  exact Boundary.PolynomialNormalForm.exists_division_zero_remainder_of_mem_listSpan
    (σ := σ) (k := k) m G hmem

/-- A Gröbner basis gives zero-remainder division witnesses for all pairwise `S`-polynomials. -/
theorem sPolynomial_exists_zero_remainder_of_isGroebnerBasis
    (m : MonomialOrder σ) (G : List (MvPolynomial σ k))
    (hG : IsGroebnerBasis (σ := σ) (k := k) m G)
    {f g : MvPolynomial σ k} (hf : f ∈ G) (hg : g ∈ G) :
    ∃ q : Fin G.length →₀ MvPolynomial σ k,
      ¬ Boundary.PolynomialNormalForm.reducibleByList (m := m) G (0 : MvPolynomial σ k) ∧
      sPolynomial (σ := σ) (k := k) m f g =
        (0 : MvPolynomial σ k) +
          q.sum (fun i a => a * Boundary.PolynomialNormalForm.listGenerators
            (σ := σ) (k := k) G i) := by
  exact sPolynomial_exists_zero_remainder_of_mem_list (σ := σ) (k := k) m G hf hg

/-- A Gröbner basis forces every pairwise `S`-polynomial to have zero remainder and remain
nonreducible. -/
theorem sPolynomial_exists_zero_remainder_and_not_reducible_of_isGroebnerBasis
    (m : MonomialOrder σ) (G : List (MvPolynomial σ k))
    (hG : IsGroebnerBasis (σ := σ) (k := k) m G)
    {f g : MvPolynomial σ k} (hf : f ∈ G) (hg : g ∈ G) :
    ∃ q : Fin G.length →₀ MvPolynomial σ k,
      ¬ Boundary.PolynomialNormalForm.reducibleByList (m := m) G
        (sPolynomial (σ := σ) (k := k) m f g) ∧
      sPolynomial (σ := σ) (k := k) m f g =
        (0 : MvPolynomial σ k) +
          q.sum (fun i a => a * Boundary.PolynomialNormalForm.listGenerators
            (σ := σ) (k := k) G i) := by
  rcases sPolynomial_exists_zero_remainder_of_isGroebnerBasis (σ := σ) (k := k) m G hG hf hg
    with ⟨q, hzero, hq⟩
  refine ⟨q, ?_, hq⟩
  exact not_reducible_sPolynomial_of_isGroebnerBasis (σ := σ) (k := k) m G hG f g hf hg

/-- A finite family is a Gröbner basis exactly when each pairwise `S`-polynomial is
nonreducible and admits a zero-remainder division witness. -/
theorem isGroebnerBasis_iff_sPolynomial_zero_remainder
    (m : MonomialOrder σ) (G : List (MvPolynomial σ k)) :
    IsGroebnerBasis (σ := σ) (k := k) m G ↔
      ∀ f ∈ G, ∀ g ∈ G,
        ¬ Boundary.PolynomialNormalForm.reducibleByList (m := m) G
          (sPolynomial (σ := σ) (k := k) m f g) ∧
        ∃ q : Fin G.length →₀ MvPolynomial σ k,
          sPolynomial (σ := σ) (k := k) m f g =
            (0 : MvPolynomial σ k) +
              q.sum (fun i a => a * Boundary.PolynomialNormalForm.listGenerators
                (σ := σ) (k := k) G i) := by
  constructor
  · intro hG f hf g hg
    refine ⟨not_reducible_sPolynomial_of_isGroebnerBasis (σ := σ) (k := k) m G hG f g hf hg, ?_⟩
    rcases sPolynomial_exists_zero_remainder_of_isGroebnerBasis (σ := σ) (k := k) m G hG hf hg
      with ⟨q, hzero, hq⟩
    exact ⟨q, hq⟩
  · intro h
    refine isGroebnerBasis_of_forall_mem (σ := σ) (k := k) m G ?_
    intro f hf g hg
    exact (h f hf g hg).1

/-- A Gröbner basis is equivalently characterized by pairwise `S`-polynomials being
nonreducible and lying in the finite list span. -/
theorem isGroebnerBasis_iff_sPolynomial_nonreducible_and_mem_listSpan
    (m : MonomialOrder σ) (G : List (MvPolynomial σ k)) :
    IsGroebnerBasis (σ := σ) (k := k) m G ↔
      ∀ f ∈ G, ∀ g ∈ G,
        ¬ Boundary.PolynomialNormalForm.reducibleByList (m := m) G
          (sPolynomial (σ := σ) (k := k) m f g) ∧
        sPolynomial (σ := σ) (k := k) m f g ∈
          Boundary.PolynomialNormalForm.listSpan (σ := σ) (k := k) G := by
  constructor
  · intro hG f hf g hg
    refine ⟨not_reducible_sPolynomial_of_isGroebnerBasis (σ := σ) (k := k) m G hG f g hf hg, ?_⟩
    rcases sPolynomial_exists_zero_remainder_of_isGroebnerBasis (σ := σ) (k := k) m G hG hf hg
      with ⟨q, hzero, hq⟩
    rw [Boundary.PolynomialNormalForm.mem_listSpan_iff_exists_division_zero_remainder
      (m := m) (G := G) (f := sPolynomial (σ := σ) (k := k) m f g)]
    exact ⟨q, hzero, hq⟩
  · intro h
    refine isGroebnerBasis_of_forall_mem (σ := σ) (k := k) m G ?_
    intro f hf g hg
    exact (h f hf g hg).1

end PolynomialGroebnerBasis
end Boundary
