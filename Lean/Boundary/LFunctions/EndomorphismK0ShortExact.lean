import Boundary.LFunctions.EndomorphismK0Core
import Boundary.LFunctions.EndomorphismK0Relations

/-!
# Short exact sequence layer for virtual endomorphism classes

This file owns the short exact sequence structure, the canonical splitting
section/equivalence, the block-matrix trace and charpoly lemmas, and the
short-exact relation subgroup.

The quotient-lift character wrappers are intentionally left to the characters
file.
-/

universe u v

namespace Boundary
namespace EndomorphismK0

noncomputable section

open LinearEulerFactor

variable (K : Type u) [Field K]

/-- A short exact sequence in the category of finite-dimensional endomorphism
objects.  The maps are required to commute with the endomorphisms. -/
structure ShortExactSequence where
  left : EndomorphismObject.{u, v} K
  middle : EndomorphismObject.{u, v} K
  right : EndomorphismObject.{u, v} K
  ι : left.carrier →ₗ[K] middle.carrier
  π : middle.carrier →ₗ[K] right.carrier
  splittingSection : right.carrier →ₗ[K] middle.carrier
  splittingSection_spec : π.comp splittingSection = LinearMap.id
  exact : Function.Exact ι π
  injective : Function.Injective ι
  comm_left : ι.comp left.endomorphism = middle.endomorphism.comp ι
  comm_right : π.comp middle.endomorphism = right.endomorphism.comp π

namespace ShortExactSequence

variable {K}

/-- The canonical splitting section is a right inverse for `π`. -/
theorem splittingSection_π (S : ShortExactSequence.{u, v} K) (x : S.right.carrier) :
    S.π (S.splittingSection x) = x := by
  exact LinearMap.congr_fun S.splittingSection_spec x

/-- The middle endomorphism commutes with the canonical inclusion into the left summand. -/
theorem middle_endomorphism_ι (S : ShortExactSequence.{u, v} K) (x : S.left.carrier) :
    S.middle.endomorphism (S.ι x) = S.ι (S.left.endomorphism x) := by
  exact (congrArg (fun f => f x) S.comm_left).symm

/-- The middle endomorphism commutes with the canonical splitting section into the right summand. -/
theorem middle_endomorphism_splittingSection (S : ShortExactSequence.{u, v} K)
    (x : S.right.carrier) :
    S.π (S.middle.endomorphism (S.splittingSection x)) = S.right.endomorphism x := by
  calc
    S.π (S.middle.endomorphism (S.splittingSection x)) =
        S.right.endomorphism (S.π (S.splittingSection x)) := by
          exact congrArg (fun f => f (S.splittingSection x)) S.comm_right
    _ = S.right.endomorphism x := by
          exact congrArg S.right.endomorphism (S.splittingSection_π x)

theorem splittingSection_sub_π_eq_zero (S : ShortExactSequence.{u, v} K)
    (z : S.middle.carrier) :
    S.π (z - S.splittingSection (S.π z)) = 0 := by
  calc
    S.π (z - S.splittingSection (S.π z))
        = S.π z - S.π (S.splittingSection (S.π z)) := by
          exact map_sub S.π z (S.splittingSection (S.π z))
    _ = S.π z - S.π z := by
          exact congrArg (fun t => S.π z - t) (S.splittingSection_π (S.π z))
    _ = 0 := sub_self (S.π z)

theorem splittingSection_sub_mem_range (S : ShortExactSequence.{u, v} K)
    (z : S.middle.carrier) :
    z - S.splittingSection (S.π z) ∈ Set.range S.ι := by
  exact (S.exact (z - S.splittingSection (S.π z))).1 (S.splittingSection_sub_π_eq_zero z)

theorem splitting_recompose (S : ShortExactSequence.{u, v} K)
    (z : S.middle.carrier) {x : S.left.carrier}
    (hx : S.ι x = z - S.splittingSection (S.π z)) :
    S.ι x + S.splittingSection (S.π z) = z := by
  calc
    S.ι x + S.splittingSection (S.π z)
        = (z - S.splittingSection (S.π z)) + S.splittingSection (S.π z) := by
          exact congrArg (fun t => t + S.splittingSection (S.π z)) hx
    _ = z - S.splittingSection (S.π z) + S.splittingSection (S.π z) := by
          rfl
    _ = z := by
          exact sub_add_cancel z (S.splittingSection (S.π z))

theorem coprod_apply_eq (S : ShortExactSequence.{u, v} K)
    (x : S.left.carrier) (y : S.right.carrier) :
    LinearMap.coprod S.ι S.splittingSection (x, y) = S.ι x + S.splittingSection y := by
  rfl

theorem π_coprod_apply (S : ShortExactSequence.{u, v} K)
    (x : S.left.carrier) (y : S.right.carrier) :
    S.π (LinearMap.coprod S.ι S.splittingSection (x, y)) = S.π (S.ι x) + S.π (S.splittingSection y) := by
  exact map_add S.π (S.ι x) (S.splittingSection y)

theorem π_coprod_apply_eq (S : ShortExactSequence.{u, v} K)
    (x : S.left.carrier) (y : S.right.carrier) :
    S.π (LinearMap.coprod S.ι S.splittingSection (x, y)) = y := by
  calc
    S.π (LinearMap.coprod S.ι S.splittingSection (x, y))
        = S.π (S.ι x) + S.π (S.splittingSection y) := by
          exact Eq.trans (congrArg S.π (S.coprod_apply_eq x y)) (S.π_coprod_apply x y)
    _ = 0 + S.π (S.splittingSection y) := by
          exact congrArg (fun t => t + S.π (S.splittingSection y))
            (congrArg (fun f => f x) S.exact.comp_eq_zero)
    _ = y := by
          exact Eq.trans (congrArg (fun t => 0 + t) (S.splittingSection_π y)) (zero_add y)

/-- The canonical splitting equivalence from the middle object to the direct sum
of the left and right objects. -/
noncomputable def splittingEquiv (S : ShortExactSequence.{u, v} K) :
    S.middle.carrier ≃ₗ[K] S.left.carrier × S.right.carrier :=
  by
    refine (LinearEquiv.ofBijective (LinearMap.coprod S.ι S.splittingSection) ?_).symm
    constructor
    · intro x y hxy
      have hπ := congrArg S.π hxy
      have h2 : x.2 = y.2 :=
        Eq.trans (S.π_coprod_apply_eq x.1 x.2).symm
          (Eq.trans hπ (S.π_coprod_apply_eq y.1 y.2))
      have hι : S.ι x.1 = S.ι y.1 := by
        calc
          S.ι x.1 = LinearMap.coprod S.ι S.splittingSection x - S.splittingSection x.2 := by
                exact (add_sub_cancel (S.ι x.1) (S.splittingSection x.2)).symm
          _ = LinearMap.coprod S.ι S.splittingSection y - S.splittingSection x.2 := by
                exact congrArg (fun t => t - S.splittingSection x.2) hxy
          _ = LinearMap.coprod S.ι S.splittingSection y - S.splittingSection y.2 := by
                exact congrArg (fun t => LinearMap.coprod S.ι S.splittingSection y - S.splittingSection t) h2
          _ = S.ι y.1 := by
                exact add_sub_cancel (S.ι y.1) (S.splittingSection y.2)
      exact Prod.ext (S.injective hι) h2
    · intro z
      have hmem : z - S.splittingSection (S.π z) ∈ Set.range S.ι :=
        S.splittingSection_sub_mem_range z
      rcases hmem with ⟨x, hx⟩
      refine ⟨(x, S.π z), ?_⟩
      calc
        LinearMap.coprod S.ι S.splittingSection (x, S.π z) =
            S.ι x + S.splittingSection (S.π z) := by
              exact S.coprod_apply_eq x (S.π z)
        _ = z := by
              exact S.splitting_recompose z hx

theorem splittingEquiv_symm_inl (S : ShortExactSequence.{u, v} K) (x : S.left.carrier) :
    S.splittingEquiv.symm (LinearMap.inl K S.left.carrier S.right.carrier x) = S.ι x := by
  exact by
    simp [ShortExactSequence.splittingEquiv]

theorem splittingEquiv_symm_inr (S : ShortExactSequence.{u, v} K) (x : S.right.carrier) :
    S.splittingEquiv.symm (LinearMap.inr K S.left.carrier S.right.carrier x) =
      S.splittingSection x := by
  exact by
    simp [ShortExactSequence.splittingEquiv]

theorem splittingEquiv_snd (S : ShortExactSequence.{u, v} K) (x : S.middle.carrier) :
    (S.splittingEquiv x).2 = S.π x := by
  rcases h : S.splittingEquiv x with ⟨a, b⟩
  have hsymm := S.splittingEquiv.symm_apply_apply x
  rw [h] at hsymm
  have h0 : S.π (S.ι a) = 0 := congrArg (fun f => f a) S.exact.comp_eq_zero
  have hpi' : S.π (S.splittingSection b) = b := S.splittingSection_π b
  have hπ : b = S.π x := by
    calc
      b = S.π (S.ι a + S.splittingSection b) := by
            calc
              b = 0 + b := by exact (zero_add b).symm
              _ = S.π (S.ι a) + b := by exact congrArg (fun t => t + b) h0.symm
              _ = S.π (S.ι a) + S.π (S.splittingSection b) := by
                    exact congrArg (fun t => S.π (S.ι a) + t) hpi'.symm
              _ = S.π (S.ι a + S.splittingSection b) := by
                    exact (map_add S.π (S.ι a) (S.splittingSection b)).symm
      _ = S.π x := congrArg S.π hsymm
  exact hπ

theorem splittingEquiv_splittingSection (S : ShortExactSequence.{u, v} K)
    (x : S.right.carrier) :
    S.splittingEquiv (S.splittingSection x) = (0, x) := by
  calc
    S.splittingEquiv (S.splittingSection x)
        = S.splittingEquiv (S.splittingEquiv.symm
            (LinearMap.inr K S.left.carrier S.right.carrier x)) := by
          exact congrArg S.splittingEquiv (S.splittingEquiv_symm_inr x).symm
    _ = (0, x) := by
          exact S.splittingEquiv.apply_symm_apply _

theorem splittingEquiv_ι (S : ShortExactSequence.{u, v} K) (x : S.left.carrier) :
    S.splittingEquiv (S.ι x) = (x, 0) := by
  calc
    S.splittingEquiv (S.ι x)
        = S.splittingEquiv (S.splittingEquiv.symm
            (LinearMap.inl K S.left.carrier S.right.carrier x)) := by
          exact congrArg S.splittingEquiv
            (S.splittingEquiv_symm_inl (S := S) (x := x)).symm
    _ = (x, 0) := by
          exact S.splittingEquiv.apply_symm_apply _

theorem splittingEquiv_conj_inl (S : ShortExactSequence.{u, v} K)
    (x : S.left.carrier) :
    (S.splittingEquiv.conj S.middle.endomorphism)
        (LinearMap.inl K S.left.carrier S.right.carrier x) =
      LinearMap.inl K S.left.carrier S.right.carrier (S.left.endomorphism x) := by
  calc
    (S.splittingEquiv.conj S.middle.endomorphism)
        (LinearMap.inl K S.left.carrier S.right.carrier x)
        = S.splittingEquiv
            (S.middle.endomorphism
              (S.splittingEquiv.symm (LinearMap.inl K S.left.carrier S.right.carrier x))) := by
            rfl
    _ = S.splittingEquiv
            (S.middle.endomorphism (S.ι x)) := by
          exact congrArg (fun t => S.splittingEquiv (S.middle.endomorphism t))
            (S.splittingEquiv_symm_inl x)
    _ = S.splittingEquiv (S.ι (S.left.endomorphism x)) := by
          exact congrArg S.splittingEquiv (S.middle_endomorphism_ι x)
    _ = LinearMap.inl K S.left.carrier S.right.carrier (S.left.endomorphism x) := by
          exact S.splittingEquiv_ι (S.left.endomorphism x)

theorem splittingEquiv_conj_inr_snd (S : ShortExactSequence.{u, v} K)
    (x : S.right.carrier) :
    ((S.splittingEquiv.conj S.middle.endomorphism)
        (LinearMap.inr K S.left.carrier S.right.carrier x)).2 = S.right.endomorphism x := by
  calc
    ((S.splittingEquiv.conj S.middle.endomorphism)
        (LinearMap.inr K S.left.carrier S.right.carrier x)).2
        = (S.splittingEquiv (S.middle.endomorphism (S.splittingSection x))).2 := by
            exact congrArg Prod.snd
              (congrArg (fun t => S.splittingEquiv (S.middle.endomorphism t))
                (S.splittingEquiv_symm_inr x))
    _ = S.π (S.middle.endomorphism (S.splittingSection x)) := by
            exact S.splittingEquiv_snd (S.middle.endomorphism (S.splittingSection x))
    _ = S.right.endomorphism x := by
            exact S.middle_endomorphism_splittingSection x

theorem splittingEquiv_conj_inl_pair (S : ShortExactSequence.{u, v} K)
    (x : S.left.carrier) :
    (S.splittingEquiv.conj S.middle.endomorphism) (x, 0) =
      (S.left.endomorphism x, 0) := by
  exact S.splittingEquiv_conj_inl x

theorem splittingEquiv_conj_inl_toMatrix_entry {ιL κR : Type*}
    [Fintype ιL] [Fintype κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier)
    (i j : ιL) :
    (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
      (S.splittingEquiv.conj S.middle.endomorphism)) (Sum.inl i) (Sum.inl j) =
      LinearMap.toMatrix bL bL S.left.endomorphism i j := by
  have hT :
      (S.splittingEquiv.conj S.middle.endomorphism) (bL j, 0) =
        (S.left.endomorphism (bL j), 0) := by
    exact S.splittingEquiv_conj_inl_pair (bL j)
  exact congrArg (fun x => (bL.prod bR).repr x (Sum.inl i)) hT

theorem splittingEquiv_conj_inr_toMatrix_entry {ιL κR : Type*}
    [Fintype ιL] [Fintype κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier)
    (i j : κR) :
    (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
      (S.splittingEquiv.conj S.middle.endomorphism)) (Sum.inr i) (Sum.inr j) =
      LinearMap.toMatrix bR bR S.right.endomorphism i j := by
  have hT :
      ((S.splittingEquiv.conj S.middle.endomorphism) (0, bR j)).2 =
        S.right.endomorphism (bR j) := by
    exact S.splittingEquiv_conj_inr_snd (bR j)
  exact congrArg (fun x : S.right.carrier => bR.repr x i) hT

theorem splittingEquiv_conj_matrix_fromBlocks
    {ιL κR : Type*}
    [Fintype ιL] [Fintype κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier)
    (M : Matrix (ιL ⊕ κR) (ιL ⊕ κR) K)
    (hT11 : M.toBlocks₁₁ = LinearMap.toMatrix bL bL S.left.endomorphism)
    (hT21 : M.toBlocks₂₁ = 0)
    (hT22 : M.toBlocks₂₂ = LinearMap.toMatrix bR bR S.right.endomorphism) :
    M =
      Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism) M.toBlocks₁₂ 0
        (LinearMap.toMatrix bR bR S.right.endomorphism) := by
  calc
    M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ := by
          exact (Matrix.fromBlocks_toBlocks M).symm
    _ = Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism) M.toBlocks₁₂ 0
          (LinearMap.toMatrix bR bR S.right.endomorphism) := by
          cases hT11
          cases hT21
          cases hT22
          rfl

theorem matrix_charpoly_fromBlocks_zero {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    (A : Matrix ιL ιL K) (B : Matrix ιL κR K) (D : Matrix κR κR K) :
    (Matrix.fromBlocks A B 0 D).charpoly = A.charpoly * D.charpoly := by
  exact Matrix.charpoly_fromBlocks_zero₂₁ (M₁₁ := A) (M₁₂ := B) (M₂₂ := D)

theorem trace_fromBlocks_zero {ιL κR : Type*} [Fintype ιL] [Fintype κR]
    (A : Matrix ιL ιL K) (B : Matrix ιL κR K) (D : Matrix κR κR K) :
    (Matrix.fromBlocks A B 0 D).trace = A.trace + D.trace := by
  calc
    (Matrix.fromBlocks A B 0 D).trace
        = ∑ s : ιL ⊕ κR, (Matrix.fromBlocks A B 0 D) s s := by
            rfl
    _ = (∑ i : ιL, (Matrix.fromBlocks A B 0 D) (Sum.inl i) (Sum.inl i)) +
          ∑ j : κR, (Matrix.fromBlocks A B 0 D) (Sum.inr j) (Sum.inr j) := by
            exact Fintype.sum_sum_type
              (fun s : ιL ⊕ κR => (Matrix.fromBlocks A B 0 D) s s)
    _ = (∑ i : ιL, A i i) + ∑ j : κR, D j j := by
            exact congrArg₂ (· + ·)
              (by
                ext i
                exact Matrix.fromBlocks_apply₁₁ A B 0 D i i)
              (by
                ext j
                exact Matrix.fromBlocks_apply₂₂ A B 0 D j j)
    _ = A.trace + D.trace := by
            rfl

theorem determinantUnit_ext
    {A B : EndomorphismObject.{u, v} K}
    (h : A.endomorphism.charpoly = B.endomorphism.charpoly) :
    EndomorphismObject.determinantUnit A = EndomorphismObject.determinantUnit B := by
  have hRat :
      EndomorphismObject.determinantRatFunc A =
        EndomorphismObject.determinantRatFunc B := by
    exact congrArg (algebraMap (Polynomial K) (RatFunc K))
      (congrArg Polynomial.reverse h)
  cases A
  cases B
  simp [EndomorphismObject.determinantUnit, EndomorphismObject.determinantRatFunc] at hRat ⊢
  exact hRat

theorem splittingEquiv_conj_charpoly {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier) :
    (S.splittingEquiv.conj S.middle.endomorphism).charpoly =
      LinearEulerFactor.eulerPolynomial (S.left.endomorphism) *
        LinearEulerFactor.eulerPolynomial (S.right.endomorphism) := by
  let M :
      Matrix (Module.Free.ChooseBasisIndex K S.left.carrier ⊕
        Module.Free.ChooseBasisIndex K S.right.carrier)
        (Module.Free.ChooseBasisIndex K S.left.carrier ⊕
          Module.Free.ChooseBasisIndex K S.right.carrier) K :=
      LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
        (S.splittingEquiv.conj S.middle.endomorphism)
  have hT21 :
      M.toBlocks₂₁ = 0 := by
    ext i j
    change (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
        (S.splittingEquiv.conj S.middle.endomorphism)) (Sum.inr i) (Sum.inl j) = 0
    have hpair :
        (S.splittingEquiv.conj S.middle.endomorphism) (bL j, 0) =
          (S.left.endomorphism (bL j), 0) := by
      exact S.splittingEquiv_conj_inl_pair (bL j)
    cases hpair
    rfl
  have hT11 :
      M.toBlocks₁₁ = LinearMap.toMatrix bL bL S.left.endomorphism := by
    ext i j
    change (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
        (S.splittingEquiv.conj S.middle.endomorphism)) (Sum.inl i) (Sum.inl j) =
      LinearMap.toMatrix bL bL S.left.endomorphism i j
    exact S.splittingEquiv_conj_inl_toMatrix_entry bL bR i j
  have hT22 :
      M.toBlocks₂₂ = LinearMap.toMatrix bR bR S.right.endomorphism := by
    ext i j
    change (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
        (S.splittingEquiv.conj S.middle.endomorphism)) (Sum.inr i) (Sum.inr j) =
      LinearMap.toMatrix bR bR S.right.endomorphism i j
    exact S.splittingEquiv_conj_inr_toMatrix_entry bL bR i j
  let U := M.toBlocks₁₂
  have hmat :
      M =
        Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism) U 0
          (LinearMap.toMatrix bR bR S.right.endomorphism) := by
    exact S.splittingEquiv_conj_matrix_fromBlocks bL bR M hT11 hT21 hT22
  calc
    M.charpoly = (Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism) U 0
        (LinearMap.toMatrix bR bR S.right.endomorphism)).charpoly := by
          exact congrArg Matrix.charpoly hmat
    _ = LinearMap.charpoly S.left.endomorphism * LinearMap.charpoly S.right.endomorphism := by
          calc
            (Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism) U 0
                (LinearMap.toMatrix bR bR S.right.endomorphism)).charpoly
                = (LinearMap.toMatrix bL bL S.left.endomorphism).charpoly *
                    (LinearMap.toMatrix bR bR S.right.endomorphism).charpoly := by
                      exact matrix_charpoly_fromBlocks_zero
                        (LinearMap.toMatrix bL bL S.left.endomorphism) U
                        (LinearMap.toMatrix bR bR S.right.endomorphism)
            _ = LinearMap.charpoly S.left.endomorphism * LinearMap.charpoly S.right.endomorphism := by
                  exact congrArg₂ (· * ·)
                    (LinearMap.charpoly_toMatrix (b := bL) (f := S.left.endomorphism))
                    (LinearMap.charpoly_toMatrix (b := bR) (f := S.right.endomorphism))

theorem splittingEquiv_conj_trace {ιL κR : Type*}
    [Fintype ιL] [Fintype κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier) :
    LinearMap.trace K S.left.carrier S.left.endomorphism +
      LinearMap.trace K S.right.carrier S.right.endomorphism =
      LinearMap.trace K (S.left.carrier × S.right.carrier)
        (S.splittingEquiv.conj S.middle.endomorphism) := by
  let M :
      Matrix (Module.Free.ChooseBasisIndex K S.left.carrier ⊕
        Module.Free.ChooseBasisIndex K S.right.carrier)
        (Module.Free.ChooseBasisIndex K S.left.carrier ⊕
          Module.Free.ChooseBasisIndex K S.right.carrier) K :=
      LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
        (S.splittingEquiv.conj S.middle.endomorphism)
  have hT21 :
      M.toBlocks₂₁ = 0 := by
    ext i j
    change (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
        (S.splittingEquiv.conj S.middle.endomorphism)) (Sum.inr i) (Sum.inl j) = 0
    have hpair :
        (S.splittingEquiv.conj S.middle.endomorphism) (bL j, 0) =
          (S.left.endomorphism (bL j), 0) := by
      exact S.splittingEquiv_conj_inl_pair (bL j)
    cases hpair
    rfl
  have hT11 :
      M.toBlocks₁₁ = LinearMap.toMatrix bL bL S.left.endomorphism := by
    ext i j
    change (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
        (S.splittingEquiv.conj S.middle.endomorphism)) (Sum.inl i) (Sum.inl j) =
      LinearMap.toMatrix bL bL S.left.endomorphism i j
    exact S.splittingEquiv_conj_inl_toMatrix_entry bL bR i j
  have hT22 :
      M.toBlocks₂₂ = LinearMap.toMatrix bR bR S.right.endomorphism := by
    ext i j
    change (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
        (S.splittingEquiv.conj S.middle.endomorphism)) (Sum.inr i) (Sum.inr j) =
      LinearMap.toMatrix bR bR S.right.endomorphism i j
    exact S.splittingEquiv_conj_inr_toMatrix_entry bL bR i j
  let U := M.toBlocks₁₂
  have hmat :
      M =
        Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism) U 0
          (LinearMap.toMatrix bR bR S.right.endomorphism) := by
    exact S.splittingEquiv_conj_matrix_fromBlocks bL bR M hT11 hT21 hT22
  have hleft :
      (LinearMap.toMatrix bL bL S.left.endomorphism).trace =
        LinearMap.trace K S.left.carrier S.left.endomorphism := by
    symm
    exact LinearMap.trace_eq_matrix_trace K bL S.left.endomorphism
  have hright :
      (LinearMap.toMatrix bR bR S.right.endomorphism).trace =
        LinearMap.trace K S.right.carrier S.right.endomorphism := by
    symm
    exact LinearMap.trace_eq_matrix_trace K bR S.right.endomorphism
  calc
    LinearMap.trace K (S.left.carrier × S.right.carrier)
        (S.splittingEquiv.conj S.middle.endomorphism) = M.trace := by
          exact LinearMap.trace_eq_matrix_trace K (bL.prod bR)
            (S.splittingEquiv.conj S.middle.endomorphism)
    _ = (LinearMap.toMatrix bL bL S.left.endomorphism).trace +
          (LinearMap.toMatrix bR bR S.right.endomorphism).trace := by
          calc
            M.trace = (Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism) U 0
                (LinearMap.toMatrix bR bR S.right.endomorphism)).trace := by
                    exact congrArg Matrix.trace hmat
            _ = (LinearMap.toMatrix bL bL S.left.endomorphism).trace +
                  (LinearMap.toMatrix bR bR S.right.endomorphism).trace := by
                    exact trace_fromBlocks_zero
                      (LinearMap.toMatrix bL bL S.left.endomorphism) U
                      (LinearMap.toMatrix bR bR S.right.endomorphism)
    _ = LinearMap.trace K S.left.carrier S.left.endomorphism +
          LinearMap.trace K S.right.carrier S.right.endomorphism := by
          exact congrArg₂ (· + ·) hleft hright

/-- The trace of the middle map in a short exact sequence is additive. -/
theorem shortExact_trace_additivity (S : ShortExactSequence.{u, v} K) :
    LinearMap.trace K S.middle.carrier S.middle.endomorphism =
      LinearMap.trace K S.left.carrier S.left.endomorphism +
        LinearMap.trace K S.right.carrier S.right.endomorphism := by
  let bL := Module.Free.chooseBasis K S.left.carrier
  let bR := Module.Free.chooseBasis K S.right.carrier
  calc
    LinearMap.trace K S.middle.carrier S.middle.endomorphism =
        LinearMap.trace K (S.left.carrier × S.right.carrier)
          (S.splittingEquiv.conj S.middle.endomorphism) := by
            exact (LinearMap.trace_conj' (S.middle.endomorphism) S.splittingEquiv).symm
    _ = LinearMap.trace K S.left.carrier S.left.endomorphism +
          LinearMap.trace K S.right.carrier S.right.endomorphism := by
            exact (S.splittingEquiv_conj_trace (bL := bL) (bR := bR)).symm

/-- The charpoly of the middle map in a short exact sequence is the product of
the charpolys of the ends. -/
theorem shortExact_middle_charpoly_eq (S : ShortExactSequence.{u, v} K) :
    S.middle.endomorphism.charpoly =
      (S.left.product S.right).endomorphism.charpoly := by
  let bL := Module.Free.chooseBasis K S.left.carrier
  let bR := Module.Free.chooseBasis K S.right.carrier
  calc
    S.middle.endomorphism.charpoly =
        (S.splittingEquiv.conj S.middle.endomorphism).charpoly := by
          symm
          exact LinearEquiv.charpoly_conj (e := S.splittingEquiv)
            (φ := S.middle.endomorphism)
    _ = S.left.endomorphism.charpoly * S.right.endomorphism.charpoly := by
          exact S.splittingEquiv_conj_charpoly (bL := bL) (bR := bR)
    _ = (S.left.product S.right).endomorphism.charpoly := by
          exact (LinearMap.charpoly_prodMap S.left.endomorphism S.right.endomorphism).symm

/-- The determinant unit of the middle map is the product of the determinant
units of the ends. -/
theorem shortExact_middle_determinantUnit_eq (S : ShortExactSequence.{u, v} K) :
    EndomorphismObject.determinantUnit S.middle =
      EndomorphismObject.determinantUnit (EndomorphismObject.product S.left S.right) := by
  exact determinantUnit_ext (A := S.middle) (B := EndomorphismObject.product S.left S.right)
    S.shortExact_middle_charpoly_eq

/-- Determinants multiply across a short exact sequence relation. -/
theorem shortExact_determinantUnit_mul (S : ShortExactSequence.{u, v} K) :
    EndomorphismObject.determinantUnit S.middle =
      EndomorphismObject.determinantUnit S.left *
        EndomorphismObject.determinantUnit S.right := by
  calc
    EndomorphismObject.determinantUnit S.middle =
        EndomorphismObject.determinantUnit (EndomorphismObject.product S.left S.right) := by
          exact S.shortExact_middle_determinantUnit_eq
    _ = EndomorphismObject.determinantUnit S.left *
        EndomorphismObject.determinantUnit S.right := by
          exact EndomorphismObject.determinantUnit_product S.left S.right

/-- The relation `[middle] - [left] - [right]` attached to a short exact
sequence. -/
def shortExactRelation (K : Type u) [Field K] (S : ShortExactSequence.{u, v} K) :
    VirtualEndomorphism K :=
  of K S.middle - of K S.left - of K S.right

/-- The subgroup generated by the direct-sum, conjugacy, zero-object, and
short-exact-sequence relations. -/
def shortExactSubgroup (K : Type u) [Field K] : AddSubgroup (VirtualEndomorphism K) :=
  AddSubgroup.closure
    {x | (∃ A B : EndomorphismObject.{u, v} K, x = directSumRelation K A B) ∨
      (∃ A B : EndomorphismObject.{u, v} K, ∃ e : A.carrier ≃ₗ[K] B.carrier,
        x = conjRelation K A e) ∨
      (∃ A : EndomorphismObject.{u, v} K, IsZeroObject K A ∧ x = of K A) ∨
      ∃ S : ShortExactSequence.{u, v} K, x = shortExactRelation K S}

/-- Short exact sequence relations lie in the subgroup they generate. -/
theorem shortExactRelation_mem_shortExactSubgroup (K : Type u) [Field K]
    (S : ShortExactSequence.{u, v} K) :
    shortExactRelation K S ∈ (shortExactSubgroup K : AddSubgroup (VirtualEndomorphism K)) := by
  change shortExactRelation K S ∈
      AddSubgroup.closure
        {x : VirtualEndomorphism K |
          (∃ A B : EndomorphismObject.{u, v} K, x = directSumRelation K A B) ∨
            (∃ A B : EndomorphismObject.{u, v} K, ∃ e : A.carrier ≃ₗ[K] B.carrier,
              x = conjRelation K A e) ∨
            (∃ A : EndomorphismObject.{u, v} K, IsZeroObject K A ∧ x = of K A) ∨
            ∃ S : ShortExactSequence.{u, v} K, x = shortExactRelation K S}
  exact AddSubgroup.subset_closure (Or.inr <| Or.inr <| Or.inr ⟨S, rfl⟩)

/-- The determinant character kills the full exact-sequence relation subgroup. -/
theorem shortExactSubgroup_le_determinantCharacter_ker :
    shortExactSubgroup K ≤ (determinantCharacter K).ker := by
  exact show AddSubgroup.closure
      {x | (∃ A B : EndomorphismObject.{u, v} K, x = directSumRelation K A B) ∨
        (∃ A B : EndomorphismObject.{u, v} K, ∃ e : A.carrier ≃ₗ[K] B.carrier,
          x = conjRelation K A e) ∨
        (∃ A : EndomorphismObject.{u, v} K, IsZeroObject K A ∧ x = of K A) ∨
        ∃ S : ShortExactSequence.{u, v} K, x = shortExactRelation K S}
      ≤ (determinantCharacter K).ker from by
    refine (AddSubgroup.closure_le).2 ?_
    rintro x (⟨A, B, rfl⟩ | ⟨A, B, e, rfl⟩ | ⟨A, hA, rfl⟩ | ⟨S, rfl⟩)
    · exact determinantCharacter_directSumRelation K A B
    · exact determinantCharacter_conjRelation K A e
    · exact determinantCharacter_zeroObject K A hA
    · exact determinantCharacter_shortExactRelation K S

/-- The first trace character kills the full exact-sequence relation subgroup. -/
theorem shortExactSubgroup_le_traceCharacter_one_ker :
    shortExactSubgroup K ≤ (traceCharacter K 1).ker := by
  exact show AddSubgroup.closure
      {x | (∃ A B : EndomorphismObject.{u, v} K, x = directSumRelation K A B) ∨
        (∃ A B : EndomorphismObject.{u, v} K, ∃ e : A.carrier ≃ₗ[K] B.carrier,
          x = conjRelation K A e) ∨
        (∃ A : EndomorphismObject.{u, v} K, IsZeroObject K A ∧ x = of K A) ∨
        ∃ S : ShortExactSequence.{u, v} K, x = shortExactRelation K S}
      ≤ (traceCharacter K 1).ker from by
    refine (AddSubgroup.closure_le).2 ?_
    rintro x (⟨A, B, rfl⟩ | ⟨A, B, e, rfl⟩ | ⟨A, hA, rfl⟩ | ⟨S, rfl⟩)
    · exact traceCharacter_directSumRelation K 1 A B
    · exact traceCharacter_conjRelation K 1 A e
    · exact traceCharacter_zeroObject K 1 A hA
    · exact traceCharacter_one_shortExactRelation K S

end ShortExactSequence

end

end EndomorphismK0
end Boundary
