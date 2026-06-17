import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.CohomologicalEulerFactor.EndomorphismK0.EndomorphismK0Core.EndomorphismK0Core
import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.CohomologicalEulerFactor.EndomorphismK0.EndomorphismK0Relations.EndomorphismK0Relations
import Mathlib.Data.Fintype.Sum

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

theorem splittingCoprod_injective_snd_eq (S : ShortExactSequence.{u, v} K)
    {x y : S.left.carrier × S.right.carrier}
    (hxy : LinearMap.coprod S.ι S.splittingSection x =
      LinearMap.coprod S.ι S.splittingSection y) :
    x.2 = y.2 := by
  exact Eq.trans (S.π_coprod_apply_eq x.1 x.2).symm
    (Eq.trans (congrArg S.π hxy) (S.π_coprod_apply_eq y.1 y.2))

theorem splittingCoprod_left_eq_sub (S : ShortExactSequence.{u, v} K)
    (x : S.left.carrier × S.right.carrier) :
    S.ι x.1 =
      LinearMap.coprod S.ι S.splittingSection x - S.splittingSection x.2 := by
  exact Eq.trans
    (add_sub_cancel_right (S.ι x.1) (S.splittingSection x.2)).symm
    (congrArg (fun t => t - S.splittingSection x.2)
      (S.coprod_apply_eq x.1 x.2).symm)

theorem splittingCoprod_sub_eq_left (S : ShortExactSequence.{u, v} K)
    (x : S.left.carrier × S.right.carrier) :
    LinearMap.coprod S.ι S.splittingSection x - S.splittingSection x.2 =
      S.ι x.1 := by
  exact Eq.trans
    (congrArg (fun t => t - S.splittingSection x.2)
      (S.coprod_apply_eq x.1 x.2))
    (add_sub_cancel_right (S.ι x.1) (S.splittingSection x.2))

theorem splittingCoprod_injective_fst_image_eq (S : ShortExactSequence.{u, v} K)
    {x y : S.left.carrier × S.right.carrier}
    (hxy : LinearMap.coprod S.ι S.splittingSection x =
      LinearMap.coprod S.ι S.splittingSection y) :
    S.ι x.1 = S.ι y.1 := by
  exact Eq.trans
    (S.splittingCoprod_left_eq_sub x)
    (Eq.trans
      (congrArg (fun t => t - S.splittingSection x.2) hxy)
      (Eq.trans
        (congrArg
          (fun t => LinearMap.coprod S.ι S.splittingSection y - S.splittingSection t)
          (S.splittingCoprod_injective_snd_eq hxy))
        (S.splittingCoprod_sub_eq_left y)))

theorem splittingCoprod_injective (S : ShortExactSequence.{u, v} K) :
    Function.Injective (LinearMap.coprod S.ι S.splittingSection) := by
  intro x y hxy
  exact Prod.ext
    (S.injective (S.splittingCoprod_injective_fst_image_eq hxy))
    (S.splittingCoprod_injective_snd_eq hxy)

theorem splittingCoprod_surjective_witness (S : ShortExactSequence.{u, v} K)
    (z : S.middle.carrier) :
    ∃ x : S.left.carrier,
      S.ι x = z - S.splittingSection (S.π z) :=
  S.splittingSection_sub_mem_range z

theorem splittingCoprod_surjective_witness_apply (S : ShortExactSequence.{u, v} K)
    (z : S.middle.carrier) {x : S.left.carrier}
    (hx : S.ι x = z - S.splittingSection (S.π z)) :
    LinearMap.coprod S.ι S.splittingSection (x, S.π z) = z := by
  exact Eq.trans (S.coprod_apply_eq x (S.π z)) (S.splitting_recompose z hx)

theorem splittingCoprod_surjective (S : ShortExactSequence.{u, v} K) :
    Function.Surjective (LinearMap.coprod S.ι S.splittingSection) := by
  intro z
  match S.splittingCoprod_surjective_witness z with
  | ⟨x, hx⟩ =>
      exact ⟨(x, S.π z), S.splittingCoprod_surjective_witness_apply z hx⟩

theorem splittingCoprod_bijective (S : ShortExactSequence.{u, v} K) :
    Function.Bijective (LinearMap.coprod S.ι S.splittingSection) :=
  ⟨S.splittingCoprod_injective, S.splittingCoprod_surjective⟩

/-- The forward equivalence from the direct sum of the ends to the middle term. -/
noncomputable def splittingCoprodEquiv (S : ShortExactSequence.{u, v} K) :
    ((S.left.carrier × S.right.carrier) ≃ₗ[K] S.middle.carrier) :=
  LinearEquiv.ofBijective (LinearMap.coprod S.ι S.splittingSection)
    S.splittingCoprod_bijective

/-- The canonical splitting equivalence from the middle object to the direct sum
of the left and right objects. -/
noncomputable def splittingEquiv (S : ShortExactSequence.{u, v} K) :
    (S.middle.carrier ≃ₗ[K] (S.left.carrier × S.right.carrier)) :=
  (splittingCoprodEquiv (K := K) S).symm

theorem splittingEquiv_symm_inl (S : ShortExactSequence.{u, v} K) (x : S.left.carrier) :
    S.splittingEquiv.symm (LinearMap.inl K S.left.carrier S.right.carrier x) = S.ι x := by
  calc
    S.splittingEquiv.symm (LinearMap.inl K S.left.carrier S.right.carrier x)
        = splittingCoprodEquiv (K := K) S (x, 0) := by
          rfl
    _ = LinearMap.coprod S.ι S.splittingSection (x, 0) := by
          rfl
    _ = S.ι x + S.splittingSection 0 := by
          exact S.coprod_apply_eq x 0
    _ = S.ι x + 0 := by
          exact congrArg (fun y => S.ι x + y) (map_zero S.splittingSection)
    _ = S.ι x := by
          exact add_zero (S.ι x)

theorem splittingEquiv_symm_inr (S : ShortExactSequence.{u, v} K) (x : S.right.carrier) :
    S.splittingEquiv.symm (LinearMap.inr K S.left.carrier S.right.carrier x) =
      S.splittingSection x := by
  calc
    S.splittingEquiv.symm (LinearMap.inr K S.left.carrier S.right.carrier x)
        = splittingCoprodEquiv (K := K) S (0, x) := by
          rfl
    _ = LinearMap.coprod S.ι S.splittingSection (0, x) := by
          rfl
    _ = S.ι 0 + S.splittingSection x := by
          exact S.coprod_apply_eq 0 x
    _ = 0 + S.splittingSection x := by
          exact congrArg (fun y => y + S.splittingSection x) (map_zero S.ι)
    _ = S.splittingSection x := by
          exact zero_add (S.splittingSection x)

theorem splittingEquiv_symm_pair_of_eq (S : ShortExactSequence.{u, v} K)
    (x : S.middle.carrier) {a : S.left.carrier} {b : S.right.carrier}
    (h : S.splittingEquiv x = (a, b)) :
    S.splittingEquiv.symm (a, b) = x := by
  exact Eq.trans (congrArg S.splittingEquiv.symm h.symm)
    (S.splittingEquiv.symm_apply_apply x)

theorem splittingEquiv_coprod_pair_of_eq (S : ShortExactSequence.{u, v} K)
    (x : S.middle.carrier) {a : S.left.carrier} {b : S.right.carrier}
    (h : S.splittingEquiv x = (a, b)) :
    S.ι a + S.splittingSection b = x := by
  exact Eq.trans (S.coprod_apply_eq a b).symm
    (S.splittingEquiv_symm_pair_of_eq x h)

theorem π_ι_eq_zero (S : ShortExactSequence.{u, v} K) (a : S.left.carrier) :
    S.π (S.ι a) = 0 :=
  congrArg (fun f => f a) S.exact.comp_eq_zero

theorem π_add_ι_splittingSection_eq_right (S : ShortExactSequence.{u, v} K)
    (a : S.left.carrier) (b : S.right.carrier) :
    S.π (S.ι a + S.splittingSection b) = b := by
  exact Eq.trans
    (map_add S.π (S.ι a) (S.splittingSection b))
    (Eq.trans
      (congrArg₂ HAdd.hAdd (S.π_ι_eq_zero a) (S.splittingSection_π b))
      (zero_add b))

theorem splittingEquiv_snd_of_eq_pair (S : ShortExactSequence.{u, v} K)
    (x : S.middle.carrier) {a : S.left.carrier} {b : S.right.carrier}
    (h : S.splittingEquiv x = (a, b)) :
    b = S.π x := by
  exact Eq.trans
    (S.π_add_ι_splittingSection_eq_right a b).symm
    (congrArg S.π (S.splittingEquiv_coprod_pair_of_eq x h))

theorem splittingEquiv_snd (S : ShortExactSequence.{u, v} K) (x : S.middle.carrier) :
    (S.splittingEquiv x).2 = S.π x := by
  match h : S.splittingEquiv x with
  | (a, b) =>
      exact S.splittingEquiv_snd_of_eq_pair x h

theorem splittingEquiv_splittingSection (S : ShortExactSequence.{u, v} K)
    (x : S.right.carrier) :
    S.splittingEquiv (S.splittingSection x) = (0, x) := by
  calc
    S.splittingEquiv (S.splittingSection x)
        = S.splittingEquiv (S.splittingEquiv.symm
            (LinearMap.inr K S.left.carrier S.right.carrier x)) := by
          exact congrArg S.splittingEquiv (splittingEquiv_symm_inr (S := S) (x := x)).symm
    _ = (0, x) := by
          exact S.splittingEquiv.apply_symm_apply _

theorem splittingEquiv_ι (S : ShortExactSequence.{u, v} K) (x : S.left.carrier) :
    S.splittingEquiv (S.ι x) = (x, 0) := by
  calc
    S.splittingEquiv (S.ι x)
        = S.splittingEquiv (S.splittingEquiv.symm
            (LinearMap.inl K S.left.carrier S.right.carrier x)) := by
          exact congrArg S.splittingEquiv
            (splittingEquiv_symm_inl (S := S) (x := x)).symm
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
            (splittingEquiv_symm_inl (S := S) (x := x))
    _ = S.splittingEquiv (S.ι (S.left.endomorphism x)) := by
          exact congrArg S.splittingEquiv (S.middle_endomorphism_ι x)
    _ = LinearMap.inl K S.left.carrier S.right.carrier (S.left.endomorphism x) := by
          exact splittingEquiv_ι (S := S) (x := S.left.endomorphism x)

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
                (splittingEquiv_symm_inr (S := S) (x := x)))
    _ = S.π (S.middle.endomorphism (S.splittingSection x)) := by
            exact S.splittingEquiv_snd (S.middle.endomorphism (S.splittingSection x))
    _ = S.right.endomorphism x := by
            exact S.middle_endomorphism_splittingSection x

theorem splittingEquiv_conj_inl_pair (S : ShortExactSequence.{u, v} K)
    (x : S.left.carrier) :
    (S.splittingEquiv.conj S.middle.endomorphism) (x, 0) =
      (S.left.endomorphism x, 0) := by
  exact S.splittingEquiv_conj_inl x

theorem basis_prod_apply_inl_pair {ιL κR : Type*}
    {L R : Type v} [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    (bL : Basis ιL K L) (bR : Basis κR K R) (i : ιL) :
    bL.prod bR (Sum.inl i) = (bL i, 0) := by
  exact Prod.ext
    (Basis.prod_apply_inl_fst (b := bL) (b' := bR) i)
    (Basis.prod_apply_inl_snd (b := bL) (b' := bR) i)

theorem basis_prod_apply_inr_pair {ιL κR : Type*}
    {L R : Type v} [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    (bL : Basis ιL K L) (bR : Basis κR K R) (i : κR) :
    bL.prod bR (Sum.inr i) = (0, bR i) := by
  exact Prod.ext
    (Basis.prod_apply_inr_fst (b := bL) (b' := bR) i)
    (Basis.prod_apply_inr_snd (b := bL) (b' := bR) i)

theorem basis_prod_repr_inl_pair {ιL κR : Type*}
    {L R : Type v} [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    (bL : Basis ιL K L) (bR : Basis κR K R) (x : L) (i : ιL) :
    (bL.prod bR).repr (x, 0) (Sum.inl i) = bL.repr x i := by
  exact Basis.prod_repr_inl (b := bL) (b' := bR) (x, 0) i

theorem basis_prod_repr_inr_pair {ιL κR : Type*}
    {L R : Type v} [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    (bL : Basis ιL K L) (bR : Basis κR K R) (y : R) (i : κR) :
    (bL.prod bR).repr (0, y) (Sum.inr i) = bR.repr y i := by
  exact Basis.prod_repr_inr (b := bL) (b' := bR) (0, y) i

theorem basis_prod_repr_inr_left_pair {ιL κR : Type*}
    {L R : Type v} [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    (bL : Basis ιL K L) (bR : Basis κR K R) (x : L) (i : κR) :
    (bL.prod bR).repr (x, 0) (Sum.inr i) = 0 := by
  exact Eq.trans
    (Basis.prod_repr_inr (b := bL) (b' := bR) (x, 0) i)
    (Eq.trans
      (congrArg (fun f : κR →₀ K => f i) (map_zero bR.repr))
      (Finsupp.zero_apply))

theorem toMatrix_entry_eq_repr_apply {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {V : Type v} [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (T : V →ₗ[K] V) (i j : ι) :
    LinearMap.toMatrix b b T i j = b.repr (T (b j)) i := by
  exact LinearMap.toMatrix_apply b b T i j

theorem repr_apply_eq_toMatrix_entry {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {V : Type v} [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (T : V →ₗ[K] V) (i j : ι) :
    b.repr (T (b j)) i = LinearMap.toMatrix b b T i j := by
  exact (toMatrix_entry_eq_repr_apply b T i j).symm

theorem toMatrix_prod_inl_entry_of_pair_eq {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    {L R : Type v} [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    (bL : Basis ιL K L) (bR : Basis κR K R)
    (T : L × R →ₗ[K] L × R) (i j : ιL) {y : L}
    (h : T (bL j, 0) = (y, 0)) :
    LinearMap.toMatrix (bL.prod bR) (bL.prod bR) T (Sum.inl i) (Sum.inl j) =
      bL.repr y i := by
  calc
    LinearMap.toMatrix (bL.prod bR) (bL.prod bR) T (Sum.inl i) (Sum.inl j)
        = (bL.prod bR).repr (T (bL.prod bR (Sum.inl j))) (Sum.inl i) := by
          exact LinearMap.toMatrix_apply (bL.prod bR) (bL.prod bR) T (Sum.inl i) (Sum.inl j)
    _ = (bL.prod bR).repr (T (bL j, 0)) (Sum.inl i) := by
          exact congrArg (fun z => (bL.prod bR).repr (T z) (Sum.inl i))
            (basis_prod_apply_inl_pair bL bR j)
    _ = (bL.prod bR).repr (y, 0) (Sum.inl i) := by
          exact congrArg (fun z => (bL.prod bR).repr z (Sum.inl i)) h
    _ = bL.repr y i := by
          exact basis_prod_repr_inl_pair bL bR y i

theorem toMatrix_prod_inl_lower_entry_of_pair_eq {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    {L R : Type v} [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    (bL : Basis ιL K L) (bR : Basis κR K R)
    (T : L × R →ₗ[K] L × R) (i : κR) (j : ιL) {y : L}
    (h : T (bL j, 0) = (y, 0)) :
    LinearMap.toMatrix (bL.prod bR) (bL.prod bR) T (Sum.inr i) (Sum.inl j) = 0 := by
  calc
    LinearMap.toMatrix (bL.prod bR) (bL.prod bR) T (Sum.inr i) (Sum.inl j)
        = (bL.prod bR).repr (T (bL.prod bR (Sum.inl j))) (Sum.inr i) := by
          exact LinearMap.toMatrix_apply (bL.prod bR) (bL.prod bR) T (Sum.inr i) (Sum.inl j)
    _ = (bL.prod bR).repr (T (bL j, 0)) (Sum.inr i) := by
          exact congrArg (fun z => (bL.prod bR).repr (T z) (Sum.inr i))
            (basis_prod_apply_inl_pair bL bR j)
    _ = (bL.prod bR).repr (y, 0) (Sum.inr i) := by
          exact congrArg (fun z => (bL.prod bR).repr z (Sum.inr i)) h
    _ = 0 := by
          exact basis_prod_repr_inr_left_pair bL bR y i

theorem toMatrix_prod_inr_entry_of_snd_eq {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    {L R : Type v} [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    (bL : Basis ιL K L) (bR : Basis κR K R)
    (T : L × R →ₗ[K] L × R) (i j : κR) {y : R}
    (h : (T (0, bR j)).2 = y) :
    LinearMap.toMatrix (bL.prod bR) (bL.prod bR) T (Sum.inr i) (Sum.inr j) =
      bR.repr y i := by
  calc
    LinearMap.toMatrix (bL.prod bR) (bL.prod bR) T (Sum.inr i) (Sum.inr j)
        = (bL.prod bR).repr (T (bL.prod bR (Sum.inr j))) (Sum.inr i) := by
          exact LinearMap.toMatrix_apply (bL.prod bR) (bL.prod bR) T (Sum.inr i) (Sum.inr j)
    _ = (bL.prod bR).repr (T (0, bR j)) (Sum.inr i) := by
          exact congrArg (fun z => (bL.prod bR).repr (T z) (Sum.inr i))
            (basis_prod_apply_inr_pair bL bR j)
    _ = bR.repr (T (0, bR j)).2 i := by
          exact Basis.prod_repr_inr (b := bL) (b' := bR) (T (0, bR j)) i
    _ = bR.repr y i := by
          exact congrArg (fun z => bR.repr z i) h

theorem splittingEquiv_conj_inl_toMatrix_entry {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier)
    (i j : ιL) :
    (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
      (S.splittingEquiv.conj S.middle.endomorphism)) (Sum.inl i) (Sum.inl j) =
      LinearMap.toMatrix bL bL S.left.endomorphism i j := by
  exact Eq.trans
    (toMatrix_prod_inl_entry_of_pair_eq bL bR
      (S.splittingEquiv.conj S.middle.endomorphism) i j
      (y := S.left.endomorphism (bL j))
      (S.splittingEquiv_conj_inl_pair (bL j)))
    (repr_apply_eq_toMatrix_entry bL S.left.endomorphism i j)

theorem splittingEquiv_conj_inr_toMatrix_entry {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier)
    (i j : κR) :
    (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
      (S.splittingEquiv.conj S.middle.endomorphism)) (Sum.inr i) (Sum.inr j) =
      LinearMap.toMatrix bR bR S.right.endomorphism i j := by
  exact Eq.trans
    (toMatrix_prod_inr_entry_of_snd_eq bL bR
      (S.splittingEquiv.conj S.middle.endomorphism) i j
      (y := S.right.endomorphism (bR j))
      (S.splittingEquiv_conj_inr_snd (bR j)))
    (repr_apply_eq_toMatrix_entry bR S.right.endomorphism i j)

theorem splittingEquiv_conj_matrix_fromBlocks
    {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
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
    _ = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
          exact congrArg
            (fun C => Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ C M.toBlocks₂₂)
            hT21
    _ = Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism) M.toBlocks₁₂ 0
          (LinearMap.toMatrix bR bR S.right.endomorphism) := by
          exact congrArg₂
            (fun A D => Matrix.fromBlocks A M.toBlocks₁₂ 0 D)
            hT11 hT22

theorem matrix_charpoly_fromBlocks_zero {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    (A : Matrix ιL ιL K) (B : Matrix ιL κR K) (D : Matrix κR κR K) :
    (Matrix.fromBlocks A B 0 D).charpoly = A.charpoly * D.charpoly := by
  exact Matrix.charpoly_fromBlocks_zero₂₁ (M₁₁ := A) (M₁₂ := B) (M₂₂ := D)

noncomputable def splittingEquivConjMatrix {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier) :
    Matrix (ιL ⊕ κR) (ιL ⊕ κR) K :=
  LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
    (S.splittingEquiv.conj S.middle.endomorphism)

theorem splittingEquivConjMatrix_eq_toMatrix {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier) :
    S.splittingEquivConjMatrix bL bR =
      LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
        (S.splittingEquiv.conj S.middle.endomorphism) := by
  rfl

theorem splittingEquivConjMatrix_blocks₂₁ {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier) :
    (S.splittingEquivConjMatrix bL bR).toBlocks₂₁ = 0 := by
  ext i j
  exact Eq.trans
    (congrArg (fun M : Matrix (ιL ⊕ κR) (ιL ⊕ κR) K => M.toBlocks₂₁ i j)
      (S.splittingEquivConjMatrix_eq_toMatrix bL bR))
    (toMatrix_prod_inl_lower_entry_of_pair_eq bL bR
      (S.splittingEquiv.conj S.middle.endomorphism) i j
      (S.splittingEquiv_conj_inl_pair (bL j)))

theorem splittingEquivConjMatrix_blocks₁₁ {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier) :
    (S.splittingEquivConjMatrix bL bR).toBlocks₁₁ =
      LinearMap.toMatrix bL bL S.left.endomorphism := by
  ext i j
  exact Eq.trans
    (congrArg (fun M : Matrix (ιL ⊕ κR) (ιL ⊕ κR) K => M.toBlocks₁₁ i j)
      (S.splittingEquivConjMatrix_eq_toMatrix bL bR))
    (S.splittingEquiv_conj_inl_toMatrix_entry bL bR i j)

theorem splittingEquivConjMatrix_blocks₂₂ {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier) :
    (S.splittingEquivConjMatrix bL bR).toBlocks₂₂ =
      LinearMap.toMatrix bR bR S.right.endomorphism := by
  ext i j
  exact Eq.trans
    (congrArg (fun M : Matrix (ιL ⊕ κR) (ιL ⊕ κR) K => M.toBlocks₂₂ i j)
      (S.splittingEquivConjMatrix_eq_toMatrix bL bR))
    (S.splittingEquiv_conj_inr_toMatrix_entry bL bR i j)

theorem splittingEquivConjMatrix_eq_fromBlocks {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier) :
    S.splittingEquivConjMatrix bL bR =
      Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism)
        (S.splittingEquivConjMatrix bL bR).toBlocks₁₂ 0
        (LinearMap.toMatrix bR bR S.right.endomorphism) := by
  exact S.splittingEquiv_conj_matrix_fromBlocks bL bR
    (S.splittingEquivConjMatrix bL bR)
    (S.splittingEquivConjMatrix_blocks₁₁ bL bR)
    (S.splittingEquivConjMatrix_blocks₂₁ bL bR)
    (S.splittingEquivConjMatrix_blocks₂₂ bL bR)

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
                exact Finset.sum_congr rfl
                  (fun i _ => Matrix.fromBlocks_apply₁₁ A B 0 D i i))
              (by
                exact Finset.sum_congr rfl
                  (fun j _ => Matrix.fromBlocks_apply₂₂ A B 0 D j j))
    _ = A.trace + D.trace := by
            rfl

theorem determinantUnit_ext
    {A B : EndomorphismObject.{u, v} K}
    (h : A.endomorphism.charpoly = B.endomorphism.charpoly) :
    EndomorphismObject.determinantUnit A = EndomorphismObject.determinantUnit B := by
  exact Units.ext
    (congrArg (algebraMap (Polynomial K) (RatFunc K))
      (congrArg Polynomial.reverse h))

theorem splittingEquiv_conj_charpoly {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier) :
    (S.splittingEquiv.conj S.middle.endomorphism).charpoly =
      S.left.endomorphism.charpoly * S.right.endomorphism.charpoly := by
  calc
    (S.splittingEquiv.conj S.middle.endomorphism).charpoly =
        (S.splittingEquivConjMatrix bL bR).charpoly := by
          exact Eq.trans
            (LinearMap.charpoly_toMatrix (b := bL.prod bR)
              (f := S.splittingEquiv.conj S.middle.endomorphism)).symm
            (congrArg Matrix.charpoly
              (S.splittingEquivConjMatrix_eq_toMatrix bL bR).symm)
    _ = (Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism)
        (S.splittingEquivConjMatrix bL bR).toBlocks₁₂ 0
        (LinearMap.toMatrix bR bR S.right.endomorphism)).charpoly := by
          exact congrArg Matrix.charpoly (S.splittingEquivConjMatrix_eq_fromBlocks bL bR)
    _ = LinearMap.charpoly S.left.endomorphism * LinearMap.charpoly S.right.endomorphism := by
          calc
            (Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism)
                (S.splittingEquivConjMatrix bL bR).toBlocks₁₂ 0
                (LinearMap.toMatrix bR bR S.right.endomorphism)).charpoly
                = (LinearMap.toMatrix bL bL S.left.endomorphism).charpoly *
                    (LinearMap.toMatrix bR bR S.right.endomorphism).charpoly := by
                      exact matrix_charpoly_fromBlocks_zero
                        (LinearMap.toMatrix bL bL S.left.endomorphism)
                        (S.splittingEquivConjMatrix bL bR).toBlocks₁₂
                        (LinearMap.toMatrix bR bR S.right.endomorphism)
            _ = LinearMap.charpoly S.left.endomorphism * LinearMap.charpoly S.right.endomorphism := by
                  exact congrArg₂ (· * ·)
                    (LinearMap.charpoly_toMatrix (b := bL) (f := S.left.endomorphism))
                    (LinearMap.charpoly_toMatrix (b := bR) (f := S.right.endomorphism))

theorem splittingEquiv_conj_trace {ιL κR : Type*}
    [Fintype ιL] [Fintype κR] [DecidableEq ιL] [DecidableEq κR]
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ιL K S.left.carrier) (bR : Basis κR K S.right.carrier) :
    LinearMap.trace K S.left.carrier S.left.endomorphism +
      LinearMap.trace K S.right.carrier S.right.endomorphism =
      LinearMap.trace K (S.left.carrier × S.right.carrier)
        (S.splittingEquiv.conj S.middle.endomorphism) := by
  exact Eq.symm
    (Eq.trans
      (Eq.trans
        (LinearMap.trace_eq_matrix_trace K (bL.prod bR)
          (S.splittingEquiv.conj S.middle.endomorphism))
        (congrArg Matrix.trace
          (S.splittingEquivConjMatrix_eq_toMatrix bL bR).symm))
      (Eq.trans
        (Eq.trans
          (congrArg Matrix.trace (S.splittingEquivConjMatrix_eq_fromBlocks bL bR))
          (trace_fromBlocks_zero
            (LinearMap.toMatrix bL bL S.left.endomorphism)
            (S.splittingEquivConjMatrix bL bR).toBlocks₁₂
            (LinearMap.toMatrix bR bR S.right.endomorphism)))
        (congrArg₂ (· + ·)
          (LinearMap.trace_eq_matrix_trace K bL S.left.endomorphism).symm
          (LinearMap.trace_eq_matrix_trace K bR S.right.endomorphism).symm)))

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
    VirtualEndomorphism.{u, v} K :=
  of K S.middle - of K S.left - of K S.right

/-- The generators for the direct-sum, conjugacy, zero-object, and
short-exact-sequence relation subgroup. -/
def shortExactGeneratingSet (K : Type u) [Field K] : Set (VirtualEndomorphism.{u, v} K) :=
  {x | (∃ A B : EndomorphismObject.{u, v} K, x = directSumRelation K A B) ∨
    (∃ A B : EndomorphismObject.{u, v} K, ∃ e : A.carrier ≃ₗ[K] B.carrier,
      x = conjRelation K A e) ∨
    (∃ A : EndomorphismObject.{u, v} K, IsZeroObject K A ∧ x = of K A) ∨
    ∃ S : ShortExactSequence.{u, v} K, x = shortExactRelation K S}

/-- The subgroup generated by the direct-sum, conjugacy, zero-object, and
short-exact-sequence relations. -/
def shortExactSubgroup (K : Type u) [Field K] : AddSubgroup (VirtualEndomorphism.{u, v} K) :=
  AddSubgroup.closure (shortExactGeneratingSet K)

/-- Short exact sequence relations lie in the subgroup they generate. -/
theorem shortExactRelation_mem_shortExactSubgroup (K : Type u) [Field K]
    (S : ShortExactSequence.{u, v} K) :
    shortExactRelation K S ∈
      (shortExactSubgroup K : AddSubgroup (VirtualEndomorphism.{u, v} K)) := by
  exact AddSubgroup.subset_closure (Or.inr <| Or.inr <| Or.inr ⟨S, rfl⟩)

theorem additive_ofMul_mul_sub_sub_eq_zero (u v : (RatFunc K)ˣ) :
    Additive.ofMul (u * v) - Additive.ofMul u - Additive.ofMul v = 0 := by
  exact sub_eq_zero.mpr
    (Eq.trans
      (show Additive.ofMul (u * v) - Additive.ofMul u =
          (Additive.ofMul u + Additive.ofMul v) - Additive.ofMul u from rfl)
      (add_sub_cancel_left (Additive.ofMul u) (Additive.ofMul v)))

theorem sub_add_sub_eq_zero_of_eq_add {G : Type*} [AddCommGroup G]
    {x y z : G} (h : x = y + z) : x - y - z = 0 := by
  exact sub_eq_zero.mpr
    (Eq.trans (congrArg (fun t => t - y) h) (add_sub_cancel_left y z))

/-- The determinant character kills the short exact sequence relation. -/
theorem determinantCharacter_shortExactRelation
    (S : ShortExactSequence.{u, v} K) :
    determinantCharacter K (shortExactRelation K S) = 0 := by
  calc
    determinantCharacter K (shortExactRelation K S)
        = determinantCharacter K (of K S.middle - of K S.left) -
            determinantCharacter K (of K S.right) := by
          exact map_sub (determinantCharacter K) (of K S.middle - of K S.left) (of K S.right)
    _ = (determinantCharacter K (of K S.middle) -
            determinantCharacter K (of K S.left)) -
            determinantCharacter K (of K S.right) := by
          exact congrArg (fun t => t - determinantCharacter K (of K S.right))
            (map_sub (determinantCharacter K) (of K S.middle) (of K S.left))
    _ = Additive.ofMul (EndomorphismObject.determinantUnit S.middle) -
          Additive.ofMul (EndomorphismObject.determinantUnit S.left) -
          Additive.ofMul (EndomorphismObject.determinantUnit S.right) := by
          exact Eq.trans
            (congrArg
              (fun t => (determinantCharacter K (of K S.middle) -
                determinantCharacter K (of K S.left)) - t)
              (determinantCharacter_of (K := K) S.right))
            (congrArg₂
              (fun a b => a - b - Additive.ofMul (EndomorphismObject.determinantUnit S.right))
              (determinantCharacter_of (K := K) S.middle)
              (determinantCharacter_of (K := K) S.left))
    _ = 0 := by
          exact Eq.trans
            (congrArg (fun t => Additive.ofMul t -
                Additive.ofMul (EndomorphismObject.determinantUnit S.left) -
                Additive.ofMul (EndomorphismObject.determinantUnit S.right))
              S.shortExact_determinantUnit_mul)
            (additive_ofMul_mul_sub_sub_eq_zero
              (K := K) (EndomorphismObject.determinantUnit S.left)
              (EndomorphismObject.determinantUnit S.right))

/-- The first trace character kills the short exact sequence relation. -/
theorem traceCharacter_one_shortExactRelation
    (S : ShortExactSequence.{u, v} K) :
    traceCharacter K 1 (shortExactRelation K S) = 0 := by
  calc
    traceCharacter K 1 (shortExactRelation K S)
        = traceCharacter K 1 (of K S.middle - of K S.left) -
            traceCharacter K 1 (of K S.right) := by
          exact map_sub (traceCharacter K 1) (of K S.middle - of K S.left) (of K S.right)
    _ = (traceCharacter K 1 (of K S.middle) -
            traceCharacter K 1 (of K S.left)) -
            traceCharacter K 1 (of K S.right) := by
          exact congrArg (fun t => t - traceCharacter K 1 (of K S.right))
            (map_sub (traceCharacter K 1) (of K S.middle) (of K S.left))
    _ = EndomorphismObject.tracePower 1 S.middle -
          EndomorphismObject.tracePower 1 S.left -
          EndomorphismObject.tracePower 1 S.right := by
          exact Eq.trans
            (congrArg
              (fun t => (traceCharacter K 1 (of K S.middle) -
                traceCharacter K 1 (of K S.left)) - t)
              (traceCharacter_of (K := K) 1 S.right))
            (congrArg₂ (fun a b => a - b - EndomorphismObject.tracePower 1 S.right)
              (traceCharacter_of (K := K) 1 S.middle)
              (traceCharacter_of (K := K) 1 S.left))
    _ = 0 := by
          change LinearMap.trace K S.middle.carrier S.middle.endomorphism -
              LinearMap.trace K S.left.carrier S.left.endomorphism -
              LinearMap.trace K S.right.carrier S.right.endomorphism = 0
          exact sub_add_sub_eq_zero_of_eq_add S.shortExact_trace_additivity

/-- The determinant character kills the full exact-sequence relation subgroup. -/
theorem shortExactSubgroup_le_determinantCharacter_ker :
    shortExactSubgroup K ≤ (determinantCharacter K).ker := by
  change AddSubgroup.closure (shortExactGeneratingSet K) ≤
    (determinantCharacter K).ker
  exact (AddSubgroup.closure_le ((determinantCharacter K).ker)).2
    (fun x hx =>
      match hx with
      | Or.inl ⟨A, B, h⟩ =>
          h ▸ determinantCharacter_directSumRelation K A B
      | Or.inr (Or.inl ⟨A, B, e, h⟩) =>
          h ▸ determinantCharacter_conjRelation K A e
      | Or.inr (Or.inr (Or.inl ⟨A, hA, h⟩)) =>
          h ▸ determinantCharacter_zeroObject K A hA
      | Or.inr (Or.inr (Or.inr ⟨S, h⟩)) =>
          h ▸ determinantCharacter_shortExactRelation (K := K) S)

/-- The first trace character kills the full exact-sequence relation subgroup. -/
theorem shortExactSubgroup_le_traceCharacter_one_ker :
    shortExactSubgroup K ≤ (traceCharacter K 1).ker := by
  change AddSubgroup.closure (shortExactGeneratingSet K) ≤
    (traceCharacter K 1).ker
  exact (AddSubgroup.closure_le ((traceCharacter K 1).ker)).2
    (fun x hx =>
      match hx with
      | Or.inl ⟨A, B, h⟩ =>
          h ▸ traceCharacter_directSumRelation K 1 A B
      | Or.inr (Or.inl ⟨A, B, e, h⟩) =>
          h ▸ traceCharacter_conjRelation K 1 A e
      | Or.inr (Or.inr (Or.inl ⟨A, hA, h⟩)) =>
          h ▸ traceCharacter_zeroObject K 1 A hA
      | Or.inr (Or.inr (Or.inr ⟨S, h⟩)) =>
          h ▸ traceCharacter_one_shortExactRelation (K := K) S)

end ShortExactSequence

/-- The exact-sequence quotient of virtual finite-dimensional endomorphism
classes. -/
abbrev K0Exact (K : Type u) [Field K] :=
  VirtualEndomorphism.{u, v} K ⧸ ShortExactSequence.shortExactSubgroup K

/-- The quotient map to the exact-sequence K₀ group. -/
def mkExact (K : Type u) [Field K] : VirtualEndomorphism.{u, v} K →+ K0Exact.{u, v} K :=
  QuotientAddGroup.mk' (ShortExactSequence.shortExactSubgroup (K := K))

/-- The determinant character descends to the exact-sequence quotient. -/
def determinantCharacterK0Exact : K0Exact.{u, v} K →+ Additive ((RatFunc K)ˣ) :=
  QuotientAddGroup.lift (ShortExactSequence.shortExactSubgroup (K := K)) (determinantCharacter K)
    (ShortExactSequence.shortExactSubgroup_le_determinantCharacter_ker (K := K))

theorem determinantCharacterK0ExactMul_map_mul
    (x y : Multiplicative (K0Exact.{u, v} K)) :
    Additive.toMul (determinantCharacterK0Exact K (Multiplicative.toAdd (x * y))) =
      Additive.toMul (determinantCharacterK0Exact K (Multiplicative.toAdd x)) *
        Additive.toMul (determinantCharacterK0Exact K (Multiplicative.toAdd y)) :=
  Eq.trans
    (congrArg Additive.toMul
      (map_add (determinantCharacterK0Exact K) (Multiplicative.toAdd x)
        (Multiplicative.toAdd y)))
    (toMul_add _ _)

/-- Multiplicative form of the determinant character on the exact-sequence
quotient. -/
def determinantCharacterK0ExactMul : Multiplicative (K0Exact.{u, v} K) →* (RatFunc K)ˣ where
  toFun x := Additive.toMul (determinantCharacterK0Exact (K := K) (Multiplicative.toAdd x))
  map_one' := by
    change Additive.toMul (determinantCharacterK0Exact K 0) = 1
    exact rfl
  map_mul' x y := by
    exact determinantCharacterK0ExactMul_map_mul (K := K) x y

theorem determinantCharacterK0ExactMul_ofAdd (x : K0Exact.{u, v} K) :
    determinantCharacterK0ExactMul K (Multiplicative.ofAdd x) =
      Additive.toMul (determinantCharacterK0Exact K x) :=
  rfl

theorem determinantCharacterK0Exact_mk (x : VirtualEndomorphism.{u, v} K) :
    determinantCharacterK0Exact K (mkExact K x) = determinantCharacter K x :=
  QuotientAddGroup.lift_mk (ShortExactSequence.shortExactSubgroup (K := K))
    (ShortExactSequence.shortExactSubgroup_le_determinantCharacter_ker (K := K)) x

theorem determinantCharacterK0Exact_of (A : EndomorphismObject.{u, v} K) :
    determinantCharacterK0Exact K (mkExact K (of K A)) =
      Additive.ofMul (EndomorphismObject.determinantUnit A) :=
  Eq.trans
    (determinantCharacterK0Exact_mk (K := K) (of K A))
    (determinantCharacter_of (K := K) A)

theorem determinantCharacterK0ExactMul_of (A : EndomorphismObject.{u, v} K) :
    determinantCharacterK0ExactMul (K := K) (Multiplicative.ofAdd (mkExact K (of K A))) =
      EndomorphismObject.determinantUnit A :=
  Eq.trans
    (determinantCharacterK0ExactMul_ofAdd (K := K) (mkExact K (of K A)))
    (congrArg Additive.toMul (determinantCharacterK0Exact_of (K := K) A))

/-- The first trace character descends to the exact-sequence quotient. -/
def traceCharacterOneK0Exact : K0Exact.{u, v} K →+ K :=
  QuotientAddGroup.lift (ShortExactSequence.shortExactSubgroup (K := K)) (traceCharacter K 1)
    (ShortExactSequence.shortExactSubgroup_le_traceCharacter_one_ker (K := K))

theorem traceCharacterOneK0Exact_mk (x : VirtualEndomorphism.{u, v} K) :
    traceCharacterOneK0Exact K (mkExact K x) = traceCharacter K 1 x :=
  QuotientAddGroup.lift_mk (ShortExactSequence.shortExactSubgroup (K := K))
    (ShortExactSequence.shortExactSubgroup_le_traceCharacter_one_ker (K := K)) x

theorem traceCharacterOneK0Exact_of (A : EndomorphismObject.{u, v} K) :
    traceCharacterOneK0Exact K (mkExact K (of K A)) = EndomorphismObject.tracePower 1 A :=
  Eq.trans
    (traceCharacterOneK0Exact_mk (K := K) (of K A))
    (traceCharacter_of (K := K) 1 A)

end

end EndomorphismK0
end Boundary
