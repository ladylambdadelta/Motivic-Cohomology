import Boundary.LFunctions.ZetaZeroOrbitContribution

/-!
# Boundary zero-side tail

This file packages the tail functional as a consumer of the zero-side
definitions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The zero tail is the tsum over completed zeros outside the excluded set. -/
theorem zetaZeroTail_eq
    (S : Finset ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroTail S φ =
      tsum (fun η : {η : ℂ // ZetaCompletedZero η ∧ η ∉ S} =>
        zetaZeroSideContribution (η : ℂ) φ) := by
  rfl

/-- The real-valued zero tail is the real part of the complex one. -/
theorem zetaZeroTailRe_eq
    (S : Finset ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroTailRe S φ = Complex.re (zetaZeroTail S φ) := by
  rfl

/-- The completed-zero subtype splits into a selected finite part and its complement. -/
noncomputable def completedZeroSubtypeFiniteComplementEquiv
    (S : Finset ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η) :
    {ρ : ℂ // ZetaCompletedZero ρ} ≃
      (S.attach ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}) := by
  classical
  refine
    { toFun := fun ρ =>
        if hρ : (ρ : ℂ) ∈ S then
          Sum.inl ⟨(ρ : ℂ), hρ⟩
        else
          Sum.inr ⟨(ρ : ℂ), ρ.2, hρ⟩
      invFun := fun x =>
        match x with
        | Sum.inl η => ⟨(η : ℂ), hS (η : ℂ) η.2⟩
        | Sum.inr ρ => ⟨(ρ : ℂ), ρ.2.1⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro ρ
    by_cases hρ : (ρ : ℂ) ∈ S
    · change
        (match
            (if h : (ρ : ℂ) ∈ S then
              Sum.inl ⟨(ρ : ℂ), h⟩
            else
              Sum.inr ⟨(ρ : ℂ), ρ.2, h⟩) with
          | Sum.inl η => ⟨(η : ℂ), hS (η : ℂ) η.2⟩
          | Sum.inr ρ => ⟨(ρ : ℂ), ρ.2.1⟩) = ρ
      have hif :
          (if h : (ρ : ℂ) ∈ S then
              Sum.inl ⟨(ρ : ℂ), h⟩
            else
              Sum.inr ⟨(ρ : ℂ), ρ.2, h⟩) =
            Sum.inl ⟨(ρ : ℂ), hρ⟩ :=
        dif_pos hρ
      exact Eq.subst
        (motive := fun x : S.attach ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          (match x with
          | Sum.inl η => ⟨(η : ℂ), hS (η : ℂ) η.2⟩
          | Sum.inr ρ => ⟨(ρ : ℂ), ρ.2.1⟩) = ρ)
        hif.symm
        (Subtype.ext rfl)
    · change
        (match
            (if h : (ρ : ℂ) ∈ S then
              Sum.inl ⟨(ρ : ℂ), h⟩
            else
              Sum.inr ⟨(ρ : ℂ), ρ.2, h⟩) with
          | Sum.inl η => ⟨(η : ℂ), hS (η : ℂ) η.2⟩
          | Sum.inr ρ => ⟨(ρ : ℂ), ρ.2.1⟩) = ρ
      have hif :
          (if h : (ρ : ℂ) ∈ S then
              Sum.inl ⟨(ρ : ℂ), h⟩
            else
              Sum.inr ⟨(ρ : ℂ), ρ.2, h⟩) =
            Sum.inr ⟨(ρ : ℂ), ρ.2, hρ⟩ :=
        dif_neg hρ
      exact Eq.subst
        (motive := fun x : S.attach ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          (match x with
          | Sum.inl η => ⟨(η : ℂ), hS (η : ℂ) η.2⟩
          | Sum.inr ρ => ⟨(ρ : ℂ), ρ.2.1⟩) = ρ)
        hif.symm
        (Subtype.ext rfl)
  · intro x
    cases x with
    | inl η =>
        change
          (if h : (((⟨(η : ℂ), hS (η : ℂ) η.2⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) ∈ S) then
              Sum.inl
                ⟨(((⟨(η : ℂ), hS (η : ℂ) η.2⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ)), h⟩
            else
              Sum.inr
                ⟨(((⟨(η : ℂ), hS (η : ℂ) η.2⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ)),
                  (⟨(η : ℂ), hS (η : ℂ) η.2⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}).2,
                  h⟩) = Sum.inl η
        have hif :
            (if h : (((⟨(η : ℂ), hS (η : ℂ) η.2⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) ∈ S) then
                Sum.inl
                  ⟨(((⟨(η : ℂ), hS (η : ℂ) η.2⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ)), h⟩
              else
                Sum.inr
                  ⟨(((⟨(η : ℂ), hS (η : ℂ) η.2⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ)),
                    (⟨(η : ℂ), hS (η : ℂ) η.2⟩ :
                      {ρ : ℂ // ZetaCompletedZero ρ}).2,
                    h⟩) =
              Sum.inl ⟨(η : ℂ), η.2⟩ :=
          dif_pos η.2
        exact Eq.subst
          (motive := fun y : S.attach ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
            y = Sum.inl η)
          hif.symm
          (congrArg Sum.inl (Subtype.ext rfl))
    | inr ρ =>
        change
          (if h : (((⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) ∈ S) then
              Sum.inl
                ⟨(((⟨(ρ : ℂ), ρ.2.1⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ)), h⟩
            else
              Sum.inr
                ⟨(((⟨(ρ : ℂ), ρ.2.1⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ)),
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}).2,
                  h⟩) = Sum.inr ρ
        have hif :
            (if h : (((⟨(ρ : ℂ), ρ.2.1⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) ∈ S) then
                Sum.inl
                  ⟨(((⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ)), h⟩
              else
                Sum.inr
                  ⟨(((⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ)),
                    (⟨(ρ : ℂ), ρ.2.1⟩ :
                      {ρ : ℂ // ZetaCompletedZero ρ}).2,
                    h⟩) =
              Sum.inr ⟨(ρ : ℂ), ρ.2.1, ρ.2.2⟩ :=
          dif_neg ρ.2.2
        exact Eq.subst
          (motive := fun y : S.attach ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
            y = Sum.inr ρ)
        hif.symm
          (congrArg Sum.inr (Subtype.ext rfl))

/-- Transport the completed-zero `tsum` across the finite/complement equivalence. -/
theorem completedZeroSubtype_tsum_eq_sumType_tsum_of_equiv
    (S : Finset ℂ)
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (hF : Summable F) :
    (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ}, F ρ) =
      (∑' x : S.attach ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm x)) := by
  exact ((completedZeroSubtypeFiniteComplementEquiv S hS).symm.tsum_eq F).symm

/-- The left summand is equivalent to the range of the left injection. -/
def sumInlRangeEquiv (α β : Type*) :
    α ≃ Set.range (Sum.inl : α → α ⊕ β) where
  toFun := fun a => ⟨Sum.inl a, ⟨a, rfl⟩⟩
  invFun := fun x =>
    match x.1 with
    | Sum.inl a => a
    | Sum.inr _ =>
        False.elim
          (by
            rcases x.2 with ⟨a, ha⟩
            cases ha)
  left_inv := by
    intro a
    rfl
  right_inv := by
    intro x
    cases x with
    | mk y hy =>
        cases y with
        | inl a => rfl
        | inr b =>
            exfalso
            rcases hy with ⟨a, ha⟩
            cases ha

/-- The right summand is equivalent to the complement of the left-injection range. -/
def sumInlRangeComplEquiv (α β : Type*) :
    β ≃ ((Set.range (Sum.inl : α → α ⊕ β))ᶜ : Set (α ⊕ β)) where
  toFun := fun b =>
    ⟨Sum.inr b,
      fun h =>
        match h with
        | ⟨_, ha⟩ => by cases ha⟩
  invFun := fun x =>
    match x.1 with
    | Sum.inl a => False.elim (x.2 ⟨a, rfl⟩)
    | Sum.inr b => b
  left_inv := by
    intro b
    rfl
  right_inv := by
    intro x
    cases x with
    | mk y hy =>
        cases y with
        | inl a =>
            exfalso
            exact hy ⟨a, rfl⟩
        | inr b => rfl

/-- Summability on both summands gives summability on their sum type. -/
theorem complex_summable_sum_type_of_summable_faces
    {α β : Type*}
    (G : α ⊕ β → ℂ)
    (hleft : Summable (fun a : α => G (Sum.inl a)))
    (hright : Summable (fun b : β => G (Sum.inr b))) :
    Summable G := by
  let s : Set (α ⊕ β) := Set.range (Sum.inl : α → α ⊕ β)
  have hleftSubtype : Summable (fun x : s => G x) := by
    exact ((sumInlRangeEquiv α β).summable_iff).mp hleft
  have hrightSubtype : Summable (fun x : sᶜ => G x) := by
    exact ((sumInlRangeComplEquiv α β).summable_iff).mp hright
  exact summable_subtype_and_compl.1 ⟨hleftSubtype, hrightSubtype⟩

/-- A complex-valued `tsum` over a sum type splits into its two oriented faces.

This is the generic topology owner lemma behind finite/complement decompositions. -/
theorem complex_tsum_sum_type_eq_add_of_summable_faces
    {α β : Type*}
    (G : α ⊕ β → ℂ)
    (hleft : Summable (fun a : α => G (Sum.inl a)))
    (hright : Summable (fun b : β => G (Sum.inr b))) :
    (∑' x : α ⊕ β, G x) =
      (∑' a : α, G (Sum.inl a)) +
        (∑' b : β, G (Sum.inr b)) := by
  let s : Set (α ⊕ β) := Set.range (Sum.inl : α → α ⊕ β)
  have htotal : Summable G :=
    complex_summable_sum_type_of_summable_faces G hleft hright
  have hsplit :
      (∑' x : s, G x) + (∑' x : sᶜ, G x) =
        (∑' x : α ⊕ β, G x) :=
    tsum_subtype_add_tsum_subtype_compl htotal s
  have hleft_tsum :
      (∑' x : s, G x) = ∑' a : α, G (Sum.inl a) :=
    ((sumInlRangeEquiv α β).tsum_eq (fun x : s => G x)).symm
  have hright_tsum :
      (∑' x : sᶜ, G x) = ∑' b : β, G (Sum.inr b) :=
    ((sumInlRangeComplEquiv α β).tsum_eq (fun x : sᶜ => G x)).symm
  exact hsplit.symm.trans
    (congrArg₂
      (fun u v : ℂ => u + v)
      hleft_tsum
      hright_tsum)

/-- Restricting a summable completed-zero family to the selected finite face is summable. -/
theorem completedZeroFiniteFace_summable
    (S : Finset ℂ)
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (hF : Summable F) :
    Summable (fun η : S.attach => F ⟨η, hS η η.2⟩) := by
  have hinj :
      Function.Injective
        (fun η : S.attach =>
          (⟨η, hS η η.2⟩ : {ρ : ℂ // ZetaCompletedZero ρ})) := by
    intro η μ hημ
    exact Subtype.ext (congrArg Subtype.val hημ)
  exact hF.comp_injective hinj

/-- Restricting a summable completed-zero family to the complementary tail face is summable. -/
theorem completedZeroComplementFace_summable
    (S : Finset ℂ)
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hF : Summable F) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
        F ⟨ρ, ρ.2.1⟩) := by
  have hinj :
      Function.Injective
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          (⟨ρ, ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ})) := by
    intro ρ η hρη
    exact Subtype.ext (congrArg Subtype.val hρη)
  exact hF.comp_injective hinj

/-- Split the finite/complement sum-type `tsum` into the selected finite side and the
complementary tail side. -/
theorem completedZeroFiniteComplement_sumType_tsum_eq_add
    (S : Finset ℂ)
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (hF : Summable F) :
    (∑' x : S.attach ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm x)) =
      (∑' η : S.attach, F ⟨η, hS η η.2⟩) +
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}, F ⟨ρ, ρ.2.1⟩) := by
  let G :
      S.attach ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} → ℂ :=
    fun x => F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm x)
  have hleft : Summable (fun η : S.attach => F ⟨η, hS η η.2⟩) :=
    completedZeroFiniteFace_summable S F hS hF
  have hright :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          F ⟨ρ, ρ.2.1⟩) :=
    completedZeroComplementFace_summable S F hF
  have hleftG : Summable (fun η : S.attach => G (Sum.inl η)) :=
    hleft
  have hrightG :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          G (Sum.inr ρ)) :=
    hright
  exact complex_tsum_sum_type_eq_add_of_summable_faces G hleftG hrightG

/-- A complex-valued `tsum` over a finite type is the finite sum over any finset that lists
all elements. -/
theorem complex_tsum_fintype_eq_finset_sum_of_finset_eq_univ
    {α : Type*} [Fintype α]
    (s : Finset α) (hs : s = Finset.univ)
    (G : α → ℂ) :
    (∑' a : α, G a) = ∑ a in s, G a := by
  have htsum :
      (∑' a : α, G a) = ∑ a : α, G a :=
    tsum_fintype G
  have hfinset :
      (∑ a : α, G a) = ∑ a in s, G a :=
    congrArg (fun t : Finset α => ∑ a in t, G a) hs.symm
  exact htsum.trans hfinset

/-- The selected finite side of the completed-zero split is a finite sum over `S.attach`. -/
theorem completedZeroFiniteSubtype_tsum_eq_finset_sum
    (S : Finset ℂ)
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η) :
    (∑' η : S.attach, F ⟨η, hS η η.2⟩) =
      ∑ η in S.attach, F ⟨η, hS η η.2⟩ := by
  exact
    complex_tsum_fintype_eq_finset_sum_of_finset_eq_univ
      S.attach
      Finset.attach_eq_univ
      (fun η : S.attach => F ⟨η, hS η η.2⟩)

/-- Finite/complement `tsum` transport for the completed-zero subtype. -/
theorem completedZeroSubtype_tsum_eq_finiteSubtype_add_complement_of_equiv
    (S : Finset ℂ)
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (hF : Summable F) :
    (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ}, F ρ) =
      (∑ η in S.attach, F ⟨η, hS η η.2⟩) +
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}, F ⟨ρ, ρ.2.1⟩) := by
  have htransport :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ}, F ρ) =
        (∑' x : S.attach ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
          F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm x)) :=
    completedZeroSubtype_tsum_eq_sumType_tsum_of_equiv S F hS hF
  have hsplit :
      (∑' x : S.attach ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
          F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm x)) =
        (∑' η : S.attach, F ⟨η, hS η η.2⟩) +
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}, F ⟨ρ, ρ.2.1⟩) :=
    completedZeroFiniteComplement_sumType_tsum_eq_add S F hS hF
  have hfinite :
      (∑' η : S.attach, F ⟨η, hS η η.2⟩) =
        ∑ η in S.attach, F ⟨η, hS η η.2⟩ :=
    completedZeroFiniteSubtype_tsum_eq_finset_sum S F hS
  exact htransport.trans
    (hsplit.trans
      (congrArg
        (fun x : ℂ =>
          x +
            (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
              F ⟨ρ, ρ.2.1⟩))
        hfinite))

/-- Pure finite-excision splitting for a completed-zero-indexed family.

This is the topology/root summability theorem behind zero-tail excision: a summable family
over the completed-zero subtype splits into the finite selected part and the complementary
subtype tail. -/
theorem completedZeroSubtype_tsum_eq_finiteSubtype_add_complement
    (S : Finset ℂ)
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (hF : Summable F) :
    (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ}, F ρ) =
      (∑ η in S.attach, F ⟨η, hS η η.2⟩) +
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}, F ⟨ρ, ρ.2.1⟩) := by
  exact completedZeroSubtype_tsum_eq_finiteSubtype_add_complement_of_equiv
    S F hS hF

/-- Generic finite-excision splitting for a completed-zero-indexed family.

This is the purely summability/topology root behind zero-tail excision.  The zeta-specific
theorem below only applies it to the zero-side contribution family. -/
theorem completedZeroSubtype_tsum_eq_finite_add_complement
    (S : Finset ℂ)
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (hF : Summable F) :
    (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ}, F ρ) =
      (∑ η in S.attach, F ⟨η, hS η η.2⟩) +
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}, F ⟨ρ, ρ.2.1⟩) :=
  completedZeroSubtype_tsum_eq_finiteSubtype_add_complement S F hS hF

/-- The attached finite zero-set sum is the ordinary finite zero-set contribution. -/
theorem zetaZeroSideContribution_sum_attach_eq_sum
    (S : Finset ℂ) (φ : ZetaAdmissibleFunction)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η) :
    (∑ η in S.attach,
      zetaZeroSideContribution
        ((⟨η, hS η η.2⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) φ) =
      ∑ η in S, zetaZeroSideContribution η φ := by
  exact Finset.sum_attach S (fun η : ℂ => zetaZeroSideContribution η φ)

/-- Majorant for the zero-side contribution over the completed-zero locus. -/
noncomputable def zetaZeroSideContributionMajorant
    (φ : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  ‖zetaZeroSideContribution (ρ : ℂ) φ‖

/-- The zero-side contribution is bounded by its majorant. -/
theorem norm_zetaZeroSideContribution_le_majorant
    (φ : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ‖zetaZeroSideContribution (ρ : ℂ) φ‖ ≤
      zetaZeroSideContributionMajorant φ ρ := by
  unfold zetaZeroSideContributionMajorant
  exact le_refl _

/-- Multiplicity-weighted transform majorant for a completed-zero contribution. -/
noncomputable def zetaZeroMultiplicityTransformMajorant
    (φ : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ *
    ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖

/-- The zero-side multiplicity-transform majorant is nonnegative. -/
theorem zetaZeroMultiplicityTransformMajorant_nonnegative
    (φ : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    0 ≤ zetaZeroMultiplicityTransformMajorant φ ρ := by
  unfold zetaZeroMultiplicityTransformMajorant
  exact mul_nonneg
    (norm_nonneg ((zetaZeroMultiplicity (ρ : ℂ) : ℂ)))
    (norm_nonneg (zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))))

/-- Vertical height of a completed zero after centering. -/
noncomputable def zetaCompletedZeroCenteredHeight
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  1 + ‖(zetaCenteredZero (ρ : ℂ)).im‖

/-- Polynomial zero-side envelope for multiplicity-weighted transform values. -/
noncomputable def zetaZeroMultiplicityTransformEnvelope
    (A : ℝ) (k : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))

/-- The zero-side envelope is nonnegative when its constant is nonnegative. -/
theorem zetaZeroMultiplicityTransformEnvelope_nonnegative
    {A : ℝ} (hA : 0 ≤ A) (k : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    0 ≤ zetaZeroMultiplicityTransformEnvelope A k ρ := by
  unfold zetaZeroMultiplicityTransformEnvelope
  unfold zetaCompletedZeroCenteredHeight
  have hheight :
      0 ≤ (1 + ‖(zetaCenteredZero (ρ : ℂ)).im‖) ^ (-(k + 3 : ℤ)) :=
    zpow_nonneg
      (add_nonneg zero_le_one
        (norm_nonneg ((zetaCenteredZero (ρ : ℂ)).im)))
      (-(k + 3 : ℤ))
  exact mul_nonneg hA hheight

/-- Polynomial zero-side envelopes are summable over the completed-zero locus.

This is the zero-counting owner theorem: completed zeros, counted with the centered
vertical height, have enough polynomial counting control for the chosen envelope. -/
theorem summable_zetaZeroMultiplicityTransformEnvelope
    (A : ℝ) (k : ℕ) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroMultiplicityTransformEnvelope A k ρ) := by
  sorry

/-- Zero multiplicity growth and Paley-Wiener transform decay give a summable polynomial
envelope for the multiplicity-weighted transform majorant. -/
theorem exists_zetaZeroMultiplicityTransformEnvelope_bound
    (φ : ZetaAdmissibleFunction) :
    ∃ A : ℝ, ∃ k : ℕ,
      0 < A ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        zetaZeroMultiplicityTransformMajorant φ ρ ≤
          zetaZeroMultiplicityTransformEnvelope A k ρ := by
  sorry

/-- The contribution majorant unfolds to multiplicity times transform size. -/
theorem zetaZeroSideContributionMajorant_eq_multiplicityTransformMajorant
    (φ : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaZeroSideContributionMajorant φ ρ =
      zetaZeroMultiplicityTransformMajorant φ ρ := by
  unfold zetaZeroSideContributionMajorant
  unfold zetaZeroMultiplicityTransformMajorant
  unfold zetaZeroSideContribution
  calc
    ‖-((zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
        zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ)))‖ =
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
          zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ := by
      exact norm_neg
        ((zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
          zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ)))
    _ =
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ *
          ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ := by
      exact norm_mul
        (zetaZeroMultiplicity (ρ : ℂ) : ℂ)
        (zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ)))

/-- Zero-counting, multiplicity, and Paley-Wiener transform decay make the
multiplicity-weighted transform majorant summable over the completed-zero locus. -/
theorem summable_zetaZeroMultiplicityTransformMajorant
    (φ : ZetaAdmissibleFunction) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroMultiplicityTransformMajorant φ ρ) := by
  rcases exists_zetaZeroMultiplicityTransformEnvelope_bound φ with
    ⟨A, k, _hApos, hbound⟩
  have henv :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroMultiplicityTransformEnvelope A k ρ) :=
    summable_zetaZeroMultiplicityTransformEnvelope A k
  have hnormBound :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖zetaZeroMultiplicityTransformMajorant φ ρ‖ ≤
          zetaZeroMultiplicityTransformEnvelope A k ρ := by
    intro ρ
    have hmajorant_nonneg :
        0 ≤ zetaZeroMultiplicityTransformMajorant φ ρ :=
      zetaZeroMultiplicityTransformMajorant_nonnegative φ ρ
    have hnorm :
        ‖zetaZeroMultiplicityTransformMajorant φ ρ‖ =
          zetaZeroMultiplicityTransformMajorant φ ρ :=
      Real.norm_of_nonneg hmajorant_nonneg
    exact Eq.subst
      (motive := fun x : ℝ =>
        x ≤ zetaZeroMultiplicityTransformEnvelope A k ρ)
      hnorm.symm
      (hbound ρ)
  exact Summable.of_norm_bounded
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      zetaZeroMultiplicityTransformEnvelope A k ρ)
    henv
    hnormBound

/-- Zero-density, multiplicity, and transform-decay estimates make the zero-side majorant
summable over the completed-zero locus. -/
theorem summable_zetaZeroSideContributionMajorant
    (φ : ZetaAdmissibleFunction) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroSideContributionMajorant φ ρ) := by
  have hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroMultiplicityTransformMajorant φ ρ) :=
    summable_zetaZeroMultiplicityTransformMajorant φ
  have hfun :
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContributionMajorant φ ρ) =
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroMultiplicityTransformMajorant φ ρ) := by
    funext ρ
    exact zetaZeroSideContributionMajorant_eq_multiplicityTransformMajorant φ ρ
  exact Eq.subst
    (motive := fun G : {ρ : ℂ // ZetaCompletedZero ρ} → ℝ => Summable G)
    hfun.symm
    hsum

/-- The completed zero-side contribution is summable over the completed zero locus.

This is the analytic convergence input that makes zero-tail excision a genuine decomposition
of the completed zero-side `tsum`. -/
theorem summable_zetaZeroSideContribution
    (φ : ZetaAdmissibleFunction) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroSideContribution (ρ : ℂ) φ) := by
  have hmajorant :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContributionMajorant φ ρ) :=
    summable_zetaZeroSideContributionMajorant φ
  unfold zetaZeroSideContributionMajorant at hmajorant
  exact hmajorant.of_norm

/-- Splitting the completed zero-side sum into a finite zero set and its complementary tail.

This is the complex owner form of zero-tail excision.  The excluded finite set must consist of
completed zeros, so its finite contribution can be compared with the ambient completed-zero
subtype sum. -/
theorem zetaCompletedZeroSideSum_eq_finite_add_tail
    (S : Finset ℂ) (φ : ZetaAdmissibleFunction)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) φ)) :
    (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        zetaZeroSideContribution (ρ : ℂ) φ) =
      (∑ η in S, zetaZeroSideContribution η φ) +
        zetaZeroTail S φ := by
  have hsplit :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          zetaZeroSideContribution (ρ : ℂ) φ) =
        (∑ η in S.attach,
          zetaZeroSideContribution
            ((⟨η, hS η η.2⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) φ) +
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
            zetaZeroSideContribution
              ((⟨ρ, ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) φ) :=
    completedZeroSubtype_tsum_eq_finite_add_complement
      S
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroSideContribution (ρ : ℂ) φ)
      hS
      hsum
  have hfinite :
      (∑ η in S.attach,
        zetaZeroSideContribution
          ((⟨η, hS η η.2⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) φ) =
        ∑ η in S, zetaZeroSideContribution η φ :=
    zetaZeroSideContribution_sum_attach_eq_sum S φ hS
  unfold zetaZeroTail
  exact Eq.trans hsplit
    (congrArg
      (fun x : ℂ =>
        x +
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
            zetaZeroSideContribution
              ((⟨ρ, ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℂ) φ))
      hfinite)

end
end LFunctions
end Boundary
