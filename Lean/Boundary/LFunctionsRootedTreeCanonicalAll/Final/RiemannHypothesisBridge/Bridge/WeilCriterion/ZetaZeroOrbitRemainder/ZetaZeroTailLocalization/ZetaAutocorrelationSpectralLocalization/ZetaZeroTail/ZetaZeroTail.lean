import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroOrbitContribution.ZetaZeroOrbitContribution
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeRapidPower
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicitySummability
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaCenteredZeroVerticalStrip.ZetaCenteredZeroVerticalStrip
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaAdmissiblePaleyWiener

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
  have hheight :
      0 ≤ zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)) :=
    zpow_nonneg
      (le_trans zero_le_one (zetaCompletedZeroCenteredHeight_ge_one ρ))
      (-(k + 3 : ℤ))
  exact mul_nonneg hA hheight

/-- Polynomial zero-side envelopes are summable over the completed-zero locus
after choosing the envelope exponent beyond the zero-counting degree.

This is the zero-counting owner theorem in the form consumed by the tail
majorant: the envelope index records the necessary counting margin. -/
theorem summable_zetaZeroMultiplicityTransformEnvelope_of_counting_bound
    (A C : ℝ) (d k : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroMultiplicityTransformEnvelope A (d + k) ρ) := by
  have hbase :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) :=
    summable_completedZero_centeredHeight_negativePower_of_counting_bound
      C d k hCpos hcount
  unfold zetaZeroMultiplicityTransformEnvelope
  exact hbase.const_mul A

/-- Polynomial growth envelope for completed-zero multiplicities. -/
noncomputable def zetaZeroMultiplicityGrowthEnvelope
    (M : ℝ) (d : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  M * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ)

/-- Rapid-decay envelope for the spectral transform evaluated at completed zeros. -/
noncomputable def zetaZeroSpectralEvalDecayEnvelope
    (B : ℝ) (N : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  B * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))

/-- Product envelope obtained before absorbing growth and decay into one polynomial tail. -/
noncomputable def zetaZeroGrowthDecayProductEnvelope
    (M : ℝ) (d : ℕ) (B : ℝ) (N : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  zetaZeroMultiplicityGrowthEnvelope M d ρ *
    zetaZeroSpectralEvalDecayEnvelope B N ρ

/-- Multiplicity growth envelopes are nonnegative for positive constants. -/
theorem zetaZeroMultiplicityGrowthEnvelope_nonnegative
    {M : ℝ} (hM : 0 < M) (d : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    0 ≤ zetaZeroMultiplicityGrowthEnvelope M d ρ := by
  unfold zetaZeroMultiplicityGrowthEnvelope
  have hheight :
      0 ≤ zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) :=
    zpow_nonneg
      (le_trans zero_le_one (zetaCompletedZeroCenteredHeight_ge_one ρ))
      (d : ℤ)
  exact mul_nonneg (le_of_lt hM) hheight

/-- Spectral decay envelopes are nonnegative for positive constants. -/
theorem zetaZeroSpectralEvalDecayEnvelope_nonnegative
    {B : ℝ} (hB : 0 < B) (N : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    0 ≤ zetaZeroSpectralEvalDecayEnvelope B N ρ := by
  unfold zetaZeroSpectralEvalDecayEnvelope
  have hheight :
      0 ≤ zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)) :=
    zpow_nonneg
      (le_trans zero_le_one (zetaCompletedZeroCenteredHeight_ge_one ρ))
      (-(N : ℤ))
  exact mul_nonneg (le_of_lt hB) hheight

/-- Growth-decay product envelopes unfold to one constant times one power product. -/
theorem zetaZeroGrowthDecayProductEnvelope_eq_constant_mul_powerProduct
    (M : ℝ) (d : ℕ) (B : ℝ) (N : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaZeroGrowthDecayProductEnvelope M d B N ρ =
      (M * B) *
        (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
          zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))) := by
  unfold zetaZeroGrowthDecayProductEnvelope
  unfold zetaZeroMultiplicityGrowthEnvelope
  unfold zetaZeroSpectralEvalDecayEnvelope
  calc
    (M * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ)) *
        (B * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))) =
        M *
          (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
            (B * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)))) := by
      exact mul_assoc M
        (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ))
        (B * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)))
    _ =
        M *
          (B *
            (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
              zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)))) := by
      exact congrArg (fun x : ℝ => M * x)
        (by
          calc
            zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
                (B * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))) =
                (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) * B) *
                  zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)) := by
              exact (mul_assoc
                (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ))
                B
                (zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)))).symm
            _ =
                (B * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ)) *
                  zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)) := by
              exact congrArg
                (fun x : ℝ => x * zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)))
                (mul_comm (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ)) B)
            _ =
                B *
                  (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
                    zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))) := by
              exact mul_assoc B
                (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ))
                (zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))))
    _ =
        (M * B) *
          (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
            zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ))) := by
      exact (mul_assoc M B
        (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
          zetaCompletedZeroCenteredHeight ρ ^ (-(N : ℤ)))).symm

/-- If the decay exponent is chosen past the growth degree, the product power is bounded
by the requested zero-tail decay power. -/
theorem zetaZero_height_growth_mul_decay_le_requestedDecay
    (d k : ℕ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
        zetaCompletedZeroCenteredHeight ρ ^ (-(d + (k + 3) + 1 : ℤ)) ≤
      zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)) := by
  exact ZetaAdmissibleFunction.polynomialDegreeTimesRapidPower_le_requestedRapidPower
    d
    (k + 3)
    (zetaCompletedZeroCenteredHeight ρ)
    (zetaCompletedZeroCenteredHeight_ge_one ρ)

/-- A growth-decay envelope with sufficiently strong decay is bounded by a single
zero-tail transform envelope. -/
theorem zetaZeroGrowthDecayProductEnvelope_le_transformEnvelope_of_largeDecay
    (M : ℝ) (d : ℕ) (B : ℝ) (k : ℕ)
    (hM : 0 < M) (hB : 0 < B)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaZeroGrowthDecayProductEnvelope M d B (d + (k + 3) + 1) ρ ≤
      zetaZeroMultiplicityTransformEnvelope (M * B) k ρ := by
  have hconstant_nonneg : 0 ≤ M * B := by
    exact mul_nonneg (le_of_lt hM) (le_of_lt hB)
  have hpower :
      zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
          zetaCompletedZeroCenteredHeight ρ ^ (-(d + (k + 3) + 1 : ℤ)) ≤
        zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)) :=
    zetaZero_height_growth_mul_decay_le_requestedDecay d k ρ
  have hscaled :
      (M * B) *
          (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
            zetaCompletedZeroCenteredHeight ρ ^ (-(d + (k + 3) + 1 : ℤ))) ≤
        (M * B) *
          zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)) :=
    mul_le_mul_of_nonneg_left hpower hconstant_nonneg
  have hunfold :
      zetaZeroGrowthDecayProductEnvelope M d B (d + (k + 3) + 1) ρ =
        (M * B) *
          (zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) *
            zetaCompletedZeroCenteredHeight ρ ^ (-(d + (k + 3) + 1 : ℤ))) :=
    zetaZeroGrowthDecayProductEnvelope_eq_constant_mul_powerProduct
      M d B (d + (k + 3) + 1) ρ
  unfold zetaZeroMultiplicityTransformEnvelope
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ (M * B) * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))
    hunfold.symm
    hscaled

/-- Completed-zero multiplicities have polynomial growth in centered height. -/
theorem exists_zetaZeroMultiplicityGrowthEnvelope_bound :
    ∃ M : ℝ, ∃ d : ℕ,
      0 < M ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ ≤
          zetaZeroMultiplicityGrowthEnvelope M d ρ := by
  rcases exists_zetaZeroMultiplicityGrowthEnvelope_bound_from_counting with
    ⟨M, d, hMpos, hbound⟩
  refine ⟨M, d, hMpos, ?_⟩
  intro ρ
  unfold zetaZeroMultiplicityGrowthEnvelope
  exact hbound ρ

/-- A Paley-Wiener vertical-strip decay constant bounds spectral evaluation on the
centered completed-zero locus. -/
theorem zetaZeroSpectralEval_norm_le_of_verticalStripDecayConstant
    (φ : ZetaAdmissibleFunction) (N : ℕ)
    (a b C : ℝ)
    (hCbound :
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖Boundary.zetaLaplaceTransform φ.toZetaTestFunction' z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)))
    (hstrip :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        a ≤ (zetaCenteredZero (ρ : ℂ)).re ∧
          (zetaCenteredZero (ρ : ℂ)).re ≤ b)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ ≤
      zetaZeroSpectralEvalDecayEnvelope C N ρ := by
  have hρstrip :
      a ≤ (zetaCenteredZero (ρ : ℂ)).re ∧
        (zetaCenteredZero (ρ : ℂ)).re ≤ b :=
    hstrip ρ
  have hbound :
      ‖Boundary.zetaLaplaceTransform φ.toZetaTestFunction' (zetaCenteredZero (ρ : ℂ))‖ ≤
        C * (1 + ‖(zetaCenteredZero (ρ : ℂ)).im‖) ^ (-(N : ℤ)) :=
    hCbound
      (zetaCenteredZero (ρ : ℂ))
      hρstrip.1
      hρstrip.2
  have heval :
      zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ)) =
        Boundary.zetaLaplaceTransform φ.toZetaTestFunction' (zetaCenteredZero (ρ : ℂ)) :=
    zetaSpectralEval_eq_laplace φ (zetaCenteredZero (ρ : ℂ))
  unfold zetaZeroSpectralEvalDecayEnvelope
  unfold zetaCompletedZeroCenteredHeight
  exact Eq.subst
    (motive := fun x : ℂ =>
      ‖x‖ ≤ C * (1 + ‖(zetaCenteredZero (ρ : ℂ)).im‖) ^ (-(N : ℤ)))
    heval.symm
    hbound

/-- Paley-Wiener decay bounds the spectral transform on the completed-zero locus. -/
theorem exists_zetaZeroSpectralEvalDecayEnvelope_bound
    (φ : ZetaAdmissibleFunction) (N : ℕ) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ ≤
          zetaZeroSpectralEvalDecayEnvelope B N ρ := by
  rcases exists_zetaCenteredZero_fixed_vertical_strip with
    ⟨a, b, hstrip⟩
  rcases zetaLaplaceTransform_verticalStripRapidDecay_of_compactSupport_smooth
      φ a b N with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro ρ
  exact zetaZeroSpectralEval_norm_le_of_verticalStripDecayConstant
    φ N a b C hCbound hstrip ρ

/-- Separate multiplicity and spectral bounds give a product-envelope bound for the
multiplicity-weighted transform majorant. -/
theorem zetaZeroMultiplicityTransformMajorant_le_growthDecayProductEnvelope
    (φ : ZetaAdmissibleFunction)
    (M : ℝ) (d : ℕ) (B : ℝ) (N : ℕ)
    (hgrowth :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ ≤
          zetaZeroMultiplicityGrowthEnvelope M d ρ)
    (hdecay :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ ≤
          zetaZeroSpectralEvalDecayEnvelope B N ρ) :
    ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
      zetaZeroMultiplicityTransformMajorant φ ρ ≤
        zetaZeroGrowthDecayProductEnvelope M d B N ρ := by
  intro ρ
  unfold zetaZeroMultiplicityTransformMajorant
  unfold zetaZeroGrowthDecayProductEnvelope
  have hleft_nonneg :
      0 ≤ ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ :=
    norm_nonneg (zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ)))
  have hright_left_nonneg :
      0 ≤ zetaZeroMultiplicityGrowthEnvelope M d ρ :=
    le_trans
      (norm_nonneg ((zetaZeroMultiplicity (ρ : ℂ) : ℂ)))
      (hgrowth ρ)
  exact mul_le_mul
    (hgrowth ρ)
    (hdecay ρ)
    hleft_nonneg
    hright_left_nonneg

/-- A growth-decay product with requested strong decay is absorbed by a single summable
polynomial envelope. -/
theorem exists_zetaZeroGrowthDecayProductEnvelope_le_transformEnvelope_of_requestedDecay
    (M : ℝ) (d : ℕ) (B : ℝ)
    (hM : 0 < M) (hB : 0 < B) :
    ∃ A : ℝ, ∃ k : ℕ,
      0 < A ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        zetaZeroGrowthDecayProductEnvelope M d B (d + (k + 3) + 1) ρ ≤
          zetaZeroMultiplicityTransformEnvelope A k ρ := by
  refine ⟨M * B, 0, ?_, ?_⟩
  · exact mul_pos hM hB
  · intro ρ
    exact zetaZeroGrowthDecayProductEnvelope_le_transformEnvelope_of_largeDecay
      M d B 0 hM hB ρ

/-- Multiplicity growth and transform decay combine into the zero-side transform envelope. -/
theorem exists_zetaZeroMultiplicityTransformEnvelope_bound_of_growth_and_decay
    (φ : ZetaAdmissibleFunction)
    (hgrowth :
      ∃ M : ℝ, ∃ d : ℕ,
        0 < M ∧
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ ≤
            zetaZeroMultiplicityGrowthEnvelope M d ρ)
    (hdecay :
      ∀ N : ℕ, ∃ B : ℝ,
        0 < B ∧
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ‖zetaSpectralEval φ (zetaCenteredZero (ρ : ℂ))‖ ≤
            zetaZeroSpectralEvalDecayEnvelope B N ρ) :
    ∃ A : ℝ, ∃ k : ℕ,
      0 < A ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        zetaZeroMultiplicityTransformMajorant φ ρ ≤
          zetaZeroMultiplicityTransformEnvelope A k ρ := by
  rcases hgrowth with ⟨M, d, hMpos, hgrowth_bound⟩
  rcases hdecay (d + (0 + 3) + 1) with ⟨B, hBpos, hdecay_bound⟩
  refine ⟨M * B, 0, mul_pos hMpos hBpos, ?_⟩
  intro ρ
  have hmajorant_product :
      zetaZeroMultiplicityTransformMajorant φ ρ ≤
        zetaZeroGrowthDecayProductEnvelope M d B (d + (0 + 3) + 1) ρ :=
    zetaZeroMultiplicityTransformMajorant_le_growthDecayProductEnvelope
      φ M d B (d + (0 + 3) + 1) hgrowth_bound hdecay_bound ρ
  have hproduct :
      zetaZeroGrowthDecayProductEnvelope M d B (d + (0 + 3) + 1) ρ ≤
        zetaZeroMultiplicityTransformEnvelope (M * B) 0 ρ :=
    zetaZeroGrowthDecayProductEnvelope_le_transformEnvelope_of_largeDecay
      M d B 0 hMpos hBpos ρ
  exact le_trans hmajorant_product hproduct

/-- Zero multiplicity growth and Paley-Wiener transform decay give a summable polynomial
envelope for the multiplicity-weighted transform majorant. -/
theorem exists_zetaZeroMultiplicityTransformEnvelope_bound
    (φ : ZetaAdmissibleFunction) :
    ∃ A : ℝ, ∃ k : ℕ,
      0 < A ∧
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroMultiplicityTransformEnvelope A k ρ) ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        zetaZeroMultiplicityTransformMajorant φ ρ ≤
          zetaZeroMultiplicityTransformEnvelope A k ρ := by
  rcases exists_completedZeroMultiplicityCounting_height_bound with
    ⟨C, dCount, hCpos, hcount⟩
  rcases exists_zetaZeroMultiplicityGrowthEnvelope_bound with
    ⟨M, dGrowth, hMpos, hgrowth_bound⟩
  let k : ℕ := dCount + (dGrowth + 1)
  rcases exists_zetaZeroSpectralEvalDecayEnvelope_bound
      φ
      (dGrowth + (k + 3) + 1) with
    ⟨B, hBpos, hdecay_bound⟩
  refine ⟨M * B, k, mul_pos hMpos hBpos, ?_, ?_⟩
  · change
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroMultiplicityTransformEnvelope (M * B)
            (dCount + (dGrowth + 1)) ρ)
    exact summable_zetaZeroMultiplicityTransformEnvelope_of_counting_bound
      (M * B) C dCount (dGrowth + 1) hCpos hcount
  · intro ρ
    have hmajorant_product :
        zetaZeroMultiplicityTransformMajorant φ ρ ≤
          zetaZeroGrowthDecayProductEnvelope M dGrowth B
            (dGrowth + (k + 3) + 1) ρ :=
      zetaZeroMultiplicityTransformMajorant_le_growthDecayProductEnvelope
        φ M dGrowth B
        (dGrowth + (k + 3) + 1)
        hgrowth_bound
        hdecay_bound
        ρ
    have hproduct :
        zetaZeroGrowthDecayProductEnvelope M dGrowth B
            (dGrowth + (k + 3) + 1) ρ ≤
          zetaZeroMultiplicityTransformEnvelope (M * B) k ρ :=
      zetaZeroGrowthDecayProductEnvelope_le_transformEnvelope_of_largeDecay
        M dGrowth B k hMpos hBpos ρ
    exact le_trans hmajorant_product hproduct

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
    ⟨A, k, _hApos, henv, hbound⟩
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
