import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroOrbitContribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaCenteredZeroVerticalStrip.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.Owner

/-!
# Boundary zero-side tail

Split owner layer for the zero-side tail proof graph.  Public theorem names are
preserved through the root owner re-export.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The zero tail is the tsum over completed zeros outside the excluded set. -/
theorem zetaZeroTail_eq
    (S : Finset ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroTail S φ =
      tsum (fun η : {η : ℂ // ZetaCompletedZero η ∧ η ∉ S} =>
        zetaZeroSideContribution (η : ℂ) φ) :=
  Eq.refl (zetaZeroTail S φ)

/-- The real-valued zero tail is the real part of the complex one. -/
theorem zetaZeroTailRe_eq
    (S : Finset ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroTailRe S φ = Complex.re (zetaZeroTail S φ) :=
  Eq.refl (zetaZeroTailRe S φ)

def completedZeroFiniteComplementTo
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)] :
    {ρ : ℂ // ZetaCompletedZero ρ} →
      ({η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}) :=
  fun ρ =>
    if hρ : (ρ : ℂ) ∈ S then
      Sum.inl ⟨(ρ : ℂ), hρ⟩
    else
      Sum.inr ⟨(ρ : ℂ), ρ.2, hρ⟩

def completedZeroFiniteComplementInv
    (S : Finset ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η) :
    ({η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}) →
      {ρ : ℂ // ZetaCompletedZero ρ} :=
  fun x =>
    match x with
    | Sum.inl η => ⟨(η : ℂ), hS (η : ℂ) η.2⟩
    | Sum.inr ρ => ⟨(ρ : ℂ), ρ.2.1⟩

theorem completedZeroFiniteComplementTo_eq_inl_of_mem
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)]
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) (hρ : (ρ : ℂ) ∈ S) :
    completedZeroFiniteComplementTo S ρ = Sum.inl ⟨(ρ : ℂ), hρ⟩ :=
  dif_pos hρ

theorem completedZeroFiniteComplementTo_eq_inr_of_not_mem
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)]
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) (hρ : (ρ : ℂ) ∉ S) :
    completedZeroFiniteComplementTo S ρ = Sum.inr ⟨(ρ : ℂ), ρ.2, hρ⟩ :=
  dif_neg hρ

theorem completedZeroFiniteComplementInv_to_of_mem
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)]
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) (hρ : (ρ : ℂ) ∈ S) :
    completedZeroFiniteComplementInv S hS
      (completedZeroFiniteComplementTo S ρ) = ρ := by
  have hto :
      completedZeroFiniteComplementTo S ρ = Sum.inl ⟨(ρ : ℂ), hρ⟩ :=
    completedZeroFiniteComplementTo_eq_inl_of_mem S ρ hρ
  have hvalue :
      completedZeroFiniteComplementInv S hS (Sum.inl ⟨(ρ : ℂ), hρ⟩) = ρ :=
    Subtype.ext (Eq.refl (ρ : ℂ))
  exact Eq.subst
    (motive := fun value :
      {η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
      completedZeroFiniteComplementInv S hS value = ρ)
    hto.symm
    hvalue

theorem completedZeroFiniteComplementInv_to_of_not_mem
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)]
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) (hρ : (ρ : ℂ) ∉ S) :
    completedZeroFiniteComplementInv S hS
      (completedZeroFiniteComplementTo S ρ) = ρ := by
  have hto :
      completedZeroFiniteComplementTo S ρ = Sum.inr ⟨(ρ : ℂ), ρ.2, hρ⟩ :=
    completedZeroFiniteComplementTo_eq_inr_of_not_mem S ρ hρ
  have hvalue :
      completedZeroFiniteComplementInv S hS
        (Sum.inr ⟨(ρ : ℂ), ρ.2, hρ⟩) = ρ :=
    Subtype.ext (Eq.refl (ρ : ℂ))
  exact Eq.subst
    (motive := fun value :
      {η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
      completedZeroFiniteComplementInv S hS value = ρ)
    hto.symm
    hvalue

theorem completedZeroFiniteComplementInv_to
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)]
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedZeroFiniteComplementInv S hS
      (completedZeroFiniteComplementTo S ρ) = ρ := by
  exact match (inferInstance : Decidable ((ρ : ℂ) ∈ S)) with
  | Decidable.isTrue hρ =>
      completedZeroFiniteComplementInv_to_of_mem S hS ρ hρ
  | Decidable.isFalse hρ =>
      completedZeroFiniteComplementInv_to_of_not_mem S hS ρ hρ

theorem completedZeroFiniteComplementTo_inv_inl
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)]
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (η : {η : ℂ // η ∈ S}) :
    completedZeroFiniteComplementTo S
      (completedZeroFiniteComplementInv S hS (Sum.inl η)) = Sum.inl η := by
  have hto :
      completedZeroFiniteComplementTo S
          (completedZeroFiniteComplementInv S hS (Sum.inl η)) =
        Sum.inl ⟨(η : ℂ), η.2⟩ :=
    completedZeroFiniteComplementTo_eq_inl_of_mem S
      (completedZeroFiniteComplementInv S hS (Sum.inl η)) η.2
  have hvalue :
      (Sum.inl ⟨(η : ℂ), η.2⟩ :
        {η : ℂ // η ∈ S} ⊕
          {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}) = Sum.inl η :=
    congrArg
      (fun value : {η : ℂ // η ∈ S} =>
        (Sum.inl value : {η : ℂ // η ∈ S} ⊕
          {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}))
      (Subtype.ext (Eq.refl (η : ℂ)))
  exact Eq.trans hto hvalue

theorem completedZeroFiniteComplementTo_inv_inr
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)]
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}) :
    completedZeroFiniteComplementTo S
      (completedZeroFiniteComplementInv S hS (Sum.inr ρ)) = Sum.inr ρ := by
  have hto :
      completedZeroFiniteComplementTo S
          (completedZeroFiniteComplementInv S hS (Sum.inr ρ)) =
        Sum.inr ⟨(ρ : ℂ), ρ.2.1, ρ.2.2⟩ :=
    completedZeroFiniteComplementTo_eq_inr_of_not_mem S
      (completedZeroFiniteComplementInv S hS (Sum.inr ρ)) ρ.2.2
  have hvalue :
      (Sum.inr ⟨(ρ : ℂ), ρ.2.1, ρ.2.2⟩ :
        {η : ℂ // η ∈ S} ⊕
          {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}) = Sum.inr ρ :=
    congrArg
      (fun value : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
        (Sum.inr value : {η : ℂ // η ∈ S} ⊕
          {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}))
      (Subtype.ext (Eq.refl (ρ : ℂ)))
  exact Eq.trans hto hvalue

theorem completedZeroFiniteComplementTo_inv
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)]
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (x : {η : ℂ // η ∈ S} ⊕
      {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}) :
    completedZeroFiniteComplementTo S
      (completedZeroFiniteComplementInv S hS x) = x :=
  match x with
  | Sum.inl η => completedZeroFiniteComplementTo_inv_inl S hS η
  | Sum.inr ρ => completedZeroFiniteComplementTo_inv_inr S hS ρ

/-- The completed-zero subtype splits into a selected finite part and its complement. -/
def completedZeroSubtypeFiniteComplementEquiv
    (S : Finset ℂ)
    [∀ η : ℂ, Decidable (η ∈ S)]
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η) :
    {ρ : ℂ // ZetaCompletedZero ρ} ≃
      ({η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}) where
  toFun := completedZeroFiniteComplementTo S
  invFun := completedZeroFiniteComplementInv S hS
  left_inv := completedZeroFiniteComplementInv_to S hS
  right_inv := completedZeroFiniteComplementTo_inv S hS

/-- Transport the completed-zero `tsum` across the finite/complement equivalence. -/
theorem completedZeroSubtype_tsum_eq_sumType_tsum_of_equiv
    (S : Finset ℂ)
    [∀ η : ℂ, Decidable (η ∈ S)]
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η) :
    (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ}, F ρ) =
      (∑' x : {η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm x)) := by
  exact ((completedZeroSubtypeFiniteComplementEquiv S hS).symm.tsum_eq F).symm

/-- The left summand is equivalent to the range of the left injection. -/
def sumInlRangeEquiv (α β : Type*) :
    α ≃ Set.range (Sum.inl : α → α ⊕ β) where
  toFun := fun a => ⟨Sum.inl a, ⟨a, Eq.refl (Sum.inl a)⟩⟩
  invFun := fun x =>
    match x with
    | ⟨Sum.inl a, leftEvidence⟩ => a
    | ⟨Sum.inr b, hx⟩ =>
        False.elim
          (match hx with
          | ⟨a, ha⟩ => nomatch ha)
  left_inv := fun a => Eq.refl a
  right_inv := fun x =>
    match x with
    | ⟨Sum.inl a, hx⟩ => Subtype.ext (Eq.refl (Sum.inl a))
    | ⟨Sum.inr b, hx⟩ =>
        False.elim
          (match hx with
          | ⟨a, ha⟩ => nomatch ha)

/-- The right summand is equivalent to the complement of the left-injection range. -/
def sumInlRangeComplEquiv (α β : Type*) :
    β ≃ ((Set.range (Sum.inl : α → α ⊕ β))ᶜ : Set (α ⊕ β)) where
  toFun := fun b =>
    (⟨Sum.inr b, fun h => match h with | ⟨a, ha⟩ => nomatch ha⟩ :
      ((Set.range (Sum.inl : α → α ⊕ β))ᶜ : Set (α ⊕ β)))
  invFun := fun x =>
    match x with
    | ⟨Sum.inl a, hx⟩ =>
        False.elim (hx ⟨a, Eq.refl (Sum.inl a)⟩)
    | ⟨Sum.inr b, rightEvidence⟩ => b
  left_inv := fun b => Eq.refl b
  right_inv := fun x =>
    match x with
    | ⟨Sum.inl a, hx⟩ =>
        False.elim (hx ⟨a, Eq.refl (Sum.inl a)⟩)
    | ⟨Sum.inr b, hx⟩ => Subtype.ext (Eq.refl (Sum.inr b))

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
  have hrightSubtype : Summable (fun x : (sᶜ : Set (α ⊕ β)) => G x) := by
    let rightF : (sᶜ : Set (α ⊕ β)) → ℂ := fun x => G x
    have hright_comp :
        (fun b : β => rightF ((sumInlRangeComplEquiv α β) b)) =
          fun b : β => G (Sum.inr b) :=
      funext (fun b =>
        congrArg G
          (show (((sumInlRangeComplEquiv α β) b :
            (sᶜ : Set (α ⊕ β))) : α ⊕ β) = Sum.inr b from
              Eq.refl (Sum.inr b)))
    have hright_base :
        Summable (fun b : β => rightF ((sumInlRangeComplEquiv α β) b)) :=
      Eq.subst (motive := fun u : β → ℂ => Summable u)
        hright_comp.symm
        hright
    exact ((sumInlRangeComplEquiv α β).summable_iff).mp hright_base
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
      (∑' x : s, G x) + (∑' x : (sᶜ : Set (α ⊕ β)), G x) =
        (∑' x : α ⊕ β, G x) :=
    tsum_subtype_add_tsum_subtype_compl htotal s
  have hleft_tsum :
      (∑' x : s, G x) = ∑' a : α, G (Sum.inl a) :=
    ((sumInlRangeEquiv α β).tsum_eq (fun x : s => G x)).symm
  have hright_tsum :
      (∑' x : (sᶜ : Set (α ⊕ β)), G x) = ∑' b : β, G (Sum.inr b) :=
    let rightF : (sᶜ : Set (α ⊕ β)) → ℂ := fun x => G x
    have hraw :
        (∑' x : (sᶜ : Set (α ⊕ β)), rightF x) =
          ∑' b : β, rightF ((sumInlRangeComplEquiv α β) b) :=
      ((sumInlRangeComplEquiv α β).tsum_eq rightF).symm
    have hfun :
        (fun b : β => rightF ((sumInlRangeComplEquiv α β) b)) =
          fun b : β => G (Sum.inr b) :=
      funext (fun b =>
        congrArg G
          (show (((sumInlRangeComplEquiv α β) b :
            (sᶜ : Set (α ⊕ β))) : α ⊕ β) = Sum.inr b from
              Eq.refl (Sum.inr b)))
    have hrhs :
        (∑' b : β, rightF ((sumInlRangeComplEquiv α β) b)) =
          ∑' b : β, G (Sum.inr b) :=
      congrArg (fun u : β → ℂ => ∑' b : β, u b) hfun
    hraw.trans hrhs
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
    Summable (fun η : {η : ℂ // η ∈ S} => F ⟨η, hS η η.2⟩) := by
  have hinj :
      Function.Injective
        (fun η : {η : ℂ // η ∈ S} =>
          (⟨η, hS η η.2⟩ : {ρ : ℂ // ZetaCompletedZero ρ})) := by
    intro η μ hημ
    have hval : (η : ℂ) = (μ : ℂ) :=
      congrArg (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} => (ρ : ℂ)) hημ
    exact Subtype.ext hval
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
    have hval : (ρ : ℂ) = (η : ℂ) :=
      congrArg (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} => (ρ : ℂ)) hρη
    exact Subtype.ext hval
  exact hF.comp_injective hinj

theorem completedZeroFiniteComplementEquiv_symm_inl
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)]
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (η : {η : ℂ // η ∈ S}) :
    (completedZeroSubtypeFiniteComplementEquiv S hS).symm (Sum.inl η) =
      (⟨(η : ℂ), hS (η : ℂ) η.2⟩ :
        {ρ : ℂ // ZetaCompletedZero ρ}) :=
  Eq.refl (completedZeroFiniteComplementInv S hS (Sum.inl η))

theorem completedZeroFiniteComplementEquiv_symm_inr
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)]
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}) :
    (completedZeroSubtypeFiniteComplementEquiv S hS).symm (Sum.inr ρ) =
      (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) :=
  Eq.refl (completedZeroFiniteComplementInv S hS (Sum.inr ρ))

theorem completedZeroFiniteComplement_leftFace_family_eq
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)]
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η) :
    (fun η : {η : ℂ // η ∈ S} =>
      F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm (Sum.inl η))) =
      fun η : {η : ℂ // η ∈ S} => F ⟨η, hS η η.2⟩ :=
  funext (fun η =>
    congrArg F (completedZeroFiniteComplementEquiv_symm_inl S hS η))

theorem completedZeroFiniteComplement_rightFace_family_eq
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)]
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η) :
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
      F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm (Sum.inr ρ))) =
      fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} => F ⟨ρ, ρ.2.1⟩ :=
  funext (fun ρ =>
    congrArg F (completedZeroFiniteComplementEquiv_symm_inr S hS ρ))

theorem completedZeroFiniteComplement_leftFace_tsum_eq
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)]
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η) :
    (∑' η : {η : ℂ // η ∈ S},
      F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm (Sum.inl η))) =
      ∑' η : {η : ℂ // η ∈ S}, F ⟨η, hS η η.2⟩ :=
  congrArg (fun family : {η : ℂ // η ∈ S} → ℂ => ∑' η, family η)
    (completedZeroFiniteComplement_leftFace_family_eq S F hS)

theorem completedZeroFiniteComplement_rightFace_tsum_eq
    (S : Finset ℂ) [∀ η : ℂ, Decidable (η ∈ S)]
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η) :
    (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
      F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm (Sum.inr ρ))) =
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}, F ⟨ρ, ρ.2.1⟩ :=
  congrArg
    (fun family : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} → ℂ =>
      ∑' ρ, family ρ)
    (completedZeroFiniteComplement_rightFace_family_eq S F hS)

/-- Split the finite/complement sum-type `tsum` into the selected finite side and the
complementary tail side. -/
theorem completedZeroFiniteComplement_sumType_tsum_eq_add
    (S : Finset ℂ)
    [∀ η : ℂ, Decidable (η ∈ S)]
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (hF : Summable F) :
    (∑' x : {η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm x)) =
      (∑' η : {η : ℂ // η ∈ S}, F ⟨η, hS η η.2⟩) +
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}, F ⟨ρ, ρ.2.1⟩) := by
  let G :
      {η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} → ℂ :=
    fun x => F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm x)
  have hleft : Summable (fun η : {η : ℂ // η ∈ S} => F ⟨η, hS η η.2⟩) :=
    completedZeroFiniteFace_summable S F hS hF
  have hright :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          F ⟨ρ, ρ.2.1⟩) :=
    completedZeroComplementFace_summable S F hF
  have hleftFamily :
      (fun η : {η : ℂ // η ∈ S} => G (Sum.inl η)) =
        fun η : {η : ℂ // η ∈ S} => F ⟨η, hS η η.2⟩ :=
    completedZeroFiniteComplement_leftFace_family_eq S F hS
  have hrightFamily :
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} => G (Sum.inr ρ)) =
        fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} => F ⟨ρ, ρ.2.1⟩ :=
    completedZeroFiniteComplement_rightFace_family_eq S F hS
  have hleftG : Summable (fun η : {η : ℂ // η ∈ S} => G (Sum.inl η)) :=
    Eq.subst (motive := fun family : {η : ℂ // η ∈ S} → ℂ => Summable family)
      hleftFamily.symm hleft
  have hrightG :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          G (Sum.inr ρ)) :=
    Eq.subst
      (motive := fun family :
        {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} → ℂ => Summable family)
      hrightFamily.symm hright
  have hsplit :
      (∑' x : {η : ℂ // η ∈ S} ⊕
          {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}, G x) =
        (∑' η : {η : ℂ // η ∈ S}, G (Sum.inl η)) +
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
            G (Sum.inr ρ)) :=
    complex_tsum_sum_type_eq_add_of_summable_faces G hleftG hrightG
  have hleftTsum :
      (∑' η : {η : ℂ // η ∈ S}, G (Sum.inl η)) =
        ∑' η : {η : ℂ // η ∈ S}, F ⟨η, hS η η.2⟩ :=
    completedZeroFiniteComplement_leftFace_tsum_eq S F hS
  have hrightTsum :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
          G (Sum.inr ρ)) =
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
          F ⟨ρ, ρ.2.1⟩ :=
    completedZeroFiniteComplement_rightFace_tsum_eq S F hS
  exact Eq.trans hsplit
    (congrArg₂ (fun leftValue rightValue : ℂ => leftValue + rightValue)
      hleftTsum hrightTsum)

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
    (∑' η : {η : ℂ // η ∈ S}, F ⟨η, hS η η.2⟩) =
      ∑ η in S.attach, F ⟨η, hS η η.2⟩ := by
  exact
    complex_tsum_fintype_eq_finset_sum_of_finset_eq_univ
      S.attach
      Finset.attach_eq_univ
      (fun η : {η : ℂ // η ∈ S} => F ⟨η, hS η η.2⟩)

/-- Finite/complement `tsum` transport for the completed-zero subtype. -/
theorem completedZeroSubtype_tsum_eq_finiteSubtype_add_complement_of_equiv
    (S : Finset ℂ)
    [∀ η : ℂ, Decidable (η ∈ S)]
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (hF : Summable F) :
    (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ}, F ρ) =
      (∑ η in S.attach, F ⟨η, hS η η.2⟩) +
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}, F ⟨ρ, ρ.2.1⟩) := by
  have htransport :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ}, F ρ) =
        (∑' x : {η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
          F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm x)) :=
    completedZeroSubtype_tsum_eq_sumType_tsum_of_equiv S F hS
  have hsplit :
      (∑' x : {η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
          F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm x)) =
        (∑' η : {η : ℂ // η ∈ S}, F ⟨η, hS η η.2⟩) +
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}, F ⟨ρ, ρ.2.1⟩) :=
    completedZeroFiniteComplement_sumType_tsum_eq_add S F hS hF
  have hfinite :
      (∑' η : {η : ℂ // η ∈ S}, F ⟨η, hS η η.2⟩) =
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
        zetaZeroSideContribution (η : ℂ) φ) =
      ∑ η in S, zetaZeroSideContribution η φ := by
  have _hS_record : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η := hS
  exact Finset.sum_attach S (fun η : ℂ => zetaZeroSideContribution η φ)

end
end LFunctions
end Boundary
