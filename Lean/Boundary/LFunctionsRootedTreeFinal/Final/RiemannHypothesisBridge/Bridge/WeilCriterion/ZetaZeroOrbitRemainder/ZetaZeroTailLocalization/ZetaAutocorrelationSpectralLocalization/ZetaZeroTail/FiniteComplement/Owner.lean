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
        zetaZeroSideContribution (η : ℂ) φ) := by
  rfl

/-- The real-valued zero tail is the real part of the complex one. -/
theorem zetaZeroTailRe_eq
    (S : Finset ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroTailRe S φ = Complex.re (zetaZeroTail S φ) := by
  rfl

/-- The completed-zero subtype splits into a selected finite part and its complement. -/
def completedZeroSubtypeFiniteComplementEquiv
    (S : Finset ℂ)
    [∀ η : ℂ, Decidable (η ∈ S)]
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η) :
    {ρ : ℂ // ZetaCompletedZero ρ} ≃
      ({η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}) := by
  let toF :
      {ρ : ℂ // ZetaCompletedZero ρ} →
        {η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} :=
    fun ρ =>
      if hρ : (ρ : ℂ) ∈ S then
        Sum.inl ⟨(ρ : ℂ), hρ⟩
      else
        Sum.inr ⟨(ρ : ℂ), ρ.2, hρ⟩
  let invF :
      {η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} →
        {ρ : ℂ // ZetaCompletedZero ρ} :=
    fun x =>
      match x with
      | Sum.inl η => ⟨(η : ℂ), hS (η : ℂ) η.2⟩
      | Sum.inr ρ => ⟨(ρ : ℂ), ρ.2.1⟩
  exact
      { toFun := toF
        invFun := invF
        left_inv := fun ρ =>
          match (inferInstance : Decidable ((ρ : ℂ) ∈ S)) with
          | isTrue hρ =>
              have hif : toF ρ = Sum.inl ⟨(ρ : ℂ), hρ⟩ :=
                dif_pos hρ
              Eq.subst
                (motive := fun x :
                  {η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
                  invF x = ρ)
                hif.symm
                (Subtype.ext rfl)
          | isFalse hρ =>
              have hif : toF ρ = Sum.inr ⟨(ρ : ℂ), ρ.2, hρ⟩ :=
                dif_neg hρ
              Eq.subst
                (motive := fun x :
                  {η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
                  invF x = ρ)
                hif.symm
                (Subtype.ext rfl)
        right_inv := fun x =>
          match x with
          | Sum.inl η =>
              have hif :
                  toF (invF (Sum.inl η)) = Sum.inl ⟨(η : ℂ), η.2⟩ :=
                dif_pos η.2
              Eq.subst
                (motive := fun y :
                  {η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
                  y = Sum.inl η)
                hif.symm
                (congrArg Sum.inl (Subtype.ext rfl))
          | Sum.inr ρ =>
              have hif :
                  toF (invF (Sum.inr ρ)) = Sum.inr ⟨(ρ : ℂ), ρ.2.1, ρ.2.2⟩ :=
                dif_neg ρ.2.2
              Eq.subst
                (motive := fun y :
                  {η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
                  y = Sum.inr ρ)
                hif.symm
                (congrArg Sum.inr (Subtype.ext rfl)) }

/-- Transport the completed-zero `tsum` across the finite/complement equivalence. -/
theorem completedZeroSubtype_tsum_eq_sumType_tsum_of_equiv
    (S : Finset ℂ)
    [∀ η : ℂ, Decidable (η ∈ S)]
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η)
    (hF : Summable F) :
    (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ}, F ρ) =
      (∑' x : {η : ℂ // η ∈ S} ⊕ {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        F ((completedZeroSubtypeFiniteComplementEquiv S hS).symm x)) := by
  have _hF_record : Summable F := hF
  exact ((completedZeroSubtypeFiniteComplementEquiv S hS).symm.tsum_eq F).symm

/-- The left summand is equivalent to the range of the left injection. -/
def sumInlRangeEquiv (α β : Type*) :
    α ≃ Set.range (Sum.inl : α → α ⊕ β) where
  toFun := fun a => ⟨Sum.inl a, ⟨a, rfl⟩⟩
  invFun := fun x =>
    match x with
    | ⟨Sum.inl a, _hx⟩ => a
    | ⟨Sum.inr _b, hx⟩ =>
        False.elim
          (match hx with
          | ⟨_a, ha⟩ => nomatch ha)
  left_inv := fun _a => rfl
  right_inv := fun x =>
    match x with
    | ⟨Sum.inl _a, _hx⟩ => Subtype.ext rfl
    | ⟨Sum.inr _b, hx⟩ =>
        False.elim
          (match hx with
          | ⟨_a, ha⟩ => nomatch ha)

/-- The right summand is equivalent to the complement of the left-injection range. -/
def sumInlRangeComplEquiv (α β : Type*) :
    β ≃ ((Set.range (Sum.inl : α → α ⊕ β))ᶜ : Set (α ⊕ β)) where
  toFun := fun b =>
    (⟨Sum.inr b, fun h => match h with | ⟨_, ha⟩ => nomatch ha⟩ :
      ((Set.range (Sum.inl : α → α ⊕ β))ᶜ : Set (α ⊕ β)))
  invFun := fun x =>
    match x with
    | ⟨Sum.inl a, hx⟩ => False.elim (hx ⟨a, rfl⟩)
    | ⟨Sum.inr b, _hx⟩ => b
  left_inv := fun _b => rfl
  right_inv := fun x =>
    match x with
    | ⟨Sum.inl a, hx⟩ => False.elim (hx ⟨a, rfl⟩)
    | ⟨Sum.inr _b, _hx⟩ => Subtype.ext rfl

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
            (sᶜ : Set (α ⊕ β))) : α ⊕ β) = Sum.inr b from rfl))
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
            (sᶜ : Set (α ⊕ β))) : α ⊕ β) = Sum.inr b from rfl))
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
  have hleftG : Summable (fun η : {η : ℂ // η ∈ S} => G (Sum.inl η)) :=
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
    completedZeroSubtype_tsum_eq_sumType_tsum_of_equiv S F hS hF
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
