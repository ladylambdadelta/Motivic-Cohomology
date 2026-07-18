import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.Prelude

namespace Boundary
namespace LFunctions
noncomputable section

theorem tsum_norm_le_of_selected_vanish_of_complement_majorant
    {α : Type*}
    (p q : α → Prop)
    (contribution : {x : α // p x} → ℂ)
    (majorant : {x : α // p x ∧ ¬ q x} → ℝ)
    (htotal : Summable (fun x : {x : α // p x} => ‖contribution x‖))
    (hmajorant : Summable majorant)
    (hzero :
      ∀ x : {x : α // p x},
        q x → contribution x = 0)
    (hbound :
      ∀ x : {x : α // p x ∧ ¬ q x},
        ‖contribution ⟨x.1, x.2.1⟩‖ ≤ majorant x) :
    ‖∑' x : {x : α // p x}, contribution x‖ ≤
      ∑' x : {x : α // p x ∧ ¬ q x}, majorant x := by
  let total := {x : α // p x}
  let selected : Set total := fun x => q x.1
  let complement := {x : α // p x ∧ ¬ q x}
  let contributionTotal : total → ℂ := contribution
  let contributionComplement : complement → ℂ :=
    fun x => contribution ⟨x.1, x.2.1⟩
  have htotalComplex : Summable contributionTotal :=
    Summable.of_norm htotal
  let complementEquiv : complement ≃ (selectedᶜ : Set total) :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      left_inv := fun x => Subtype.ext (Eq.refl x.1)
      right_inv := fun x =>
        Subtype.ext (Subtype.ext (Eq.refl x.1.1)) }
  have hsplit :
      (∑' x : selected, contributionTotal x) +
          (∑' x : (selectedᶜ : Set total), contributionTotal x) =
        ∑' x : total, contributionTotal x :=
      tsum_subtype_add_tsum_subtype_compl htotalComplex selected
  have hselected_fun :
      (fun x : selected => contributionTotal x) =
        (fun selectedElement : selected => 0) := by
    funext x
    exact hzero (x.1 : total) x.2
  have hselected_tsum :
      (∑' x : selected, contributionTotal x) = 0 := by
    exact Eq.trans
      (congrArg
        (fun f : selected → ℂ => ∑' x : selected, f x)
        hselected_fun)
      tsum_zero
  have hcomplement_tsum :
      (∑' x : (selectedᶜ : Set total), contributionTotal x) =
        ∑' x : complement, contributionComplement x := by
    have htransport :
        (∑' x : (selectedᶜ : Set total), contributionTotal x) =
          ∑' x : complement, contributionTotal (complementEquiv x) :=
      (complementEquiv.tsum_eq
        (fun x : (selectedᶜ : Set total) => contributionTotal x)).symm
    have hterms :
        (fun x : complement => contributionTotal (complementEquiv x)) =
          contributionComplement := by
      funext x
      exact Eq.refl (contribution ⟨x.1, x.2.1⟩)
    exact Eq.trans htransport
      (congrArg
        (fun f : complement → ℂ => ∑' x : complement, f x)
        hterms)
  have htotal_eq_complement :
      (∑' x : total, contributionTotal x) =
        ∑' x : complement, contributionComplement x := by
    exact Eq.trans
      hsplit.symm
      (Eq.trans
        (congrArg
          (fun z : ℂ => z +
            (∑' x : (selectedᶜ : Set total), contributionTotal x))
          hselected_tsum)
        (Eq.trans
          (zero_add (∑' x : (selectedᶜ : Set total), contributionTotal x))
          hcomplement_tsum))
  have hnorm_summable :
      Summable (fun x : complement => ‖contributionComplement x‖) := by
    let embed : complement → total :=
      fun x => ⟨x.1, x.2.1⟩
    have hinjective : Function.Injective embed := by
      intro left right heq
      exact Subtype.ext
        (congrArg (fun value : {x : α // p x} => value.1) heq)
    have hcomposed :
        Summable ((fun x : total => ‖contributionTotal x‖) ∘ embed) :=
      htotal.comp_injective hinjective
    have hcomposed_eq :
        ((fun x : total => ‖contributionTotal x‖) ∘ embed) =
          (fun x : complement => ‖contributionComplement x‖) := by
      funext x
      exact Eq.refl (‖contribution ⟨x.1, x.2.1⟩‖)
    exact Eq.subst
      (motive := fun sequence : complement → ℝ => Summable sequence)
      hcomposed_eq
      hcomposed
  have hnorm_tsum :
      ‖∑' x : complement, contributionComplement x‖ ≤
        ∑' x : complement, ‖contributionComplement x‖ :=
    norm_tsum_le_tsum_norm hnorm_summable
  have hmajorant_comparison :
      (∑' x : complement, ‖contributionComplement x‖) ≤
        ∑' x : complement, majorant x :=
    tsum_le_tsum hbound hnorm_summable hmajorant
  have hcomplement_bound :
      ‖∑' x : complement, contributionComplement x‖ ≤
        ∑' x : complement, majorant x :=
    le_trans hnorm_tsum hmajorant_comparison
  change ‖∑' x : total, contributionTotal x‖ ≤
    ∑' x : complement, majorant x
  exact htotal_eq_complement.symm ▸ hcomplement_bound

end
end LFunctions
end Boundary
