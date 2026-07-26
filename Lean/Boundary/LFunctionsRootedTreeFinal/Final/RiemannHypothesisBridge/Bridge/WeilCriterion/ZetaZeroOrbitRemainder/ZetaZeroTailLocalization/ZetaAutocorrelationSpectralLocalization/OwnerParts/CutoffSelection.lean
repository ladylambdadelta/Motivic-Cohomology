import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.TailBounds

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Removing an ambient finite non-dagger zero window is equivalent to removing
that window inside the non-dagger completed-zero tail. -/
def completedZeroTailNonDaggerCutoffComplementEquiv
    (S : Finset ℂ)
    (P : Finset ℂ)
    (T₀ : Finset ℂ)
    (U : Finset
      {rho : ℂ //
        ZetaCompletedZero rho ∧
          rho ∉ S ∧
          zetaCenteredZero rho ∉ daggerClosedSpectralSampleFinset P})
    (hUbase :
      T₀.preimage
        (fun rho :
          {rho : ℂ //
            ZetaCompletedZero rho ∧
              rho ∉ S ∧
              zetaCenteredZero rho ∉ daggerClosedSpectralSampleFinset P} =>
            (rho : ℂ))
        Subtype.val_injective.injOn ⊆ U) :
    {rho : ℂ //
      ZetaCompletedZero rho ∧
        rho ∉ S ∧
        rho ∉ T₀ ∪ U.image
          (⟨(fun zero :
            {rho : ℂ //
              ZetaCompletedZero rho ∧
                rho ∉ S ∧
                zetaCenteredZero rho ∉ daggerClosedSpectralSampleFinset P} =>
              (zero : ℂ)), Subtype.val_injective⟩ :
            {rho : ℂ //
              ZetaCompletedZero rho ∧
                rho ∉ S ∧
                zetaCenteredZero rho ∉ daggerClosedSpectralSampleFinset P} ↪ ℂ) ∧
        zetaCenteredZero rho ∉ daggerClosedSpectralSampleFinset P} ≃
      {rho :
        {rho : ℂ //
          ZetaCompletedZero rho ∧
            rho ∉ S ∧
            zetaCenteredZero rho ∉ daggerClosedSpectralSampleFinset P} //
        rho ∉ U} where
  toFun := fun rho =>
    ⟨⟨(rho : ℂ), rho.2.1, rho.2.2.1, rho.2.2.2.2⟩,
      fun hrhoU =>
        rho.2.2.2.1
          (Finset.mem_union.mpr
            (Or.inr
              (Finset.mem_image.mpr
                ⟨⟨(rho : ℂ), rho.2.1, rho.2.2.1, rho.2.2.2.2⟩,
                  hrhoU, Eq.refl (rho : ℂ)⟩)))⟩
  invFun := fun rho =>
    ⟨(rho : ℂ),
      rho.1.2.1,
      rho.1.2.2.1,
      fun hrhoT =>
        match Finset.mem_union.mp hrhoT with
        | Or.inl hrhoT₀ =>
            rho.2 (hUbase (Finset.mem_preimage.mpr hrhoT₀))
        | Or.inr hrhoImage =>
            match Finset.mem_image.mp hrhoImage with
            | ⟨rhoU, hrhoU, hrhoEquality⟩ =>
                rho.2
                  (Eq.subst
                    (motive := fun zero :
                      {rho : ℂ //
                        ZetaCompletedZero rho ∧
                        rho ∉ S ∧
                          zetaCenteredZero rho ∉
                            daggerClosedSpectralSampleFinset P} =>
                        zero ∈ U)
                    (Subtype.ext hrhoEquality)
                    hrhoU),
      rho.1.2.2.2⟩
  left_inv := fun rho => Subtype.ext (Eq.refl (rho : ℂ))
  right_inv := fun rho =>
    Subtype.ext (Subtype.ext (Eq.refl (rho.1.1 : ℂ)))

theorem exists_commonPolynomialEnvelope_completedZeroTailCutoff_nonDagger_from_eventual_complement
    (S : Finset ℂ)
    (P : Finset ℂ)
    (T₀ : Finset ℂ)
    (hT₀ :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (ε : ℝ)
    (hε : 0 < ε)
    (A : ℝ)
    (k : ℕ)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        (∑' ρ :
          {ρ : ℂ //
            ZetaCompletedZero ρ ∧
              ρ ∉ S ∧
              ρ ∉ T ∧
              zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε :=
  let β :=
    {ρ : ℂ //
      ZetaCompletedZero ρ ∧
        ρ ∉ S ∧
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P}
  let envelopeβ : β → ℝ :=
    fun ρ =>
      A * zetaCompletedZeroCenteredHeight
        (⟨(ρ : ℂ), ρ.2.1⟩ :
          {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))
  let base : Finset β :=
    T₀.preimage
      (fun ρ : β => (ρ : ℂ))
      (Subtype.val_injective.injOn)
  have htail_eventually :
      ∀ᶠ U in (Filter.atTop : Filter (Finset β)),
        (∑' ρ : {ρ : β // ρ ∉ U}, envelopeβ ρ) < ε :=
    (tendsto_tsum_compl_atTop_zero envelopeβ).eventually
      (Iio_mem_nhds hε)
  have hbase_eventually :
      ∀ᶠ U in (Filter.atTop : Filter (Finset β)), base ⊆ U :=
    Filter.eventually_ge_atTop base
  match (hbase_eventually.and htail_eventually).exists with
  | ⟨U, hUbase, hUtail⟩ =>
      let T : Finset ℂ := T₀ ∪ U.image
        (⟨(fun ρ : β => (ρ : ℂ)), Subtype.val_injective⟩ :
          β ↪ ℂ)
      have hT₀T : T₀ ⊆ T :=
        Finset.subset_union_left
      have hT :
          ∀ ρ : ℂ, ρ ∈ T →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P :=
        fun ρ hρT =>
          match Finset.mem_union.mp hρT with
          | Or.inl hρT₀ => hT₀ ρ hρT₀
          | Or.inr hρU =>
              match Finset.mem_image.mp hρU with
              | ⟨ρZero, hρZeroU, hρZero_eq⟩ =>
                  Eq.subst
                    (motive := fun z : ℂ =>
                      zetaCenteredZero z ∉ daggerClosedSpectralSampleFinset P)
                    hρZero_eq
                    ρZero.2.2.2
      let htail_transport :
          (∑' ρ :
            {ρ : ℂ //
              ZetaCompletedZero ρ ∧
                ρ ∉ S ∧
                ρ ∉ T ∧
                zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) =
            ∑' ρ : {ρ : β // ρ ∉ U}, envelopeβ ρ :=
        let γ :=
          {ρ : ℂ //
            ZetaCompletedZero ρ ∧
              ρ ∉ S ∧
              ρ ∉ T ∧
              zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P}
        let δ := {ρ : β // ρ ∉ U}
        let tailEquiv : γ ≃ δ :=
          completedZeroTailNonDaggerCutoffComplementEquiv S P T₀ U hUbase
        have hraw :
            (∑' ρ : γ,
              A * zetaCompletedZeroCenteredHeight
                (⟨(ρ : ℂ), ρ.2.1⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) =
              ∑' ρ : δ,
                A * zetaCompletedZeroCenteredHeight
                  (⟨((tailEquiv.symm ρ : γ) : ℂ),
                    (tailEquiv.symm ρ : γ).2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) :=
          (tailEquiv.symm.tsum_eq
            (fun ρ : γ =>
              A * zetaCompletedZeroCenteredHeight
                (⟨(ρ : ℂ), ρ.2.1⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))).symm
        let hterm :
            (fun ρ : δ =>
              A * zetaCompletedZeroCenteredHeight
                (⟨((tailEquiv.symm ρ : γ) : ℂ),
                  (tailEquiv.symm ρ : γ).2.1⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) =
              fun ρ : δ => envelopeβ ρ :=
          funext (fun ρ => Eq.refl (envelopeβ ρ))
        Eq.trans hraw
          (congrArg
            (fun F : δ → ℝ => ∑' ρ : δ, F ρ)
            hterm)
      have htail :
          (∑' ρ :
            {ρ : ℂ //
              ZetaCompletedZero ρ ∧
                ρ ∉ S ∧
                ρ ∉ T ∧
                zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε :=
        Eq.subst
          (motive := fun x : ℝ => x < ε)
          htail_transport.symm
          hUtail
      Exists.intro
        T
        (And.intro
          hT₀T
          (And.intro hT htail))

/-- Public supported non-dagger cutoff for a summable completed-zero envelope. -/
theorem exists_commonPolynomialEnvelope_completedZeroTailCutoff_nonDagger_supported
    (S : Finset ℂ)
    (P : Finset ℂ)
    (T₀ : Finset ℂ)
    (hT₀ :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (ε : ℝ)
    (hε : 0 < ε)
    (A : ℝ)
    (k : ℕ)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        (∑' ρ :
          {ρ : ℂ //
            ZetaCompletedZero ρ ∧
              ρ ∉ S ∧
              ρ ∉ T ∧
              zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P},
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε :=
  exists_commonPolynomialEnvelope_completedZeroTailCutoff_nonDagger_from_eventual_complement
    S P T₀ hT₀ ε hε A k hsum

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
