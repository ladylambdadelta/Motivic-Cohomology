import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTailEnvelope

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Complement equivalence for the retained non-dagger cutoff data. -/
def completedZeroTailCutoffDataComplementEquiv
    (S : Finset ℂ)
    (P : Finset ℂ)
    (T₀ : Finset ℂ)
    (U : Finset
      {rho : ℂ //
        ZetaCompletedZero rho ∧
          rho ∉ S ∧
          rho ∉ daggerClosedSpectralSampleFinset P})
    (hUbase :
      T₀.preimage
        (fun rho :
          {rho : ℂ //
            ZetaCompletedZero rho ∧
              rho ∉ S ∧
              rho ∉ daggerClosedSpectralSampleFinset P} =>
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
                rho ∉ daggerClosedSpectralSampleFinset P} =>
              (zero : ℂ)), Subtype.val_injective⟩ :
            {rho : ℂ //
              ZetaCompletedZero rho ∧
                rho ∉ S ∧
                rho ∉ daggerClosedSpectralSampleFinset P} ↪ ℂ) ∧
        rho ∉ daggerClosedSpectralSampleFinset P} ≃
      {rho :
        {rho : ℂ //
          ZetaCompletedZero rho ∧
            rho ∉ S ∧
            rho ∉ daggerClosedSpectralSampleFinset P} //
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
    ⟨(rho : ℂ), rho.1.2.1, rho.1.2.2.1,
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
                          rho ∉
                            daggerClosedSpectralSampleFinset P} =>
                        zero ∈ U)
                    (Subtype.ext hrhoEquality)
                    hrhoU),
      rho.1.2.2.2⟩
  left_inv := fun rho => Subtype.ext (Eq.refl (rho : ℂ))
  right_inv := fun rho =>
    Subtype.ext (Subtype.ext (Eq.refl (rho.1.1 : ℂ)))

/-- A summable non-dagger completed-zero polynomial envelope admits a finite cutoff
whose support facts are retained explicitly. -/
theorem exists_commonPolynomialEnvelope_completedZeroTailCutoff_nonDagger_supported_data_from_eventual_complement
    (S : Finset ℂ)
    (P : Finset ℂ)
    (T₀ : Finset ℂ)
    (hT₀zero : ∀ ρ : ℂ, ρ ∈ T₀ → ZetaCompletedZero ρ)
    (hT₀S : ∀ ρ : ℂ, ρ ∈ T₀ → ρ ∉ S)
    (hT₀dagger :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        ρ ∉ daggerClosedSpectralSampleFinset P)
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
        (∀ ρ : ℂ, ρ ∈ T → ZetaCompletedZero ρ) ∧
        (∀ ρ : ℂ, ρ ∈ T → ρ ∉ S) ∧
        (∀ ρ : ℂ, ρ ∈ T →
          ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        (∑' ρ :
          {ρ : ℂ //
            ZetaCompletedZero ρ ∧
              ρ ∉ S ∧
              ρ ∉ T ∧
              ρ ∉ daggerClosedSpectralSampleFinset P},
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε :=
  let β :=
    {ρ : ℂ //
      ZetaCompletedZero ρ ∧
        ρ ∉ S ∧
        ρ ∉ daggerClosedSpectralSampleFinset P}
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
      have hTzero :
          ∀ ρ : ℂ, ρ ∈ T → ZetaCompletedZero ρ :=
        fun ρ hρT =>
          match Finset.mem_union.mp hρT with
          | Or.inl hρT₀ => hT₀zero ρ hρT₀
          | Or.inr hρU =>
              match Finset.mem_image.mp hρU with
              | ⟨ρZero, hρZeroU, hρZero_eq⟩ =>
                  Eq.subst
                    (motive := fun z : ℂ => ZetaCompletedZero z)
                    hρZero_eq
                    ρZero.2.1
      have hTS :
          ∀ ρ : ℂ, ρ ∈ T → ρ ∉ S :=
        fun ρ hρT =>
          match Finset.mem_union.mp hρT with
          | Or.inl hρT₀ => hT₀S ρ hρT₀
          | Or.inr hρU =>
              match Finset.mem_image.mp hρU with
              | ⟨ρZero, hρZeroU, hρZero_eq⟩ =>
                  Eq.subst
                    (motive := fun z : ℂ => z ∉ S)
                    hρZero_eq
                    ρZero.2.2.1
      have hTdagger :
          ∀ ρ : ℂ, ρ ∈ T →
            ρ ∉ daggerClosedSpectralSampleFinset P :=
        fun ρ hρT =>
          match Finset.mem_union.mp hρT with
          | Or.inl hρT₀ => hT₀dagger ρ hρT₀
          | Or.inr hρU =>
              match Finset.mem_image.mp hρU with
              | ⟨ρZero, hρZeroU, hρZero_eq⟩ =>
                  Eq.subst
                    (motive := fun z : ℂ =>
                      z ∉ daggerClosedSpectralSampleFinset P)
                    hρZero_eq
                    ρZero.2.2.2
      let htail_transport :
          (∑' ρ :
            {ρ : ℂ //
              ZetaCompletedZero ρ ∧
                ρ ∉ S ∧
                ρ ∉ T ∧
                ρ ∉ daggerClosedSpectralSampleFinset P},
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) =
            ∑' ρ : {ρ : β // ρ ∉ U}, envelopeβ ρ :=
        let γ :=
          {ρ : ℂ //
            ZetaCompletedZero ρ ∧
              ρ ∉ S ∧
              ρ ∉ T ∧
              ρ ∉ daggerClosedSpectralSampleFinset P}
        let δ := {ρ : β // ρ ∉ U}
        let tailEquiv : γ ≃ δ :=
          completedZeroTailCutoffDataComplementEquiv S P T₀ U hUbase
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
                ρ ∉ daggerClosedSpectralSampleFinset P},
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
          (And.intro
            hTzero
            (And.intro
              hTS
              (And.intro hTdagger htail))))

/-- Public cutoff-data theorem. -/
theorem exists_commonPolynomialEnvelope_completedZeroTailCutoff_nonDagger_supported_data
    (S : Finset ℂ)
    (P : Finset ℂ)
    (T₀ : Finset ℂ)
    (hT₀zero : ∀ ρ : ℂ, ρ ∈ T₀ → ZetaCompletedZero ρ)
    (hT₀S : ∀ ρ : ℂ, ρ ∈ T₀ → ρ ∉ S)
    (hT₀dagger :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        ρ ∉ daggerClosedSpectralSampleFinset P)
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
        (∀ ρ : ℂ, ρ ∈ T → ZetaCompletedZero ρ) ∧
        (∀ ρ : ℂ, ρ ∈ T → ρ ∉ S) ∧
        (∀ ρ : ℂ, ρ ∈ T →
          ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        (∑' ρ :
          {ρ : ℂ //
            ZetaCompletedZero ρ ∧
              ρ ∉ S ∧
              ρ ∉ T ∧
              ρ ∉ daggerClosedSpectralSampleFinset P},
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε :=
  exists_commonPolynomialEnvelope_completedZeroTailCutoff_nonDagger_supported_data_from_eventual_complement
    S P T₀ hT₀zero hT₀S hT₀dagger ε hε A k hsum

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
