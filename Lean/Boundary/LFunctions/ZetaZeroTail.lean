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
  sorry

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
  sorry

/-- The selected finite side of the completed-zero split is a finite sum over `S.attach`. -/
theorem completedZeroFiniteSubtype_tsum_eq_finset_sum
    (S : Finset ℂ)
    (F : {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hS : ∀ η : ℂ, η ∈ S → ZetaCompletedZero η) :
    (∑' η : S.attach, F ⟨η, hS η η.2⟩) =
      ∑ η in S.attach, F ⟨η, hS η η.2⟩ := by
  sorry

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

/-- Zero-density, multiplicity, and transform-decay estimates make the zero-side majorant
summable over the completed-zero locus. -/
theorem summable_zetaZeroSideContributionMajorant
    (φ : ZetaAdmissibleFunction) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroSideContributionMajorant φ ρ) := by
  sorry

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
