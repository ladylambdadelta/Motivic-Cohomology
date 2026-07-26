import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.AutocorrelationInterface.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core

/-!
# Boundary zeta zero Krein form

This file owns the zero-side Krein form used as the first analytic target in
the completed explicit-formula chain. It lives on the probe carrier and is
definitionally the completed zero-side real form.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The completed zero-side sum in complex-valued residue form. -/
noncomputable def zetaCompletedZeroSideComplex
    (φ : ZetaProbe) : ℂ :=
  ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
    zetaZeroSideContribution (ρ : ℂ) φ

namespace ZetaAdmissibleFunction

/- The historical namespace-qualified spelling is retained as a thin owner-level
   alias; the construction itself remains owned by `Boundary.LFunctions`. -/
noncomputable def zetaCompletedZeroSideComplex
    (φ : ZetaProbe) : ℂ :=
  Boundary.LFunctions.zetaCompletedZeroSideComplex φ

end ZetaAdmissibleFunction

/-- The completed zero-side sum in real-valued form. -/
noncomputable def zetaCompletedZeroSideRe
    (φ : ZetaProbe) : ℝ :=
  Complex.re (zetaCompletedZeroSideComplex φ)

/-- The completed zero-side real form is the real part of the complex residue sum. -/
theorem zetaCompletedZeroSideRe_eq_complex_re
    (φ : ZetaProbe) :
    zetaCompletedZeroSideRe φ =
      Complex.re (zetaCompletedZeroSideComplex φ) := by
  rfl

/-- The completed zero-side Krein form attached to a probe. -/
noncomputable def zetaCompletedZeroKreinGram (φ : ZetaProbe) : ℝ :=
  zetaCompletedZeroSideRe φ

/-- The completed spectral Weil form on the zero side. -/
noncomputable def zetaCompletedSpectralWeilForm (φ : ZetaProbe) : ℝ :=
  zetaCompletedZeroSideRe φ

/-- The completed Weil form on the probe class. -/
noncomputable def zetaWeilFormCompleted (φ : ZetaProbe) : ℝ :=
  zetaCompletedSpectralWeilForm φ

/-- The completed spectral Weil form is definitionally the completed zero-side sum. -/
theorem zetaCompletedSpectralWeilForm_def
    (φ : ZetaProbe) :
    zetaCompletedSpectralWeilForm φ = zetaCompletedZeroSideRe φ := by
  rfl

/-- The completed Weil form is definitionally the completed spectral form. -/
theorem zetaWeilFormCompleted_def
    (φ : ZetaProbe) :
    zetaWeilFormCompleted φ = zetaCompletedSpectralWeilForm φ := by
  rfl

/-- The completed spectral Weil form is the completed zero-side real sum. -/
theorem zetaCompletedSpectralWeilForm_eq_zeroSide
    (φ : ZetaProbe) :
    zetaCompletedSpectralWeilForm φ = zetaCompletedZeroSideRe φ := by
  rfl

/-- The completed Weil form is the completed zero-side real sum. -/
theorem zetaWeilFormCompleted_eq_zeroSide
    (φ : ZetaProbe) :
    zetaWeilFormCompleted φ = zetaCompletedZeroSideRe φ := by
  exact (zetaWeilFormCompleted_def φ).trans
    (zetaCompletedSpectralWeilForm_eq_zeroSide φ)

/-- The completed Weil form is the zero-side Krein form. -/
theorem zetaWeilFormCompleted_eq_zeroKreinGram (φ : ZetaProbe) :
    zetaWeilFormCompleted φ = zetaCompletedZeroKreinGram φ := by
  rfl

/-- The zero-side Krein form is definitionally the completed zero-side form. -/
theorem zetaCompletedZeroKreinGram_eq_zeroSide
    (φ : ZetaProbe) :
    zetaCompletedZeroKreinGram φ = zetaCompletedZeroSideRe φ := by
  rfl

/-- The completed zero-side real form depends only on the underlying test function. -/
theorem zetaCompletedZeroSideRe_congr_toZetaTestFunction
    {φ ψ : ZetaProbe}
    (h : φ.toZetaTestFunction' = ψ.toZetaTestFunction') :
    zetaCompletedZeroSideRe φ = zetaCompletedZeroSideRe ψ := by
  have hφψ : φ = ψ := by
    exact ZetaAdmissibleFunction.ext
      (fun x =>
        have htest_fun :
            φ.toZetaTestFunction'.toFun = ψ.toZetaTestFunction'.toFun :=
          congrArg ZetaTestFunction.toFun h
        have htest_x :
            φ.toZetaTestFunction' x = ψ.toZetaTestFunction' x :=
          congrFun htest_fun x
        calc
          φ x = φ.toZetaTestFunction' x := by
            exact (ZetaAdmissibleFunction.toZetaTestFunction'_apply φ x).symm
          _ = ψ.toZetaTestFunction' x := htest_x
          _ = ψ x := by
            exact ZetaAdmissibleFunction.toZetaTestFunction'_apply ψ x)
  exact Eq.subst
    (motive := fun χ : ZetaProbe => zetaCompletedZeroSideRe φ = zetaCompletedZeroSideRe χ)
    hφψ
    rfl

/-- The zero-side Krein form depends only on the underlying test function. -/
theorem zetaCompletedZeroKreinGram_congr_toZetaTestFunction
    {φ ψ : ZetaProbe}
    (h : φ.toZetaTestFunction' = ψ.toZetaTestFunction') :
    zetaCompletedZeroKreinGram φ = zetaCompletedZeroKreinGram ψ := by
  have hzero :
      zetaCompletedZeroSideRe φ = zetaCompletedZeroSideRe ψ :=
    zetaCompletedZeroSideRe_congr_toZetaTestFunction h
  exact
    (zetaCompletedZeroKreinGram_eq_zeroSide φ).trans
      (hzero.trans (zetaCompletedZeroKreinGram_eq_zeroSide ψ).symm)

/-- The completed Weil form depends only on the underlying test function. -/
theorem zetaWeilFormCompleted_congr_toZetaTestFunction
    {φ ψ : ZetaProbe}
    (h : φ.toZetaTestFunction' = ψ.toZetaTestFunction') :
    zetaWeilFormCompleted φ = zetaWeilFormCompleted ψ := by
  have hzero :
      zetaCompletedZeroSideRe φ = zetaCompletedZeroSideRe ψ :=
    zetaCompletedZeroSideRe_congr_toZetaTestFunction h
  exact
    (zetaWeilFormCompleted_eq_zeroSide φ).trans
      (hzero.trans (zetaWeilFormCompleted_eq_zeroSide ψ).symm)

/-- The raw completed Weil-positivity statement on all probes. -/
def ZetaWeilPositivity : Prop :=
  ∀ φ : ZetaProbe, 0 ≤ zetaWeilFormCompleted φ

/-- The quadratic Weil-positivity statement after passing seeds to autocorrelations. -/
def ZetaWeilQuadraticPositivity : Prop :=
  ∀ f : ZetaAdmissibleFunction,
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f)

/-- Convolution-autocorrelation probes have the same completed Weil form as their zero-side
real sum. -/
theorem zetaWeilFormCompleted_convolutionAutocorrelation_eq_zeroSide
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact zetaWeilFormCompleted_eq_zeroSide
    (ZetaAdmissibleFunction.convolutionAutocorrelation f)

/-- Historical name for the convolution-autocorrelation zero-side bridge. -/
theorem zetaWeilFormCompleted_autocorrelation_eq_zeroSide
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact zetaWeilFormCompleted_convolutionAutocorrelation_eq_zeroSide f

/-- The completed zero-side Krein form decomposes as the sum of a specific zero's orbit
contribution and the remainder (all other zeros). -/
theorem zetaCompletedZeroKreinGram_eq_zeroOrbitContribution_add_remainder
    (ρ : ℂ) (φ : ZetaAdmissibleFunction)
    (hρ : ZetaCompletedZero ρ)
    (hsum :
      Summable
        (fun ξ : {ξ : ℂ // ZetaCompletedZero ξ} =>
          zetaZeroSideContribution (ξ : ℂ) φ)) :
    zetaCompletedZeroKreinGram φ =
      zetaZeroOrbitContributionRe ρ φ + zetaZeroOrbitRemainderRe ρ φ := by
  show zetaCompletedZeroSideRe φ =
    zetaZeroOrbitContributionRe ρ φ + zetaZeroOrbitRemainderRe ρ φ
  show Complex.re (zetaCompletedZeroSideComplex φ) =
    zetaZeroOrbitContributionRe ρ φ + zetaZeroOrbitRemainderRe ρ φ
  have h_orbit_eq : zetaZeroOrbitContribution ρ φ =
    Finset.sum (zetaZeroOrbitFinset ρ) (fun η => zetaZeroSideContribution η φ) :=
    zetaZeroOrbitContribution_eq_sum ρ φ
  have h_remainder_eq : zetaZeroOrbitRemainder ρ φ =
    zetaZeroTail (zetaZeroOrbitFinset ρ) φ :=
    zetaZeroOrbitRemainder_eq_tail ρ φ
  have horbit_zero :
      ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η := by
    intro η hη
    exact
      match (zetaZeroOrbitFinset_mem_iff ρ η).1 hη with
      | Or.inl hηρ =>
          Eq.subst
            (motive := fun ζ : ℂ => ZetaCompletedZero ζ)
            hηρ.symm
            hρ
      | Or.inr hηneg =>
          Eq.subst
            (motive := fun ζ : ℂ => ZetaCompletedZero ζ)
            hηneg.symm
            (zetaCompletedZero_neg hρ)
  calc Complex.re (zetaCompletedZeroSideComplex φ)
    = Complex.re (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        zetaZeroSideContribution (ρ : ℂ) φ) := rfl
    _ = Complex.re (
        (∑ η in zetaZeroOrbitFinset ρ, zetaZeroSideContribution η φ) +
        (∑' ξ : {ξ : ℂ // ZetaCompletedZero ξ ∧ ξ ∉ zetaZeroOrbitFinset ρ},
          zetaZeroSideContribution (ξ : ℂ) φ)) := by
      have h_decomp : (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        zetaZeroSideContribution (ρ : ℂ) φ) =
        (∑ η in zetaZeroOrbitFinset ρ, zetaZeroSideContribution η φ) +
        (∑' ξ : {ξ : ℂ // ZetaCompletedZero ξ ∧ ξ ∉ zetaZeroOrbitFinset ρ},
          zetaZeroSideContribution (ξ : ℂ) φ) :=
        let S : Finset ℂ := zetaZeroOrbitFinset ρ
        let F : {ξ : ℂ // ZetaCompletedZero ξ} → ℂ :=
          fun ξ => zetaZeroSideContribution (ξ : ℂ) φ
        let orbitEmbedding :
            {η : ℂ // η ∈ S} ↪ {ξ : ℂ // ZetaCompletedZero ξ} := {
          toFun := fun η => ⟨η, horbit_zero η η.2⟩
          inj' := by
            intro η θ hηθ
            exact Subtype.ext
              (congrArg
                (fun ζ : {ξ : ℂ // ZetaCompletedZero ξ} => (ζ : ℂ))
                hηθ) }
        let Szero : Finset {ξ : ℂ // ZetaCompletedZero ξ} :=
          S.attach.map orbitEmbedding
        have hsplit :
            (∑ ξ in Szero, F ξ) +
                (∑' ξ : ↑(Szero : Set {ξ : ℂ // ZetaCompletedZero ξ})ᶜ, F ξ) =
              (∑' ξ : {ξ : ℂ // ZetaCompletedZero ξ}, F ξ) :=
          sum_add_tsum_compl hsum
        have hfinite :
            (∑ ξ in Szero, F ξ) =
              ∑ η in S, zetaZeroSideContribution η φ :=
          have hmap :
              (∑ ξ in Szero, F ξ) =
                ∑ η in S.attach, F (orbitEmbedding η) :=
            Finset.sum_map S.attach orbitEmbedding F
          hmap.trans
            (Finset.sum_attach S (fun η : ℂ => zetaZeroSideContribution η φ))
        let tailEquiv :
            ↑(Szero : Set {ξ : ℂ // ZetaCompletedZero ξ})ᶜ ≃
              {ξ : ℂ // ZetaCompletedZero ξ ∧ ξ ∉ S} := {
          toFun := fun ξ =>
            ⟨(ξ.1 : ℂ),
              ⟨ξ.1.2,
                fun hmem =>
                  ξ.2
                    (Finset.mem_coe.mpr
                      (Finset.mem_map.mpr
                        ⟨⟨(ξ.1 : ℂ), hmem⟩,
                          (Finset.mem_attach S
                            ⟨(ξ.1 : ℂ), hmem⟩),
                          Subtype.ext rfl⟩))⟩⟩
          invFun := fun ξ =>
            ⟨⟨ξ, ξ.2.1⟩,
              fun hmem =>
                ξ.2.2
                  (match Finset.mem_map.mp (Finset.mem_coe.mp hmem) with
                  | ⟨η, _hη, hηξ⟩ =>
                      have hval : (η : ℂ) = (ξ : ℂ) :=
                        congrArg
                          (fun ζ : {ξ : ℂ // ZetaCompletedZero ξ} => (ζ : ℂ))
                          hηξ
                      Eq.subst
                        (motive := fun z : ℂ => z ∈ S)
                        hval
                        η.2)⟩
          left_inv := by
            intro ξ
            exact Subtype.ext (Subtype.ext rfl)
          right_inv := by
            intro ξ
            exact Subtype.ext rfl }
        have htail :
            (∑' ξ : ↑(Szero : Set {ξ : ℂ // ZetaCompletedZero ξ})ᶜ, F ξ) =
              (∑' ξ : {ξ : ℂ // ZetaCompletedZero ξ ∧ ξ ∉ S},
                zetaZeroSideContribution (ξ : ℂ) φ) :=
          Eq.trans
            ((tailEquiv.symm.tsum_eq
              (fun ξ : ↑(Szero : Set {ξ : ℂ // ZetaCompletedZero ξ})ᶜ =>
                F ξ)).symm)
            (tsum_congr
              (fun ξ : {ξ : ℂ // ZetaCompletedZero ξ ∧ ξ ∉ S} => rfl))
        hsplit.symm.trans
          (Eq.trans
            (congrArg
              (fun x : ℂ =>
                x +
                  (∑' ξ : ↑(Szero : Set {ξ : ℂ // ZetaCompletedZero ξ})ᶜ,
                    F ξ))
              hfinite)
            (congrArg
              (fun x : ℂ =>
                (∑ η in S, zetaZeroSideContribution η φ) + x)
              htail))
      exact congrArg (fun x : ℂ => Complex.re x) h_decomp
    _ = (Complex.re (∑ η in zetaZeroOrbitFinset ρ,
          zetaZeroSideContribution η φ)) +
        (Complex.re (∑' ξ : {ξ : ℂ // ZetaCompletedZero ξ ∧ ξ ∉ zetaZeroOrbitFinset ρ},
          zetaZeroSideContribution (ξ : ℂ) φ)) := by
      exact Complex.add_re _ _
    _ = zetaZeroOrbitContributionRe ρ φ + zetaZeroOrbitRemainderRe ρ φ := by
      exact congrArg₂ HAdd.hAdd (congrArg Complex.re h_orbit_eq) (congrArg Complex.re h_remainder_eq)

end
end LFunctions
end Boundary
