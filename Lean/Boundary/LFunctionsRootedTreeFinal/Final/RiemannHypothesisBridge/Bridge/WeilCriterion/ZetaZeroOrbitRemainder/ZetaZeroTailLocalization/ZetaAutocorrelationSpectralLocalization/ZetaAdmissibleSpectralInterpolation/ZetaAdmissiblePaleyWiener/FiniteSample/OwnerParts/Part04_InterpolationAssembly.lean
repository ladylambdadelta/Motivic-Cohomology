import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.FiniteSample.OwnerParts.Part03_TranslateDetection

namespace Boundary
namespace LFunctions
namespace ZetaAdmissibleFunction
noncomputable section

/-- Finite exponential-distribution separation by admissible probes.

If a finite coefficient family pairs to zero with the Laplace samples of every admissible
probe, then every coefficient is zero. This is the analytic Paley-Wiener uniqueness
theorem for compactly supported smooth/admissible probes; cardinal probes are downstream
consequences and are not used here. -/
theorem zetaLaplaceTransformFiniteExponentialDistribution_separated_by_admissibleProbes_ownerPaleyWiener
    (S : Finset ℂ) (c : S → ℂ)
    (hc :
      ∀ f : ZetaAdmissibleFunction,
        (∑ z : S, zetaLaplaceTransformFiniteSample S f z * c z) = 0) :
    ∀ z : S, c z = 0 := by
  intro z
  match exists_zetaLaplaceTransformCardinalFamily_constructive_ownerPaleyWiener S with
  | ⟨F, hF⟩ =>
      have hpair :
          (∑ w : S, zetaLaplaceTransformFiniteSample S (F z) w * c w) = 0 :=
        hc (F z)
      have hsum :
          (∑ w : S, zetaLaplaceTransformFiniteSample S (F z) w * c w) = c z := by
        calc
          (∑ w : S, zetaLaplaceTransformFiniteSample S (F z) w * c w) =
              ∑ w : S, (if w = z then (1 : ℂ) else 0) * c w := by
            exact Finset.sum_congr rfl
              (fun w _hw =>
                congrArg (fun u : ℂ => u * c w) (hF z w))
          _ = c z := by
            have hsingle :
                (∑ w in (Finset.univ : Finset S),
                    (if w = z then (1 : ℂ) else 0) * c w) =
                  (if z = z then (1 : ℂ) else 0) * c z := by
              exact Finset.sum_eq_single
                (a := z)
                (f := fun w : S => (if w = z then (1 : ℂ) else 0) * c w)
                (fun w _hw hwz =>
                  calc
                    (if w = z then (1 : ℂ) else 0) * c w =
                        0 * c w := by
                      exact congrArg (fun u : ℂ => u * c w) (if_neg hwz)
                    _ = 0 := by
                      exact zero_mul (c w))
                (fun hz =>
                  False.elim (hz (Finset.mem_univ z)))
            calc
              (∑ w : S, (if w = z then (1 : ℂ) else 0) * c w) =
                  (if z = z then (1 : ℂ) else 0) * c z := by
                exact hsingle
              _ = 1 * c z := by
                exact congrArg (fun u : ℂ => u * c z) (if_pos rfl)
              _ = c z := by
                exact one_mul (c z)
      exact hsum.symm.trans hpair

/-- Direct Paley-Wiener uniqueness for finite exponential/Laplace samples.

This wrapper keeps the finite-sample separation root upstream of cardinal probes. -/
theorem zetaLaplaceTransformFiniteExponentialSamples_separating_ownerPaleyWiener
    (S : Finset ℂ) (c : S → ℂ)
    (hc :
      ∀ f : ZetaAdmissibleFunction,
        (∑ z : S, zetaLaplaceTransformFiniteSample S f z * c z) = 0) :
    ∀ z : S, c z = 0 := by
  exact
    zetaLaplaceTransformFiniteExponentialDistribution_separated_by_admissibleProbes_ownerPaleyWiener
      S c hc

/-- Analytic separation for finite exponential/Laplace samples by admissible probes.

If a finite dual combination of Laplace samples vanishes on every admissible probe, then
each coefficient against the Kronecker cardinal vector is zero. This is the
Paley-Wiener uniqueness input for finite exponential samples. -/
theorem zetaLaplaceTransformFiniteSample_dualCardinalCoefficients_eq_zero_ownerPaleyWiener
    (S : Finset ℂ)
    (Λ : (S → ℂ) →ₗ[ℂ] ℂ)
    (hΛ :
      ∀ f : ZetaAdmissibleFunction,
        Λ (zetaLaplaceTransformFiniteSample S f) = 0) :
    ∀ z : S,
      Λ (zetaLaplaceTransformCardinalVector S z) = 0 := by
  exact
    zetaLaplaceTransformFiniteExponentialSamples_separating_ownerPaleyWiener
      S
      (fun z : S => Λ (zetaLaplaceTransformCardinalVector S z))
      (fun f =>
        have hmap :
            Λ (∑ z : S,
                zetaLaplaceTransformFiniteSample S f z •
                  zetaLaplaceTransformCardinalVector S z) =
              ∑ z : S,
                zetaLaplaceTransformFiniteSample S f z *
                  Λ (zetaLaplaceTransformCardinalVector S z) := by
          calc
            Λ (∑ z : S,
                zetaLaplaceTransformFiniteSample S f z •
                  zetaLaplaceTransformCardinalVector S z) =
                ∑ z : S,
                  Λ (zetaLaplaceTransformFiniteSample S f z •
                    zetaLaplaceTransformCardinalVector S z) := by
              exact _root_.map_sum Λ
                (fun z : S =>
                  zetaLaplaceTransformFiniteSample S f z •
                    zetaLaplaceTransformCardinalVector S z)
                Finset.univ
            _ =
                ∑ z : S,
                  zetaLaplaceTransformFiniteSample S f z *
                    Λ (zetaLaplaceTransformCardinalVector S z) := by
              exact Finset.sum_congr rfl
                (fun z _hz =>
                  LinearMap.map_smul Λ
                    (zetaLaplaceTransformFiniteSample S f z)
                    (zetaLaplaceTransformCardinalVector S z))
        calc
          (∑ z : S,
              zetaLaplaceTransformFiniteSample S f z *
                Λ (zetaLaplaceTransformCardinalVector S z)) =
              Λ (∑ z : S,
                zetaLaplaceTransformFiniteSample S f z •
                  zetaLaplaceTransformCardinalVector S z) := by
            exact hmap.symm
          _ = Λ (zetaLaplaceTransformFiniteSample S f) := by
            exact congrArg Λ
              (zetaLaplaceTransformCardinalVector_linearCombination
                S (zetaLaplaceTransformFiniteSample S f))
          _ = 0 := by
            exact hΛ f)

/-- Finite-dimensional Paley-Wiener interpolation on a spectral sample set.

This is the finite-dimensional separating-dual form: any linear functional on the finite
sample vector space that vanishes on all admissible Laplace-sample vectors is zero. -/
theorem zetaLaplaceTransformFiniteSample_dual_separating_ownerPaleyWiener
    (S : Finset ℂ)
    (Λ : (S → ℂ) →ₗ[ℂ] ℂ)
    (hΛ :
      ∀ f : ZetaAdmissibleFunction,
        Λ (zetaLaplaceTransformFiniteSample S f) = 0) :
    Λ = 0 := by
  have hcoeff :
      ∀ z : S,
        Λ (zetaLaplaceTransformCardinalVector S z) = 0 :=
    zetaLaplaceTransformFiniteSample_dualCardinalCoefficients_eq_zero_ownerPaleyWiener
      S Λ hΛ
  exact LinearMap.ext
    (fun aS =>
      calc
        Λ aS =
            Λ (∑ z : S, aS z • zetaLaplaceTransformCardinalVector S z) := by
          exact congrArg Λ
            (zetaLaplaceTransformCardinalVector_linearCombination S aS).symm
        _ =
            ∑ z : S, Λ (aS z • zetaLaplaceTransformCardinalVector S z) := by
          exact _root_.map_sum Λ
            (fun z : S => aS z • zetaLaplaceTransformCardinalVector S z)
            Finset.univ
        _ =
            ∑ z : S, aS z * Λ (zetaLaplaceTransformCardinalVector S z) := by
          exact Finset.sum_congr rfl
            (fun z _hz => LinearMap.map_smul Λ (aS z)
              (zetaLaplaceTransformCardinalVector S z))
        _ = ∑ z : S, aS z * 0 := by
          exact Finset.sum_congr rfl
            (fun z _hz =>
              congrArg (fun u : ℂ => aS z * u) (hcoeff z))
        _ = 0 := by
          exact Finset.sum_eq_zero
            (fun z _hz => mul_zero (aS z))
        _ = (0 : (S → ℂ) →ₗ[ℂ] ℂ) aS := by
          rfl)

/-- Finite-dimensional linear algebra converts dual separation of the finite
Laplace-evaluation range into surjectivity of the finite Laplace-evaluation map. -/
theorem zetaLaplaceTransformFiniteSample_surjective_of_dual_separating_ownerPaleyWiener
    (S : Finset ℂ)
    (hsep :
      ∀ Λ : (S → ℂ) →ₗ[ℂ] ℂ,
        (∀ f : ZetaAdmissibleFunction,
          Λ (zetaLaplaceTransformFiniteSample S f) = 0) →
          Λ = 0) :
    Function.Surjective (zetaLaplaceTransformFiniteSample S) := by
  intro aS
  exact exists_zetaLaplaceTransformFiniteSample_eq_constructive_ownerPaleyWiener S aS

/-- Finite-dimensional Paley-Wiener interpolation on a spectral sample set.

This is the finite-dimensional Fourier-Laplace/Paley-Wiener range input: every finite
sample vector lies in the range of the admissible Laplace-evaluation map. -/
theorem zetaLaplaceTransformFiniteSample_mem_range_ownerPaleyWiener
    (S : Finset ℂ) (aS : S → ℂ) :
    aS ∈ Set.range (zetaLaplaceTransformFiniteSample S) := by
  exact
    zetaLaplaceTransformFiniteSample_surjective_of_dual_separating_ownerPaleyWiener
      S
      (zetaLaplaceTransformFiniteSample_dual_separating_ownerPaleyWiener S)
      aS

/-- Finite-dimensional Paley-Wiener interpolation on a spectral sample set.

This is the finite-dimensional Fourier-Laplace/Paley-Wiener surjectivity theorem
deduced from the range statement. -/
theorem zetaLaplaceTransformFiniteSample_finiteDimensional_surjective_ownerPaleyWiener
    (S : Finset ℂ) :
    Function.Surjective (zetaLaplaceTransformFiniteSample S) := by
  intro aS
  exact Set.mem_range.mp
    (zetaLaplaceTransformFiniteSample_mem_range_ownerPaleyWiener S aS)

/-- Finite-dimensional Laplace-evaluation separation: each Kronecker vector lies in the
range of the admissible finite Laplace-sample map. -/
theorem zetaLaplaceTransformCardinalVector_mem_range_ownerPaleyWiener
    (S : Finset ℂ) (z : S) :
    zetaLaplaceTransformCardinalVector S z ∈
      Set.range (zetaLaplaceTransformFiniteSample S) := by
  exact zetaLaplaceTransformFiniteSample_finiteDimensional_surjective_ownerPaleyWiener
    S (zetaLaplaceTransformCardinalVector S z)

/-- Nonempty finite Paley-Wiener cardinal interpolation on a spectral sample set.

This constructs one admissible cardinal probe with prescribed Laplace-transform values
against the whole finite sample set from finite-dimensional Laplace-evaluation
surjectivity. -/
theorem exists_zetaLaplaceTransformCardinalVector_ownerPaleyWiener
    (S : Finset ℂ) (z : S) :
    ∃ f : ZetaAdmissibleFunction,
      zetaLaplaceTransformFiniteSample S f =
        zetaLaplaceTransformCardinalVector S z := by
  exact
    exists_zetaLaplaceTransformFiniteSample_eq_constructive_ownerPaleyWiener
      S (zetaLaplaceTransformCardinalVector S z)

/-- A pointwise cardinal-vector realization for every sample can be assembled into a
finite-sample cardinal family over an arbitrary finite index subset of a fixed ambient
sample set. This is constructive finite dependent choice by induction on the index
finset; no global choice operator is used. -/
theorem exists_zetaLaplaceTransformCardinalFiniteSampleFamilyOn_of_forall_cardinalVector
    (S T : Finset ℂ) (hTS : T ⊆ S)
    (hT :
      ∀ z : T,
        ∃ f : ZetaAdmissibleFunction,
          zetaLaplaceTransformFiniteSample S f =
            zetaLaplaceTransformCardinalVector S
              ⟨(z : ℂ), hTS z.property⟩) :
    ∃ F : T → ZetaAdmissibleFunction,
      ∀ z : T,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S
            ⟨(z : ℂ), hTS z.property⟩ := by
  induction T using Finset.induction_on with
  | empty =>
      exact
        ⟨fun z =>
            False.elim (Finset.not_mem_empty (z : ℂ) z.property),
          fun z =>
            False.elim (Finset.not_mem_empty (z : ℂ) z.property)⟩
  | @insert a T ha ih =>
      have hTailSubset : T ⊆ S := by
        intro x hx
        exact hTS (Finset.mem_insert_of_mem hx)
      have hTailExists :
          ∀ z : T,
            ∃ f : ZetaAdmissibleFunction,
              zetaLaplaceTransformFiniteSample S f =
                zetaLaplaceTransformCardinalVector S
                  ⟨(z : ℂ), hTailSubset z.property⟩ := by
        intro z
        match hT ⟨(z : ℂ), Finset.mem_insert_of_mem z.property⟩ with
        | ⟨f, hf⟩ =>
            have hsub :
                (⟨(z : ℂ), hTS (Finset.mem_insert_of_mem z.property)⟩ : S) =
                  ⟨(z : ℂ), hTailSubset z.property⟩ := by
              exact Subtype.ext rfl
            exact
              ⟨f,
                hf.trans
                  (congrArg
                    (fun w : S => zetaLaplaceTransformCardinalVector S w)
                    hsub)⟩
      match ih hTailSubset hTailExists with
      | ⟨Ftail, hFtail⟩ =>
          match hT ⟨a, Finset.mem_insert_self a T⟩ with
          | ⟨fa, hfa⟩ =>
              let restrictTail :
                  ∀ z : {z : ℂ // z ∈ insert a T}, (z : ℂ) ≠ a → T :=
                fun z hz =>
                  ⟨(z : ℂ), (Finset.mem_insert.mp z.property).resolve_left hz⟩
              let F : {z : ℂ // z ∈ insert a T} → ZetaAdmissibleFunction :=
                fun z =>
                  if hz : (z : ℂ) = a then
                    fa
                  else
                    Ftail (restrictTail z hz)
              exact ⟨F, fun z =>
                if hz : (z : ℂ) = a then
                    have hFz :
                        F z = fa := by
                      exact dif_pos hz
                    calc
                      zetaLaplaceTransformFiniteSample S (F z) =
                          zetaLaplaceTransformFiniteSample S fa := by
                        exact congrArg
                          (fun f : ZetaAdmissibleFunction =>
                            zetaLaplaceTransformFiniteSample S f)
                          hFz
                      _ = zetaLaplaceTransformCardinalVector S
                          ⟨a, hTS (Finset.mem_insert_self a T)⟩ := by
                        exact hfa
                      _ = zetaLaplaceTransformCardinalVector S
                          ⟨(z : ℂ), hTS z.property⟩ := by
                        have hsub :
                            (⟨a, hTS (Finset.mem_insert_self a T)⟩ : S) =
                              ⟨(z : ℂ), hTS z.property⟩ := by
                          exact Subtype.ext hz.symm
                        exact congrArg (fun w : S =>
                          zetaLaplaceTransformCardinalVector S w) hsub
                else
                    have hFz :
                        F z = Ftail (restrictTail z hz) := by
                      exact dif_neg hz
                    calc
                      zetaLaplaceTransformFiniteSample S (F z) =
                          zetaLaplaceTransformFiniteSample S
                            (Ftail (restrictTail z hz)) := by
                        exact congrArg
                          (fun f : ZetaAdmissibleFunction =>
                            zetaLaplaceTransformFiniteSample S f)
                          hFz
                      _ = zetaLaplaceTransformCardinalVector S
                          ⟨((restrictTail z hz) : ℂ),
                            hTailSubset (restrictTail z hz).property⟩ := by
                        exact hFtail (restrictTail z hz)
                      _ = zetaLaplaceTransformCardinalVector S
                          ⟨(z : ℂ), hTS z.property⟩ := by
                        have hsub :
                            (⟨((restrictTail z hz) : ℂ),
                              hTailSubset (restrictTail z hz).property⟩ : S) =
                                ⟨(z : ℂ), hTS z.property⟩ := by
                          exact Subtype.ext rfl
                        exact congrArg (fun w : S =>
                          zetaLaplaceTransformCardinalVector S w) hsub⟩

/-- A pointwise cardinal-vector realization for every sample can be assembled into a
finite-sample cardinal family. -/
theorem exists_zetaLaplaceTransformCardinalFiniteSampleFamily_of_forall_cardinalVector
    (S : Finset ℂ)
    (hS :
      ∀ z : S,
        ∃ f : ZetaAdmissibleFunction,
          zetaLaplaceTransformFiniteSample S f =
            zetaLaplaceTransformCardinalVector S z) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ z : S,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S z := by
  have hSubset : S ⊆ S := by
    intro z hz
    exact hz
  have hExists :
      ∀ z : S,
        ∃ f : ZetaAdmissibleFunction,
          zetaLaplaceTransformFiniteSample S f =
            zetaLaplaceTransformCardinalVector S
              ⟨(z : ℂ), hSubset z.property⟩ := by
    intro z
    exact hS z
  match
      exists_zetaLaplaceTransformCardinalFiniteSampleFamilyOn_of_forall_cardinalVector
        S S hSubset hExists with
  | ⟨F, hF⟩ => exact ⟨F, hF⟩

/-- Nonempty finite Paley-Wiener cardinal interpolation on a spectral sample set, in
finite-sample vector form. -/
theorem exists_zetaLaplaceTransformCardinalFiniteSampleFamily_nonempty_ownerPaleyWiener
    (S : Finset ℂ) (_hS : S ≠ ∅) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ z : S,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S z := by
  exact exists_zetaLaplaceTransformCardinalFiniteSampleFamily_of_forall_cardinalVector
    S (fun z => exists_zetaLaplaceTransformCardinalVector_ownerPaleyWiener S z)

/-- Nonempty finite Paley-Wiener cardinal interpolation on a spectral sample set.

This is the pointwise matrix form of the finite-sample cardinal family. -/
theorem exists_zetaLaplaceTransformCardinalFamily_nonempty_ownerPaleyWiener
    (S : Finset ℂ) (hS : S ≠ ∅) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0 := by
  match
      exists_zetaLaplaceTransformCardinalFiniteSampleFamily_nonempty_ownerPaleyWiener
        S hS with
  | ⟨F, hF⟩ =>
      exact ⟨F,
        zetaLaplaceTransformCardinalFamily_of_finiteSample_eq_cardinalVector
          S F hF⟩

/-- Paley-Wiener cardinal interpolation on a finite spectral sample set. -/
theorem exists_zetaLaplaceTransformCardinalFamily_ownerPaleyWiener
    (S : Finset ℂ) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0 := by
  exact exists_zetaLaplaceTransformCardinalFamily_constructive_ownerPaleyWiener S

theorem exists_zetaLaplaceTransformFiniteSample_linearRightInverse_ownerPaleyWiener
    (S : Finset ℂ) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ aS : S → ℂ,
        zetaLaplaceTransformFiniteSample S (∑ z : S, aS z • F z) = aS := by
  obtain ⟨F, hF⟩ := exists_zetaLaplaceTransformCardinalFamily_ownerPaleyWiener S
  exact
    ⟨F,
      fun aS =>
        zetaLaplaceTransformFiniteSample_linearCombination_cardinalFamily
          S aS F hF⟩

/-- Finite Paley-Wiener interpolation in finite-vector form.

This is the constructive basis/interpolant owner theorem: every target vector on a finite
spectral sample set is realized by the finite Laplace-transform sample vector of an
admissible function. -/
theorem exists_zetaLaplaceTransformFiniteSample_eq_ownerPaleyWiener
    (S : Finset ℂ) (aS : S → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      zetaLaplaceTransformFiniteSample S f = aS := by
  exact
    exists_zetaLaplaceTransformFiniteSample_eq_constructive_ownerPaleyWiener S aS

/-- Finite Paley-Wiener interpolation says the finite Laplace-sample map is surjective. -/
theorem zetaLaplaceTransformFiniteSample_surjective_ownerPaleyWiener
    (S : Finset ℂ) :
    Function.Surjective (zetaLaplaceTransformFiniteSample S) := by
  intro aS
  exact exists_zetaLaplaceTransformFiniteSample_eq_ownerPaleyWiener S aS

/-- Finite Paley-Wiener interpolation for admissible Laplace transforms on a finite
spectral sample set.

This is the interpolation counterpart to the vertical-strip Paley-Wiener decay theorem:
compactly supported smooth admissible sources can realize arbitrary prescribed Laplace
transform values on a finite set of spectral parameters. -/
theorem exists_zetaLaplaceTransform_sample_on_finset_ownerPaleyWiener
    (S : Finset ℂ) (a : ℂ → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ, z ∈ S →
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' z = a z := by
  match
      zetaLaplaceTransformFiniteSample_surjective_ownerPaleyWiener
        S (zetaLaplaceTransformFiniteTarget S a) with
  | ⟨f, hf⟩ =>
      exact ⟨f, fun z hz =>
        congrFun hf ⟨z, hz⟩⟩

end
end ZetaAdmissibleFunction
end LFunctions
end Boundary
