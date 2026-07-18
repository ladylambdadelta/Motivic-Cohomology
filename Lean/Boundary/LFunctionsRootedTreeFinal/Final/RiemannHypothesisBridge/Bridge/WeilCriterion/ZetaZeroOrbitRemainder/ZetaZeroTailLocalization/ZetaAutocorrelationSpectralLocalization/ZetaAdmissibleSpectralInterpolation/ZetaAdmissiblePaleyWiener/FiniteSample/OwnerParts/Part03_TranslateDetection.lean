import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.FiniteSample.OwnerParts.Part02_CorrectedResidual

namespace Boundary
namespace LFunctions
namespace ZetaAdmissibleFunction
noncomputable section

/-- A finite linear combination of scaled translates realizes the Lagrange-recombined
finite distribution pairing. -/
theorem zetaLaplaceTransformFiniteSample_scaledTranslateCombination_pairing
    (S : Finset ℂ) (coeff : S → ℂ)
    (seed : ZetaAdmissibleFunction)
    (δ : ℝ) (weights : Fin (Finset.univ : Finset S).card → ℂ) :
    let χ : S → ℂ :=
      fun z : S => zetaScaledTranslateCharacter δ (z : ℂ)
    let H : ZetaAdmissibleFunction :=
      ∑ k : Fin (Finset.univ : Finset S).card,
        weights k •
          ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed
    (∑ z : S, zetaLaplaceTransformFiniteSample S H z * coeff z) =
      ∑ k : Fin (Finset.univ : Finset S).card,
        weights k *
          (∑ z : S,
            (coeff z *
              Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                χ z ^ (k : ℕ)) := by
  intro χ H
  have hH :
      H =
        ∑ k : Fin (Finset.univ : Finset S).card,
          weights k •
            ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed := by
    rfl
  calc
    (∑ z : S, zetaLaplaceTransformFiniteSample S H z * coeff z) =
        ∑ z : S,
          zetaLaplaceTransformFiniteSample S
            (∑ k : Fin (Finset.univ : Finset S).card,
              weights k •
                ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed) z * coeff z := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrArg
            (fun u : ZetaAdmissibleFunction =>
              zetaLaplaceTransformFiniteSample S u z * coeff z)
            hH)
    _ =
        ∑ z : S,
          (∑ k : Fin (Finset.univ : Finset S).card,
            zetaLaplaceTransformFiniteSample S
              (weights k •
                ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed) z) *
              coeff z := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          have hsumPoint :
              zetaLaplaceTransformFiniteSample S
                  (∑ k : Fin (Finset.univ : Finset S).card,
                    weights k •
                      ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed) z =
                  ∑ k : Fin (Finset.univ : Finset S).card,
                    zetaLaplaceTransformFiniteSample S
                      (weights k •
                        ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed) z := by
            calc
              zetaLaplaceTransformFiniteSample S
                  (∑ k : Fin (Finset.univ : Finset S).card,
                    weights k •
                      ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed) z =
                  (∑ k : Fin (Finset.univ : Finset S).card,
                    zetaLaplaceTransformFiniteSample S
                      (weights k •
                        ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed)) z := by
                exact congrFun
                  (zetaLaplaceTransformFiniteSample_sum
                    S
                    (Finset.univ : Finset (Fin (Finset.univ : Finset S).card))
                    (fun k : Fin (Finset.univ : Finset S).card =>
                      weights k •
                        ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed))
                  z
              _ =
                  ∑ k : Fin (Finset.univ : Finset S).card,
                    zetaLaplaceTransformFiniteSample S
                      (weights k •
                        ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed) z := by
                exact
                  Finset.sum_apply
                    z
                    (Finset.univ : Finset (Fin (Finset.univ : Finset S).card))
                    (fun k : Fin (Finset.univ : Finset S).card =>
                      zetaLaplaceTransformFiniteSample S
                        (weights k •
                          ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed))
          congrArg
            (fun u : ℂ => u * coeff z)
            hsumPoint)
    _ =
        ∑ z : S,
          (∑ k : Fin (Finset.univ : Finset S).card,
            weights k *
              Boundary.zetaLaplaceTransform
                (ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed).toZetaTestFunction'
                (z : ℂ)) *
              coeff z := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrArg
            (fun u : ℂ => u * coeff z)
            (Finset.sum_congr rfl
              (fun k _hk =>
                congrFun
                  (zetaLaplaceTransformFiniteSample_smul
                    S
                    (weights k)
                    (ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed))
                  z)))
    _ =
        ∑ z : S,
          ∑ k : Fin (Finset.univ : Finset S).card,
            (weights k *
              Boundary.zetaLaplaceTransform
                (ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed).toZetaTestFunction'
                (z : ℂ)) *
              coeff z := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          Finset.sum_mul
            (s := (Finset.univ : Finset (Fin (Finset.univ : Finset S).card)))
            (f := fun k : Fin (Finset.univ : Finset S).card =>
              weights k *
                Boundary.zetaLaplaceTransform
                  (ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed).toZetaTestFunction'
                  (z : ℂ))
            (a := coeff z))
    _ =
        ∑ k : Fin (Finset.univ : Finset S).card,
          ∑ z : S,
            (weights k *
              Boundary.zetaLaplaceTransform
                (ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed).toZetaTestFunction'
                (z : ℂ)) *
              coeff z := by
      exact Finset.sum_comm
    _ =
        ∑ k : Fin (Finset.univ : Finset S).card,
          ∑ z : S,
            weights k *
              ((coeff z *
                Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                  χ z ^ (k : ℕ)) := by
      exact Finset.sum_congr rfl
        (fun k _hk =>
          Finset.sum_congr rfl
            (fun z _hz =>
              calc
                (weights k *
                    Boundary.zetaLaplaceTransform
                      (ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed).toZetaTestFunction'
                      (z : ℂ)) *
                    coeff z =
                    (weights k *
                      (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) *
                        Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ))) *
                      coeff z := by
                  exact congrArg
                    (fun u : ℂ => (weights k * u) * coeff z)
                    (Boundary.zetaLaplaceTransform_translate ((k : ℝ) * δ) seed (z : ℂ))
                _ =
                    weights k *
                      ((coeff z *
                        Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                          χ z ^ (k : ℕ)) := by
                  have hpow :
                      χ z ^ (k : ℕ) =
                        Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) :=
                    zetaScaledTranslateCharacter_pow δ (z : ℂ) (k : ℕ)
                  calc
                    (weights k *
                        (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) *
                          Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ))) *
                        coeff z =
                        weights k *
                          ((Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) *
                            Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                              coeff z) := by
                      exact mul_assoc
                        (weights k)
                        (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) *
                          Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ))
                        (coeff z)
                    _ =
                        weights k *
                          (coeff z *
                            (Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ) *
                              Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))))) := by
                      exact congrArg
                        (fun u : ℂ => weights k * u)
                        (calc
                          (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) *
                              Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                              coeff z =
                              coeff z *
                                (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) *
                                  Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) := by
                            exact mul_comm
                              (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))) *
                                Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ))
                              (coeff z)
                          _ =
                              coeff z *
                                (Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ) *
                                  Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ)))) := by
                            exact congrArg
                              (fun u : ℂ => coeff z * u)
                              (mul_comm
                                (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))))
                                (Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ))))
                    _ =
                        weights k *
                          ((coeff z *
                            Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                              Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ)))) := by
                      exact congrArg
                        (fun u : ℂ => weights k * u)
                        ((mul_assoc
                            (coeff z)
                            (Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ))
                            (Complex.exp (-((z : ℂ) * (((k : ℝ) * δ : ℝ) : ℂ))))).symm)
                    _ =
                        weights k *
                          ((coeff z *
                            Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                              χ z ^ (k : ℕ)) := by
                      exact congrArg
                        (fun u : ℂ =>
                          weights k *
                            ((coeff z *
                              Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                                u))
                        hpow.symm))
    _ =
        ∑ k : Fin (Finset.univ : Finset S).card,
          weights k *
            (∑ z : S,
              (coeff z *
                Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                  χ z ^ (k : ℕ)) := by
      exact Finset.sum_congr rfl
        (fun k _hk =>
          (Finset.mul_sum Finset.univ
            (fun z : S =>
              (coeff z *
                Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                  χ z ^ (k : ℕ))
            (weights k)).symm)

/-- If the residual coefficient has a seed whose Laplace value is nonzero at the
insertion point, finite Lagrange recombination of scaled translates detects the
corrected residual. -/
theorem exists_zetaLaplaceTransformCorrectedResidual_nonzero_of_seed_ownerPaleyWiener
    (T : Finset ℂ) (a : ℂ) (haT : a ∉ T)
    (Ftail : T → ZetaAdmissibleFunction)
    (seed : ZetaAdmissibleFunction)
    (hseed :
      Boundary.zetaLaplaceTransform seed.toZetaTestFunction' a ≠ 0) :
    ∃ h : ZetaAdmissibleFunction,
      zetaLaplaceTransformCorrectedResidual T a Ftail h ≠ 0 := by
  let S : Finset ℂ := insert a T
  let coeff : S → ℂ :=
    zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail
  let anew : S := ⟨a, Finset.mem_insert_self a T⟩
  let support : Finset S := Finset.univ
  let sample : S → ℂ := fun z : S => (z : ℂ)
  let δ : ℝ := zetaFiniteImaginaryDifferenceScaleFinset support sample
  let χ : S → ℂ := fun z : S => zetaScaledTranslateCharacter δ (z : ℂ)
  let seededCoeff : S → ℂ :=
    fun z : S =>
      coeff z * Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)
  have hsample :
      Set.InjOn sample (support : Set S) := by
    intro z _hz w _hw hzw
    exact Subtype.ext hzw
  have hχ :
      Set.InjOn χ (support : Set S) :=
    zetaScaledTranslateCharacter_injOn_finiteSmallScale_finset
      (s := support)
      (sample := sample)
      hsample
  have hanew_mem : anew ∈ support :=
    Finset.mem_univ anew
  have hcoeff_nonzero :
      coeff anew ≠ 0 :=
    zetaLaplaceTransformCorrectedResidualCoefficient_nonzero T a Ftail
  have hseed_anew :
      Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (anew : ℂ) ≠ 0 := by
    exact hseed
  have hseeded_nonzero :
      seededCoeff anew ≠ 0 := by
    exact mul_ne_zero hcoeff_nonzero hseed_anew
  match
      zetaFiniteExponentialMoments_lagrange_recombine_finset
        (s := support)
        (χ := χ)
        (seededCoeff := seededCoeff)
        hχ
        hanew_mem with
  | ⟨weights, hweights⟩ =>
      let h : ZetaAdmissibleFunction :=
        ∑ k : Fin support.card,
          weights k •
            ZetaAdmissibleFunction.translate ((k : ℝ) * δ) seed
      have hpair_value :
          (∑ z : S,
            zetaLaplaceTransformFiniteSample S h z * coeff z) =
            seededCoeff anew := by
        calc
          (∑ z : S,
              zetaLaplaceTransformFiniteSample S h z * coeff z) =
              ∑ k : Fin support.card,
                weights k *
                  (∑ z : S,
                    (coeff z *
                      Boundary.zetaLaplaceTransform seed.toZetaTestFunction' (z : ℂ)) *
                        χ z ^ (k : ℕ)) := by
            exact
              zetaLaplaceTransformFiniteSample_scaledTranslateCombination_pairing
                S coeff seed δ weights
          _ = seededCoeff anew := by
            exact hweights
      have hpair_nonzero :
          (∑ z : S,
            zetaLaplaceTransformFiniteSample S h z * coeff z) ≠ 0 := by
        intro hzero
        exact hseeded_nonzero (hpair_value.symm.trans hzero)
      exact ⟨h, fun hResidualZero =>
        hpair_nonzero
          ((zetaLaplaceTransformCorrectedResidual_eq_insertCoefficientSum
            T a haT Ftail h).symm.trans hResidualZero)⟩

/-- The residual coefficient at an insertion step is a nonzero finite exponential
distribution, hence some admissible probe has nonzero corrected residual. -/
theorem exists_zetaLaplaceTransformCorrectedResidual_nonzero_ownerPaleyWiener
    (T : Finset ℂ) (a : ℂ) (haT : a ∉ T)
    (Ftail : T → ZetaAdmissibleFunction) :
    ∃ h : ZetaAdmissibleFunction,
      zetaLaplaceTransformCorrectedResidual T a Ftail h ≠ 0 := by
  match exists_zetaLaplaceTransform_nonzero_seed a with
  | ⟨seed, hseed⟩ =>
      exact
        exists_zetaLaplaceTransformCorrectedResidual_nonzero_of_seed_ownerPaleyWiener
          T a haT Ftail seed hseed

/-- Constructive finite Paley-Wiener cardinal interpolation, obtained by inserting
samples one at a time and detecting the corrected residual at each insertion step. -/
theorem exists_zetaLaplaceTransformCardinalFamily_constructive_ownerPaleyWiener
    (S : Finset ℂ) :
    ∃ F : S → ZetaAdmissibleFunction,
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0 := by
  exact
    exists_zetaLaplaceTransformCardinalFamily_of_nonzeroCorrectedResiduals
      (fun T a haT Ftail _hFtail =>
        exists_zetaLaplaceTransformCorrectedResidual_nonzero_ownerPaleyWiener
          T a haT Ftail)
      S

/-- Constructive finite Paley-Wiener interpolation in finite-vector form. -/
theorem exists_zetaLaplaceTransformFiniteSample_eq_constructive_ownerPaleyWiener
    (S : Finset ℂ) (aS : S → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      zetaLaplaceTransformFiniteSample S f = aS := by
  match exists_zetaLaplaceTransformCardinalFamily_constructive_ownerPaleyWiener S with
  | ⟨F, hF⟩ =>
      exact
        exists_zetaLaplaceTransformFiniteSample_eq_of_cardinalFamily_ownerPaleyWiener
          S aS F hF

end
end ZetaAdmissibleFunction
end LFunctions
end Boundary
