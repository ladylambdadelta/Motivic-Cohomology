import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.FiniteZeroProduct.InsertionGluing.PuncturedGerm

/-!
# Punctured finite-support avoidance

This file owns the finite-avoidance topology used by normalized factor
insertion near a support point.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Every nonempty real open interval contains a point outside a prescribed
finite set. -/
theorem real_Ioo_avoidFinite_nonempty
    (T : Finset ℝ)
    {u v : ℝ}
    (huv : u < v) :
    ∃ t : ℝ,
      t ∈ Set.Ioo u v ∧
        ∀ r : ℝ, r ∈ T → t ≠ r := by
  exact
    match (Set.Ioo_infinite huv).exists_not_mem_finset T with
    | Exists.intro t ht =>
        Exists.intro t
          (And.intro ht.1
            (fun r hr htr =>
              ht.2
                (Eq.subst (motive := fun x : ℝ => x ∈ T) htr.symm hr)))

/-- One-sided real finite avoidance near `1`.

This is the real topology core used by radial finite avoidance: numbers
`t < 1`, arbitrarily close to `1`, can be chosen outside a prescribed finite
set. -/
theorem real_leftNhds_one_avoidFinite_frequently
    (T : Finset ℝ) :
    ∃ᶠ t in 𝓝[<] (1 : ℝ),
      0 ≤ t ∧
      t < 1 ∧
        ∀ r : ℝ, r ∈ T → t ≠ r := by
  exact Filter.frequently_iff.2
    (fun {U : Set ℝ} hU =>
      match
        (mem_nhdsWithin_Iio_iff_exists_Ioo_subset (a := (1 : ℝ)) (s := U)).mp hU with
      | Exists.intro l hl =>
          have hl_lt_one : l < 1 :=
            hl.1
          have hmax_lt_one : max l 0 < 1 :=
            max_lt hl_lt_one zero_lt_one
          match real_Ioo_avoidFinite_nonempty T hmax_lt_one with
          | Exists.intro t ht =>
              have ht_mem_U : t ∈ U :=
                hl.2
                  ⟨lt_of_le_of_lt (le_max_left l 0) ht.1.1, ht.1.2⟩
              have ht_nonneg : 0 ≤ t :=
                (le_max_right l 0).trans ht.1.1.le
              Exists.intro t
                (And.intro ht_mem_U
                  (And.intro ht_nonneg
                    (And.intro ht.1.2 ht.2))))

/-- Radial finite-avoidance inside a closed disk.

For a nonzero point `a` in `closedBall 0 ρ`, the inward radial points
`t • a`, with `t < 1` and `t → 1`, stay in the closed disk, are punctured at
`a`, and avoid any prescribed finite set frequently. -/
theorem complex_closedBall_radial_punctured_avoidFinite_frequently
    (a : ℂ)
    (ρ : ℝ)
    (T : Finset ℂ)
    (ha0 : a ≠ 0)
    (haρ : ‖a‖ ≤ ρ) :
    ∃ᶠ w in 𝓝[{a}ᶜ] a,
      w ≠ a ∧
      ‖w‖ ≤ ρ ∧
        ∀ z : ℂ, z ∈ T → w ≠ z := by
  let badScalars : Finset ℝ :=
    T.image (fun z : ℂ => (z / a).re)
  have hreal :
      ∃ᶠ t in 𝓝[<] (1 : ℝ),
        0 ≤ t ∧
        t < 1 ∧
          ∀ r : ℝ, r ∈ badScalars → t ≠ r :=
    real_leftNhds_one_avoidFinite_frequently badScalars
  have htendsto_nhds :
      Filter.Tendsto (fun t : ℝ => (t : ℂ) * a) (𝓝[<] (1 : ℝ)) (𝓝 a) := by
    have hcont :
        ContinuousAt (fun t : ℝ => (t : ℂ) * a) (1 : ℝ) :=
      (Complex.continuous_ofReal.continuousAt).mul continuousAt_const
    have hvalue :
        (fun t : ℝ => (t : ℂ) * a) 1 = a := by
      exact one_mul a
    exact
      Eq.subst
        (motive := fun x : ℂ =>
          Filter.Tendsto (fun t : ℝ => (t : ℂ) * a) (𝓝[<] (1 : ℝ)) (𝓝 x))
        hvalue
        (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  have heventually_punctured :
      Filter.Eventually
        (fun t : ℝ => (t : ℂ) * a ∈ ({a}ᶜ : Set ℂ))
        (𝓝[<] (1 : ℝ)) := by
    exact
      (eventually_mem_nhdsWithin : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Set.Iio (1 : ℝ)).mono
        (fun t ht h_eq =>
          have h_eq_one_mul : (t : ℂ) * a = 1 * a :=
            h_eq.trans (one_mul a).symm
          have hscalar_complex : (t : ℂ) = 1 :=
            mul_right_cancel₀ ha0 h_eq_one_mul
          have ht_eq_one : t = 1 :=
            Complex.ofReal_injective hscalar_complex
          have hnot : ¬ t = 1 :=
            ne_of_lt ht
          hnot ht_eq_one)
  have htendsto :
      Filter.Tendsto (fun t : ℝ => (t : ℂ) * a) (𝓝[<] (1 : ℝ)) (𝓝[{a}ᶜ] a) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun t : ℝ => (t : ℂ) * a)
      htendsto_nhds
      heventually_punctured
  exact
    htendsto.frequently
      (hreal.mono
        (fun t ht =>
          have ht_nonneg : 0 ≤ t :=
            ht.1
          have ht_lt_one : t < 1 :=
            ht.2.1
          have ht_abs_eq : |t| = t :=
            abs_of_nonneg ht_nonneg
          have ht_abs_le_one : |t| ≤ 1 :=
            Eq.subst (motive := fun x : ℝ => x ≤ 1) ht_abs_eq.symm ht_lt_one.le
          have hnorm_scalar : ‖(t : ℂ)‖ = |t| := by
            calc
              ‖(t : ℂ)‖ = Complex.abs (t : ℂ) := Complex.norm_eq_abs (t : ℂ)
              _ = |t| := Complex.abs_ofReal t
          have hnorm_le_a : ‖(t : ℂ) * a‖ ≤ ‖a‖ := by
            calc
              ‖(t : ℂ) * a‖ = ‖(t : ℂ)‖ * ‖a‖ := by
                exact norm_mul (t : ℂ) a
              _ = |t| * ‖a‖ := by
                exact congrArg (fun r : ℝ => r * ‖a‖) hnorm_scalar
              _ ≤ 1 * ‖a‖ :=
                mul_le_mul_of_nonneg_right ht_abs_le_one (norm_nonneg a)
              _ = ‖a‖ := one_mul ‖a‖
          have hnorm_le_ρ : ‖(t : ℂ) * a‖ ≤ ρ :=
            hnorm_le_a.trans haρ
          ⟨fun h_eq =>
              have h_eq_one_mul : (t : ℂ) * a = 1 * a :=
                h_eq.trans (one_mul a).symm
              have hscalar_complex : (t : ℂ) = 1 :=
                mul_right_cancel₀ ha0 h_eq_one_mul
              have ht_eq_one : t = 1 :=
                Complex.ofReal_injective hscalar_complex
              have hnot : ¬ t = 1 :=
                ne_of_lt ht_lt_one
              hnot ht_eq_one,
            hnorm_le_ρ,
            fun z hz h_eq =>
              have hz_bad :
                  (z / a).re ∈ badScalars :=
                Finset.mem_image.2 ⟨z, hz, rfl⟩
              have hz_div_eq : z / a = (t : ℂ) := by
                calc
                  z / a = ((t : ℂ) * a) / a := by
                    exact congrArg (fun q : ℂ => q / a) h_eq.symm
                  _ = (t : ℂ) := mul_div_cancel_right₀ (t : ℂ) ha0
              have ht_re_eq : t = (z / a).re := by
                exact (congrArg Complex.re hz_div_eq).symm
              ht.2.2 (z / a).re hz_bad ht_re_eq⟩))

/-- Good punctured closed-disk points near a nonzero support point.

This is the topology input for finite normalized-factor cancellation: near a
nonzero point `a` with `‖a‖ ≤ ρ`, points of the closed disk that avoid `a` and
the finitely many other support centers occur frequently in the punctured
neighborhood of `a`. -/
theorem entireFunction_closedDisk_puncturedGoodPoints_frequently
    (F : ℂ → ℂ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha : a ∈ S)
    (ha0 : (a : ℂ) ≠ 0)
    (ρ : ℝ)
    (haρ : ‖(a : ℂ)‖ ≤ ρ) :
    ∃ᶠ w in 𝓝[{(a : ℂ)}ᶜ] (a : ℂ),
      w ≠ (a : ℂ) ∧
      ‖w‖ ≤ ρ ∧
        ∀ z : EntireFunctionZero F,
          z ∈ S.erase a →
            w ≠ (z : ℂ) := by
  have hradial :
      ∃ᶠ w in 𝓝[{(a : ℂ)}ᶜ] (a : ℂ),
        w ≠ (a : ℂ) ∧
        ‖w‖ ≤ ρ ∧
          ∀ z : ℂ,
            z ∈ (S.erase a).image (fun z : EntireFunctionZero F => (z : ℂ)) →
              w ≠ z :=
    complex_closedBall_radial_punctured_avoidFinite_frequently
      (a : ℂ)
      ρ
      ((S.erase a).image (fun z : EntireFunctionZero F => (z : ℂ)))
      ha0
      haρ
  exact
    hradial.mono
      (fun w hw =>
        ⟨hw.1, hw.2.1,
          fun z hz =>
            hw.2.2
              (z : ℂ)
              (Finset.mem_image.2 ⟨z, hz, rfl⟩)⟩)

end
end LFunctions
end Boundary
