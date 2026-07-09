import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongActiveWeyl
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseAdditivePrincipalCover

/-!
# Additive one-shift all-integer resonance cover

This file owns the one-shift monotone-curvature resonance decomposition with
the additive complement count: resonance-family gaps plus principal-strip
crossings.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The active complement admits an additive principal-branch gap cover: the
number of pieces is bounded by the resonance-family gap count plus the
principal-strip crossing count. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_exists_additivePrincipalGapCover
    (t : ℝ)
    {a b h : ℕ}
    {eta lo hi : ℝ}
    (habh : a ≤ b - h)
    (heta_pi : eta ≤ Real.pi)
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ hi)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ∃ gaps : Finset (ℕ × ℕ),
      ∃ center : ℕ × ℕ → ℤ,
        Complex.realPhase_IcoFamilyUnion gaps =
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h eta ∧
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) ∧
          (∀ p : ℕ × ℕ,
            p ∈ gaps →
              a ≤ p.1 ∧ p.2 ≤ b - h) ∧
          (∀ p : ℕ × ℕ,
            p ∈ gaps →
              ∀ n : ℕ,
                n ∈ Finset.Ico p.1 p.2 →
                  Complex.realPhase_integerIncrement
                      (Complex.realPhase_integerLatticeShift
                        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                          h)
                        (center p))
                      n ∈
                    Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) ∧
          gaps.card ≤
            ((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h eta).card +
              (Complex.realPhase_integerIncrementRangeActiveCenters
                lo hi Real.pi).card) + 1 := by
  let ψ : ℝ → ℝ :=
    Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h
  let Keta : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
      t a b h eta
  let Kpi : Finset ℤ :=
    Complex.realPhase_integerIncrementRangeActiveCenters lo hi Real.pi
  have hgap_exists :
      ∃ gaps : Finset (ℕ × ℕ),
        Complex.realPhase_IcoFamilyUnion gaps =
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h eta ∧
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) ∧
          Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
          Complex.realPhase_IcoFamilyBounded a (b - h) gaps ∧
          gaps.card ≤ Keta.card + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_exists_bounded_IcoFamily_cover_of_mono_of_le_pi
      t habh hinc_mono heta_pi
  match hgap_exists with
  | ⟨gaps, hgap_cover, hgap_disjoint, _hconnected, hgap_bounded, hgap_card⟩ =>
      have hblock_subset :
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h eta ⊆
            Finset.Ico a (b - h) := by
        intro n hn
        exact
          (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
            ψ).mp hn |>.1
      have hcomplement_subset_principal :
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h eta ⊆
            Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
              ψ a (b - h) Kpi :=
        Complex.finset_subset_integerIncrementPrincipalStripFamilyUnion_rangeActiveCenters
          ψ hblock_subset hrange
      have hrefine_exists :
          ∃ refined : Finset (ℕ × ℕ),
            ∃ center : ℕ × ℕ → ℤ,
              refined.card ≤ gaps.card + Kpi.card ∧
                Complex.realPhase_IcoFamilyUnion refined =
                  (Complex.realPhase_IcoFamilyUnion gaps).filter
                    (fun n : ℕ =>
                      n ∈
                        Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                          ψ a (b - h) Kpi) ∧
                (∀ q₁ : ℕ × ℕ,
                  q₁ ∈ refined →
                    ∀ q₂ : ℕ × ℕ,
                      q₂ ∈ refined →
                        q₁ ≠ q₂ →
                          Disjoint (Finset.Ico q₁.1 q₁.2)
                            (Finset.Ico q₂.1 q₂.2)) ∧
                (∀ q : ℕ × ℕ,
                  q ∈ refined →
                    a ≤ q.1 ∧ q.2 ≤ b - h) ∧
        ∀ q : ℕ × ℕ,
          q ∈ refined →
            ∀ n : ℕ,
              n ∈ Finset.Ico q.1 q.2 →
                Complex.realPhase_integerIncrement
                            (Complex.realPhase_integerLatticeShift ψ (center q))
                            n ∈
                          Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
        Complex.realPhase_exists_additivePrincipalRefinement
          ψ habh gaps Kpi hgap_bounded hgap_disjoint hinc_mono
      match hrefine_exists with
      | ⟨refined, center, hrefined_card, hrefined_cover_filter,
          hrefined_disjoint, hrefined_bounded, hrefined_principal⟩ =>
          have hrefined_cover :
              Complex.realPhase_IcoFamilyUnion refined =
                Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
                  t a b h eta := by
            exact Finset.ext
              (fun n =>
                Iff.intro
                  (fun hn =>
                    have hn_filter :
                        n ∈
                          (Complex.realPhase_IcoFamilyUnion gaps).filter
                            (fun m : ℕ =>
                              m ∈
                                Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                                  ψ a (b - h) Kpi) :=
                      Eq.subst
                        (motive := fun S : Finset ℕ => n ∈ S)
                        hrefined_cover_filter
                        hn
                    have hn_gap :
                        n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
                      (Finset.mem_filter.mp hn_filter).1
                    Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      hgap_cover
                      hn_gap)
                  (fun hn =>
                    have hn_gap :
                        n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
                      Eq.subst
                        (motive := fun S : Finset ℕ => n ∈ S)
                        hgap_cover.symm
                        hn
                    have hn_principal :
                        n ∈
                          Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                            ψ a (b - h) Kpi :=
                      hcomplement_subset_principal hn
                    have hn_filter :
                        n ∈
                          (Complex.realPhase_IcoFamilyUnion gaps).filter
                            (fun m : ℕ =>
                              m ∈
                                Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                                  ψ a (b - h) Kpi) :=
                      Finset.mem_filter.mpr (And.intro hn_gap hn_principal)
                    Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      hrefined_cover_filter.symm
                      hn_filter))
          have hcard_add :
              refined.card ≤ (Keta.card + 1) + Kpi.card :=
            le_trans hrefined_card (Nat.add_le_add_right hgap_card Kpi.card)
          have hcard_target :
              refined.card ≤ (Keta.card + Kpi.card) + 1 := by
            have hperm : (Keta.card + 1) + Kpi.card =
                (Keta.card + Kpi.card) + 1 :=
              Nat.add_right_comm Keta.card 1 Kpi.card
            exact
              Eq.subst
                (motive := fun m : ℕ => refined.card ≤ m)
                hperm
                hcard_add
          exact Exists.intro refined
            (Exists.intro center
              (And.intro hrefined_cover
                (And.intro hrefined_disjoint
                  (And.intro hrefined_bounded
                    (And.intro hrefined_principal hcard_target)))))

/-- The active-family complement is controlled by the additive number of
monotone resonance gaps and principal-strip crossings. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_additivePrincipalCount_mul_firstDerivativeMajorant
    (t : ℝ)
    {a b h : ℕ}
    {eta lo hi : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ hi)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h eta,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card +
          (Complex.realPhase_integerIncrementRangeActiveCenters
            lo hi Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
        (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) := by
  have hcover_exists :
      ∃ gaps : Finset (ℕ × ℕ),
        ∃ center : ℕ × ℕ → ℤ,
          Complex.realPhase_IcoFamilyUnion gaps =
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
                t a b h eta ∧
            (∀ p₁ : ℕ × ℕ,
              p₁ ∈ gaps →
                ∀ p₂ : ℕ × ℕ,
                  p₂ ∈ gaps →
                    p₁ ≠ p₂ →
                      Disjoint (Finset.Ico p₁.1 p₁.2)
                        (Finset.Ico p₂.1 p₂.2)) ∧
            (∀ p : ℕ × ℕ,
              p ∈ gaps →
                a ≤ p.1 ∧ p.2 ≤ b - h) ∧
            (∀ p : ℕ × ℕ,
              p ∈ gaps →
                ∀ n : ℕ,
                  n ∈ Finset.Ico p.1 p.2 →
                    Complex.realPhase_integerIncrement
                        (Complex.realPhase_integerLatticeShift
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                            h)
                          (center p))
                        n ∈
                      Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) ∧
            gaps.card ≤
              ((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                  t a b h eta).card +
                (Complex.realPhase_integerIncrementRangeActiveCenters
                  lo hi Real.pi).card) + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_exists_additivePrincipalGapCover
      t habh heta_pi hrange hinc_mono
  match hcover_exists with
  | ⟨gaps, center, hcover, hdisjoint, hbounded, hprincipal, hcard⟩ =>
      have hsum :
          ‖∑ n ∈
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h eta,
            Complex.exp
              (Complex.I *
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h n : ℂ))‖ ≤
          ((gaps.card : ℝ) *
            (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_firstDerivativeMajorant_of_principal_integerLatticeShift_gaps
          t gaps center ha heta_pos hcover hdisjoint hbounded hinc_mono
          hprincipal
      have hmajorant_nonneg :
          0 ≤ 4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
        have heta_inv_nonneg : 0 ≤ eta⁻¹ :=
          inv_nonneg.mpr (le_of_lt heta_pos)
        have hinner_nonneg : 0 ≤ eta⁻¹ + 1 :=
          add_nonneg heta_inv_nonneg zero_le_one
        have hleft_nonneg : 0 ≤ 4 * (eta⁻¹ + 1) :=
          mul_nonneg zero_le_four hinner_nonneg
        have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
          mul_nonneg zero_le_four Real.pi_nonneg
        have hright_nonneg : 0 ≤ 4 * Real.pi * eta⁻¹ :=
          mul_nonneg hfour_pi_nonneg heta_inv_nonneg
        exact add_nonneg hleft_nonneg hright_nonneg
      have hcard_real :
          (gaps.card : ℝ) ≤
            (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h eta).card +
              (Complex.realPhase_integerIncrementRangeActiveCenters
                lo hi Real.pi).card : ℕ) + 1 : ℕ) : ℝ) :=
        Nat.cast_le.mpr hcard
      have hmul :
          ((gaps.card : ℝ) *
            (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) ≤
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h eta).card +
              (Complex.realPhase_integerIncrementRangeActiveCenters
                lo hi Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
            (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
        mul_le_mul_of_nonneg_right hcard_real hmajorant_nonneg
      exact le_trans hsum hmul

/-- Closed shifted correlations inherit the standard additive all-integer
monotone-curvature resonance decomposition.

The complement is covered by the resonance-family gaps plus the principal
integer-strip crossings additively. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_additivePrincipalFirstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b h : ℕ}
    {eta W lo hi : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ hi)
    (hwindow :
      ∀ k : ℤ,
        k ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h eta →
          ((Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) eta).card : ℝ) ≤ W)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h eta).card : ℝ) * W) +
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h eta).card +
            (Complex.realPhase_integerIncrementRangeActiveCenters
              lo hi Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹))) +
        1 := by
  let ψ : ℝ → ℝ :=
    Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h
  let R : ℝ :=
    (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
      t a b h eta).card : ℝ) * W)
  let G : ℝ :=
    (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h eta).card +
        (Complex.realPhase_integerIncrementRangeActiveCenters
          lo hi Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
      (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹))
  have hunion :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion
          t a b h eta,
        Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤ R :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion_sum_norm_le_card_mul_window_bound
      t hwindow
  have hcomplement :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h eta,
        Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤ G :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_additivePrincipalCount_mul_firstDerivativeMajorant
      t ha habh heta_pos heta_pi hrange hinc_mono
  have hIco :
      ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤ R + G :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_of_activeResonanceFamily_bounds
      t eta hunion hcomplement (le_refl (R + G))
  have hclosed :
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
        ‖∑ n ∈ Finset.Ico a (b - h),
          Complex.exp (Complex.I * (ψ n : ℂ))‖ + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_Ico_sum_norm_add_one
      t habh
  have hwith_terminal :
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
        (R + G) + 1 :=
    le_trans hclosed (add_le_add_right hIco 1)
  exact hwith_terminal

end

end LFunctions
end Boundary
