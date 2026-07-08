import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongWeylTarget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseResonanceActiveCover

/-!
# Active-resonance long Weyl estimates

This file owns the active all-integer resonance decomposition estimates used by
the long Weyl target.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- A disjoint half-open gap cover whose every gap is assigned an integer
lattice shift gives the standard finite-gap complement estimate.  This is the
summation step for the monotone-curvature resonance decomposition after each
gap has been placed in its own principal branch. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_curvatureMajorant_of_integerLatticeShift_gaps
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam : ℝ}
    (gaps : Finset (ℕ × ℕ))
    (center : ℕ × ℕ → ℤ)
    (ha : 1 ≤ a)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hcover :
      Complex.realPhase_IcoFamilyUnion gaps =
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam)
    (hdisjoint :
      ∀ p₁ ∈ gaps,
        ∀ p₂ ∈ gaps,
          p₁ ≠ p₂ →
            Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2))
    (hgap_bounds :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          a ≤ p.1 ∧ p.2 ≤ b - h)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (havoid :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ∀ n : ℕ,
            n ∈ Finset.Ico p.1 p.2 →
              n ∉ Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (center p : ℝ)) lam)
    (hprincipal :
      ∀ p : ℕ × ℕ,
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
                Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((gaps.card : ℝ) *
        Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  let ψ : ℝ → ℝ :=
    Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h
  let F : ℕ → ℂ :=
    fun n : ℕ => Complex.exp (Complex.I * (ψ n : ℂ))
  have hgap :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ‖∑ n ∈ Finset.Ico p.1 p.2, F n‖ ≤
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
    intro p hp
    have hp_bounds : a ≤ p.1 ∧ p.2 ≤ b - h :=
      hgap_bounds p hp
    have hsub : Finset.Ico p.1 p.2 ⊆ Finset.Ico a (b - h) :=
      Finset.Ico_subset_Ico hp_bounds.1 hp_bounds.2
    exact
      Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_integerLatticeShift_gap
        (t := t) (ht := ht) (a := a) (b := b) (c := p.1) (d := p.2)
        (h := h) (lam := lam)
        (center p)
        (le_trans ha hp_bounds.1)
        hpos hlam hinc_mono hsub
        (havoid p hp)
        (hprincipal p hp)
  exact
    Complex.realPhase_sum_norm_le_card_mul_of_IcoFamily_cover
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam)
      gaps F hcover hdisjoint hgap

/-- Active-complement membership discharges the avoidance of the resonance
window for the integer lattice shift assigned to each gap.  The only remaining
geometric input is principal-branch control for that assigned shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_curvatureMajorant_of_principal_integerLatticeShift_gaps
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam : ℝ}
    (gaps : Finset (ℕ × ℕ))
    (center : ℕ × ℕ → ℤ)
    (ha : 1 ≤ a)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hcover :
      Complex.realPhase_IcoFamilyUnion gaps =
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam)
    (hdisjoint :
      ∀ p₁ ∈ gaps,
        ∀ p₂ ∈ gaps,
          p₁ ≠ p₂ →
            Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2))
    (hgap_bounds :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          a ≤ p.1 ∧ p.2 ≤ b - h)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hprincipal :
      ∀ p : ℕ × ℕ,
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
                Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((gaps.card : ℝ) *
        Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  have havoid :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ∀ n : ℕ,
            n ∈ Finset.Ico p.1 p.2 →
              n ∉ Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (center p : ℝ)) lam := by
    intro p hp n hn hn_window
    have hn_union :
        n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
      Finset.mem_biUnion.mpr
        (Exists.intro p (And.intro hp hn))
    have hn_complement :
        n ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
            t a b h lam :=
      Eq.subst
        (motive := fun S : Finset ℕ => n ∈ S)
        hcover
        hn_union
    have hsep :
        lam ≤
          ‖Complex.realPhase_integerIncrement
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h)
              n -
            (2 * Real.pi * (center p : ℝ))‖ :=
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_separated
        t hn_complement (center p)
    have hlt :
        ‖Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n -
          (2 * Real.pi * (center p : ℝ))‖ < lam :=
      (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
        (φ :=
          Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
        (a := a)
        (b := b - h)
        (n := n)
        (resonance := 2 * Real.pi * (center p : ℝ))
        (lam := lam)).mp hn_window |>.2
    exact not_lt_of_ge hsep hlt
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_curvatureMajorant_of_integerLatticeShift_gaps
      t ht gaps center ha hpos hlam hcover hdisjoint hgap_bounds
      hinc_mono havoid hprincipal

/-- A canonical active-complement gap cover, once each gap has been assigned
its principal lattice branch, gives the usual active-center-count complement
bound.  This is the counted summation form of the all-integer resonance
decomposition; the branch assignment is the only input not supplied by the
active-center cover itself. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_curvatureMajorant_of_principal_gap_cover
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hlam_pi : lam ≤ Real.pi)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hprincipal_cover :
      ∀ gaps : Finset (ℕ × ℕ),
        Complex.realPhase_IcoFamilyUnion gaps =
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h lam →
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) →
            Complex.realPhase_IcoFamilyBounded a (b - h) gaps →
              ∃ center : ℕ × ℕ → ℤ,
                ∀ p : ℕ × ℕ,
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
                          Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam).card + 1 : ℕ) : ℝ) *
        Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  have hcover_exists :
      ∃ gaps : Finset (ℕ × ℕ),
        Complex.realPhase_IcoFamilyUnion gaps =
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h lam ∧
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) ∧
          Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
          Complex.realPhase_IcoFamilyBounded a (b - h) gaps ∧
          gaps.card ≤
            (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h lam).card + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_exists_bounded_IcoFamily_cover_of_mono_of_le_pi
      t habh hinc_mono hlam_pi
  match hcover_exists with
  | ⟨gaps, hcover, hdisjoint, _hconnected, hbounded, hcard⟩ =>
      match hprincipal_cover gaps hcover hdisjoint hbounded with
      | ⟨center, hprincipal⟩ =>
          have hgap_bound :
              ‖∑ n ∈
                Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
                  t a b h lam,
                Complex.exp
                  (Complex.I *
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h n : ℂ))‖ ≤
                ((gaps.card : ℝ) *
                  Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_curvatureMajorant_of_principal_integerLatticeShift_gaps
              t ht gaps center ha hpos hlam hcover hdisjoint hbounded
              hinc_mono hprincipal
          have hmajorant_nonneg :
              0 ≤ Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h :=
            Real.secondDerivativeVdc_shiftedCorrelationMajorant_nonneg ht hpos
          have hcard_real :
              (gaps.card : ℝ) ≤
                (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                  t a b h lam).card + 1 : ℕ) : ℝ) :=
            Nat.cast_le.mpr hcard
          have hmul :
              ((gaps.card : ℝ) *
                  Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
                ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                  t a b h lam).card + 1 : ℕ) : ℝ) *
                  Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
            mul_le_mul_of_nonneg_right hcard_real hmajorant_nonneg
          exact le_trans hgap_bound hmul

/-- A disjoint half-open gap cover of the active-family complement gives the
standard finite-gap complement estimate.  The active-family complement supplies
the lattice separation on each gap; the supplied cover supplies only the
finite interval decomposition. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_curvatureMajorant
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam : ℝ}
    (gaps : Finset (ℕ × ℕ))
    (ha : 1 ≤ a)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hcover :
      Complex.realPhase_IcoFamilyUnion gaps =
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam)
    (hdisjoint :
      ∀ p₁ ∈ gaps,
        ∀ p₂ ∈ gaps,
          p₁ ≠ p₂ →
            Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2))
    (hgap_bounds :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          a ≤ p.1 ∧ p.2 ≤ b - h)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ) ≤
            ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((gaps.card : ℝ) *
        Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  let ψ : ℝ → ℝ :=
    Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h
  let F : ℕ → ℂ :=
    fun n : ℕ => Complex.exp (Complex.I * (ψ n : ℂ))
  have hgap :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ‖∑ n ∈ Finset.Ico p.1 p.2, F n‖ ≤
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
    intro p hp
    have hp_bounds : a ≤ p.1 ∧ p.2 ≤ b - h :=
      hgap_bounds p hp
    have hp_subset :
        Finset.Ico p.1 p.2 ⊆
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
            t a b h lam := by
      intro n hn
      have hn_union :
          n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
        Finset.mem_biUnion.mpr
          (Exists.intro p (And.intro hp hn))
      exact
        Eq.subst
          (motive := fun S : Finset ℕ => n ∈ S)
          hcover
          hn_union
    exact
      Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_activeComplement
        (t := t) (ht := ht) (a := a) (b := b) (c := p.1) (d := p.2)
        (h := h) (lam := lam)
        (le_trans ha hp_bounds.1) hp_bounds.1 hp_bounds.2 hpos hlam hp_subset
        hderiv_antitone hderiv_lower hinc_mono hred_mono
  exact
    Complex.realPhase_sum_norm_le_card_mul_of_IcoFamily_cover
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam)
      gaps F hcover hdisjoint hgap

/-- The active-family complement is bounded by the finite integer-center gap
count once monotonicity supplies the canonical bounded gap cover. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_curvatureMajorant
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hlam_pi : lam ≤ Real.pi)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ) ≤
            ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam).card + 1 : ℕ) : ℝ) *
        Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  have hcover_exists :
      ∃ gaps : Finset (ℕ × ℕ),
        Complex.realPhase_IcoFamilyUnion gaps =
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h lam ∧
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) ∧
          Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
          Complex.realPhase_IcoFamilyBounded a (b - h) gaps ∧
          gaps.card ≤
            (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h lam).card + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_exists_bounded_IcoFamily_cover_of_mono_of_le_pi
      t habh hinc_mono hlam_pi
  match hcover_exists with
  | ⟨gaps, hcover, hdisjoint, _hconnected, hbounded, hcard⟩ =>
      have hgap_bound :
          ‖∑ n ∈
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h lam,
            Complex.exp
              (Complex.I *
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h n : ℂ))‖ ≤
            ((gaps.card : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_curvatureMajorant
          t ht gaps ha hpos hlam hcover hdisjoint hbounded
          hderiv_antitone hderiv_lower hinc_mono hred_mono
      have hmajorant_nonneg :
          0 ≤ Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h :=
        Real.secondDerivativeVdc_shiftedCorrelationMajorant_nonneg ht hpos
      have hcard_real :
          (gaps.card : ℝ) ≤
            (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h lam).card + 1 : ℕ) : ℝ) :=
        Nat.cast_le.mpr hcard
      have hmul :
          ((gaps.card : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h lam).card + 1 : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
        mul_le_mul_of_nonneg_right hcard_real hmajorant_nonneg
      exact le_trans hgap_bound hmul

/-- All integer-centered active resonance windows together with their bounded
complement gaps control one shifted half-open correlation block. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_activeCenterCount_window_add_gapMajorants
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam W : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hlam_pi : lam ≤ Real.pi)
    (hwindow :
      ∀ k : ℤ,
        k ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h lam →
          ((Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) lam).card : ℝ) ≤ W)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ) ≤
            ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈ Finset.Ico a (b - h),
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam).card : ℝ) * W) +
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h lam).card + 1 : ℕ) : ℝ) *
          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  have hunion :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion
          t a b h lam,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h lam).card : ℝ) * W) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion_sum_norm_le_card_mul_window_bound
      t hwindow
  have hgap :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h lam).card + 1 : ℕ) : ℝ) *
          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_curvatureMajorant
      t ht ha habh hpos hlam hlam_pi hderiv_antitone hderiv_lower
      hinc_mono hred_mono
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_of_activeResonanceFamily_bounds
      t lam hunion hgap (le_of_eq rfl)

/-- Closed shifted correlations inherit the all-integer active-resonance
decomposition with the terminal endpoint contribution made explicit. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_gapMajorants_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam W : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hlam_pi : lam ≤ Real.pi)
    (hwindow :
      ∀ k : ℤ,
        k ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h lam →
          ((Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) lam).card : ℝ) ≤ W)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ) ≤
            ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam).card : ℝ) * W) +
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h lam).card + 1 : ℕ) : ℝ) *
          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
        1 := by
  have hclosed :
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
        ‖∑ n ∈ Finset.Ico a (b - h),
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_Ico_sum_norm_add_one
      t habh
  have hIco :
      ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h lam).card : ℝ) * W) +
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h lam).card + 1 : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_activeCenterCount_window_add_gapMajorants
      t ht ha habh hpos hlam hlam_pi hwindow
      hderiv_antitone hderiv_lower hinc_mono hred_mono
  exact le_trans hclosed (add_le_add_right hIco 1)

/-- The shifted-correlation envelope is controlled by the all-integer active
resonance decomposition on each Weyl shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_activeCenterCount_window_add_gapMajorants_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b H : ℕ}
    {lam W : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h ≤ Real.pi)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h)
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ x : ℝ,
            x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
              ‖t‖ *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ) ≤
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h) x‖)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (lam h)).card : ℝ) * W h) +
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card + 1 : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
          1) := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (lam h)).card : ℝ) * W h) +
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card + 1 : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
          1)
  exact Finset.sum_le_sum
    (fun h hh =>
      Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_gapMajorants_add_one
        t ht ha (habh h hh) (hpos h hh) (hlam h hh) (hlam_pi h hh)
        (hwindow h hh) (hderiv_antitone h hh) (hderiv_lower h hh)
        (hinc_mono h hh) (hred_mono h hh))

/-- A numerical cardinal budget for each active-center family converts the
active decomposition envelope into a counted majorant. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_counted_activeCenter_window_add_gapMajorants_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b H : ℕ}
    {lam W : ℕ → ℝ}
    (C : ℕ → ℕ)
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h ≤ Real.pi)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h)
    (hcard :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card ≤ C h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 ≤ W h)
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ x : ℝ,
            x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
              ‖t‖ *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ) ≤
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h) x‖)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((((C h : ℕ) : ℝ) * W h +
          (((C h + 1 : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
          1) := by
  have hraw :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b H ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card : ℝ) * W h) +
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1 : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
            1) :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_activeCenterCount_window_add_gapMajorants_add_one
      t ht ha habh hpos hlam hlam_pi hwindow
      hderiv_antitone hderiv_lower hinc_mono hred_mono
  have hsum :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card : ℝ) * W h) +
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1 : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
            1)) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ((((C h : ℕ) : ℝ) * W h +
            (((C h + 1 : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
            1) := by
    exact Finset.sum_le_sum
      (fun h hh =>
        have hcard_real :
            ((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card : ℝ) ≤ ((C h : ℕ) : ℝ) :=
          Nat.cast_le.mpr (hcard h hh)
        have hleft :
            (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card : ℝ) * W h) ≤
              ((C h : ℕ) : ℝ) * W h :=
          mul_le_mul_of_nonneg_right hcard_real (hW_nonneg h hh)
        have hcard_succ :
            (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1 ≤ C h + 1 :=
          Nat.succ_le_succ (hcard h hh)
        have hcard_succ_real :
            (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1 : ℕ) : ℝ) ≤
              ((C h + 1 : ℕ) : ℝ) :=
          Nat.cast_le.mpr hcard_succ
        have hgap_nonneg :
            0 ≤ Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h :=
          Real.secondDerivativeVdc_shiftedCorrelationMajorant_nonneg
            ht (hpos h hh)
        have hright :
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1 : ℕ) : ℝ) *
                Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
              (((C h + 1 : ℕ) : ℝ) *
                Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
          mul_le_mul_of_nonneg_right hcard_succ_real hgap_nonneg
        add_le_add_right (add_le_add hleft hright) 1)
  exact le_trans hraw hsum

/-- Explicit increment ranges supply the active-center count in the active
all-integer resonance envelope. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_rangeCounted_activeCenter_window_add_gapMajorants_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b H : ℕ}
    {lam W lo hi : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 ≤ W h)
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ x : ℝ,
            x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
              ‖t‖ *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ) ≤
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h) x‖)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.realPhase_integerIncrementRangeActiveCenters
            (lo h) (hi h) (lam h)).card : ℕ) : ℝ) * W h +
          ((((Complex.realPhase_integerIncrementRangeActiveCenters
              (lo h) (hi h) (lam h)).card + 1 : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
          1) := by
  let C : ℕ → ℕ :=
    fun h : ℕ =>
      (Complex.realPhase_integerIncrementRangeActiveCenters
        (lo h) (hi h) (lam h)).card
  have hcard :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card ≤ C h := by
    intro h hh
    exact
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters_card_le_rangeActiveCenters_card
        t (hrange h hh)
  exact
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_counted_activeCenter_window_add_gapMajorants_add_one
      t ht C ha habh hpos hlam hlam_pi hwindow hcard hW_nonneg
      hderiv_antitone hderiv_lower hinc_mono hred_mono

/-- Range-counted all-integer active resonance control supplies the positive
long Weyl target once the resulting explicit radicand is below the target
square. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_rangeCounted_activeCenter_window_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    {lam W lo hi : ℕ → ℝ}
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          lam h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ W h)
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ x : ℝ,
            x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
              ‖t‖ *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ) ≤
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h) x‖)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  (((((Complex.realPhase_integerIncrementRangeActiveCenters
                      (lo h) (hi h) (lam h)).card : ℕ) : ℝ) * W h +
                    ((((Complex.realPhase_integerIncrementRangeActiveCenters
                        (lo h) (hi h) (lam h)).card + 1 : ℕ) : ℝ) *
                      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
                    1))) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have henvelope :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
          (((((Complex.realPhase_integerIncrementRangeActiveCenters
              (lo h) (hi h) (lam h)).card : ℕ) : ℝ) * W h +
            ((((Complex.realPhase_integerIncrementRangeActiveCenters
                (lo h) (hi h) (lam h)).card + 1 : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
            1) :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_rangeCounted_activeCenter_window_add_gapMajorants_add_one
      t ht ha habh hpos hlam hlam_pi hrange hwindow hW_nonneg
      hderiv_antitone hderiv_lower hinc_mono hred_mono
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_shiftedCorrelationEnvelope_bound
      t ht hab hlong_sqrt henvelope hrad

end

end LFunctions
end Boundary
