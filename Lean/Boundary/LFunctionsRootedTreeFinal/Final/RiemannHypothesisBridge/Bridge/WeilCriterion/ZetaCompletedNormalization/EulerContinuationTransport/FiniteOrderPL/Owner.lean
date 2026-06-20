import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.BoundaryTransport.Owner

/-!
# Finite-order Phragmen-Lindelof transport

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.EulerContinuationTransport.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem real_isBigO_exp_eventually_le_pos_mul
    {f : ℝ → ℝ}
    (c : ℝ)
    (h : f =O[Filter.atTop] fun T : ℝ => Real.exp (c * T)) :
    ∃ D : ℝ,
      0 < D ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        f T ≤ D * Real.exp (c * T) := by
  match h.isBigOWith with
  | ⟨C, hC⟩ =>
        have hnonneg :
            ∀ᶠ T : ℝ in Filter.atTop,
              0 ≤ Real.exp (c * T) :=
          Filter.Eventually.of_forall
            (fun T => le_of_lt (Real.exp_pos (c * T)))
            exact
              ⟨|C| + 1, add_pos_of_nonneg_of_pos (abs_nonneg C) zero_lt_one,
                (hC.bound.and hnonneg).mono
                  (fun T hT =>
                    by
                      let G : ℝ := Real.exp (c * T)
                      let D : ℝ := |C| + 1
                      have hf_le_norm : f T ≤ ‖f T‖ :=
                        Real.le_norm_self (f T)
                      have hC_le_abs : C ≤ |C| :=
                        le_abs_self C
                      have hC_le_D : C ≤ D :=
                        le_trans hC_le_abs (le_add_of_nonneg_right zero_le_one)
                      have hG_norm_nonneg : 0 ≤ ‖G‖ :=
                        norm_nonneg G
                      have hmul_le : C * ‖G‖ ≤ D * ‖G‖ :=
                        mul_le_mul_of_nonneg_right hC_le_D hG_norm_nonneg
                      have hG_norm : ‖G‖ = G :=
                        Real.norm_of_nonneg hT.2
                      have hmul_eq : D * ‖G‖ = D * G :=
                        congrArg (fun x : ℝ => D * x) hG_norm
                      calc
                        f T ≤ ‖f T‖ :=
                          hf_le_norm
                        _ ≤ C * ‖G‖ :=
                          hT.1
                        _ ≤ D * ‖G‖ :=
                          hmul_le
                        _ = D * G :=
                          hmul_eq)⟩

/-- Standard shifted-polynomial/exponential comparison used in finite-order
envelope domination. -/
theorem finiteOrder_shiftedPower_isBigO_scaledPower
    (c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => (1 + T) ^ m) =O[Filter.atTop]
      fun T : ℝ => (c * T) ^ m := by
  let K : ℝ := (2 / c) ^ m
  have hK_nonneg : 0 ≤ K :=
    pow_nonneg (le_of_lt (div_pos two_pos hc)) m
  exact
    IsBigO.of_bound K
      (eventually_atTop.2
        ⟨1, fun T hT =>
            have hT_nonneg : 0 ≤ T :=
              le_trans zero_le_one hT
            have hcT_nonneg : 0 ≤ c * T :=
              mul_nonneg (le_of_lt hc) hT_nonneg
            have hleft_nonneg : 0 ≤ (1 + T) ^ m :=
              pow_nonneg (add_nonneg zero_le_one hT_nonneg) m
            have hnorm_left :
                ‖(1 + T) ^ m‖ = (1 + T) ^ m :=
              Real.norm_of_nonneg hleft_nonneg
            have hnorm_right_base :
                ‖(c * T) ^ m‖ = (c * T) ^ m :=
              Real.norm_of_nonneg (pow_nonneg hcT_nonneg m)
            have hshift_le_twoT : 1 + T ≤ 2 * T := by
              calc
                1 + T ≤ T + T :=
                  add_le_add_right hT T
                _ = 2 * T :=
                  (two_mul T).symm
            have htwoT_eq :
                2 * T = (2 / c) * (c * T) := by
              calc
                (2 / c) * (c * T) = ((2 / c) * c) * T :=
                  mul_assoc (2 / c) c T
                _ = 2 * T := by
                  exact congrArg (fun x : ℝ => x * T) (div_mul_cancel₀ 2 (ne_of_gt hc))
            have hbase_le :
                1 + T ≤ (2 / c) * (c * T) :=
              Eq.subst
                (motive := fun x : ℝ => 1 + T ≤ x)
                htwoT_eq
                hshift_le_twoT
            have hpow_le :
                (1 + T) ^ m ≤ ((2 / c) * (c * T)) ^ m :=
              pow_le_pow_left₀ (add_nonneg zero_le_one hT_nonneg) hbase_le m
            have hmul_pow :
                ((2 / c) * (c * T)) ^ m = K * (c * T) ^ m :=
              mul_pow (2 / c) (c * T) m
            have hraw :
                (1 + T) ^ m ≤ K * (c * T) ^ m :=
              Eq.subst
                (motive := fun x : ℝ => (1 + T) ^ m ≤ x)
                hmul_pow
                hpow_le
            have htarget :
                ‖(1 + T) ^ m‖ ≤ K * ‖(c * T) ^ m‖ :=
              Eq.subst
                (motive := fun x : ℝ => ‖(1 + T) ^ m‖ ≤ K * x)
                hnorm_right_base.symm
                (Eq.subst
                  (motive := fun x : ℝ => x ≤ K * (c * T) ^ m)
                  hnorm_left.symm
                  hraw)
            htarget
        ⟩)

/-- Positive linear changes of variable preserve the standard polynomial-versus-exponential
comparison at infinity. -/
theorem finiteOrder_scaledPower_isBigO_exp_scaled
    (c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => (c * T) ^ m) =O[Filter.atTop]
      fun T : ℝ => Real.exp (c * T) := by
  exact
    (Real.isLittleO_pow_exp_atTop (n := m)).isBigO.comp_tendsto
      (Filter.Tendsto.const_mul_atTop hc tendsto_id)

/-- Shifted polynomial height is `O(exp (cT))` for every positive `c`. -/
theorem finiteOrder_shiftedPower_isBigO_exp
    (c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => (1 + T) ^ m) =O[Filter.atTop]
      fun T : ℝ => Real.exp (c * T) := by
  exact
    (finiteOrder_shiftedPower_isBigO_scaledPower c m hc).trans
      (finiteOrder_scaledPower_isBigO_exp_scaled c m hc)

theorem finiteOrder_verticalExponent_isBigO_exp
    (A B c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => Real.log A + B * (1 + T) ^ m) =O[Filter.atTop]
      fun T : ℝ => Real.exp (c * T) := by
  have hconst :
      (fun _T : ℝ => Real.log A) =O[Filter.atTop]
        fun T : ℝ => Real.exp (c * T) := by
    have hone :
        (fun _T : ℝ => (1 : ℝ)) =O[Filter.atTop]
          fun T : ℝ => Real.exp (c * T) := by
      exact
        Real.isBigO_one_exp_comp.2
          ((Filter.Tendsto.const_mul_atTop hc tendsto_id))
    exact
      (isBigO_const_mul_self (Real.log A)
        (fun _T : ℝ => (1 : ℝ)) Filter.atTop).trans hone
  have hpoly :
      (fun T : ℝ => B * (1 + T) ^ m) =O[Filter.atTop]
        fun T : ℝ => Real.exp (c * T) := by
    exact
      (finiteOrder_shiftedPower_isBigO_exp c m hc).const_mul_left B
  exact IsBigO.add hconst hpoly

/-- Real exponent comparison behind finite-order versus double-exponential
domination.

This is the canonical real-analysis core: a polynomial in `1 + T`, after
adding the fixed logarithmic constant `log A`, is eventually bounded by a
positive multiple of `exp (cT)`.  It is the only growth-rate input needed for
the vertical finite-order envelope domination below. -/
theorem finiteOrder_verticalExponent_eventually_le_doubleExponentialExponent
    (A B c : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      0 < D ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        Real.log A + B * (1 + T) ^ m ≤ D * Real.exp (c * T) := by
  exact real_isBigO_exp_eventually_le_pos_mul c
    (finiteOrder_verticalExponent_isBigO_exp A B c m hc)

/-- Exponentiating the real finite-order/double-exponential comparison gives
eventual domination of the vertical envelopes. -/
theorem finiteOrder_verticalEnvelope_eventually_le_doubleExponential
    (A B c : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      0 < D ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        A * Real.exp (B * (1 + T) ^ m) ≤
          Real.exp (D * Real.exp (c * T)) := by
  match finiteOrder_verticalExponent_eventually_le_doubleExponentialExponent
      A B c m hA hB hc with
  | ⟨D, hD_pos, hcompare⟩ =>
      exact ⟨D, hD_pos, hcompare.mono
            (fun T hT =>
              by
                have hA_exp_log : A = Real.exp (Real.log A) :=
                  (Real.exp_log hA).symm
                have hleft_exp :
                    A * Real.exp (B * (1 + T) ^ m) =
                      Real.exp (Real.log A + B * (1 + T) ^ m) := by
                  calc
                    A * Real.exp (B * (1 + T) ^ m) =
                        Real.exp (Real.log A) * Real.exp (B * (1 + T) ^ m) := by
                      exact congrArg
                        (fun x : ℝ => x * Real.exp (B * (1 + T) ^ m))
                        hA_exp_log
                    _ = Real.exp (Real.log A + B * (1 + T) ^ m) :=
                      (Real.exp_add (Real.log A) (B * (1 + T) ^ m)).symm
                have hexp_le :
                    Real.exp (Real.log A + B * (1 + T) ^ m) ≤
                      Real.exp (D * Real.exp (c * T)) :=
                  Real.exp_le_exp.mpr hT
                Eq.subst
                  (motive := fun x : ℝ =>
                    x ≤ Real.exp (D * Real.exp (c * T)))
                  hleft_exp.symm
                  hexp_le)⟩

/-- Pure real eventual domination of finite-order vertical envelopes by a
double-exponential envelope.

This is the exact real-variable core behind the admissible-growth conversion:
for every `0 < c`, polynomial height in the exponent,
`B * (1 + T)^m`, is eventually dominated by `D * exp (c * T)`.
After exponentiating, the ordinary finite-order envelope is controlled by the
subcritical Phragmen-Lindelöf growth envelope. -/
theorem finiteOrder_verticalEnvelope_isBigO_doubleExponential
    (A B c : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      (fun T : ℝ => A * Real.exp (B * (1 + T) ^ m)) =O[Filter.atTop]
        fun T : ℝ => Real.exp (D * Real.exp (c * T)) := by
  match finiteOrder_verticalEnvelope_eventually_le_doubleExponential
      A B c m hA hB hc with
  | ⟨D, _hD_pos, hdom⟩ =>
      exact ⟨D,
            IsBigO.of_bound 1
              (hdom.mono
                (fun T hT =>
                  by
                    let R : ℝ := Real.exp (D * Real.exp (c * T))
                    have hR_nonneg : 0 ≤ R :=
                      le_of_lt (Real.exp_pos (D * Real.exp (c * T)))
                    have hR_norm : ‖R‖ = R :=
                      Real.norm_of_nonneg hR_nonneg
                    have hone_norm : 1 * ‖R‖ = R := by
                      calc
                        1 * ‖R‖ = ‖R‖ :=
                          one_mul ‖R‖
                        _ = R :=
                          hR_norm
                    Eq.subst
                      (motive := fun x : ℝ =>
                        ‖A * Real.exp (B * (1 + T) ^ m)‖ ≤ x)
                      hone_norm.symm
                      (le_trans
                        (le_of_eq
                          (Real.norm_of_nonneg
                            (mul_nonneg (le_of_lt hA)
                              (le_of_lt (Real.exp_pos (B * (1 + T) ^ m))))))
                        hT)))⟩
        
        /-- Bounded-strip height comparison in the exact form used by the
finite-order-to-admissible-envelope transport. -/
theorem strip_norm_height_le_vertical_height_envelope
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    1 + ‖z‖ ≤ (|a| + |b| + 2) * (1 + ‖z.im‖) :=
  strip_basicHeight_le_verticalHeight a b hza hzb

/-- On a closed bounded strip, the finite-order complex-height envelope is
`O` of the corresponding vertical-height envelope. -/
theorem finiteOrder_stripEnvelope_isBigO_verticalEnvelope
    (A B a b : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B) :
    (fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m)) =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
      fun z : ℂ =>
        A * Real.exp ((B * (|a| + |b| + 2) ^ m) * (1 + ‖z.im‖) ^ m) := by
  exact
    IsBigO.of_bound 1
      (eventually_inf_principal.mpr
        (Filter.Eventually.of_forall
          (fun z hz =>
            let E₁ : ℝ := A * Real.exp (B * (1 + ‖z‖) ^ m)
            let E₂ : ℝ :=
              A * Real.exp ((B * (|a| + |b| + 2) ^ m) * (1 + ‖z.im‖) ^ m)
            have hpoint : E₁ ≤ E₂ :=
              finiteOrder_norm_envelope_le_strip_vertical_envelope
                (le_of_lt hA)
                (le_of_lt hB)
                hz.1
                hz.2
            have hE₁_nonneg : 0 ≤ E₁ :=
              mul_nonneg (le_of_lt hA)
                (le_of_lt (Real.exp_pos (B * (1 + ‖z‖) ^ m)))
            have hE₂_nonneg : 0 ≤ E₂ :=
              le_trans hE₁_nonneg hpoint
            have hE₁_norm : ‖E₁‖ = E₁ :=
              Real.norm_of_nonneg hE₁_nonneg
            have hE₂_norm : ‖E₂‖ = E₂ :=
              Real.norm_of_nonneg hE₂_nonneg
            have hone_norm : 1 * ‖E₂‖ = E₂ := by
              calc
                1 * ‖E₂‖ = ‖E₂‖ :=
                  one_mul ‖E₂‖
                _ = E₂ :=
                  hE₂_norm
            Eq.subst
              (motive := fun x : ℝ => ‖E₁‖ ≤ x)
              hone_norm.symm
              (Eq.subst
                (motive := fun x : ℝ => x ≤ E₂)
                hE₁_norm.symm
                hpoint))))

/-- The real vertical double-exponential domination transports through
`z ↦ |im z|` to the closed-strip filter. -/
theorem finiteOrder_verticalEnvelope_comp_im_isBigO_doubleExponential_on_closedStrip
    (A B c a b : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      (fun z : ℂ => A * Real.exp (B * (1 + ‖z.im‖) ^ m)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  match finiteOrder_verticalEnvelope_eventually_le_doubleExponential
      A B c m hA hB hc with
  | ⟨D, _hD_pos, hdom⟩ =>
      have hcomap :
          ∀ᶠ z : ℂ in Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop,
            A * Real.exp (B * (1 + |z.im|) ^ m) ≤
              Real.exp (D * Real.exp (c * |z.im|)) :=
        hdom.comap (_root_.abs ∘ Complex.im)
      have hclosed :
          ∀ᶠ z : ℂ in
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b},
            A * Real.exp (B * (1 + |z.im|) ^ m) ≤
              Real.exp (D * Real.exp (c * |z.im|)) :=
        hcomap.filter_mono inf_le_left
      exact
        ⟨D,
          IsBigO.of_bound 1
            (hclosed.mono
              (fun z hz =>
                by
                  let E : ℝ := A * Real.exp (B * (1 + ‖z.im‖) ^ m)
                  let R : ℝ := Real.exp (D * Real.exp (c * |z.im|))
                  have him_norm_eq_abs : ‖z.im‖ = |z.im| :=
                    Real.norm_eq_abs z.im
                  have hraw : E ≤ R :=
                    Eq.subst
                      (motive := fun x : ℝ =>
                        A * Real.exp (B * (1 + x) ^ m) ≤ R)
                      him_norm_eq_abs.symm
                      hz
                  have hE_nonneg : 0 ≤ E :=
                    mul_nonneg (le_of_lt hA)
                      (le_of_lt (Real.exp_pos (B * (1 + ‖z.im‖) ^ m)))
                  have hR_nonneg : 0 ≤ R :=
                    le_of_lt (Real.exp_pos (D * Real.exp (c * |z.im|)))
                  have hE_norm : ‖E‖ = E :=
                    Real.norm_of_nonneg hE_nonneg
                  have hR_norm : ‖R‖ = R :=
                    Real.norm_of_nonneg hR_nonneg
                  have hone_norm : 1 * ‖R‖ = R := by
                    calc
                      1 * ‖R‖ = ‖R‖ :=
                        one_mul ‖R‖
                      _ = R :=
                        hR_norm
                  Eq.subst
                    (motive := fun x : ℝ => ‖E‖ ≤ x)
                    hone_norm.symm
                    (Eq.subst
                      (motive := fun x : ℝ => x ≤ R)
                      hE_norm.symm
                      hraw)))⟩

/-- Bounded-strip finite-order envelopes are admissible double-exponential
envelopes after reducing complex height to vertical height.

The proof first uses `finiteOrder_norm_envelope_le_strip_vertical_envelope` to
replace `1 + ‖z‖` by a fixed multiple of `1 + ‖im z‖` on the strip, then uses
the pure real eventual domination theorem for the vertical envelope. -/
theorem finiteOrder_stripEnvelope_isBigO_doubleExponential
    (A B c a b : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      (fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  let Bv : ℝ := B * (|a| + |b| + 2) ^ m
  have hK_pos : 0 < |a| + |b| + 2 := by
    have hsum_nonneg : 0 ≤ |a| + |b| :=
      add_nonneg (abs_nonneg a) (abs_nonneg b)
    have htwo_pos : (0 : ℝ) < 2 :=
      zero_lt_two
    have htwo_le : (2 : ℝ) ≤ |a| + |b| + 2 :=
      le_add_of_nonneg_left hsum_nonneg
    exact lt_of_lt_of_le htwo_pos htwo_le
  have hBv_pos : 0 < Bv :=
    mul_pos hB (pow_pos hK_pos m)
  have hstrip_to_vertical :
      (fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
        fun z : ℂ => A * Real.exp (Bv * (1 + ‖z.im‖) ^ m) :=
    finiteOrder_stripEnvelope_isBigO_verticalEnvelope
      A B a b m hA hB
  match finiteOrder_verticalEnvelope_comp_im_isBigO_doubleExponential_on_closedStrip
      A Bv c a b m hA hBv_pos hc with
  | ⟨D, hvertical_to_double⟩ =>
      exact ⟨D, hstrip_to_vertical.trans hvertical_to_double⟩

/-- Membership in the open vertical strip gives the corresponding closed-strip
inequalities needed by finite-order pointwise bounds. -/
theorem openStrip_mem_closedStrip_bounds
    {a b : ℝ}
    {z : ℂ}
    (hz : z ∈ Complex.re ⁻¹' Set.Ioo a b) :
    a ≤ z.re ∧ z.re ≤ b :=
  ⟨le_of_lt hz.1, le_of_lt hz.2⟩

/-- A pointwise finite-order bound on a strip gives the matching `IsBigO`
bound against the finite-order envelope on the same strip filter. -/
theorem finiteOrder_function_isBigO_stripEnvelope_of_pointwise_strip_bound
    (f : ℂ → ℂ)
    (A B a b : ℝ)
    (m : ℕ)
    (hbound :
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    f =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    IsBigO.of_bound 1
      (eventually_inf_principal.mpr
        (Filter.Eventually.of_forall
          (fun z hz =>
            let E : ℝ := A * Real.exp (B * (1 + ‖z‖) ^ m)
            have hstrip : a ≤ z.re ∧ z.re ≤ b :=
              openStrip_mem_closedStrip_bounds hz
            have hpoint : ‖f z‖ ≤ E :=
              hbound z hstrip.1 hstrip.2
            have hE_nonneg : 0 ≤ E :=
              le_trans (norm_nonneg (f z)) hpoint
            have hE_norm : ‖E‖ = E :=
              Real.norm_of_nonneg hE_nonneg
            have hone_norm : 1 * ‖E‖ = E := by
              calc
                1 * ‖E‖ = ‖E‖ :=
                  one_mul ‖E‖
                _ = E :=
                  hE_norm
            Eq.subst
              (motive := fun x : ℝ => ‖f z‖ ≤ x)
              hone_norm.symm
              hpoint)))

/-- An `IsBigO` statement on the closed-strip principal filter restricts to
the corresponding open-strip principal filter. -/
theorem isBigO_on_openStrip_of_isBigO_on_closedStrip
    {F G : ℂ → ℝ}
    {a b : ℝ}
    (h :
      F =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
        G) :
      F =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        G := by
  let L : Filter ℂ :=
    Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop
  have hopen_subset_closed :
      Complex.re ⁻¹' Set.Ioo a b ⊆ {z : ℂ | a ≤ z.re ∧ z.re ≤ b} :=
    fun _z hz => openStrip_mem_closedStrip_bounds hz
  have hprincipal :
      𝓟 (Complex.re ⁻¹' Set.Ioo a b) ≤
        𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b} :=
    principal_mono.2 hopen_subset_closed
  have hle_left :
      L ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo a b) ≤ L :=
    inf_le_left
  have hle_right :
      L ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo a b) ≤
        𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b} :=
    le_trans inf_le_right hprincipal
  have hle :
      L ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo a b) ≤
        L ⊓ 𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b} :=
    le_inf hle_left hle_right
  exact h.mono hle

/-- The closed-strip envelope domination can be used on the open-strip filter. -/
theorem finiteOrder_stripEnvelope_isBigO_doubleExponential_on_openStrip
    (A B c a b : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      (fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  match finiteOrder_stripEnvelope_isBigO_doubleExponential
      A B c a b m hA hB hc with
  | ⟨D, hclosed⟩ =>
      exact ⟨D, isBigO_on_openStrip_of_isBigO_on_closedStrip hclosed⟩

/-- The half-width Phragmen-Lindelöf growth parameter is strictly below the
strip threshold. -/
theorem real_pi_div_two_width_lt_pi_div_width
    {a b : ℝ}
    (hab : a < b) :
    Real.pi / (2 * (b - a)) < Real.pi / (b - a) := by
  let w : ℝ := b - a
  have hw_pos : 0 < w :=
    sub_pos.mpr hab
  have hw_lt_two_w : w < 2 * w := by
    calc
      w = 1 * w := (one_mul w).symm
      _ < 2 * w := mul_lt_mul_of_pos_right one_lt_two hw_pos
  exact
    div_lt_div₀'
      (le_refl Real.pi)
      hw_lt_two_w
      Real.pi_pos
      hw_pos

/-- Ordinary finite-order growth in a bounded vertical strip gives the
subcritical double-exponential admissible-growth hypothesis used by the
bounded-boundary Phragmen-Lindelöf theorem.

This is the generic envelope conversion: on a fixed-width strip, every
polynomial/exponential finite-order envelope
`A * exp (B * (1 + ‖z‖)^m)` is eventually dominated by
`exp (D * exp (c * |im z|))` for any positive `c`, so one chooses a small
`c < π / (b - a)`. -/
theorem strip_admissible_doubleExponential_growth_of_finiteOrder_growth
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hfinite :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ c : ℝ,
      c < Real.pi / (b - a) ∧
      ∃ D : ℝ,
        f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  match hfinite with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      let c : ℝ := Real.pi / (2 * (b - a))
      have hwidth_pos : 0 < b - a :=
        sub_pos.mpr hab
      have hc_pos : 0 < c := by
        exact div_pos Real.pi_pos (mul_pos two_pos hwidth_pos)
      have hc_lt : c < Real.pi / (b - a) :=
        real_pi_div_two_width_lt_pi_div_width hab
      match finiteOrder_stripEnvelope_isBigO_doubleExponential_on_openStrip
          A B c a b m hA hB hc_pos with
      | ⟨D, henv⟩ =>
          have hfunction :
              f =O[
                  Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                    𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
                fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m) :=
            finiteOrder_function_isBigO_stripEnvelope_of_pointwise_strip_bound
              f A B a b m hbound
          exact ⟨c, hc_lt, D, hfunction.trans henv⟩

/-- Global finite-order growth for the pole-cleared Riemann zeta factor.

This is the canonical standard zeta theorem behind the strip-local growth
input: `(s - 1)ζ(s)` is an entire function of finite order.  Analytically this
is proved from the meromorphic finite-order theory of `ζ`, using
Euler-Maclaurin/Abel estimates in the right half-plane, the functional equation
and Gamma/Stirling transport in the left half-plane, and local boundedness near
the removable pole. -/
theorem poleClearedRiemannZeta_rightHalfPlane_finiteOrder_growth_from_EulerMaclaurin :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match riemannZeta_farRightHalfPlane_dirichletSeries_bound with
  | ⟨A, hA, hzeta_bound⟩ =>
      exact
        ⟨A, 1, 1, hA, zero_lt_one,
          fun z hz_far =>
            have hz_ne_one : z ≠ 1 :=
              fun hz_eq =>
              have hz_re_one : z.re = 1 := by
                calc
                  z.re = (1 : ℂ).re := by
                    exact congrArg Complex.re hz_eq
                  _ = 1 := by
                    exact Complex.one_re
              have htwo_le_one : (2 : ℝ) ≤ 1 := by
                exact hz_far.trans_eq hz_re_one
              (not_le_of_gt one_lt_two) htwo_le_one
            have hpc :
                poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
              poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
            let H : ℝ := 1 + ‖z‖
            have hH_ge_one : (1 : ℝ) ≤ H :=
              le_add_of_nonneg_right (norm_nonneg z)
            have hH_nonneg : 0 ≤ H :=
              le_trans zero_le_one hH_ge_one
            have hzeta : ‖riemannZeta z‖ ≤ A :=
              hzeta_bound z hz_far
            have hsub_norm : ‖z - 1‖ ≤ H := by
              calc
                ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ :=
                  norm_sub_le z (1 : ℂ)
                _ = ‖z‖ + 1 := by
                  exact congrArg (fun x : ℝ => ‖z‖ + x) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
                _ = H := by
                  exact add_comm ‖z‖ 1
            have hproduct :
                ‖(z - 1) * riemannZeta z‖ ≤ H * A := by
              calc
                ‖(z - 1) * riemannZeta z‖ =
                    ‖z - 1‖ * ‖riemannZeta z‖ := by
                  exact norm_mul (z - 1) (riemannZeta z)
                _ ≤ H * A :=
                  mul_le_mul hsub_norm hzeta (norm_nonneg (riemannZeta z)) hH_nonneg
            have hH_le_expH : H ≤ Real.exp H :=
              le_trans (le_add_of_nonneg_right zero_le_one) (add_one_le_exp H)
            have hscaled :
                H * A ≤ A * Real.exp H := by
              calc
                H * A = A * H := by
                  exact mul_comm H A
                _ ≤ A * Real.exp H :=
                  mul_le_mul_of_nonneg_left hH_le_expH (le_of_lt hA)
            have hexponent :
                (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) = H := by
              calc
                (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) =
                    (1 + ‖z‖) ^ (1 : ℕ) := by
                  exact one_mul ((1 + ‖z‖) ^ (1 : ℕ))
                _ = 1 + ‖z‖ := by
                  exact pow_one (1 + ‖z‖)
                _ = H := rfl
            have hraw :
                ‖poleClearedRiemannZeta z‖ ≤ A * Real.exp H :=
              Eq.subst
                (motive := fun w : ℂ => ‖w‖ ≤ A * Real.exp H)
                hpc.symm
                (le_trans hproduct hscaled)
            Eq.subst
              (motive := fun x : ℝ => ‖poleClearedRiemannZeta z‖ ≤ A * Real.exp x)
              hexponent.symm
              hraw⟩

/-- Far-right finite-order growth for the raw pole-cleared zeta product.

This is the Dirichlet-series half-plane estimate on `2 ≤ Re s`, with the
elementary pole-clearing factor absorbed into the finite-order envelope. -/
theorem riemannZeta_poleCleared_rightHalfPlane_two_le_finiteOrder_growth_from_dirichletSeries :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        2 ≤ w.re →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  match poleClearedRiemannZeta_rightHalfPlane_finiteOrder_growth_from_EulerMaclaurin with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      exact
        ⟨A, B, m, hA, hB,
          fun w hw_two =>
            have hw_ne_one : w ≠ 1 :=
              fun hw_one =>
              have hw_re_one : w.re = 1 := by
                calc
                  w.re = (1 : ℂ).re := by
                    exact congrArg Complex.re hw_one
                  _ = 1 := by
                    exact Complex.one_re
              have htwo_le_one : (2 : ℝ) ≤ 1 :=
                hw_two.trans_eq hw_re_one
              (not_le_of_gt one_lt_two) htwo_le_one
            have hpole :
                poleClearedRiemannZeta w = (w - 1) * riemannZeta w :=
              poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
            Eq.subst
              (motive := fun u : ℂ =>
                ‖u‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
              hpole
              (hbound w hw_two)⟩

/-- Left boundary finite-order growth for the removable pole-cleared zeta on
`Re s = 1`, from the Abel/Euler-Maclaurin boundary estimate. -/
theorem poleClearedRiemannZeta_one_two_strip_leftBoundary_growth_from_EulerMaclaurin :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 1 →
        1 ≤ ‖z.im‖ →
        (∀ {x : ℝ},
          (⌊2 + ‖z.im‖⌋₊ : ℝ) ≤ x →
            ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum z.im ⌊x⌋₊‖ ≤
              8 * ((x / ‖z.im‖) + Real.sqrt (1 + ‖z.im‖)) * Real.log (2 + x)) →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match riemannZeta_poleCleared_boundaryLine_one_growth_bound_ownerPrimitive with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      exact
        ⟨A, B, m, hA, hB,
          fun z hz_re hz_im hpartial =>
            have hz_ne_one : z ≠ 1 :=
              fun hz_one =>
              have hz_im_zero : z.im = 0 := by
                calc
                  z.im = (1 : ℂ).im := by
                    exact congrArg Complex.im hz_one
                  _ = 0 := by
                    exact Complex.one_im
              have hz_im_norm_zero : ‖z.im‖ = 0 := by
                calc
                  ‖z.im‖ = ‖(0 : ℝ)‖ := by
                    exact congrArg norm hz_im_zero
                  _ = 0 := by
                    exact norm_zero
              have hone_le_zero : (1 : ℝ) ≤ 0 :=
                Eq.subst
                  (motive := fun x : ℝ => (1 : ℝ) ≤ x)
                  hz_im_norm_zero
                  hz_im
              not_lt_of_ge hone_le_zero zero_lt_one
            have hpole :
                poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
              poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
            Eq.subst
              (motive := fun w : ℂ =>
                ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
              hpole.symm
              (hbound z hz_re hz_im hpartial)⟩

/-- Right boundary finite-order growth for the removable pole-cleared zeta on
`Re s = 2`, from the Dirichlet-series estimate. -/
theorem poleClearedRiemannZeta_one_two_strip_rightBoundary_growth_from_dirichletSeries :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_growth_bound

/-- Holomorphicity of the removable pole-cleared zeta on the open strip
`1 < Re s < 2`, inherited from the larger right-critical strip. -/
theorem poleClearedRiemannZeta_one_two_strip_diffContOnCl :
    DiffContOnCl ℂ poleClearedRiemannZeta
      (Complex.re ⁻¹' Set.Ioo 1 2) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl.mono
    (fun _z hz => ⟨lt_trans zero_lt_one hz.1, hz.2⟩)

/-- Euler-Maclaurin cutoff used in the bounded strip `1 ≤ Re s ≤ 2`.

The choice is height-comparable and avoids the zero cutoff; it is the same
classical scale as the boundary-line Abel/Euler-Maclaurin truncation. -/

end
end LFunctions
end Boundary
