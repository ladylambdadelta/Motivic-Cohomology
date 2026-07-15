import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualStationaryPhase

/-!
# Dual stationary amplitude and finite variation

The leading size of a logarithmic stationary packet is its canonical radius.
On the positive dual coordinate this is

`R(u) = sqrt (‖t‖ / (2*pi*u))`.

It is nonnegative and antitone.  Consequently its discrete total variation on
an integer interval is exactly the endpoint drop.  This is the amplitude input
for Abel summation of the dual stationary oscillation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualStationaryAmplitude
    (t u : ℝ) : ℝ :=
  Real.sqrt (Complex.logarithmicPhaseDualStationaryCenter t u)

def Complex.logarithmicPhaseDualStationaryAmplitudeNat
    (t : ℝ) (k : ℕ) : ℝ :=
  Complex.logarithmicPhaseDualStationaryAmplitude t (k : ℝ)

def Complex.logarithmicPhaseDualOscillation
    (t u : ℝ) : ℂ :=
  Complex.exp
    (Complex.I *
      (Complex.logarithmicPhaseDualStationaryActionClosed t u : ℂ))

def Complex.logarithmicPhaseDualOscillationNat
    (t : ℝ) (k : ℕ) : ℂ :=
  Complex.logarithmicPhaseDualOscillation t (k : ℝ)

def Complex.logarithmicPhaseDualWeightedTerm
    (t : ℝ) (k : ℕ) : ℂ :=
  (Complex.logarithmicPhaseDualStationaryAmplitudeNat t k : ℂ) *
    Complex.logarithmicPhaseDualOscillationNat t k

theorem Complex.logarithmicPhaseDualStationaryAmplitude_nonneg
    (t u : ℝ) :
    0 ≤ Complex.logarithmicPhaseDualStationaryAmplitude t u := by
  unfold Complex.logarithmicPhaseDualStationaryAmplitude
  exact Real.sqrt_nonneg _

theorem Complex.logarithmicPhaseDualStationaryAmplitude_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) {u : ℝ} (hu : 0 < u) :
    0 < Complex.logarithmicPhaseDualStationaryAmplitude t u := by
  unfold Complex.logarithmicPhaseDualStationaryAmplitude
  exact Real.sqrt_pos.mpr
    (Complex.logarithmicPhaseDualStationaryCenter_pos t ht hu)

theorem Complex.logarithmicPhaseDualStationaryAmplitude_sq
    (t : ℝ) (ht : 1 ≤ ‖t‖) {u : ℝ} (hu : 0 < u) :
    Complex.logarithmicPhaseDualStationaryAmplitude t u *
        Complex.logarithmicPhaseDualStationaryAmplitude t u =
      Complex.logarithmicPhaseDualStationaryCenter t u := by
  unfold Complex.logarithmicPhaseDualStationaryAmplitude
  exact Real.mul_self_sqrt
    (le_of_lt
      (Complex.logarithmicPhaseDualStationaryCenter_pos t ht hu))

theorem Complex.logarithmicPhaseDualStationaryCenter_antitoneOn :
    AntitoneOn
      (Complex.logarithmicPhaseDualStationaryCenter t)
      (Set.Ioi 0) := by
  intro u hu v hv huv
  unfold Complex.logarithmicPhaseDualStationaryCenter
  have hnorm := norm_nonneg t
  have htwoPi := le_of_lt Complex.two_mul_pi_pos
  have hdenom := mul_le_mul_of_nonneg_left huv htwoPi
  have huDenom := Real.two_pi_mul_pos hu
  exact div_le_div_of_nonneg_left hnorm huDenom hdenom

theorem Complex.logarithmicPhaseDualStationaryCenter_strictAntiOn
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    StrictAntiOn
      (Complex.logarithmicPhaseDualStationaryCenter t)
      (Set.Ioi 0) := by
  intro u hu v hv huv
  unfold Complex.logarithmicPhaseDualStationaryCenter
  have hnorm : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have htwoPi : 0 < 2 * Real.pi := Complex.two_mul_pi_pos
  have hdenom : 2 * Real.pi * u < 2 * Real.pi * v :=
    mul_lt_mul_of_pos_left huv htwoPi
  exact div_lt_div_of_pos_left hnorm
    (Real.two_pi_mul_pos hu) hdenom

theorem Complex.logarithmicPhaseDualStationaryAmplitude_antitoneOn :
    AntitoneOn
      (Complex.logarithmicPhaseDualStationaryAmplitude t)
      (Set.Ioi 0) := by
  intro u hu v hv huv
  unfold Complex.logarithmicPhaseDualStationaryAmplitude
  exact Real.sqrt_le_sqrt
    (Complex.logarithmicPhaseDualStationaryCenter_antitoneOn hu hv huv)

theorem Complex.logarithmicPhaseDualStationaryAmplitude_strictAntiOn
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    StrictAntiOn
      (Complex.logarithmicPhaseDualStationaryAmplitude t)
      (Set.Ioi 0) := by
  intro u hu v hv huv
  unfold Complex.logarithmicPhaseDualStationaryAmplitude
  exact Real.sqrt_lt_sqrt
    (Complex.logarithmicPhaseDualStationaryCenter_strictAntiOn t ht hu hv huv)

theorem Complex.logarithmicPhaseDualStationaryAmplitudeNat_antitone
    (t : ℝ) {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) :
    Complex.logarithmicPhaseDualStationaryAmplitudeNat t k ≤
      Complex.logarithmicPhaseDualStationaryAmplitudeNat t j := by
  unfold Complex.logarithmicPhaseDualStationaryAmplitudeNat
  have hjReal : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj
  have hk : 0 < k := lt_of_lt_of_le hj hjk
  have hkReal : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hjkReal : (j : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjk
  exact Complex.logarithmicPhaseDualStationaryAmplitude_antitoneOn
    hjReal hkReal hjkReal

theorem Complex.logarithmicPhaseDualStationaryAmplitudeNat_succ_le
    (t : ℝ) {k : ℕ} (hk : 0 < k) :
    Complex.logarithmicPhaseDualStationaryAmplitudeNat t (k + 1) ≤
      Complex.logarithmicPhaseDualStationaryAmplitudeNat t k := by
  exact Complex.logarithmicPhaseDualStationaryAmplitudeNat_antitone
    t hk (Nat.le_add_right k 1)

theorem Complex.logarithmicPhaseDualStationaryAmplitudeNat_difference_nonneg
    (t : ℝ) {k : ℕ} (hk : 0 < k) :
    0 ≤ Complex.logarithmicPhaseDualStationaryAmplitudeNat t k -
      Complex.logarithmicPhaseDualStationaryAmplitudeNat t (k + 1) := by
  exact sub_nonneg.mpr
    (Complex.logarithmicPhaseDualStationaryAmplitudeNat_succ_le t hk)

theorem Complex.logarithmicPhaseDualOscillation_norm
    (t u : ℝ) :
    ‖Complex.logarithmicPhaseDualOscillation t u‖ = 1 := by
  unfold Complex.logarithmicPhaseDualOscillation
  exact Complex.norm_exp_ofReal_mul_I
    (Complex.logarithmicPhaseDualStationaryActionClosed t u)

theorem Complex.logarithmicPhaseDualOscillationNat_norm
    (t : ℝ) (k : ℕ) :
    ‖Complex.logarithmicPhaseDualOscillationNat t k‖ = 1 := by
  unfold Complex.logarithmicPhaseDualOscillationNat
  exact Complex.logarithmicPhaseDualOscillation_norm t (k : ℝ)

theorem Complex.logarithmicPhaseDualWeightedTerm_norm
    (t : ℝ) (k : ℕ) :
    ‖Complex.logarithmicPhaseDualWeightedTerm t k‖ =
      Complex.logarithmicPhaseDualStationaryAmplitudeNat t k := by
  unfold Complex.logarithmicPhaseDualWeightedTerm
  have hampNonneg :=
    Complex.logarithmicPhaseDualStationaryAmplitude_nonneg t (k : ℝ)
  have hampNorm :
      ‖(Complex.logarithmicPhaseDualStationaryAmplitudeNat t k : ℂ)‖ =
        Complex.logarithmicPhaseDualStationaryAmplitudeNat t k := by
    exact Complex.norm_real_of_nonneg hampNonneg
  exact Eq.trans
    (norm_mul
      (Complex.logarithmicPhaseDualStationaryAmplitudeNat t k : ℂ)
      (Complex.logarithmicPhaseDualOscillationNat t k))
    (Eq.trans
      (congrArg₂ (fun x y : ℝ => x * y) hampNorm
        (Complex.logarithmicPhaseDualOscillationNat_norm t k))
      (mul_one _))

theorem Finset.sum_range_forwardDifference
    {G : Type*} [AddCommGroup G]
    (w : ℕ → G) (n : ℕ) :
    (∑ j ∈ Finset.range n, (w j - w (j + 1))) = w 0 - w n := by
  induction n with
  | zero =>
      have hempty : Finset.range 0 = ∅ := Finset.range_zero
      have hsum : (∑ j ∈ Finset.range 0, (w j - w (j + 1))) = 0 := by
        exact Eq.trans
          (congrArg (fun s : Finset ℕ => ∑ j ∈ s, (w j - w (j + 1)))
            hempty)
          (Finset.sum_empty)
      exact Eq.trans hsum (sub_self (w 0)).symm
  | succ n ih =>
      have hsum := Finset.sum_range_succ
        (fun j : ℕ => w j - w (j + 1)) n
      have hstep :
          (w 0 - w n) + (w n - w (n + 1)) =
            w 0 - w (n + 1) := by
        exact sub_add_sub_cancel (w 0) (w n) (w (n + 1))
      exact Eq.trans hsum
        (Eq.trans (congrArg
          (fun z : G => z + (w n - w (n + 1))) ih) hstep)

theorem Finset.sum_Ico_shifted_forwardDifference
    {G : Type*} [AddCommGroup G]
    (w : ℕ → G) (K N : ℕ) :
    (∑ j ∈ Finset.Ico K (K + N), (w j - w (j + 1))) =
      w K - w (K + N) := by
  have hmap :
      Finset.Ico K (K + N) =
        (Finset.range N).map
          ⟨fun j : ℕ => K + j,
            fun x y hxy => Nat.add_left_cancel hxy⟩ := by
    exact Finset.Ico_eq_map_range
  have hsumMap :
      (∑ j ∈ (Finset.range N).map
          ⟨fun j : ℕ => K + j,
            fun x y hxy => Nat.add_left_cancel hxy⟩,
          (w j - w (j + 1))) =
        ∑ j ∈ Finset.range N,
          (w (K + j) - w (K + (j + 1))) := by
    exact Finset.sum_map _ _
  have htel := Finset.sum_range_forwardDifference
    (fun j : ℕ => w (K + j)) N
  have hzero : K + 0 = K := Nat.add_zero K
  exact Eq.trans
    (congrArg
      (fun s : Finset ℕ => ∑ j ∈ s, (w j - w (j + 1))) hmap)
    (Eq.trans hsumMap
      (Eq.trans htel
        (congrArg₂ (fun x y : G => x - y)
          (congrArg w hzero) rfl)))

theorem Complex.logarithmicPhaseDualStationaryAmplitudeNat_totalVariation_eq_drop
    (t : ℝ) (K N : ℕ) :
    (∑ j ∈ Finset.Ico K (K + N),
      (Complex.logarithmicPhaseDualStationaryAmplitudeNat t j -
        Complex.logarithmicPhaseDualStationaryAmplitudeNat t (j + 1))) =
      Complex.logarithmicPhaseDualStationaryAmplitudeNat t K -
        Complex.logarithmicPhaseDualStationaryAmplitudeNat t (K + N) := by
  exact Finset.sum_Ico_shifted_forwardDifference
    (Complex.logarithmicPhaseDualStationaryAmplitudeNat t) K N

theorem Complex.logarithmicPhaseDualStationaryAmplitudeNat_totalVariation_le_initial
    (t : ℝ) (K N : ℕ) :
    (∑ j ∈ Finset.Ico K (K + N),
      (Complex.logarithmicPhaseDualStationaryAmplitudeNat t j -
        Complex.logarithmicPhaseDualStationaryAmplitudeNat t (j + 1))) ≤
      Complex.logarithmicPhaseDualStationaryAmplitudeNat t K := by
  have hfinal :=
    Complex.logarithmicPhaseDualStationaryAmplitude_nonneg t ((K + N : ℕ) : ℝ)
  have hdrop := sub_le_self
    (Complex.logarithmicPhaseDualStationaryAmplitudeNat t K) hfinal
  exact Eq.subst (motive := fun z : ℝ => z ≤ _)
    (Complex.logarithmicPhaseDualStationaryAmplitudeNat_totalVariation_eq_drop
      t K N).symm hdrop

theorem Complex.logarithmicPhaseDualStationaryAmplitude_modeIndex_eq_radius
    (t : ℝ) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseDualStationaryAmplitudeNat t
        (Complex.logarithmicPhaseNegativeModeIndex m) =
      Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  unfold Complex.logarithmicPhaseDualStationaryAmplitudeNat
  unfold Complex.logarithmicPhaseDualStationaryAmplitude
  unfold Complex.logarithmicPhasePoissonCanonicalRadius
  exact congrArg Real.sqrt
    (Complex.logarithmicPhaseDualStationaryCenter_modeIndex_eq t hm)

end

end LFunctions
end Boundary
