import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactivePacketBounds

/-!
# Natural reindexing of finite right-inactive frequencies

Let `q = -m` and `R = b + 1/3`.  Right inactivity gives
`q < ‖t‖/(2πR)`.  The maximal possible natural frequency is therefore
`ceil(‖t‖/(2πR)) - 1`.  Reversing the finite family from this endpoint makes
the derivative gap an affine shifted gap with step `2π`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteRightFrequencyThreshold
    (t : ℝ) (b : ℤ) : ℝ :=
  ‖t‖ /
    (2 * Real.pi * Complex.logarithmicPhaseQuantitativeSupportRight b)

def Complex.logarithmicPhaseFiniteRightFrequencyTop
    (t : ℝ) (b : ℤ) : ℕ :=
  ⌈Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b⌉₊ - 1

def Complex.logarithmicPhaseFiniteRightResidual
    (t : ℝ) (b : ℤ) : ℝ :=
  ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
    (2 * Real.pi) *
      (Complex.logarithmicPhaseFiniteRightFrequencyTop t b : ℝ)

def Complex.logarithmicPhaseFiniteRightModeNat
    {t : ℝ} {a b : ℤ}
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) : ℕ :=
  Int.toNat (-(m : ℤ))

def Complex.logarithmicPhaseFiniteRightReverseIndex
    {t : ℝ} {a b : ℤ}
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) : ℕ :=
  Complex.logarithmicPhaseFiniteRightFrequencyTop t b -
    Complex.logarithmicPhaseFiniteRightModeNat m

theorem Complex.logarithmicPhaseFiniteRightModeNat_cast
    {t : ℝ} {a b : ℤ}
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    ((Complex.logarithmicPhaseFiniteRightModeNat m : ℕ) : ℤ) = -(m : ℤ) := by
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t a b (m : ℤ)).mp m.property).2.1
  have hnegNonneg : (0 : ℤ) ≤ -(m : ℤ) := neg_nonneg.mpr (le_of_lt hmNeg)
  unfold Complex.logarithmicPhaseFiniteRightModeNat
  exact Int.toNat_of_nonneg hnegNonneg

theorem Complex.logarithmicPhaseFiniteRightModeNat_real_cast
    {t : ℝ} {a b : ℤ}
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    (Complex.logarithmicPhaseFiniteRightModeNat m : ℝ) = -((m : ℤ) : ℝ) := by
  have hint := Complex.logarithmicPhaseFiniteRightModeNat_cast m
  have hcast := congrArg (fun value : ℤ => (value : ℝ)) hint
  exact hcast.trans (Int.cast_neg (m : ℤ))

theorem Complex.logarithmicPhaseFiniteRightModeNat_pos
    {t : ℝ} {a b : ℤ}
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    0 < Complex.logarithmicPhaseFiniteRightModeNat m := by
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t a b (m : ℤ)).mp m.property).2.1
  have hnegPos : (0 : ℤ) < -(m : ℤ) := neg_pos.mpr hmNeg
  have hcast := Complex.logarithmicPhaseFiniteRightModeNat_cast m
  exact Int.ofNat_pos.mp
    (Eq.subst (motive := fun value : ℤ => 0 < value) hcast.symm hnegPos)

theorem Complex.logarithmicPhaseFiniteRightModeNat_lt_threshold
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    (Complex.logarithmicPhaseFiniteRightModeNat m : ℝ) <
      Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b := by
  have hgap :=
    Complex.logarithmicPhaseRightInactiveGap_ge_curvature_third
      t ht a b ha hab m.property
  have hdetPos :=
    Complex.logarithmicPhaseFiniteRightInactiveGap_pos t ht a b ha hab
  have hactualPos := lt_of_lt_of_le hdetPos hgap
  have hstrict :
      2 * Real.pi * (-((m : ℤ) : ℝ)) <
        ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b := by
    exact sub_pos.mp hactualPos
  have htwoPiPos := Complex.two_mul_pi_pos
  have hstrictOrdered :
      -((m : ℤ) : ℝ) * (2 * Real.pi) <
        ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b :=
    Eq.subst
      (motive := fun value : ℝ =>
        value < ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b)
      (mul_comm (2 * Real.pi) (-((m : ℤ) : ℝ))) hstrict
  have hdivide := (lt_div_iff₀ htwoPiPos).mpr hstrictOrdered
  unfold Complex.logarithmicPhaseFiniteRightFrequencyThreshold
  have hright :
      (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b) /
          (2 * Real.pi) =
        ‖t‖ /
          (2 * Real.pi * Complex.logarithmicPhaseQuantitativeSupportRight b) := by
    exact (div_div ‖t‖
      (Complex.logarithmicPhaseQuantitativeSupportRight b)
      (2 * Real.pi)).trans
      (congrArg (fun value : ℝ => ‖t‖ / value)
        (mul_comm
          (Complex.logarithmicPhaseQuantitativeSupportRight b)
          (2 * Real.pi)))
  exact Eq.subst
    (motive := fun value : ℝ => value <
      ‖t‖ /
        (2 * Real.pi * Complex.logarithmicPhaseQuantitativeSupportRight b))
    (Complex.logarithmicPhaseFiniteRightModeNat_real_cast m).symm
    (Eq.subst
      (motive := fun value : ℝ => -((m : ℤ) : ℝ) < value)
      hright hdivide)

theorem Complex.logarithmicPhaseFiniteRightModeNat_lt_ceil
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    Complex.logarithmicPhaseFiniteRightModeNat m <
      ⌈Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b⌉₊ := by
  exact Nat.lt_ceil.mpr
    (Complex.logarithmicPhaseFiniteRightModeNat_lt_threshold
      t ht a b ha hab m)

theorem Complex.logarithmicPhaseFiniteRightModeNat_le_top
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    Complex.logarithmicPhaseFiniteRightModeNat m ≤
      Complex.logarithmicPhaseFiniteRightFrequencyTop t b := by
  unfold Complex.logarithmicPhaseFiniteRightFrequencyTop
  exact Nat.le_sub_one_of_lt
    (Complex.logarithmicPhaseFiniteRightModeNat_lt_ceil
      t ht a b ha hab m)

theorem Complex.logarithmicPhaseFiniteRightReverseIndex_injective
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Function.Injective
      (Complex.logarithmicPhaseFiniteRightReverseIndex
        (t := t) (a := a) (b := b)) := by
  intro m n hindex
  have hmTop :=
    Complex.logarithmicPhaseFiniteRightModeNat_le_top
      t ht a b ha hab m
  have hnTop :=
    Complex.logarithmicPhaseFiniteRightModeNat_le_top
      t ht a b ha hab n
  unfold Complex.logarithmicPhaseFiniteRightReverseIndex at hindex
  have hmRecover := Nat.sub_add_cancel hmTop
  have hnRecover := Nat.sub_add_cancel hnTop
  have hnat :
      Complex.logarithmicPhaseFiniteRightModeNat m =
        Complex.logarithmicPhaseFiniteRightModeNat n := by
    have hsum :
        (Complex.logarithmicPhaseFiniteRightFrequencyTop t b -
            Complex.logarithmicPhaseFiniteRightModeNat m) +
          Complex.logarithmicPhaseFiniteRightModeNat m =
        (Complex.logarithmicPhaseFiniteRightFrequencyTop t b -
            Complex.logarithmicPhaseFiniteRightModeNat n) +
          Complex.logarithmicPhaseFiniteRightModeNat n :=
      hmRecover.trans hnRecover.symm
    have hsameLeft :
        (Complex.logarithmicPhaseFiniteRightFrequencyTop t b -
            Complex.logarithmicPhaseFiniteRightModeNat n) +
          Complex.logarithmicPhaseFiniteRightModeNat m =
        (Complex.logarithmicPhaseFiniteRightFrequencyTop t b -
            Complex.logarithmicPhaseFiniteRightModeNat n) +
          Complex.logarithmicPhaseFiniteRightModeNat n :=
      Eq.subst
        (motive := fun value : ℕ =>
          value + Complex.logarithmicPhaseFiniteRightModeNat m =
            (Complex.logarithmicPhaseFiniteRightFrequencyTop t b -
              Complex.logarithmicPhaseFiniteRightModeNat n) +
                Complex.logarithmicPhaseFiniteRightModeNat n)
        hindex hsum
    exact Nat.add_left_cancel hsameLeft
  have hmCast := Complex.logarithmicPhaseFiniteRightModeNat_cast m
  have hnCast := Complex.logarithmicPhaseFiniteRightModeNat_cast n
  have hmodeNeg : -(m : ℤ) = -(n : ℤ) :=
    hmCast.symm.trans
      ((congrArg (fun value : ℕ => (value : ℤ)) hnat).trans hnCast)
  exact Subtype.ext (neg_injective hmodeNeg)

theorem Complex.logarithmicPhaseFiniteRightResidual_add_step_index
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    Complex.logarithmicPhaseRightInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportRight b) =
      Complex.logarithmicPhaseFiniteRightResidual t b +
        (2 * Real.pi) *
          (Complex.logarithmicPhaseFiniteRightReverseIndex m : ℝ) := by
  have hmTop :=
    Complex.logarithmicPhaseFiniteRightModeNat_le_top
      t ht a b ha hab m
  have hcastSub :
      ((Complex.logarithmicPhaseFiniteRightFrequencyTop t b -
        Complex.logarithmicPhaseFiniteRightModeNat m : ℕ) : ℝ) =
      (Complex.logarithmicPhaseFiniteRightFrequencyTop t b : ℝ) -
        (Complex.logarithmicPhaseFiniteRightModeNat m : ℝ) :=
    Nat.cast_sub hmTop
  unfold Complex.logarithmicPhaseRightInactiveGap
  unfold Complex.logarithmicPhaseFiniteRightResidual
  unfold Complex.logarithmicPhaseFiniteRightReverseIndex
  have hmode := Complex.logarithmicPhaseFiniteRightModeNat_real_cast m
  calc
    ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
        2 * Real.pi * (-((m : ℤ) : ℝ)) =
      ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
        2 * Real.pi * (Complex.logarithmicPhaseFiniteRightModeNat m : ℝ) := by
      exact congrArg
        (fun value : ℝ =>
          ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
            2 * Real.pi * value)
        hmode.symm
    _ =
      (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
        2 * Real.pi *
          (Complex.logarithmicPhaseFiniteRightFrequencyTop t b : ℝ)) +
        2 * Real.pi *
          ((Complex.logarithmicPhaseFiniteRightFrequencyTop t b : ℝ) -
            (Complex.logarithmicPhaseFiniteRightModeNat m : ℝ)) := by
      exact Eq.trans
        (sub_add_sub_cancel _
          (2 * Real.pi * (Complex.logarithmicPhaseFiniteRightFrequencyTop t b : ℝ))
          (2 * Real.pi * (Complex.logarithmicPhaseFiniteRightModeNat m : ℝ))).symm
        (congrArg
          (fun value : ℝ =>
            (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
              2 * Real.pi *
                (Complex.logarithmicPhaseFiniteRightFrequencyTop t b : ℝ)) + value)
          (mul_sub (2 * Real.pi)
            (Complex.logarithmicPhaseFiniteRightFrequencyTop t b : ℝ)
            (Complex.logarithmicPhaseFiniteRightModeNat m : ℝ)).symm)
    _ =
      (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
        2 * Real.pi *
          (Complex.logarithmicPhaseFiniteRightFrequencyTop t b : ℝ)) +
        2 * Real.pi *
          (Complex.logarithmicPhaseFiniteRightFrequencyTop t b -
            Complex.logarithmicPhaseFiniteRightModeNat m : ℕ) := by
      exact congrArg
        (fun value : ℝ =>
          (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
            2 * Real.pi *
              (Complex.logarithmicPhaseFiniteRightFrequencyTop t b : ℝ)) +
            2 * Real.pi * value)
        hcastSub.symm

end

end LFunctions
end Boundary
