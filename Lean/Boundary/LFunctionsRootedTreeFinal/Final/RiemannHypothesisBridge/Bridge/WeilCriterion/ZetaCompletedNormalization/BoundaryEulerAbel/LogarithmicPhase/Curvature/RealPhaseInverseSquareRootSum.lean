import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicPostCutoffTail

/-!
# Finite inverse-square-root sums

The global stationary family must be summed with its varying packet size,
rather than bounded by cardinality times a worst packet.  This owner proves
the elementary telescoping estimate
`sum_{1 ≤ k ≤ N} 1 / sqrt k ≤ 2 sqrt N`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.sqrt_nat_nonneg (n : ℕ) :
    0 ≤ Real.sqrt (n : ℝ) :=
  Real.sqrt_nonneg _

theorem Real.sqrt_nat_pos {n : ℕ} (hn : 0 < n) :
    0 < Real.sqrt (n : ℝ) :=
  Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)

theorem Real.sqrt_nat_sq (n : ℕ) :
    Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
  Real.sq_sqrt (Nat.cast_nonneg n)

theorem Real.sqrt_nat_succ_sub_mul_add
    (n : ℕ) :
    (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) *
        (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) = 1 := by
  have hdifference := mul_add
    (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
    (Real.sqrt ((n + 1 : ℕ) : ℝ)) (Real.sqrt (n : ℝ))
  have hsqIdentity :
      (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) *
          (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) =
        Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 -
          Real.sqrt (n : ℝ) ^ 2 := by
    exact Eq.trans hdifference
      (Eq.trans
        (congrArg₂ (fun left right : ℝ => left + right)
          (Eq.trans (sub_mul _ _ _)
            (Eq.trans
              (congrArg₂ (fun left right : ℝ => left - right)
                (pow_two _).symm rfl)
              rfl))
          (Eq.trans (sub_mul _ _ _)
            (Eq.trans
              (congrArg₂ (fun left right : ℝ => left - right)
                rfl (pow_two _).symm)
              rfl)))
        (add_sub_add_right_eq_sub _ _ _))
  have hsquares :
      Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 - Real.sqrt (n : ℝ) ^ 2 =
        ((n + 1 : ℕ) : ℝ) - (n : ℝ) :=
    congrArg₂ (fun left right : ℝ => left - right)
      (Real.sqrt_nat_sq (n + 1)) (Real.sqrt_nat_sq n)
  have hcast : (((n + 1 : ℕ) : ℝ)) - (n : ℝ) = 1 := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value - (n : ℝ))
        (Nat.cast_add_one n))
      (add_sub_cancel_left (n : ℝ) 1)
  exact Eq.trans hsqIdentity (Eq.trans hsquares hcast)

theorem Real.sqrt_nat_succ_add_pos (n : ℕ) :
    0 < Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ) :=
  add_pos_of_pos_of_nonneg
    (Real.sqrt_nat_pos (Nat.succ_pos n))
    (Real.sqrt_nat_nonneg n)

theorem Real.sqrt_nat_succ_sub_eq_inv_add
    (n : ℕ) :
    Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ) =
      (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))⁻¹ := by
  let D := Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)
  let A := Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)
  have hproduct : D * A = 1 :=
    Real.sqrt_nat_succ_sub_mul_add n
  have hAne : A ≠ 0 := ne_of_gt (Real.sqrt_nat_succ_add_pos n)
  have hcancel := congrArg (fun value : ℝ => value * A⁻¹) hproduct
  exact Eq.trans
    (Eq.trans
      (congrArg (fun value : ℝ => value * A⁻¹) hproduct.symm)
      (Eq.trans (mul_assoc D A A⁻¹)
        (Eq.trans
          (congrArg (fun value : ℝ => D * value) (mul_inv_cancel₀ hAne))
          (mul_one D))))
    (one_mul A⁻¹).symm

theorem Real.sqrt_nat_pred_le_sqrt_nat
    {n : ℕ} (hn : 0 < n) :
    Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
  exact Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.pred_le n))

theorem Real.sqrt_nat_add_pred_le_two_sqrt
    {n : ℕ} (hn : 0 < n) :
    Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ) ≤
      2 * Real.sqrt (n : ℝ) := by
  have hadd := add_le_add_left
    (Real.sqrt_nat_pred_le_sqrt_nat hn) (Real.sqrt (n : ℝ))
  exact le_trans hadd (le_of_eq (two_mul (Real.sqrt (n : ℝ))).symm)

theorem Real.inv_sqrt_nat_le_two_mul_sqrt_difference
    {n : ℕ} (hn : 0 < n) :
    (Real.sqrt (n : ℝ))⁻¹ ≤
      2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  have hnEq : n = k + 1 := hk
  have hpred : n - 1 = k := by
    exact Eq.trans (congrArg (fun value : ℕ => value - 1) hnEq)
      (Nat.add_sub_cancel k 1)
  have hsumPos := Real.sqrt_nat_succ_add_pos k
  have hsqrtPos := Real.sqrt_nat_pos hn
  have hsumLe :
      Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt (n : ℝ) :=
    Real.sqrt_nat_add_pred_le_two_sqrt hn
  have hinverseOrder := inv_le_inv₀ hsumPos hsqrtPos
  have hhalf :
      (2 * Real.sqrt (n : ℝ))⁻¹ ≤
        (Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ))⁻¹ :=
    (inv_le_inv₀ hsumPos
      (mul_pos (OfNat.zero_lt 2) hsqrtPos)).mpr hsumLe
  have htwoScaled := mul_le_mul_of_nonneg_left hhalf (OfNat.zero_le 2)
  have hleft : 2 * (2 * Real.sqrt (n : ℝ))⁻¹ =
      (Real.sqrt (n : ℝ))⁻¹ := by
    have htwoNe : (2 : ℝ) ≠ 0 := ne_of_gt (OfNat.zero_lt 2)
    have hsqrtNe := ne_of_gt hsqrtPos
    exact Eq.trans
      (congrArg (fun value : ℝ => 2 * value)
        (mul_inv₀ 2 (Real.sqrt (n : ℝ))))
      (Eq.trans
        (mul_assoc 2 2⁻¹ (Real.sqrt (n : ℝ))⁻¹)
        (Eq.trans
          (congrArg (fun value : ℝ => value *
            (Real.sqrt (n : ℝ))⁻¹) (mul_inv_cancel₀ htwoNe))
          (one_mul _)))
  have hright :
      (Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ))⁻¹ =
        Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ) := by
    exact Eq.trans
      (congrArg Inv.inv
        (congrArg₂ (fun left right : ℝ => left + right)
          (congrArg (fun value : ℕ => Real.sqrt (value : ℝ)) hnEq)
          (congrArg (fun value : ℕ => Real.sqrt (value : ℝ)) hpred)))
      (Real.sqrt_nat_succ_sub_eq_inv_add k).symm
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hleft.symm
    (Eq.subst
      (motive := fun value : ℝ => 2 * (2 * Real.sqrt (n : ℝ))⁻¹ ≤
        2 * value)
      hright.symm htwoScaled)

theorem Real.sum_Icc_inv_sqrt_le_two_sqrt
    (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹) ≤
      2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero =>
      have hempty : Finset.Icc 1 0 = (∅ : Finset ℕ) :=
        Finset.eq_empty_iff_forall_not_mem.mpr (fun n hn =>
          have hdata := Finset.mem_Icc.mp hn
          (not_le_of_gt Nat.zero_lt_one) (le_trans hdata.1 hdata.2))
      exact Eq.subst (motive := fun modes : Finset ℕ =>
        (∑ n ∈ modes, (Real.sqrt (n : ℝ))⁻¹) ≤
          2 * Real.sqrt (0 : ℝ)) hempty.symm
        (Eq.subst (motive := fun value : ℝ => 0 ≤ 2 * value)
          Real.sqrt_zero.symm (OfNat.zero_le 0))
  | succ N hN =>
      have hsplit : Finset.Icc 1 (N + 1) =
          Finset.Icc 1 N ∪ {N + 1} := by
        exact Finset.ext (fun n =>
          Iff.intro
            (fun hn =>
              have hdata := Finset.mem_Icc.mp hn
              match lt_or_eq_of_le hdata.2 with
              | Or.inl hlt => Finset.mem_union_left _
                  (Finset.mem_Icc.mpr (And.intro hdata.1
                    (Nat.lt_succ_iff.mp hlt)))
              | Or.inr heq => Finset.mem_union_right _
                  (Finset.mem_singleton.mpr heq))
            (fun hn =>
              match Finset.mem_union.mp hn with
              | Or.inl hleft =>
                  have hdata := Finset.mem_Icc.mp hleft
                  Finset.mem_Icc.mpr
                    (And.intro hdata.1 (Nat.le_trans hdata.2 (Nat.le_succ N)))
              | Or.inr hright =>
                  have heq := Finset.mem_singleton.mp hright
                  Eq.subst (motive := fun value : ℕ => value ∈ Finset.Icc 1 (N + 1))
                    heq.symm
                    (Finset.mem_Icc.mpr
                      (And.intro (Nat.succ_le_succ (Nat.zero_le N))
                        (Nat.le_refl _)))))
      have hdisjoint : Disjoint (Finset.Icc 1 N) ({N + 1} : Finset ℕ) :=
        Finset.disjoint_left.mpr (fun n hn hsingleton =>
          have hle := (Finset.mem_Icc.mp hn).2
          have heq := Finset.mem_singleton.mp hsingleton
          (not_lt_of_ge hle)
            (Eq.subst (motive := fun value : ℕ => N < value)
              heq.symm (Nat.lt_succ_self N)))
      have hsumUnion := Finset.sum_union hdisjoint
        (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
      have hpoint := Real.inv_sqrt_nat_le_two_mul_sqrt_difference
        (Nat.succ_pos N)
      have hcombined := add_le_add hN hpoint
      have htelescopes :
          2 * Real.sqrt (N : ℝ) +
              2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) =
            2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
        exact Eq.trans
          (add_sub_assoc
            (2 * Real.sqrt (N : ℝ))
            (2 * Real.sqrt ((N + 1 : ℕ) : ℝ))
            (2 * Real.sqrt (N : ℝ)))
          (Eq.trans
            (congrArg (fun value : ℝ => value - 2 * Real.sqrt (N : ℝ))
              (add_comm
                (2 * Real.sqrt (N : ℝ))
                (2 * Real.sqrt ((N + 1 : ℕ) : ℝ))))
            (add_sub_cancel_right _ _))
      exact Eq.subst (motive := fun modes : Finset ℕ =>
        (∑ n ∈ modes, (Real.sqrt (n : ℝ))⁻¹) ≤
          2 * Real.sqrt ((N + 1 : ℕ) : ℝ))
        hsplit.symm
        (Eq.subst (motive := fun value : ℝ => value ≤ _)
          (Eq.trans hsumUnion
            (congrArg
              (fun value : ℝ =>
                (∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹) + value)
              (Finset.sum_singleton (N + 1)
                (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹))))
          (le_trans hcombined (le_of_eq htelescopes)))

end

end LFunctions
end Boundary
