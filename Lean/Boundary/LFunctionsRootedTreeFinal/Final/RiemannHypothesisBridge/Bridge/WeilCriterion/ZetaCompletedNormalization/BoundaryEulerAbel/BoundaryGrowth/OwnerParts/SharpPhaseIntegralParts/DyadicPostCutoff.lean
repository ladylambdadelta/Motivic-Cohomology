import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.Part04_ClassicalPrefixAndSplitting
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseDyadicPrefixBudget

/-!
# Dyadic post-cutoff logarithmic-phase blocks

This owner transports the unconditional dyadic prefix estimate to a block
beginning at the canonical boundary cutoff.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology

/-- The natural canonical cutoff for boundary logarithmic-phase blocks. -/
noncomputable def boundaryGrowthCanonicalCutoff (t : ℝ) : ℕ :=
  ⌊2 + ‖t‖⌋₊

/-- The unweighted logarithmic-phase block beginning strictly after the
canonical cutoff. -/
noncomputable def boundaryGrowthPostCutoffPhaseBlock
    (t : ℝ) (K : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc (boundaryGrowthCanonicalCutoff t) K,
    ((n : ℂ) ^ (-(t : ℂ) * Complex.I))

/-- The unconditional dyadic budget at the right endpoint. -/
noncomputable def boundaryGrowthDyadicRightBudget
    (t : ℝ) (K : ℕ) : ℝ :=
  80 *
    (3 * (K : ℝ) / ‖t‖ +
      ((Nat.log2 K + 1 : ℕ) : ℝ) * Real.sqrt (1 + ‖t‖))

/-- The canonical prefix budget at the left endpoint. -/
noncomputable def boundaryGrowthDyadicLeftBudget (t : ℝ) : ℝ :=
  400 * Real.sqrt (1 + ‖t‖) *
    Real.log (2 + (boundaryGrowthCanonicalCutoff t : ℝ))

/-- The sum of the right dyadic endpoint budget and the canonical left-prefix
budget. -/
noncomputable def boundaryGrowthDyadicPostCutoffBudget
    (t : ℝ) (K : ℕ) : ℝ :=
  boundaryGrowthDyadicRightBudget t K +
    boundaryGrowthDyadicLeftBudget t

/-- Explicit right-endpoint estimate package. -/
structure BoundaryGrowthDyadicRightEndpointEstimate (t : ℝ) (K : ℕ) : Prop where
  bound :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K‖ ≤
      boundaryGrowthDyadicRightBudget t K

/-- Explicit left-endpoint estimate package. -/
structure BoundaryGrowthDyadicLeftEndpointEstimate (t : ℝ) : Prop where
  bound :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        (boundaryGrowthCanonicalCutoff t)‖ ≤
      boundaryGrowthDyadicLeftBudget t

/-- The explicit proposition package for the dyadic post-cutoff block
estimate. -/
structure BoundaryGrowthDyadicPostCutoffEstimate (t : ℝ) (K : ℕ) : Prop where
  bound :
    ‖boundaryGrowthPostCutoffPhaseBlock t K‖ ≤
      boundaryGrowthDyadicPostCutoffBudget t K

/-- Explicit positivity of the named canonical cutoff. -/
theorem boundaryGrowthCanonicalCutoffPos (t : ℝ) :
    0 < boundaryGrowthCanonicalCutoff t :=
  boundaryLineOnePointRealParam_cutoff_pos t

/-- Definitional expansion of the named right-endpoint budget. -/
theorem boundaryGrowthDyadicRightBudgetEqExpanded
    (t : ℝ) (K : ℕ) :
    boundaryGrowthDyadicRightBudget t K =
      80 *
        (3 * (K : ℝ) / ‖t‖ +
          ((Nat.log2 K + 1 : ℕ) : ℝ) * Real.sqrt (1 + ‖t‖)) :=
  rfl

/-- Definitional expansion of the named left-endpoint budget. -/
theorem boundaryGrowthDyadicLeftBudgetEqExpanded (t : ℝ) :
    boundaryGrowthDyadicLeftBudget t =
      400 * Real.sqrt (1 + ‖t‖) *
        Real.log (2 + (boundaryGrowthCanonicalCutoff t : ℝ)) :=
  rfl

/-- Definitional expansion of the combined endpoint budget. -/
theorem boundaryGrowthDyadicPostCutoffBudgetEqEndpoints
    (t : ℝ) (K : ℕ) :
    boundaryGrowthDyadicPostCutoffBudget t K =
      boundaryGrowthDyadicRightBudget t K +
        boundaryGrowthDyadicLeftBudget t :=
  rfl

/-- The post-cutoff block is exactly the right partial sum minus the canonical
left partial sum. -/
theorem boundaryGrowthPostCutoffPhaseBlockEqSub
    (t : ℝ)
    (K : ℕ)
    (hK : boundaryGrowthCanonicalCutoff t ≤ K) :
    boundaryGrowthPostCutoffPhaseBlock t K =
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K -
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          (boundaryGrowthCanonicalCutoff t) := by
  let C : ℕ := boundaryGrowthCanonicalCutoff t
  let T : ℂ := boundaryGrowthPostCutoffPhaseBlock t K
  have hsplit :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K =
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C + T :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq_prefix_add_Ioc_tail
      t hK
  have htail :
      T = boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K -
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C :=
    eq_sub_iff_add_eq.mpr
      (Eq.trans
        (add_comm T
          (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C))
        hsplit.symm)
  exact htail

/-- Norm transport of the exact post-cutoff subtraction identity. -/
theorem boundaryGrowthPostCutoffPhaseBlockNormLeEndpointNorms
    (t : ℝ)
    (K : ℕ)
    (hK : boundaryGrowthCanonicalCutoff t ≤ K) :
    ‖boundaryGrowthPostCutoffPhaseBlock t K‖ ≤
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K‖ +
        ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          (boundaryGrowthCanonicalCutoff t)‖ := by
  have htail :
      boundaryGrowthPostCutoffPhaseBlock t K =
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K -
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            (boundaryGrowthCanonicalCutoff t) :=
    boundaryGrowthPostCutoffPhaseBlockEqSub t K hK
  have hdifference :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K -
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            (boundaryGrowthCanonicalCutoff t)‖ ≤
        ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K‖ +
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            (boundaryGrowthCanonicalCutoff t)‖ :=
    norm_sub_le
      (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K)
      (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        (boundaryGrowthCanonicalCutoff t))
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤
        ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K‖ +
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            (boundaryGrowthCanonicalCutoff t)‖)
    htail.symm
    hdifference

/-- The right endpoint receives the unconditional dyadic-prefix budget. -/
theorem boundaryGrowthDyadicRightEndpointBound
    (t : ℝ)
    (ht : (1 : ℝ) ≤ ‖t‖)
    (K : ℕ)
    (hK : boundaryGrowthCanonicalCutoff t ≤ K) :
    BoundaryGrowthDyadicRightEndpointEstimate t K := by
  have hK_pos : 0 < K :=
    lt_of_lt_of_le (boundaryGrowthCanonicalCutoffPos t) hK
  have hraw :
      ‖Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K‖ ≤
        80 *
          (3 * (K : ℝ) / ‖t‖ +
            ((Nat.log2 K + 1 : ℕ) : ℝ) * Real.sqrt (1 + ‖t‖)) :=
    Complex.logarithmicPhase_dyadicPrefix_norm_le_budget t ht hK_pos
  have hindexBridge :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K =
        Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq_positiveIndex
      t ht K
  have hrawLocal :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K‖ ≤
        80 *
          (3 * (K : ℝ) / ‖t‖ +
            ((Nat.log2 K + 1 : ℕ) : ℝ) * Real.sqrt (1 + ‖t‖)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          80 *
            (3 * (K : ℝ) / ‖t‖ +
              ((Nat.log2 K + 1 : ℕ) : ℝ) * Real.sqrt (1 + ‖t‖)))
      hindexBridge.symm
      hraw
  have hbudget :
      boundaryGrowthDyadicRightBudget t K =
        80 *
          (3 * (K : ℝ) / ‖t‖ +
            ((Nat.log2 K + 1 : ℕ) : ℝ) * Real.sqrt (1 + ‖t‖)) :=
    boundaryGrowthDyadicRightBudgetEqExpanded t K
  have hbound :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K‖ ≤
        boundaryGrowthDyadicRightBudget t K :=
    Eq.subst
      (motive := fun value : ℝ =>
        ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K‖ ≤ value)
      hbudget.symm
      hrawLocal
  exact BoundaryGrowthDyadicRightEndpointEstimate.mk hbound

/-- The left endpoint receives the already-proved canonical-prefix budget. -/
theorem boundaryGrowthDyadicLeftEndpointBound
    (t : ℝ)
    (ht : (1 : ℝ) ≤ ‖t‖) :
    BoundaryGrowthDyadicLeftEndpointEstimate t := by
  have hraw :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          (boundaryGrowthCanonicalCutoff t)‖ ≤
        400 * Real.sqrt (1 + ‖t‖) *
          Real.log (2 + (boundaryGrowthCanonicalCutoff t : ℝ)) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_classicalPrefix_norm_le
      t ht
  have hbudget :
      boundaryGrowthDyadicLeftBudget t =
        400 * Real.sqrt (1 + ‖t‖) *
          Real.log (2 + (boundaryGrowthCanonicalCutoff t : ℝ)) :=
    boundaryGrowthDyadicLeftBudgetEqExpanded t
  have hbound :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          (boundaryGrowthCanonicalCutoff t)‖ ≤
        boundaryGrowthDyadicLeftBudget t :=
    Eq.subst
      (motive := fun value : ℝ =>
        ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            (boundaryGrowthCanonicalCutoff t)‖ ≤ value)
      hbudget.symm
      hraw
  exact BoundaryGrowthDyadicLeftEndpointEstimate.mk hbound

/-- A post-cutoff logarithmic-phase block inherits the two dyadic endpoint
budgets. -/
theorem boundaryGrowthDyadicPostCutoffBoundOfEndpoints
    (t : ℝ)
    (ht : (1 : ℝ) ≤ ‖t‖)
    (K : ℕ)
    (hK : boundaryGrowthCanonicalCutoff t ≤ K) :
    BoundaryGrowthDyadicPostCutoffEstimate t K := by
  have hright :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K‖ ≤
        boundaryGrowthDyadicRightBudget t K :=
    (boundaryGrowthDyadicRightEndpointBound t ht K hK).bound
  have hleft :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          (boundaryGrowthCanonicalCutoff t)‖ ≤
        boundaryGrowthDyadicLeftBudget t :=
    (boundaryGrowthDyadicLeftEndpointBound t ht).bound
  have hendpoints :
      ‖boundaryGrowthPostCutoffPhaseBlock t K‖ ≤
        ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t K‖ +
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            (boundaryGrowthCanonicalCutoff t)‖ :=
    boundaryGrowthPostCutoffPhaseBlockNormLeEndpointNorms t K hK
  have hbound :
      ‖boundaryGrowthPostCutoffPhaseBlock t K‖ ≤
        boundaryGrowthDyadicPostCutoffBudget t K :=
    Eq.subst
      (motive := fun value : ℝ =>
        ‖boundaryGrowthPostCutoffPhaseBlock t K‖ ≤ value)
      (boundaryGrowthDyadicPostCutoffBudgetEqEndpoints t K).symm
      (le_trans hendpoints (add_le_add hright hleft))
  exact BoundaryGrowthDyadicPostCutoffEstimate.mk hbound

end
end LFunctions
end Boundary
