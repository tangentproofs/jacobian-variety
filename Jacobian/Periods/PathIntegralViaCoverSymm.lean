import Jacobian.Periods.PathIntegralViaCover
import Jacobian.Periods.PathIntegralSegmentSymm
import Jacobian.Periods.PathPartitionCoverSymm
import Jacobian.Periods.PathPartitionCoverSigmaForm
import Jacobian.Periods.PathIntegralCongr

/-!
# Multi-chart path integral negates with the path

`pathIntegralViaCoverWith ω γ.symm ...` equals
`- pathIntegralViaCoverWith ω γ ...`, where the cover for γ.symm is
constructed by re-indexing γ's cover via `Fin.rev`.
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option maxHeartbeats 1000000 in
/-- The multi-chart path integral negates with the path. -/
theorem pathIntegralViaCoverWith_symm
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith ω γ.symm n hn (pickChart ∘ Fin.rev)
        (cover_symm_of_cover γ n hn pickChart hcov) =
      - pathIntegralViaCoverWith ω γ n hn pickChart hcov := by
  unfold pathIntegralViaCoverWith
  rw [← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv Fin.revPerm _ _ ?_
  intro i
  simp only [Fin.revPerm_apply]
  show pathIntegralViaChartCorrect (chartAt E (pickChart (Fin.rev i))) ω _ _ =
       - pathIntegralViaChartCorrect (chartAt E (pickChart (Fin.rev i))) ω _ _
  -- Apply per-segment symm
  rw [pathIntegralViaChartCorrect_symm_subpath_divFinIcc
        (chartAt E (pickChart (Fin.rev i))) ω γ n hn i.val i.isLt
        (range_subpath_sigma_subset_source γ n hn pickChart hcov i)]
  -- Now need to bridge σ-form path on RHS to the arith-form path with Fin.rev i
  congr 1
  -- Endpoints arithmetic
  have hi : i.val + 1 ≤ n := i.isLt
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : σ (divFinIcc n hn (i.val + 1) i.isLt) =
      divFinIcc n hn (Fin.rev i).val (le_of_lt (Fin.rev i).isLt) := by
    apply Subtype.ext
    simp only [coe_symm_eq, divFinIcc_val]
    rw [Fin.val_rev, Nat.cast_sub hi]
    push_cast
    field_simp
  have e2 : σ (divFinIcc n hn i.val (Nat.le_of_succ_le i.isLt)) =
      divFinIcc n hn ((Fin.rev i).val + 1) (Fin.rev i).isLt := by
    apply Subtype.ext
    simp only [coe_symm_eq, divFinIcc_val]
    rw [Fin.val_rev]
    have hnat : n - (i.val + 1) + 1 = n - i.val := by omega
    rw [hnat, Nat.cast_sub (Nat.le_of_succ_le hi)]
    field_simp
  refine pathIntegralViaChartCorrect_eq_of_heq
    (chartAt E (pickChart (Fin.rev i))) ω
    (congrArg γ e1) (congrArg γ e2) ?_ _ _
  -- HEq path equality
  rw [e1, e2]
  rfl

end JacobianChallenge.Periods
