import Jacobian.AbelJacobi.Telescoping
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# `Finset.sum` telescoping for `witnessAbelJacobi`

For a finite sequence of points `f 0, f 1, …, f n`, the witness
sum telescopes to `witness (f 0) (f n) v`.
-/

namespace JacobianChallenge.AbelJacobi

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AnalyticJacobian

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- `witnessAbelJacobi (f 0) (f n) v = ∑_{i ∈ range n} witness (f i) (f (i+1)) v`. -/
theorem witnessAbelJacobi_sum_range
    (f : ℕ → X) (n : ℕ) (v : E) :
    witnessAbelJacobi (E := E) (X := X) (f 0) (f n) v =
      ∑ i ∈ Finset.range n,
        witnessAbelJacobi (E := E) (X := X) (f i) (f (i + 1)) v := by
  induction n with
  | zero =>
      simp [witnessAbelJacobi_self]
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact (witnessAbelJacobi_chain_three (f 0) (f n) (f (n + 1)) v).symm

/--
Closed-loop telescoping: a closed sequence (f 0 = f n) gives a
zero sum.
-/
theorem witnessAbelJacobi_sum_range_loop
    (f : ℕ → X) (n : ℕ) (h : f n = f 0) (v : E) :
    ∑ i ∈ Finset.range n,
      witnessAbelJacobi (E := E) (X := X) (f i) (f (i + 1)) v = 0 := by
  rw [← witnessAbelJacobi_sum_range f n v, h, witnessAbelJacobi_self]

/-- A constant sequence makes every term zero. -/
theorem witnessAbelJacobi_sum_range_const
    (P : X) (n : ℕ) (v : E) :
    ∑ i ∈ Finset.range n,
      witnessAbelJacobi (E := E) (X := X) ((fun _ : ℕ => P) i)
        ((fun _ : ℕ => P) (i + 1)) v = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact witnessAbelJacobi_self P v

/-- Splitting a chain at an intermediate index. -/
theorem witnessAbelJacobi_sum_range_split
    (f : ℕ → X) (n m : ℕ) (v : E) :
    witnessAbelJacobi (E := E) (X := X) (f 0) (f n) v =
      witnessAbelJacobi (E := E) (X := X) (f 0) (f m) v +
      witnessAbelJacobi (E := E) (X := X) (f m) (f n) v := by
  rw [witnessAbelJacobi_chain_three]

end JacobianChallenge.AbelJacobi
