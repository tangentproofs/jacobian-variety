import Jacobian.AbelJacobi.Defs
import Jacobian.AbelJacobi.Composition
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Combined sub/add witness identities

A few corollaries of `witnessAbelJacobi_chain` and the Defs-level
algebra, exposing useful three-point combinations involving
subtraction.
-/

namespace JacobianChallenge.AbelJacobi

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AnalyticJacobian

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/--
`(witness A B) + (witness B A) = 0` (sym pairing). Direct corollary
of the swap identity.
-/
theorem witnessAbelJacobi_add_swap_eq_zero
    (A B : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) A B v +
      witnessAbelJacobi B A v = 0 := by
  rw [witnessAbelJacobi_swap A B v]
  exact neg_add_cancel _

/-- `witness A C - witness A B = witness B C`. Direct from chain. -/
theorem witnessAbelJacobi_sub_chain
    (A B C : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) A C v -
      witnessAbelJacobi A B v =
      witnessAbelJacobi B C v :=
  witnessAbelJacobi_chain A B C v

/-- `witness A C - witness B C = witness A B`. -/
theorem witnessAbelJacobi_sub_chain_basePoint
    (A B C : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) A C v -
      witnessAbelJacobi B C v =
      witnessAbelJacobi A B v := by
  unfold witnessAbelJacobi
  abel

/--
`witness A B + witness B A + witness A B = witness A B`
(self-cancellation).
-/
theorem witnessAbelJacobi_swap_cancel
    (A B : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) A B v +
      witnessAbelJacobi B A v +
      witnessAbelJacobi A B v =
      witnessAbelJacobi A B v := by
  rw [witnessAbelJacobi_add_swap_eq_zero, zero_add]

end JacobianChallenge.AbelJacobi
