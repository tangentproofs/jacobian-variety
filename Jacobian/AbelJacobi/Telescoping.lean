import Jacobian.AbelJacobi.Coset
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Telescoping / 4-point chain identities for `witnessAbelJacobi`

Generalises `witnessAbelJacobi_chain_three` to longer chains and
exposes a few useful telescoping forms.
-/

namespace JacobianChallenge.AbelJacobi

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AnalyticJacobian

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- 4-point chain: `(P→Q) + (Q→R) + (R→S) = (P→S)`. -/
theorem witnessAbelJacobi_chain_four
    (P Q R S : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) P Q v +
      witnessAbelJacobi (E := E) (X := X) Q R v +
      witnessAbelJacobi (E := E) (X := X) R S v =
      witnessAbelJacobi (E := E) (X := X) P S v := by
  unfold witnessAbelJacobi
  abel

/-- Telescoping pair: `(P→Q) + (Q→P) = 0`. -/
theorem witnessAbelJacobi_telescope_pair
    (P Q : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) P Q v +
      witnessAbelJacobi (E := E) (X := X) Q P v = 0 :=
  witnessAbelJacobi_add_swap_eq_zero P Q v

/-- Closed-loop telescoping: `(P→Q) + (Q→R) + (R→P) = 0`. -/
theorem witnessAbelJacobi_telescope_loop
    (P Q R : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) P Q v +
      witnessAbelJacobi (E := E) (X := X) Q R v +
      witnessAbelJacobi (E := E) (X := X) R P v = 0 := by
  unfold witnessAbelJacobi
  abel

/--
Antisymmetric `_eq_iff` form: cosets coincide iff swapped witnesses
both vanish.
-/
theorem witnessAbelJacobi_eq_iff_swap_eq_zero
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 ↔
      witnessAbelJacobi (E := E) (X := X) P basePoint v = 0 :=
  witnessAbelJacobi_swap_eq_zero_iff basePoint P v

end JacobianChallenge.AbelJacobi
