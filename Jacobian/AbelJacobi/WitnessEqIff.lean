import Jacobian.AbelJacobi.WitnessZeroIff
import Jacobian.AbelJacobi.Composition
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Equality characterizations for `witnessAbelJacobi`

Equality of two witnesses (sharing either a base point or an
endpoint) is characterized by vanishing of a third witness, via
`witnessAbelJacobi_chain`. Includes both the iff form and the
`of`-style sufficient direction.
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
With a shared base point: `witness A P = witness A Q` iff `witness P Q = 0`.
Proof via `witnessAbelJacobi_chain` and `sub_eq_zero`.
-/
theorem witnessAbelJacobi_endpoint_eq_iff_chain_zero
    (A P Q : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) A P v =
        witnessAbelJacobi A Q v ↔
      witnessAbelJacobi (E := E) (X := X) P Q v = 0 := by
  rw [← witnessAbelJacobi_chain A P Q v, sub_eq_zero]
  exact eq_comm

/--
Sufficient direction: equal endpoint chain ⇒ equal witnesses
(shared base point).
-/
theorem witnessAbelJacobi_endpoint_eq_of_chain_zero
    (A P Q : X) (v : E)
    (h : witnessAbelJacobi (E := E) (X := X) P Q v = 0) :
    witnessAbelJacobi (E := E) (X := X) A P v =
      witnessAbelJacobi A Q v :=
  (witnessAbelJacobi_endpoint_eq_iff_chain_zero A P Q v).mpr h

/--
With a shared endpoint: `witness A R = witness B R` iff `witness A B = 0`.
Reduces via the chain identity
`witness A R - witness B R = witness A B`.
-/
theorem witnessAbelJacobi_basePoint_eq_iff_chain_zero
    (A B R : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) A R v =
        witnessAbelJacobi B R v ↔
      witnessAbelJacobi (E := E) (X := X) A B v = 0 := by
  have key :
      witnessAbelJacobi (E := E) (X := X) A R v -
          witnessAbelJacobi B R v =
        witnessAbelJacobi A B v := by
    unfold witnessAbelJacobi
    abel
  rw [← sub_eq_zero, key]

/--
Sufficient direction: equal base-point chain ⇒ equal witnesses
(shared endpoint).
-/
theorem witnessAbelJacobi_basePoint_eq_of_chain_zero
    (A B R : X) (v : E)
    (h : witnessAbelJacobi (E := E) (X := X) A B v = 0) :
    witnessAbelJacobi (E := E) (X := X) A R v =
      witnessAbelJacobi B R v :=
  (witnessAbelJacobi_basePoint_eq_iff_chain_zero A B R v).mpr h

end JacobianChallenge.AbelJacobi
