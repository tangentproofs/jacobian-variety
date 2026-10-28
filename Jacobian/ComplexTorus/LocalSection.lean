import Jacobian.ComplexTorus.Defs
import Mathlib.Logic.Function.Basic
import Jacobian.ComplexTorus.IsolationAtZero
import Jacobian.ComplexTorus.MkInjOnSmallBall
import Jacobian.ComplexTorus.MkImage

/-!
# Local section of `mk` on a chart ball

The section is defined as `Function.invFunOn (mk V Λ) (Metric.ball v r)`
and inherits the standard `Function.invFunOn` API: it is a right
inverse of `mk` on the image, and its values lie in the source set
when the input is in the image.

This is the function that will become the `toFun` field of the
`OpenPartialHomeomorph` chart in the next packet.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V]

/--
A local section of `mk` on the small ball `Metric.ball v r`. By
definition it is the canonical `Function.invFunOn` and inherits all
the section/range properties from that API.
-/
noncomputable def localSection (Λ : FullComplexLattice V) (v : V) (r : ℝ) :
    quotient V Λ → V :=
  Function.invFunOn (mk V Λ) (Metric.ball v r)

/-- The local section is a right-inverse of `mk` on `mk '' Metric.ball v r`. -/
lemma mk_localSection (Λ : FullComplexLattice V) (v : V) (r : ℝ)
    {q : quotient V Λ} (hq : q ∈ mk V Λ '' Metric.ball v r) :
    mk V Λ (localSection Λ v r q) = q :=
  Function.invFunOn_eq hq

/-- The local section maps `mk '' Metric.ball v r` into `Metric.ball v r`. -/
lemma localSection_mem (Λ : FullComplexLattice V) (v : V) (r : ℝ)
    {q : quotient V Λ} (hq : q ∈ mk V Λ '' Metric.ball v r) :
    localSection Λ v r q ∈ Metric.ball v r :=
  Function.invFunOn_mem hq

end JacobianChallenge.ComplexTorus
