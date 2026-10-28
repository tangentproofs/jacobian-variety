# Analytic core: plan for the last three classical inputs

Remaining classical inputs (2026-10-28): C2 (period lattice discrete), C3 (Abel, two-point
form), C5 (analytic genus 0 ⇒ `ℂ̂`). All three need an existence theorem for the
`∂̄`-equation on a compact Riemann surface. The route chosen is the L² / Hodge route; it
uses only Mathlib's Hilbert-space projection, convolution and change-of-variables API.

## The central theorem (DECOMP)

Every smooth `(0,1)`-form `θ` on a compact connected Riemann surface is `∂̄u + ν̄`, with `u`
a smooth function and `ν` a holomorphic 1-form.

Proof:

* Project `θ` onto the closure `E` of `{∂̄u}` in the L² space of `(0,1)`-forms, which is
  intrinsic: it is built with a partition of unity.
* The residue `r = θ − e` is orthogonal to every `∂̄φ`. In each chart it is therefore weakly
  antiholomorphic, so by Weyl's lemma for `∂̄` it is `ν̄` with `ν` holomorphic.
* So `e = θ − ν̄` is smooth and an L² limit of `∂̄u_n`. Since `‖∂u‖ = ‖∂̄u‖` (Stokes),
  `∇u_n` is Cauchy in L² in every chart.
* By local Poincaré on chart squares, chained over a finite cover of the connected surface,
  `u_n` (normalized) converges in L² to `U` with `∂̄U = e` weakly.
* Locally, `U − T(e)` is weakly holomorphic, where `T` is the Cauchy transform with
  `∂̄T = id`. So `U` is smooth.

## Consequences

* **DBAR.** If `∫ θ ∧ ω = 0` for every holomorphic `ω`, then `θ = ∂̄u`.
  Proof: pair with `ω = ν`. `∫ ∂̄u ∧ ν = 0` by Stokes, so `∫ ν̄ ∧ ν = 0`, so `ν = 0`.
* **C5.** For genus 0, `f = χ/z − u` with `∂̄u = ∂̄(χ/z)` is meromorphic with a single
  simple pole. By the residue theorem (Cauchy–Pompeiu plus Stokes) it takes every value
  exactly once, so it is a bijection, hence a homeomorphism `X ≃ₜ ℂ̂`.
* **C3.** Suppose `∫_c ω` is a period for a chain `c` from `Q₁` to `Q₂`.
  * Set `f₀ = ∏ₖ fₖ`, where `fₖ = (z−b)/(z−a)` near the segment `[a,b]`, patched to `1`
    with a cutoff through `Log`.
  * `θ = −∂̄f₀/f₀` satisfies `∫ θ ∧ ω = π ∫_{c'} ω = 0`, using Cauchy–Pompeiu along each
    segment.
  * So `f = e^u f₀` is meromorphic with divisor `Q₂ − Q₁`, which gives degree 1, hence `ℂ̂`,
    hence genus 0.
* **C2.**
  * The lattice `Λ` is finitely generated: finitely many chart balls, and primitives differ
    by locally constant functions with finitely many values on compacts.
  * Every additive `ψ : Λ → ℝ` is realised by the periods of a closed real form `α`,
    patched from a partition of unity.
  * Apply DECOMP to `α^{0,1}`: `α = da + 2 Re ν` (the imaginary part is harmonic, hence
    constant), so `ψ = Re⟨c, ·⟩` is `ℝ`-linear.
  * A finitely generated subgroup spanning `ℝ^{2g}` on which every `ℤ`-homomorphism to `ℝ`
    is `ℝ`-linear has rank `2g`, so it is a lattice.

## Modules

1. `Analysis/PlaneCalculus` (done): Green's identity.
2. `Analysis/MeanValue`: radial mollifiers, the mean value property for holomorphic
   functions against radial kernels.
3. `Analysis/WeylDbar`: weakly holomorphic `L¹_loc` functions are a.e. holomorphic.
4. `Analysis/CauchyPompeiu`: `∫ ∂̄φ(w+ζ)/ζ = −π φ(w)`; the Cauchy transform.
5. `Analysis/Poincare`: Poincaré inequality on squares.
6. `Surface/*`: smooth functions and chart families, partition of unity, integration of
   `(1,1)`-families, Stokes, holomorphic forms from compatible chart coefficients.
7. `Surface/Hodge`: DECOMP.
8. Consequences: C5, C3, C2.
