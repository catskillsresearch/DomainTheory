/-ai
This file gathers and re-exports the fixed computable projection pairs for the sum, product, and function space of the universal domain with itself, the three combinators built from those pairs, and the effective presentations of the three constructs.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.sumUUPresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.prodUUPresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.funSpaceUUPresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.iPlus
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.jPlus
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.iTimes
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.jTimes
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.iArrow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.jArrow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.sumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.prodComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.lamComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.arrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.U_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.sumUU_isEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.prodUU_isEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.funSpaceUU_isEffectivelyGiven

@[expose] public section

/-!
# Definition 8.9 (Scott 1981, PRG-19) — the combinators `a+b`, `a×b`, `a→b` on projections of `𝒰`

> **Definition 8.9.** Let the computable projection pairs `i₊ : 𝒰+𝒰 → 𝒰` and `j₊ : 𝒰 → 𝒰+𝒰` be
> fixed. Similarly choose `i_×, j_×` and `i_→, j_→` for `𝒰×𝒰` and `𝒰→𝒰`. Define, for all
> `a, b : 𝒰 → 𝒰`:
>
> `a + b = cond ∘ ⟨which, i₊∘in₀∘a∘out₀, i₊∘in₁∘b∘out₁⟩ ∘ j₊`;
> `a × b = i_× ∘ ⟨a∘proj₀, b∘proj₁⟩ ∘ j_×`;
> `a → b = i_→ ∘ (λf. b∘f∘a) ∘ j_→`.

## The six fixed maps

`𝒰+𝒰`, `𝒰×𝒰`, `𝒰→𝒰` are each effectively given (Theorem 7.4/7.5 applied twice to `U`'s own
presentation), so `theorem_8_8_b_strong` (`Theorem88n.lean`) hands each of them a *computable*
projection pair into `U`. Scott's "let ... be fixed" is exactly a choice out of that (non-unique)
existential — extracted here via `Exists.choose`, the same way every other "fixed but arbitrary
choice" in this development is handled (e.g. `U` itself, `Definition87.lean`). Since
`theorem_8_8_b_strong` already carries `U`'s own inherited `Classical.choice` footprint (see
`Theorem88n.lean`), this extraction adds no *marginal* taint.

## The three combinators

Built by direct transcription of Scott's formulas from existing combinators: `cond`/`whichMap`
(Exercise 3.26), `inMap₀/₁`/`outMap₀/₁` (Exercise 3.18/3.19), `paired`/`proj₀/₁` (Lecture III,
`Product.lean`), and `curry`/`evalMap`/`prodMap` (`FunctionSpace.lean`, Exercise 3.19) for the
`λf. b∘f∘a` clause: uncurried, `(f,x) ↦ b(f(a(x)))` is
`b ∘ eval ∘ (id ×ₘ a)`, so `λf. b∘f∘a = curry (b ∘ eval ∘ (id ×ₘ a))`.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

/-! ## `𝒰`-nonemptiness, and the three effectively-given constructs -/








/-! ## Definition 8.9 — the six fixed computable projection pairs -/







/-! ## Definition 8.9 — the three combinators -/




end DomainTheory.NeighbourhoodSystems
