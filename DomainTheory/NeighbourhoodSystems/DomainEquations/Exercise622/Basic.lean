module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Cnat
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Cone
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.NExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.MExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.NStarExpr

@[expose] public section

/-!
# Exercise 6.22 (Scott 1981, PRG-19, §6) — commenting on three domain equations

> **EXERCISE 6.22.** Comment on these domain equations:
> `N ≅ {{0}, {0, Λ}} ⊕ N`,
> `M ≅ {{Λ}} + M`,
> `N* ≅ N ⊕ (N ⊗ N*)`.

This is a *"comment on"* exercise, so the substantive formal content is to recognise each equation as
an instance of the fixed-point machinery built in Exercises 6.19–6.21. Every right-hand side is a
construct `T(X)` of the algebra `GExpr` (constants, identity, `+`, `×`, `⊕`, `⊗`), whose constants are
**rooted** (contain `Λ`). Hence by `gExists_singleton_subsystem` (Exercise 6.21/6.20) there is a token
set `Γ` with `Γ = tok(T({Γ}))`, so `{Γ} ◁ T({Γ})` and **Theorem 6.14 applies**: each equation has a
solution.

## What the three domains *are* (the "comment")

* `N ≅ {{0},{0,Λ}} ⊕ N`. The constant `{{0},{0,Λ}}` is the **two-point domain** (a chain `{0} ⊏ Δ`,
  i.e. one proper point above the bottom). Folding it under the **coalesced** sum `⊕` — which
  *identifies* the bottoms at each stage — stacks the proper points into a single chain. So `N` is the
  domain of **vertical natural numbers**: a chain `⊥ ⊑ 0 ⊑ 1 ⊑ ⋯` topped by a limit `∞`.
* `M ≅ {{Λ}} + M`. The constant `{{Λ}}` is the **one-point domain** `𝟙` (the terminal object). Folding
  it under the **separated** sum `+` — which keeps the two bottoms *apart*, offering a genuine
  stop/continue choice at each step — yields the **lazy natural numbers**: each `n` is a distinct
  partial element `succⁿ(stop)`, with `⊥` below every finite stage and one infinite element. The only
  difference from `N` is coalesced vs. separated: `⊕` collapses the choice into a chain, `+` keeps it
  branching.
* `N* ≅ N ⊕ (N ⊗ N*)`. With the **smash** product `⊗` (strict pairing: a pair is `⊥` unless *both*
  coordinates are proper) and the coalesced `⊕`, this is the cons-cell equation `X ≅ N ⊕ (N ⊗ X)`: an
  element is either a single datum from `N` or a strict head/tail pair. So `N*` is the domain of
  **finite and infinite strict sequences (streams) over `N`**.

All three solutions are obtained uniformly below; the only per-equation work is exhibiting the
constant systems `{{0},{0,Λ}}`, `{{Λ}}` and checking they are `∅`-free and rooted. Everything is
**choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619

/-! ## The two constant domains -/



/-! ## The three domain equations as `GExpr` constructs -/




/-! ## Each equation has a solution (`Γ = tok(T({Γ}))`, so `{Γ} ◁ T({Γ})` and 6.14 applies) -/
end Exercise619
end DomainTheory.NeighbourhoodSystems
