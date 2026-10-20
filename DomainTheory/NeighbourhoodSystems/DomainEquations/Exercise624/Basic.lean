module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.gTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.fTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.pIter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.GammaD
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.GammaE
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Dsol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Esol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Fsol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Gsol
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.nil_mem_GammaD
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.nil_mem_GammaE

@[expose] public section

/-!
# Exercise 6.24 (Scott 1981, PRG-19, §6) — a **double fixed point** for a system of domain equations

> **EXERCISE 6.24.** Show that there must exist domains satisfying
> `D ≅ D + (D × E)` and `E ≅ D + E`,
> by using a double fixed-point method. First decide what the underlying set of tokens should be, and
> then define `D` and `E` by simultaneous fixed points. (Syntactical domains as in 6.23 may very well
> require several simultaneous equations.)

This is the **simultaneous** analogue of Exercise 6.20/6.21: there the conclusion was a single
`Γ` with `Γ = tok(T({Γ}))`, so that `{Γ} ◁ T({Γ})` and Theorem 6.14 applies; here we produce a
**pair** `(Γ_D, Γ_E)` of token sets that solve the two coupled token equations
**simultaneously**, so that the two singleton systems sit as subsystems of the two right-hand sides
at once — exactly the joint hypothesis the simultaneous form of Theorem 6.14 needs.

## Deciding the tokens

Both `D` and `E` are taken to be `∅`-free neighbourhood systems over the **single** token type
`Str = {0,1}*` (Scott's uniform category of Exercise 6.19). The two right-hand sides are built from
the uniform sum `+` (`ScottSys.sum`) and product `×` (`ScottSys.prod`), whose *master* (token set)
is in both cases the tagged union `{Λ} ∪ 0·(…) ∪ 1·(…)`. Writing `tok(𝒟) = 𝒟.master` and `{Γ}` for
the one-neighbourhood system `singletonSys Γ`, the two token recursions are

* `gTok p q = tok((D + E))      = {Λ} ∪ 0p ∪ 1q`  (for `D = {p}`, `E = {q}`),
* `fTok p q = tok((D + (D×E)))  = {Λ} ∪ 0p ∪ 1(gTok p q)`,

so `fTok p q = gTok p (gTok p q)` (the product `D × E` and the sum `D + E` have the *same* tagged
master shape).

## The double fixed point

The pair map `Φ(p, q) = (fTok p q, gTok p q)` is iterated from the bottom pair `({Λ}, {Λ})`
(`pIter`); its two component unions

`Γ_D = ⋃ₙ (Φⁿ).₁`,  `Γ_E = ⋃ₙ (Φⁿ).₂`

solve `fTok Γ_D Γ_E = Γ_D` and `gTok Γ_D Γ_E = Γ_E` (`fTok_GammaD_GammaE`, `gTok_GammaD_GammaE`).
Both `fTok`/`gTok` are *fully additive* (built from `insert`, `embBit`, `∪`), and — crucially — every
token of `fTok`/`gTok` references **at most one** of the two coordinates, so each membership is
witnessed at a *single* finite stage (no directedness merge is needed). This is the elementary
token-level continuity that makes the Kleene union a fixed point.

## The conclusion (`{Γ_D} ◁ D + (D×E)` and `{Γ_E} ◁ D + E`)

Setting `D = {Γ_D}`, `E = {Γ_E}`, the fixed-point equations say exactly that `Γ_D` (resp. `Γ_E`) is
the master of `D + (D×E)` (resp. `D + E`), so the singleton systems are subsystems of the two
right-hand sides — `Dsol_subsystem`, `Esol_subsystem`. These two facts *together* are the hypotheses
of the simultaneous Theorem 6.14, which then yields the required isomorphisms
`D ≅ D + (D×E)` and `E ≅ D + E`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624

/-! ## The two token recursions `gTok` and `fTok` -/



/-! ## Token-level continuity over a chain: a membership reaches a single finite stage -/

/-! ## The simultaneous Kleene iteration `Φⁿ({Λ}, {Λ})` -/






/-! ## The double fixed point -/

/-! ## The two solution systems and the simultaneous subsystem facts -/




end Exercise624
end DomainTheory.NeighbourhoodSystems
