/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise619PartB

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

namespace DomainTheory.Neighborhood

open NeighborhoodSystem DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB

namespace Exercise624

/-! ## The two token recursions `gTok` and `fTok` -/

/-- `gTok p q = tok((D + E))` for `D = {p}`, `E = {q}`: the tagged union `{Λ} ∪ 0p ∪ 1q`. It is also
the master of the product `{p} × {q}` (sum and product share the master shape over `{0,1}*`). -/
def gTok (p q : Set Str) : Set Str := insert ([] : Str) (embBit false p ∪ embBit true q)

/-- `fTok p q = tok((D + (D×E)))` for `D = {p}`, `E = {q}`: `{Λ} ∪ 0p ∪ 1(gTok p q)`, equivalently
`gTok p (gTok p q)`. -/
def fTok (p q : Set Str) : Set Str := gTok p (gTok p q)

/-! ## Token-level continuity over a chain: a membership reaches a single finite stage -/

/-! ## The simultaneous Kleene iteration `Φⁿ({Λ}, {Λ})` -/

/-- The pair iteration `Φ(p, q) = (fTok p q, gTok p q)` from the bottom pair `({Λ}, {Λ})`. -/
def pIter : ℕ → Set Str × Set Str
  | 0 => ({([] : Str)}, {([] : Str)})
  | n + 1 => (fTok (pIter n).1 (pIter n).2, gTok (pIter n).1 (pIter n).2)

/-- The first component of the double fixed point, `Γ_D = ⋃ₙ (Φⁿ).₁`. -/
def GammaD : Set Str := ⋃ n, (pIter n).1

/-- The second component of the double fixed point, `Γ_E = ⋃ₙ (Φⁿ).₂`. -/
def GammaE : Set Str := ⋃ n, (pIter n).2

theorem nil_mem_GammaD : ([] : Str) ∈ GammaD := Set.mem_iUnion.mpr ⟨0, rfl⟩

theorem nil_mem_GammaE : ([] : Str) ∈ GammaE := Set.mem_iUnion.mpr ⟨0, rfl⟩

/-! ## The double fixed point -/

/-! ## The two solution systems and the simultaneous subsystem facts -/

/-- The solution system `D = {Γ_D}`. -/
def Dsol : ScottSys := singletonSys GammaD ⟨[], nil_mem_GammaD⟩

/-- The solution system `E = {Γ_E}`. -/
def Esol : ScottSys := singletonSys GammaE ⟨[], nil_mem_GammaE⟩

/-- The first right-hand side `D + (D × E)`. -/
def Fsol (D E : ScottSys) : ScottSys := D.sum (D.prod E)

/-- The second right-hand side `D + E`. -/
def Gsol (D E : ScottSys) : ScottSys := D.sum E
end Exercise624
end DomainTheory.Neighborhood
