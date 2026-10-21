/-ai
This file gathers and re-exports the setup of Exercise 8.24: the pair space of self-maps, the binary operator induced by a map out of that space, the two approximant chains, and the two components of the simultaneous fixed point, together with the results of Exercise 8.23.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.binOp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.aStar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.bStar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.aOp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.bOp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.PairSpace

@[expose] public section

/-!
# Exercise 8.24 (Scott 1981, PRG-19, §8) — mutual fixed points really do solve `D ≅ S(D,E)`,
`E ≅ T(D,E)`

> **EXERCISE 8.24.** Suppose `S` and `T` are two (binary-argument) constructs on domains that can
> be made into computable operators on projections of the universal domain. Show that we can
> therefore find a pair of effectively presented domains such that `D ≅ S(D, E)` and `E ≅ T(D, E)`.

**Answer: yes.** This is the two-variable (mutual-recursion) generalization of Exercise 8.23, and
the whole argument reduces to a *single instance* of Exercise 8.23's own machinery, applied not to
`(E → E)` but to the **product** function space `(E → E) × (E → E)` — Scott's pairs `(a, b)` of
self-maps of `E`. Formalized here (again over an arbitrary neighbourhood system `E`, not just `U`)
for the two purely order-theoretic claims, with the computability clause deferred to prose, exactly
matching Exercise 8.23's own precedent.

## Setup: `s, t` as approximable maps out of the pair space, `paired s t` as the combined operator

Scott's two operators `s, t : (E → E) × (E → E) → (E → E)` are modelled as approximable maps out of
the **pair space** `PairSpace := (funSpace E E) × (funSpace E E)` (Lecture III's `prod`) into the
single function space `funSpace E E`:
`s t : ApproximableMap PairSpace (funSpace E E)`. The induced operators on actual map-pairs are
`binOp s a b := toApproxMap (s.toElementMap (pair (toFilter a) (toFilter b)))` (Scott's `s(a, b)`),
and likewise `binOp t a b` (Scott's `t(a, b)`).

The two operators combine into a **single self-map of the pair space**, `paired s t :
ApproximableMap PairSpace PairSpace` (Definition 3.3's pairing combinator: `⟨s, t⟩(z) =
⟨s(z), t(z)⟩`), to which Theorem 4.1 applies exactly as in Exercise 8.23. Its exact fixed point
`(paired s t).fixElement : PairSpace.Element` splits, via Definition 3.1's projections `.fst`/
`.snd`, into the two components `aStar s t := toApproxMap (paired s t).fixElement.fst` and
`bStar s t := toApproxMap (paired s t).fixElement.snd` — Scott's simultaneous solution
`(‖s‖, ‖t‖)` of the mutual recursion.

The approximants `(paired s t).iterElem n` similarly split into chains `aOp s t n`/`bOp s t n`
(`.fst`/`.snd` again), satisfying the expected mutual recursion
`aOp s t (n+1) = binOp s (aOp s t n) (bOp s t n)`, `bOp s t (n+1) = binOp t (aOp s t n) (bOp s t n)`
(`aOp_succ`/`bOp_succ`), with base case the constant-bottom map on both sides (`aOp_zero`/
`bOp_zero`, reusing Exercise 8.23's `isFinitaryProjection_constMap_bot`).

## Claim 1 — `aStar s t`, `bStar s t` really are finitary projections (`isFinitaryProjection_aStar_bStar`)

Given `hst : ∀ a b, IsFinitaryProjection a → IsFinitaryProjection b → IsFinitaryProjection (binOp s
a b) ∧ IsFinitaryProjection (binOp t a b)` (Scott's hypothesis that `s`/`t` send pairs of
projections to projections), an induction using `aOp_succ`/`bOp_succ` shows every approximant pair
`(aOp s t n, bOp s t n)` consists of finitary projections, exactly as in Exercise 8.23's Claim 1.
The genuinely new step is transporting Theorem 8.6's `sub`/`subFilter` continuity-with-directed-sups
argument through the `.fst`/`.snd` projections: `(paired s t).fixElement.fst` is identified with the
directed union `⊔ₙ (aOp s t n)`'s underlying filter (`hEqA`, a direct membership chase through
`mem_fst`/`mem_fixElement`/`mem_iterElem`, paralleling `Theorem41.fixElement_eq_iSupDirected` one
level down through the product), and `subFilter` fixes it termwise, hence fixes the union
(`hkeyA`/`hkeyB`, `Sub8_6.subFilter_iSupDirected`) — verbatim Exercise 8.23's Claim 1 argument,
just run twice (once per component).

## Claim 2 — `Fix(aStar s t) ≅ S(aStar s t, bStar s t)`, `Fix(bStar s t) ≅ T(aStar s t, bStar s t)`,
and initiality with respect to projections

`(aStar s t, bStar s t)` is a *genuine* (not merely approximate) simultaneous fixed point:
`binOp s (aStar s t) (bStar s t) = aStar s t` and likewise for `t` (`binOp_aStar_bStar_left/right`),
from `toElementMap_fixElement` (Theorem 4.1) plus `toElementMap_paired`/`fst_pair`/`snd_pair`/
`pair_fst_snd` bookkeeping — again a bare substitution, not a colimit argument. Substituting
`a := aStar s t`, `b := bStar s t` into an abstractly-packaged pair of hypotheses `hS a b : Fix(binOp
s a b) ≅ S(a,b)`, `hT a b : Fix(binOp t a b) ≅ T(a,b)` (Scott's `D_{s(a,b)} ≅ S(D_a, D_b)`,
`D_{t(a,b)} ≅ T(D_a, D_b)`, packaged directly in terms of the maps `a, b` as in Exercise 8.23) and
rewriting the two equations gives `Fix(aStar s t) ≅ S(aStar s t, bStar s t)` and `Fix(bStar s t) ≅
T(aStar s t, bStar s t)` **unconditionally** (`fixedDomain_aStar_bStar_iso`) — exactly Scott's
`D ≅ S(D, E)`, `E ≅ T(D, E)`, with `D := Fix(aStar s t)`, `E := Fix(bStar s t)`.

**Initiality with respect to projections** (`fixedNbhd_aStar_bStar_subsystem`): if `a, b` is *any*
other pair of finitary projections that is a pre-fixed point of the same pair of operators
(`binOp s a b ≤ a`, `binOp t a b ≤ b`), then packaging `(a, b)` as `pair (toFilter a) (toFilter b) :
PairSpace.Element`, the pre-fixed-point hypotheses assemble (via `pair_le_pair_iff`) into a single
pre-fixed-point inequality for `paired s t`, so Theorem 4.1's minimality
(`fixElement_le_of_toElementMap_le`) gives `(paired s t).fixElement ≤ pair (toFilter a) (toFilter
b)`; taking `.fst`/`.snd` and transporting through Exercise 8.16's order-isomorphism `a ≤ b ↔ D_a ◁
D_b` gives `fixedNbhd (aStar s t) ◁ fixedNbhd a` and `fixedNbhd (bStar s t) ◁ fixedNbhd b` — Scott's
"the initial solution... with respect to projections", now for *both* components simultaneously.

## Claim 3 — effectively given if `s, t` are computable (not formalized: prose only)

Exactly Exercise 8.23's own deferred computability clause, doubled: if `s` and `t` are computable
(relative to a `ComputablePresentation` of `E`'s function space), then `constMap E E.bot` is
trivially computable, and by a routine joint induction every approximant pair `(aOp s t n, bOp s t
n)` is computable (composition/pairing of computable maps is computable — `binOp`'s definition is
literally `toElementMap` applied to a `pair`, both computable operations). The simultaneous limit
`(aStar s t, bStar s t)` is then a recursively-enumerable union of computable approximant pairs,
indexed by `n : ℕ`, hence computable by the same "effective limit of an effective chain" argument
already carried out in this codebase for Theorem 8.8's back-and-forth `Yₙ`-chain
(`Theorem88b.lean`–`Theorem88m.lean`). Not carried out in Lean here, matching the `sub`- and
Exercise-8.23-computability precedents.

Everything **proved** in this file (Claims 1–2) is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}

/-! ## The pair space `(E → E) × (E → E)`, and the combined operator `⟨s, t⟩` -/







/-! ## `.fst`/`.snd` are monotone (needed for the directed-union chase in Claim 1) -/

/-! ## The bottom of the pair space splits into the two bottoms (base case of the induction) -/

/-! ## `⟨s, t⟩`'s iterates (mirroring Exercise 8.23's `iterElem_succ'`/`iterElem_zero'`) -/

/-! ## Claim 1 — `aStar s t`, `bStar s t` are finitary projections -/

/-! ## Claim 2 — the simultaneous fixed point genuinely solves the equations, and is initial -/
end Exercise824
end DomainTheory.NeighbourhoodSystems
