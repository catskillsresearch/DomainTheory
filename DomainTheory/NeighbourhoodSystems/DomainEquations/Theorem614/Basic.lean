/-ai
The colimit of the iterated tower is a T-algebra whose structure map is the isomorphism from the image of the colimit to the colimit. As category objects over the token type, the colimit is that system and the n-th level is the n-th system of the tower. The image under T of the n-th projection is the induced endomorphism of the image of the colimit.

The zeroth level of the tower is the generating system. The equality is definitional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Setup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.iter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Tcolim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.isoOfEq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colimIso
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.rho
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.iSupRho
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.subsystem_cast
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.rec_trans
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.mem_cast
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.set_rec_trans
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dceq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dchain
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.chain_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.mem_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys_sub_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colimCeq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys_sub_Tcolim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Tcolim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim_sub_Tcolim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Tcolim_sub_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Tcolim_eq_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.domainObj_ext
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colimObj_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.rho_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.rho_mono

@[expose] public section

/-!
# Lecture VI — Theorem 6.14 (Scott 1981, PRG-19): existence of initial `T`-algebras

> **THEOREM 6.14.** If the functor `T` is continuous on maps and monotone and continuous on domains,
> and if there is a set `Γ` such that `{Γ} ◁ T({Γ})`, then there exists an initial `T`-algebra.

Scott's proof iterates the functor from the generating system `{Γ}`. The assumption
`{Γ} ◁ T({Γ})` means `T({Γ})` is a system over the same token set `Γ`; iterating, every
`Tⁿ({Γ})` is over `Γ` and `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ})`. The colimit

`𝒟 = ⋃ₙ Tⁿ({Γ})`

is then a system over `Γ` with `Tⁿ({Γ}) ◁ 𝒟`, whence `𝒟 ◁ T(𝒟)`, and *continuity on domains*
gives `T(𝒟) = 𝒟` — the isomorphism `𝒟 ≅ T(𝒟)` is the **identity**. So `𝒟` is a `T`-algebra, and:

* **existence** of homomorphisms out of `𝒟` is Theorem 6.9 (`nonempty_algHom_of_continuousOnMaps`);
* **uniqueness** is the `ρₙ = iₙ ∘ jₙ` projection-chain argument: `T(ρₙ) = ρₙ₊₁` (monotone on
  domains), `⋃ₙ ρₙ = I_𝒟`, and any homomorphism `h` is `⋃ₙ h∘ρₙ`, the least fixed point of
  `λh. k ∘ T(h)`.

## The carrier-type subtlety

The abstract `T : Endofunctor DomainObj` need not preserve token types, so `Tⁿ({Γ})` a priori live
over different carriers. The hypothesis `{Γ} ◁ T({Γ})` already pins `T({Γ})` to `Γ`'s carrier, and
*monotone on domains* (Definition 6.13, `MonotoneAt.carrier_eq`) propagates the identification up the
tower. We carry the carrier equalities explicitly and transport along them; the transport of the
subdomain relation is the choice-free `subsystem_cast`.

## Lean note: `rw` fragility on defeq-but-not-syntactic implicits

Throughout the uniqueness half, `rw` with explicit arguments at the `ApproximableMap` /
`NeighborhoodSystem` level repeatedly failed with "did not find an occurrence of the pattern" even
when the pattern was visibly present — because the implicit carriers/systems were **defeq but not
syntactically equal** (`colim s` vs `(colimAlg s).carrier.sys` vs `(objColim s).sys`; the abbrev
`objColim` vs the literal `⟨Tok, colim s⟩`). Three fixes, used throughout `gcomp_rho_succ`/`gcomp_eq`:
* work at the categorical `⊚` / `Category.assoc` level, where the implicits are concrete `DomainObj`s
  rather than systems, so unification has nothing to get stuck on;
* prefer `congrArg` / `calc` **term-mode** proofs (e.g. `congrArg (fun x => g.hom ⊚ x) (key_rho s n)`),
  since `calc` bridges adjacent steps by defeq rather than by syntactic match;
* to rewrite with a lemma whose implicit is pinned to the "wrong" representation (e.g. `comp_idMap`,
  whose `idMap` arg is tied to `g.hom`'s domain `(colimAlg s).carrier.sys`), first bind the fact via a
  `have` stated in the *desired* form (`have e : g.hom.comp (idMap (colim s)) = g.hom := comp_idMap
  g.hom` — the `have` unifies by defeq), then `rw [← e]`.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614

/-! ### Carrier-transport helpers -/

variable {α : Type w}


/-! ### The setup bundle (hypotheses of Theorem 6.14) -/


/-! ### The iterated functor tower `Tⁿ({Γ})` -/


/-! ### The colimit `𝒟 = ⋃ₙ Tⁿ({Γ})` -/


/-! ### `T(𝒟)` and the relation `𝒟 ◁ T(𝒟)` -/


/-! ### `𝒟` is a `T`-algebra: the iso `𝒟 ≅ T(𝒟)` is the identity -/


/-- The colimit `𝒟` as a `T`-algebra, with structure map the iso `T(𝒟) → 𝒟`. -/
abbrev colimAlg (s : Setup.{w}) : TAlgebra s.T :=
  ⟨⟨s.Tok, colim s⟩, (colimIso s).hom⟩

/-! ### Existence of homomorphisms (Theorem 6.9) -/

/-! ### The projection chain `ρₙ = iₙ ∘ jₙ` and `⋃ₙ ρₙ = I_𝒟` -/


/-! ### Theorem 6.14 — the existence half (the canonical solution and its homomorphisms) -/

/-! ### Theorem 6.14 — the uniqueness half (`T(ρₙ) = ρₙ₊₁`, then `g = ⋃ₙ g∘ρₙ`)

Scott shows homomorphisms out of `𝒟` are unique by showing they are determined on the finite
elements. Concretely, the projection chain `ρₙ = iₙ ∘ jₙ` satisfies `T(ρₙ) = ρₙ₊₁` (because `T` is
monotone on domains, so it carries the projection pair `iₙ, jₙ` to `iₙ₊₁, jₙ₊₁`) and
`⋃ₙ ρₙ = I_𝒟`. For any homomorphism `g : 𝒟 → E`, the sequence `gₙ = g ∘ ρₙ` is then **independent
of `g`**: `g₀ = ⊥` (because `g` is strict and `ρ₀ = ⊥`), and `gₙ₊₁ = k ∘ T(gₙ) ∘ j` by the
homomorphism square; so `g = ⋃ₙ gₙ` is forced. -/

/-- The colimit `𝒟` as a category object `⟨Tok, 𝒟⟩`. -/
abbrev objColim (s : Setup.{w}) : DomainObj := ⟨s.Tok, colim s⟩

/-- The `n`-th tower system `Tⁿ({Γ})` as a category object `⟨Tok, Tⁿ({Γ})⟩`. -/
abbrev objDsys (s : Setup.{w}) (n : ℕ) : DomainObj := ⟨s.Tok, Dsys s n⟩

/-- `T(ρₙ)` as an endomorphism of `T(𝒟)`, with the category objects pinned (they cannot be inferred
from `rho s n`'s `ApproximableMap` type alone). -/
abbrev Tmap_rho (s : Setup.{w}) (n : ℕ) :
    ApproximableMap (s.T.obj (objColim s)).sys (s.T.obj (objColim s)).sys :=
  s.T.map (X := objColim s) (Y := objColim s) (rho s n)

/-! ### The `g`-independent fixed-point recursion -/

@[simp] theorem Dsys_zero (s : Setup.{w}) : Dsys s 0 = s.Γ := rfl

/-! ### Uniqueness and initiality (among strict algebras) -/
end Theorem614
end DomainTheory.NeighbourhoodSystems
