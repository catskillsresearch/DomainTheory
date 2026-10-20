/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_cons_code
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_isPDmem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PDmem_exists_Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.interCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_interCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.primrec_interCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_interEq_computable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- **Proposition 7.10 (Part B), parametrised.** The `ℙ𝒟` presentation built from an explicit
primitive-recursive consistency decider `cons` for `𝒟` (cf. `funPresentation`, Theorem 7.5). The data
(`X = Ypd`, `inter = interCode cons`, `masterIdx`) is choice-free given `cons`. -/
def PDPresentation (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    ComputablePresentation V.PowerDomain where
  X := V.Ypd P
  mem_X := fun c => V.Ypd_isPDmem P c
  surj := fun hW => V.PDmem_exists_Ypd P hW
  interEq_computable := V.Ypd_interEq_computable P cons hconsp hcons
  cons_computable :=
    recDecidable_of_forall (fun t => ⟨0, by rw [V.Ypd_zero P]; exact Set.empty_subset _⟩)
  inter := V.interCode P cons
  inter_primrec := V.primrec_interCode P cons hconsp
  inter_spec := fun _ => V.Ypd_interCode P cons _ _ hcons
  masterIdx := Nat.pair P.masterIdx 0 + 1
  masterIdx_spec := by
    show V.Ypd P (Nat.pair P.masterIdx 0 + 1) = V.PowerDomain.master
    rw [V.Ypd_cons_code P, V.Ypd_zero P, Set.union_empty, P.masterIdx_spec, PowerDomain_master]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
