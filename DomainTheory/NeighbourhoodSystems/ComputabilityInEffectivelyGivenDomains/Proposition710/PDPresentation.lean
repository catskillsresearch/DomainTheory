/-ai
The computable presentation of the Smyth power domain built from an explicit primitive-recursive consistency decider for the original system enumerates neighbourhoods by finite unions of down-sets, intersects them by the intersection code of that decider, and takes as master index the code of the singleton list containing the original master index. Surjectivity is the enumeration theorem, intersection-equality is the computed decider, consistency holds of every code because the empty union is contained in every neighbourhood, and the intersection and master-index specifications are the corresponding correctness lemmas.
ai-/
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
