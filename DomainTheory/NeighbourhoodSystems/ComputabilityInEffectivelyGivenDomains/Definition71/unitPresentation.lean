/-ai
The one-point neighbourhood system has the constant computable presentation that enumerates the whole token set at every index. That set is the only neighbourhood, so every index is a neighbourhood and the enumeration is surjective. Any two enumerated sets are equal and every intersection is the whole set, so both of Scott's relations hold for every index tuple and are decided by the constantly true decider. The intersection function is the constant zero, which is primitive recursive, and the master index is zero.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.ComputablePresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*}

/-- The trivial presentation of the one-point system `𝟙 = unitSys`: the constant enumeration
`Xₙ = Δ = univ`. Both of Scott's relations are *always true* here (any two neighbourhoods are equal
and consistent), hence trivially recursively decidable via the constant `1` decider. -/
def unitPresentation : ComputablePresentation unitSys where
  X _ := Set.univ
  mem_X _ := rfl
  surj := by rintro Y rfl; exact ⟨0, rfl⟩
  interEq_computable := recDecidable_of_forall fun _ => Set.inter_self Set.univ
  cons_computable := recDecidable_of_forall fun _ =>
    ⟨0, by rw [Set.inter_self]⟩
  inter _ _ := 0
  inter_primrec := Nat.Primrec.zero
  inter_spec _ := by rw [Set.inter_self]
  masterIdx := 0
  masterIdx_spec := rfl

end DomainTheory.NeighbourhoodSystems
