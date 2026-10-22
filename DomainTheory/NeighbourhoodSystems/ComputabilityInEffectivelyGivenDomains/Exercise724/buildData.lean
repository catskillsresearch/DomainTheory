module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LFunData
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.BasicInst2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.HasMin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.exists_extend_of_not_hasMin

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- **Choice-built data**: the length-`n` list `x.mem`s, together with the invariant, by iterating
`exists_extend_of_not_hasMin`. This is the one genuinely non-constructive step (`Classical.choose`
picking a witness coordinate at every stage), unavoidable for a *general* filter `x` (no
computability is assumed of `x` at this point in the exercise). -/
noncomputable def buildData (x : L.Element) (hx : ¬ HasMin x) :
    ∀ n : ℕ, {l : List ℕ // x.mem (nbhd l) ∧ l.length = n} :=
  fun n =>
    Nat.rec (⟨[], x.master_mem, rfl⟩ : {l : List ℕ // x.mem (nbhd l) ∧ l.length = 0})
      (fun n prev =>
        ⟨prev.1 ++ [Classical.choose (exists_extend_of_not_hasMin hx prev.2.1)],
          Classical.choose_spec (exists_extend_of_not_hasMin hx prev.2.1),
          by rw [List.length_append, List.length_singleton, prev.2.2]⟩)
      n

end DomainTheory.NeighbourhoodSystems.Exercise724
