module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.T
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.Token
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.bitNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.T_nbhd_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.mem_encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_nil

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- Two prefixes that both bound a common non-empty `T^∞`-neighbourhood agree where both defined. -/
theorem encSet_agree {τ τ' : Str} {W : Set (ℕ × Token)} (hW : (iterSys T).mem W)
    (h : W ⊆ encSet τ) (h' : W ⊆ encSet τ') {i : ℕ} {b b' : Bool}
    (hb : τ[i]? = some b) (hb' : τ'[i]? = some b') : b = b' := by
  obtain ⟨t, ht⟩ := T_nbhd_nonempty (hW.1 i)
  have h1 : t ∈ bitNbhd b := (h ht) b hb
  have h2 : t ∈ bitNbhd b' := (h' ht) b' hb'
  by_contra hne
  cases b <;> cases b' <;> simp_all [bitNbhd, Example12.zero, Example12.one]

end DomainTheory.NeighbourhoodSystems.Exercise317
