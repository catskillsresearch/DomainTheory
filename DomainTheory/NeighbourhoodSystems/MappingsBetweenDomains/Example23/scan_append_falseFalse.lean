module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **Two leading `0`'s cancel.** `scan([0,0]++τ) = scan τ`: reading two extra zeros flips the
parity twice, i.e. not at all (`Bool.not_not`). (Exercise 2.16's third equation, at the token
level — the recursive step behind the uniqueness argument for the parity map.) -/
theorem scan_append_falseFalse (τ : Str) : scan ([false, false] ++ τ) = scan τ := by
  show scan (false :: false :: τ) = scan τ
  cases h : scan τ with
  | none => simp [scan_false, h]
  | some b => simp [scan_false, h, Bool.not_not]

end DomainTheory.NeighbourhoodSystems.Example23
