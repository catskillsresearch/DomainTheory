module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Truth

@[expose] public section

open DomainTheory.NeighbourhoodSystems.Truth

/-- Scott's Example 2.3: scanning leading zeros before the first one yields the
parity map into the two-token truth domain. -/
theorem example_2_3 :
    (∀ τ, scan ([false, false] ++ τ) = scan τ) ∧
    (∀ τ, scan ([false, true] ++ τ) = some false) ∧
    (∀ τ, scan ([true] ++ τ) = some true) :=
  ⟨scan_append_falseFalse, scan_append_falseTrue, scan_append_true⟩
