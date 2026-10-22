module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}


/-- **The hard half of Theorem 8.6's range characterization, now unblocked by Theorem 8.5.** Every
finitary projection is a fixed point of `sub`: `⊇` is `sub_le`; `⊆` unwinds `X f Z` via
`rel_iff_mem_principal` into `Z ∈ f(↑X)`, and Theorem 8.5's formula
(`formula_of_isFinitaryProjection`) rewrites this as exactly `sub_rel`'s defining formula. -/
theorem sub_eq_self_of_isFinitaryProjection {f : ApproximableMap E E}
    (h : FinitaryProjection f) : sub f = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · exact sub_le f X Z
  · intro hXZ
    have hX : E.mem X := f.rel_dom hXZ
    have hZ : E.mem Z := f.rel_cod hXZ
    have hmem : (f.toElementMap (E.principal hX)).mem Z := (f.rel_iff_mem_principal hX).mp hXZ
    obtain ⟨-, W, hW, hWZ, hWf⟩ := (formula_of_isFinitaryProjection h (E.principal hX)).mp hmem
    obtain ⟨hWE, hXW⟩ := (E.mem_principal hX).mp hW
    exact sub_rel.mpr ⟨hX, hZ, W, ⟨hWE, hWf⟩, hXW, hWZ⟩

end DomainTheory.NeighbourhoodSystems
