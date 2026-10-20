module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
import all Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ApproximableMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.mem_toElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.idMap_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Theorem 2.5(ii) (Scott 1981, PRG-19) — composition `g ∘ f`.** `X (g∘f) Z ↔ ∃ Y, X f Y ∧ Y g Z`.
Approximability is Scott's verification: (i) use `Y = Δ₁`; (ii) intersect both witnesses via
`f.inter_right` then `g.inter_right` (narrowing the inner neighbourhood with `g.mono`); (iii) narrow
the input with `f.mono` and widen the output with `g.mono`, keeping the same witness. -/
def comp (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) : ApproximableMap V₀ V₂ where
  rel X Z := ∃ Y, f.rel X Y ∧ g.rel Y Z
  rel_dom := fun ⟨_, hXY, _⟩ => f.rel_dom hXY
  rel_cod := fun ⟨_, _, hYZ⟩ => g.rel_cod hYZ
  master_rel := ⟨V₁.master, f.master_rel, g.master_rel⟩
  inter_right := by
    rintro X Z Z' ⟨Y, hXY, hYZ⟩ ⟨Y', hXY', hY'Z'⟩
    refine ⟨Y ∩ Y', f.inter_right hXY hXY', ?_⟩
    have hYY'mem : V₁.mem (Y ∩ Y') := f.rel_cod (f.inter_right hXY hXY')
    have h1 : g.rel (Y ∩ Y') Z :=
      g.mono hYZ Set.inter_subset_left subset_rfl hYY'mem (g.rel_cod hYZ)
    have h2 : g.rel (Y ∩ Y') Z' :=
      g.mono hY'Z' Set.inter_subset_right subset_rfl hYY'mem (g.rel_cod hY'Z')
    exact g.inter_right h1 h2
  mono := by
    rintro X X' Z Z' ⟨Y, hXY, hYZ⟩ hX'X hZZ' hX' hZ'
    refine ⟨Y, f.mono hXY hX'X subset_rfl hX' (f.rel_cod hXY), ?_⟩
    exact g.mono hYZ subset_rfl hZZ' (g.rel_dom hYZ) hZ'

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
