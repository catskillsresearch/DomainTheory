module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
import all Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ApproximableMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Proposition 2.2(i) (Scott 1981, PRG-19).** The elementwise function determined by an
approximable mapping: `f(x) = {Y ∈ 𝒟₁ ∣ ∃ X ∈ x, X f Y}`. The four filter laws use *all* of
Definition 2.1: `master_mem` uses (i); `inter_mem` uses (ii) together with (iii) (to pull both
outputs back along the common input `X ∩ X'`); `up_mem` uses (iii). -/
def toElementMap (f : ApproximableMap V₀ V₁) (x : V₀.Element) : V₁.Element where
  mem Y := ∃ X, x.mem X ∧ f.rel X Y
  sub := fun ⟨_, _, hXY⟩ => f.rel_cod hXY
  master_mem := ⟨V₀.master, x.master_mem, f.master_rel⟩
  inter_mem := by
    rintro Y Y' ⟨X, hX, hXY⟩ ⟨X', hX', hX'Y'⟩
    have hXX'mem : x.mem (X ∩ X') := x.inter_mem hX hX'
    have hXX' : V₀.mem (X ∩ X') := x.sub hXX'mem
    refine ⟨X ∩ X', hXX'mem, ?_⟩
    have h1 : f.rel (X ∩ X') Y :=
      f.mono hXY Set.inter_subset_left subset_rfl hXX' (f.rel_cod hXY)
    have h2 : f.rel (X ∩ X') Y' :=
      f.mono hX'Y' Set.inter_subset_right subset_rfl hXX' (f.rel_cod hX'Y')
    exact f.inter_right h1 h2
  up_mem := by
    rintro Y Y' ⟨X, hX, hXY⟩ hY' hYY'
    exact ⟨X, hX, f.mono hXY subset_rfl hYY' (x.sub hX) hY'⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
