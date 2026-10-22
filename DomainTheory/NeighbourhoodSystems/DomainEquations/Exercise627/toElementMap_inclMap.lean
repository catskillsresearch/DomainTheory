module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem toElementMap_inclMap (φ : (strictFun V₀ V₁).Element) :
    inclMap.toElementMap φ = incl φ := by
  apply Element.ext
  intro M
  constructor
  · rintro ⟨W, hφW, _, hincl⟩
    obtain ⟨hMmem, hg⟩ := hincl
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hMmem
    refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    obtain ⟨hsstep, hWsub⟩ := toStrictMap_rel.mp (hg p hp)
    exact φ.up_mem hφW hsstep hWsub
  · rintro ⟨hMmem, hgφ⟩
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hMmem
    have hφL : φ.mem (sstepFun L) :=
      (mem_sstepFun_iff φ hL).mpr (fun p hp => toStrictMap_rel.mp (hgφ p hp))
    refine ⟨sstepFun L, hφL, φ.sub hφL, ⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    exact ⟨φ.sub (toStrictMap_rel.mp (hgφ p hp)), fun f hf => hf p hp⟩

end Part5
end Exercise627
end DomainTheory.NeighbourhoodSystems
