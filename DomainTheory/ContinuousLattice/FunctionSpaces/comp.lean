/-ai
The composite of two maps that preserve directed suprema again preserves directed suprema.

A map that preserves directed suprema is monotone, so the image of a nonempty directed set under the inner map is nonempty and directed. Preservation for the inner map rewrites its value at the supremum as the supremum of the image, preservation for the outer map rewrites the outer value as the supremum of the further image, and the image of a composite is the composite of the images.

Composition of Scott maps is this set-theoretic composite. The composite preserves directed suprema by the previous fact together with Proposition 2.5 applied to the continuity of each Scott map, and a map that preserves directed suprema is continuous, so the composite is a Scott map.
ai-/
module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.ScottMaps.proposition_2_5
public import DomainTheory.ContinuousLattice.ScottMaps.preservesDirectedSup_monotone

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

namespace ScottMap

theorem preservesDirectedSup_comp {f : D' → D''} {g : D → D'} (hf : PreservesDirectedSup f)
    (hg : PreservesDirectedSup g) : PreservesDirectedSup (f ∘ g) := by
  intro S hS hSdir
  have hmono : Monotone g := preservesDirectedSup_monotone hg
  have hdir' : DirectedOn (· ≤ ·) (g '' S) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨g c, Set.mem_image_of_mem g hc, hmono hac, hmono hbc⟩
  have hne : (g '' S).Nonempty := Set.image_nonempty.2 hS
  rw [Function.comp_apply, hg hS hSdir, hf hne hdir']
  congr 1
  exact (Set.image_comp f g S).symm

def comp (f : ScottMap D' D'') (g : ScottMap D D') : ScottMap D D'' :=
  ⟨f ∘ g, continuous_of_preservesDirectedSup (preservesDirectedSup_comp
    ((proposition_2_5 (Subtype.val f)).mp f.property)
    ((proposition_2_5 (Subtype.val g)).mp g.property))⟩

end ScottMap

end DomainTheory.ContinuousLattice
