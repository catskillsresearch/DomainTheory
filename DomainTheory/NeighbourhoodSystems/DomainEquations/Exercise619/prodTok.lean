/-ai
prodTok is the concrete product system of Exercise 6.19 over binary words. Its neighbourhoods are the sets formed by the empty word together with the false-tagged copy of a neighbourhood of the first factor and the true-tagged copy of a neighbourhood of the second, and its master is that construction on the two masters. Consistent intersection is componentwise, by the inclusion and intersection laws for product neighbourhoods together with the intersection laws of the factors.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTokNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_false
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_true
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTokNbhd_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTokNbhd_subset_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- **Exercise 6.19 — the concrete product system `𝒟₀ × 𝒟₁` over `{0,1}*`.** Neighbourhoods are
`{Λ} ∪ 0X ∪ 1Y` with `X ∈ 𝒟₀`, `Y ∈ 𝒟₁`. Closed under consistent intersection by Scott's (1)/(2)
together with the factors' closure. -/
def prodTok (D₀ D₁ : NeighborhoodSystem Str) : NeighborhoodSystem Str where
  mem W := ∃ X Y, D₀.mem X ∧ D₁.mem Y ∧ W = prodTokNbhd X Y
  master := prodTokNbhd D₀.master D₁.master
  master_nonempty := ⟨[], mem_prodTokNbhd_nil⟩
  master_mem := ⟨D₀.master, D₁.master, D₀.master_mem, D₁.master_mem, rfl⟩
  inter_mem := by
    rintro W W' Z ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ ⟨Z₀, Z₁, hZ₀, hZ₁, rfl⟩ hsub
    rw [prodTokNbhd_inter] at hsub ⊢
    obtain ⟨hsub₀, hsub₁⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X ∩ X', Y ∩ Y', D₀.inter_mem hX hX' hZ₀ hsub₀, D₁.inter_mem hY hY' hZ₁ hsub₁, rfl⟩
  sub_master := by
    rintro W ⟨X, Y, hX, hY, rfl⟩
    exact prodTokNbhd_subset_iff.mpr ⟨D₀.sub_master hX, D₁.sub_master hY⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
