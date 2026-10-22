module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.SmashProper
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.inter_ne_master_left
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.inter_ne_master_right

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 5.10 (Scott 1981, PRG-19) — the smash product `𝒟₀ ⊗ 𝒟₁`.** Neighbourhoods are the
master `Δ₀ ∪ Δ₁` together with the *proper* product neighbourhoods `X ∪ Y` (both factors proper).

*This is a neighbourhood system.* Condition (i) is the master clause. Condition (ii) is the new
content: given two smash neighbourhoods with a consistency witness `Z`,

* if either is the master, the intersection collapses to the other (since `X ⊆ Δ₀`, `Y ⊆ Δ₁`);
* if both are proper, `Z` cannot be the master (that would force a factor to be `Δ₀`/`Δ₁`), so `Z` is
  a *proper* `U ∪ V`; `U ⊆ X ∩ X'` and `V ⊆ Y ∩ Y'` then witness `X ∩ X' ∈ 𝒟₀`, `Y ∩ Y' ∈ 𝒟₁`, both
  still proper (`inter_ne_master_*`). -/
def smash (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : NeighborhoodSystem (α ⊕ β) where
  mem W := W = prodNbhd V₀.master V₁.master ∨ SmashProper V₀ V₁ W
  master := prodNbhd V₀.master V₁.master
  master_nonempty := by
    obtain ⟨a, ha⟩ := V₀.master_nonempty
    exact ⟨Sum.inl a, mem_prodNbhd_inl.mpr ha⟩
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' Z (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩) hW' hZ hZsub
    · -- W = master
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · left; rw [Set.inter_self]
      · right
        refine ⟨X', Y', hX', hX'ne, hY', hY'ne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_right.mpr (V₀.sub_master hX'),
          Set.inter_eq_right.mpr (V₁.sub_master hY')]
    · -- W = X ∪ Y proper
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · right
        refine ⟨X, Y, hX, hXne, hY, hYne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_left.mpr (V₀.sub_master hX),
          Set.inter_eq_left.mpr (V₁.sub_master hY)]
      · -- both proper: use the witness Z
        right
        rw [prodNbhd_inter] at hZsub ⊢
        rcases hZ with hZeq | ⟨U, V, hU, _, hV, _, rfl⟩
        · -- Z = master is impossible
          exfalso
          rw [hZeq] at hZsub
          obtain ⟨hΔ₀, _⟩ := prodNbhd_subset_iff.mp hZsub
          exact hXne (Set.Subset.antisymm (V₀.sub_master hX) (hΔ₀.trans Set.inter_subset_left))
        · obtain ⟨hUsub, hVsub⟩ := prodNbhd_subset_iff.mp hZsub
          refine ⟨X ∩ X', Y ∩ Y', ?_, ?_, ?_, ?_, rfl⟩
          · exact V₀.inter_mem hX hX' hU hUsub
          · exact inter_ne_master_left hX hXne
          · exact V₁.inter_mem hY hY' hV hVsub
          · exact inter_ne_master_right hY hYne
  sub_master := by
    rintro W (rfl | ⟨X, Y, hX, _, hY, _, rfl⟩)
    · exact subset_rfl
    · exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, V₁.sub_master hY⟩

end DomainTheory.NeighbourhoodSystems.Exercise510
