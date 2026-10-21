/-ai
The smash-product action of two approximable maps relates W to W' in one of two ways: W is a neighbourhood of the smash product and W' is the product neighbourhood of the two codomain masters; or there are proper neighbourhoods X, Y, X', Y' with the left map relating X to X', the right map relating Y to Y', and W, W' the corresponding product neighbourhoods. The domain and codomain of a related pair are the corresponding membership clauses of the smash product. The master relates to the master. Intersection on the right cases on the two relations. A master output meeting a proper rectangle reduces by the componentwise intersection of product neighbourhoods, because each component lies under its master. Two proper rectangles have the same underlying coordinates by injectivity of product neighbourhoods, and the component intersection laws together with the left-factor intersection lemma give the intersected rectangle. Monotonicity cases on the relation. A master output is forced because the master lies under every neighbourhood. A proper rectangle whose larger input is the master would force a component to equal its master by the componentwise characterization of inclusion of product neighbourhoods. If the larger output is the master, the result is the master clause, with the input a proper rectangle. If both sides are proper rectangles, the two inclusions unpack componentwise and the component monotonicity laws apply.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.inter_ne_of_ne_left
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimes
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesTok_mem_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesTok_mem_prod

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- **`f₀ ⊗ f₁`, the action of the smash product on maps.** -/
def otimesMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.otimes A₁).sys (B₀.otimes B₁).sys where
  rel W W' :=
    ((A₀.otimes A₁).sys.mem W ∧ W' = prodTokNbhd B₀.sys.master B₁.sys.master) ∨
    (∃ X Y X' Y', f₀.rel X X' ∧ f₁.rel Y Y' ∧ X ≠ A₀.sys.master ∧ Y ≠ A₁.sys.master ∧
      X' ≠ B₀.sys.master ∧ Y' ≠ B₁.sys.master ∧ W = prodTokNbhd X Y ∧ W' = prodTokNbhd X' Y')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, Y, X', Y', h0, h1, hXne, hYne, -, -, rfl, -⟩)
    · exact hW
    · exact otimesTok_mem_prod (f₀.rel_dom h0) (f₁.rel_dom h1) hXne hYne
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, Y, X', Y', h0, h1, -, -, hX'ne, hY'ne, -, rfl⟩)
    · exact otimesTok_mem_master
    · exact otimesTok_mem_prod (f₀.rel_cod h0) (f₁.rel_cod h1) hX'ne hY'ne
  master_rel := Or.inl ⟨(A₀.otimes A₁).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · refine Or.inr ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, hWeq, ?_⟩
        rw [prodTokNbhd_inter, Set.inter_eq_right.mpr (B₀.sys.sub_master (f₀.rel_cod hr0)),
          Set.inter_eq_right.mpr (B₁.sys.sub_master (f₁.rel_cod hr1))]
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, Y₂, X'₂, Y'₂, hr0₂, hr1₂, hX₂ne, hY₂ne, hX'₂ne, hY'₂ne, hWeq, rfl⟩
      · refine Or.inr ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, rfl, ?_⟩
        rw [Set.inter_comm, prodTokNbhd_inter,
          Set.inter_eq_right.mpr (B₀.sys.sub_master (f₀.rel_cod hr0)),
          Set.inter_eq_right.mpr (B₁.sys.sub_master (f₁.rel_cod hr1))]
      · obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
        refine Or.inr ⟨X, Y, X' ∩ X'₂, Y' ∩ Y'₂, f₀.inter_right hr0 hr0₂,
          f₁.inter_right hr1 hr1₂, hXne, hYne,
          inter_ne_of_ne_left (B₀.sys.sub_master (f₀.rel_cod hr0)) hX'ne,
          inter_ne_of_ne_left (B₁.sys.sub_master (f₁.rel_cod hr1)) hY'ne, rfl, ?_⟩
        rw [prodTokNbhd_inter]
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hZmem hZ'mem
    rcases h with ⟨-, rfl⟩ | ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩
    · exact Or.inl ⟨hZmem, Set.Subset.antisymm ((B₀.otimes B₁).sys.sub_master hZ'mem) hZZ'⟩
    · rcases hZmem with rfl | ⟨Xz, Yz, hXz, hYz, hXzne, hYzne, rfl⟩
      · obtain ⟨hsubX, -⟩ := prodTokNbhd_subset_iff.mp hWW
        exact absurd (Set.Subset.antisymm (A₀.sys.sub_master (f₀.rel_dom hr0)) hsubX) hXne
      · rcases hZ'mem with rfl | ⟨Xz', Yz', hXz', hYz', hXz'ne, hYz'ne, rfl⟩
        · exact Or.inl ⟨otimesTok_mem_prod hXz hYz hXzne hYzne, rfl⟩
        · obtain ⟨hXzX, hYzY⟩ := prodTokNbhd_subset_iff.mp hWW
          obtain ⟨hX'Xz', hY'Yz'⟩ := prodTokNbhd_subset_iff.mp hZZ'
          exact Or.inr ⟨Xz, Yz, Xz', Yz', f₀.mono hr0 hXzX hX'Xz' hXz hXz',
            f₁.mono hr1 hYzY hY'Yz' hYz hYz', hXzne, hYzne, hXz'ne, hYz'ne, rfl, rfl⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
