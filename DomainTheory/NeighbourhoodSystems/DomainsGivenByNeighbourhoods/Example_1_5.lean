module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Example15
section

open NeighborhoodSystem

abbrev Token := Fin 4

def P4Mem (X : Set Token) : Prop := X.Nonempty

theorem P4_inter_mem {X Y Z : Set Token} (_hX : P4Mem X) (_hY : P4Mem Y)
    (hZ : P4Mem Z) (hZsub : Z ⊆ X ∩ Y) : P4Mem (X ∩ Y) :=
  hZ.mono hZsub

def master : Set Token := Set.univ

theorem P4_master_mem : P4Mem master := by
  rw [master]; exact Set.univ_nonempty

theorem P4_master_nonempty : master.Nonempty := by
  exact ⟨0, Set.mem_univ 0⟩

theorem P4_sub_master {X : Set Token} (_h : P4Mem X) : X ⊆ master :=
  Set.subset_univ _

def neighborhoodSystem : NeighborhoodSystem Token where
  mem := P4Mem
  master
  master_nonempty := P4_master_nonempty
  master_mem := P4_master_mem
  inter_mem := P4_inter_mem
  sub_master := P4_sub_master

/-- **Example 1.5.** Tokens $\Delta=\{0,1,2,3\}$ and neighbourhoods
$\mathcal{D}=$ all nonempty subsets of $\Delta$ form a neighbourhood system. -/
theorem example_1_5 :
    ∃ (V : NeighborhoodSystem Token),
      V.master = (Set.univ : Set Token) ∧
        (∀ X : Set Token, V.mem X ↔ X.Nonempty) :=
  ⟨neighborhoodSystem, rfl, fun _ => Iff.rfl⟩

end

end DomainTheory.NeighbourhoodSystems.Example15
end
