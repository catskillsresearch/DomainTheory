module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Example15
section

open NeighborhoodSystem

/-- Tokens for Example 1.5: `Δ = {0, 1, 2, 3}`. -/
abbrev Token := Fin 4

/-- Membership: the non-empty subsets of `Δ`. -/
def P4Mem (X : Set Token) : Prop := X.Nonempty

/-- A non-empty witness inside `X ∩ Y` shows the intersection is a neighbourhood. -/
theorem P4_inter_mem {X Y Z : Set Token} (_hX : P4Mem X) (_hY : P4Mem Y)
    (hZ : P4Mem Z) (hZsub : Z ⊆ X ∩ Y) : P4Mem (X ∩ Y) :=
  hZ.mono hZsub

/-- The master neighbourhood `Δ = {0, 1, 2, 3}`. -/
def master : Set Token := Set.univ

/-- `Δ` is non-empty. -/
theorem P4_master_mem : P4Mem master := by
  rw [master]; exact Set.univ_nonempty

/-- The master token set itself is non-empty. -/
theorem P4_master_nonempty : master.Nonempty := by
  exact ⟨0, Set.mem_univ 0⟩

/-- Every neighbourhood is a subset of `Δ`. -/
theorem P4_sub_master {X : Set Token} (_h : P4Mem X) : X ⊆ master :=
  Set.subset_univ _

/- concordance: source L208 EXAMPLE 1.5 all nonempty subsets -/
/-- **Example 1.5.** The neighbourhood system of all non-empty subsets of `Δ = {0,1,2,3}`. -/
def neighborhoodSystem : NeighborhoodSystem Token where
  mem := P4Mem
  master := master
  master_nonempty := P4_master_nonempty
  master_mem := P4_master_mem
  inter_mem := P4_inter_mem
  sub_master := P4_sub_master

/-- The neighbourhoods of Example 1.5 are a finite family, hence countable. -/
instance P4_countable : Countable {S : Set Token // neighborhoodSystem.mem S} :=
  inferInstance
end

end DomainTheory.NeighbourhoodSystems.Example15
end
