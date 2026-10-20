module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.univ_ne_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.singleton_ne_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.singleton_nat_inj
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- The *strict* approximable map `N → V` determined by a choice of value `val n ∈ |V|` for each
`n`: it sends the total element `n̂` to `val n` and the bottom `⊥` to `⊥`. The relation
`X f Y` holds when either `X = Δ_N` forces the blunt output `Y = Δ_V` (the strict `⊥ ↦ ⊥` clause),
or `X = {n}` and `Y` is a neighbourhood of `val n`.

Definition 2.1 checks uniformly: (i) `Δ_N f Δ_V`; (ii) intersect outputs — distinct inputs are
impossible (`ℕ ≠ {n}`, singletons are one-one), so both outputs come from the *same* `val n` and
`inter_mem` of the filter `val n` applies; (iii) sharpening `{n} ⊆ X` keeps the input a singleton
`{n}`, and `up_mem` of `val n` widens the output, while a blunt input `Δ_N` forces `Δ_V`. -/
def constLiftN {β : Type*} (V : NeighborhoodSystem β) (val : ℕ → V.Element) :
    ApproximableMap N V where
  rel X Y := (X = Set.univ ∧ Y = V.master) ∨ (∃ n, X = {n} ∧ (val n).mem Y)
  rel_dom := by
    rintro X Y (⟨rfl, _⟩ | ⟨n, rfl, _⟩)
    · exact memN_univ
    · exact memN_singleton n
  rel_cod := by
    rintro X Y (⟨_, rfl⟩ | ⟨n, _, hY⟩)
    · exact V.master_mem
    · exact (val n).sub hY
  master_rel := Or.inl ⟨rfl, rfl⟩
  inter_right := by
    rintro X Y Y' (⟨rfl, rfl⟩ | ⟨n, rfl, hY⟩) hc'
    · rcases hc' with ⟨_, rfl⟩ | ⟨n, hX, _⟩
      · exact Or.inl ⟨rfl, by rw [Set.inter_self]⟩
      · exact (univ_ne_singleton n hX).elim
    · rcases hc' with ⟨hX, _⟩ | ⟨n', hX', hY'⟩
      · exact (singleton_ne_univ n hX).elim
      · have hnn' : n = n' := singleton_nat_inj hX'
        subst hnn'
        exact Or.inr ⟨n, rfl, (val n).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' (⟨rfl, rfl⟩ | ⟨n, rfl, hY⟩) hX'X hYY' hX' hY'
    · have hY'master : Y' = V.master := Set.Subset.antisymm (V.sub_master hY') hYY'
      subst hY'master
      rcases hX' with rfl | ⟨k, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨k, rfl, (val k).master_mem⟩
    · rcases hX' with rfl | ⟨k, rfl⟩
      · exact (singleton_ne_univ n (Set.univ_subset_iff.mp hX'X)).elim
      · have hkn : k = n := Set.mem_singleton_iff.mp (Set.singleton_subset_iff.mp hX'X)
        subst hkn
        exact Or.inr ⟨k, rfl, (val k).up_mem hY hY' hYY'⟩

end DomainTheory.NeighbourhoodSystems.Example43
