module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Truth
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NestedOrDisjoint

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NatDom
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

def memN (X : Set ℕ) : Prop := X = Set.univ ∨ ∃ n, X = {n}

theorem memN_singleton (n : ℕ) : memN ({n} : Set ℕ) := Or.inr ⟨n, rfl⟩

theorem memN_univ : memN (Set.univ : Set ℕ) := Or.inl rfl

theorem nestedOrDisjoint : NestedOrDisjoint memN := by
  rintro X Y (rfl | ⟨n, rfl⟩) (rfl | ⟨m, rfl⟩)
  · exact Or.inl (Set.Subset.refl _)
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inl (Set.subset_univ _)
  · by_cases h : n = m
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext k
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl hkm
      exact h hkm

end DomainTheory.NeighbourhoodSystems.NatDom

namespace DomainTheory.NeighbourhoodSystems.NatDom
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

abbrev N : NeighborhoodSystem ℕ :=
  NeighborhoodSystem.ofNestedOrDisjoint memN Set.univ Set.univ_nonempty memN_univ nestedOrDisjoint
    (fun _ => Set.subset_univ _)

@[simp] theorem N_mem {X : Set ℕ} : N.mem X ↔ memN X := Iff.rfl

@[simp] theorem N_master : N.master = (Set.univ : Set ℕ) := rfl

abbrev T : NeighborhoodSystem TwoToken.Token := Truth.T

def natElem (n : ℕ) : N.Element := N.principal (N_mem.mpr (memN_singleton n))

def predVal : ℕ → N.Element
  | 0 => N.bot
  | (k + 1) => natElem k

theorem singleton_nat_inj {n m : ℕ} (h : ({n} : Set ℕ) = {m}) : n = m := by
  have h1 : n ∈ ({n} : Set ℕ) := rfl
  rw [h] at h1
  exact h1

theorem univ_ne_singleton (n : ℕ) : (Set.univ : Set ℕ) ≠ {n} := by
  intro h
  have h1 : (n + 1) ∈ ({n} : Set ℕ) := h ▸ Set.mem_univ (n + 1)
  exact Nat.succ_ne_self n h1

theorem singleton_ne_univ (n : ℕ) : ({n} : Set ℕ) ≠ Set.univ := fun h => univ_ne_singleton n h.symm

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

def predMap : ApproximableMap N N := constLiftN N predVal

def succMap : ApproximableMap N N := constLiftN N (fun n => natElem (n + 1))

def zeroElt : N.Element := natElem 0

def zeroVal : ℕ → T.Element
  | 0 => Truth.trueElt
  | (_ + 1) => Truth.falseElt

def zeroMap : ApproximableMap N T := constLiftN T zeroVal

theorem N_bot_mem {X : Set ℕ} : N.bot.mem X ↔ X = Set.univ := NeighborhoodSystem.mem_bot N

theorem constLiftN_bot {β : Type*} (V : NeighborhoodSystem β) (val : ℕ → V.Element) :
    (constLiftN V val).toElementMap N.bot = V.bot := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hXmem, hrel⟩
    rw [N_bot_mem] at hXmem
    subst hXmem
    rcases hrel with ⟨_, rfl⟩ | ⟨k, hXk, _⟩
    · exact V.mem_bot.mpr rfl
    · exact (univ_ne_singleton k hXk).elim
  · intro hY
    rw [V.mem_bot] at hY
    subst hY
    exact ⟨Set.univ, N_bot_mem.mpr rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem mem_natElem_iff {n : ℕ} {Y : Set ℕ} :
    (natElem n).mem Y ↔ Y = Set.univ ∨ Y = {n} := by
  unfold natElem
  rw [mem_principal]
  constructor
  · rintro ⟨hY, hsub⟩
    rcases hY with rfl | ⟨m, rfl⟩
    · exact Or.inl rfl
    · have hnm : n = m := Set.mem_singleton_iff.mp (Set.singleton_subset_iff.mp hsub)
      subst hnm; exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨memN_univ, Set.subset_univ _⟩
    · exact ⟨memN_singleton n, subset_rfl⟩

theorem constLiftN_natElem {β : Type*} (V : NeighborhoodSystem β) (val : ℕ → V.Element) (n : ℕ) :
    (constLiftN V val).toElementMap (natElem n) = val n := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hXmem, hrel⟩
    rw [mem_natElem_iff] at hXmem
    rcases hrel with ⟨_, rfl⟩ | ⟨k, hXk, hY⟩
    · exact (val n).master_mem
    · rcases hXmem with rfl | rfl
      · exact (univ_ne_singleton k hXk).elim
      · have hnk : n = k := singleton_nat_inj hXk
        subst hnk; exact hY
  · intro hY
    exact ⟨{n}, mem_natElem_iff.mpr (Or.inr rfl), Or.inr ⟨n, rfl, hY⟩⟩

theorem predMap_bot : predMap.toElementMap N.bot = N.bot :=
  constLiftN_bot N predVal

theorem predMap_natElem_succ (k : ℕ) : predMap.toElementMap (natElem (k + 1)) = natElem k :=
  constLiftN_natElem N predVal (k + 1)

theorem predMap_natElem_zero : predMap.toElementMap (natElem 0) = N.bot :=
  constLiftN_natElem N predVal 0

theorem succMap_bot : succMap.toElementMap N.bot = N.bot :=
  constLiftN_bot N (fun n => natElem (n + 1))

theorem succMap_natElem (n : ℕ) : succMap.toElementMap (natElem n) = natElem (n + 1) :=
  constLiftN_natElem N (fun n => natElem (n + 1)) n

theorem predMap_succMap_natElem (n : ℕ) :
    predMap.toElementMap (succMap.toElementMap (natElem n)) = natElem n := by
  rw [succMap_natElem, predMap_natElem_succ]

theorem zeroMap_bot : zeroMap.toElementMap N.bot = T.bot :=
  constLiftN_bot T zeroVal

theorem zeroMap_natElem_succ (n : ℕ) : zeroMap.toElementMap (natElem (n + 1)) = Truth.falseElt :=
  constLiftN_natElem T zeroVal (n + 1)

theorem zeroMap_natElem_zero : zeroMap.toElementMap (natElem 0) = Truth.trueElt :=
  constLiftN_natElem T zeroVal 0

end DomainTheory.NeighbourhoodSystems.NatDom
